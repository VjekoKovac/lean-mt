#!/usr/bin/env python3
"""Build the two sides in separate sandboxes and compare their checked exports.

Run from any directory after fetching the pinned dependency caches. This is an
additional source-to-export check for x86_64 Linux. Palomar can still run its
normal source build and Comparator. Requires Python 3, git and bubblewrap.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile


REPO = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
# Lean 4.35.0, Lake/CLI/Check.lean, builtinTargets and primitiveTargets.
QUOT = "Quot Quot.mk Quot.lift Quot.ind".split()
PRIMITIVES = (
    "Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble "
    "Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat "
    "List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
).split()
MILESTONES = [
    "MT.localConstant_mono", "MT.powerLoss_of_transfer_and_amplification",
    "MT.Seed.exists_bounded_seed",
]


def command(args, **kwargs):
    print("$ " + shlex.join(map(str, args)), flush=True)
    try:
        return subprocess.run(list(map(str, args)), check=True, **kwargs)
    except subprocess.CalledProcessError as error:
        if error.stderr:
            if isinstance(error.stderr, bytes):
                sys.stderr.buffer.write(error.stderr)
            else:
                sys.stderr.write(error.stderr)
        raise


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def dependencies():
    manifest = json.loads((REPO / "lake-manifest.json").read_text())
    paths = {}
    for package in manifest["packages"]:
        name = package["name"]
        package_dir = (REPO / manifest["packagesDir"] / name).resolve(strict=True)
        revision = subprocess.check_output(
            ["git", "-C", str(package_dir), "rev-parse", "HEAD"], text=True
        ).strip()
        if revision != package["rev"]:
            raise ValueError(f"Unexpected checkout of {name} at {revision}")
        compiled = package_dir / ".lake/build/lib/lean"
        print(f"Dependency {name} {revision}", flush=True)
        if compiled.is_dir():
            paths[name] = compiled
    return paths


def snapshot(module, stage):
    source = stage / "src"
    source.mkdir(parents=True)
    paths = [REPO / f"{module}.lean"]
    if module == "Solution":
        paths.extend((REPO / "MT").rglob("*.lean"))
        paths.append(REPO / "MT.lean")
    for path in paths:
        relative = path.relative_to(REPO)
        dest = source / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(path.read_bytes())
    return source


def export_side(module, stage, toolchain, paths, config):
    source = snapshot(module, stage)
    objects = stage / "objects"
    objects.mkdir()
    args = [
        "bwrap", "--unshare-all", "--unshare-user", "--disable-userns", "--new-session", "--die-with-parent",
        "--cap-drop", "ALL", "--clearenv", "--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp",
        "--ro-bind", "/lib", "/lib", "--ro-bind", "/lib64", "/lib64",
        "--ro-bind", str(toolchain), "/opt/lean", "--ro-bind", str(source), "/src",
        "--dir", "/deps", "--chdir", "/src", "--setenv", "HOME", "/tmp",
        "--setenv", "PATH", "/opt/lean/bin", "--setenv", "LEAN_NUM_THREADS", "1",
        "--setenv", "LEAN_ABORT_ON_PANIC", "1", "--setenv", "LANG", "C.UTF-8",
    ]
    search = ["/out"]
    for name, path in paths.items():
        if module == "Challenge" and name == "Nyll":
            continue
        mountpoint = "/deps/" + name
        args.extend(["--ro-bind", str(path), mountpoint])
        search.append(mountpoint)
    args.extend(["--setenv", "LEAN_PATH", ":".join(search)])

    def sandbox(argv, writable=False, **kwargs):
        access = "--bind" if writable else "--ro-bind"
        return command(args + [access, str(objects), "/out", "--"] + argv, **kwargs)

    built = set()
    def compile_module(name):
        if name in built:
            return
        path = Path(*name.split(".")).with_suffix(".lean")
        src_name = str(Path("/src") / path)
        info = sandbox(["/opt/lean/bin/lean", "--deps-json", src_name], capture_output=True)
        header, = json.loads(info.stdout)["imports"]
        if header["errors"]:
            raise ValueError(f"Could not parse imports of {name}: {header['errors']}")
        for entry in header["result"]["imports"]:
            dependency = entry["module"]
            if dependency == "MT" or dependency.startswith("MT."):
                compile_module(dependency)
            if dependency in {"Challenge", "Solution"}:
                raise ValueError(f"Unexpected cross-import {name} -> {dependency}")
        print(f"Source {module} {sha256(source / path)}  {path}", flush=True)
        (objects / path).parent.mkdir(parents=True, exist_ok=True)
        out_name = str(Path("/out") / path.with_suffix(".olean"))
        sandbox(["/opt/lean/bin/lean", "-j1", "-R", "/src", "-o", out_name, src_name], writable=True)
        built.add(name)

    compile_module(module)
    legal = config["permitted_axioms"]
    decls = (QUOT if "Quot.sound" in legal else []) + config["theorem_names"] + legal + PRIMITIVES
    export = stage / "proof.ndjson"
    # stdout goes to the host-owned file. The exporter sees only read-only source,
    # its own read-only objects, read-only dependency objects, and a disposable /tmp.
    with export.open("xb") as output:
        sandbox(["/opt/lean/bin/leanexport", module, "--", *decls], stdout=output)
    print(f"Export {module} {sha256(export)} ({export.stat().st_size} bytes)", flush=True)
    return export


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", nargs="?", choices=["full", "milestone"], default="full")
    mode = parser.parse_args().mode
    os.chdir(REPO)
    os.environ["LEAN_ABORT_ON_PANIC"] = "1"
    os.environ.setdefault("LEAN_NUM_THREADS", "1")
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()).resolve()
    expected = (REPO / "lean-toolchain").read_text().strip()
    if expected != "leanprover/lean4:v4.35.0":
        raise ValueError("Review the primitive export list when updating the pinned Lean version")
    version = command([prefix / "bin/lean", "--version"], capture_output=True, text=True).stdout
    if "version 4.35.0," not in version:
        raise ValueError(f"Unexpected compiler: {version}")
    print(version.strip(), flush=True)
    command([prefix / "bin/lake", "--version"])
    config = json.loads((REPO / "comparator.json").read_text())
    if (set(config) != {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
            or config["challenge_module"] != "Challenge" or config["solution_module"] != "Solution"
            or config["theorem_names"] != ["MT.powerlossMT"]
            or not set(config["permitted_axioms"]) <= ALLOWED):
        raise ValueError("Invalid canonical Comparator configuration")
    if mode == "milestone":
        config["theorem_names"] = MILESTONES
    config["external_kernels"] = {
        "con-ron": [str(prefix / "bin/con-ron")], "nanoda": [str(prefix / "bin/nanoda_bin")],
    }
    for key in ["leanexport", "leanchecker", "con-ron", "nanoda_bin"]:
        if not os.access(prefix / "bin" / key, os.X_OK):
            raise FileNotFoundError(prefix / "bin" / key)
    paths = dependencies()
    print(f"Configuration {json.dumps(config, sort_keys=True)}", flush=True)
    for fname in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "comparator.json"]:
        print(f"Input {sha256(REPO / fname)}  {fname}", flush=True)
    with tempfile.TemporaryDirectory(prefix="mt-comparator-") as temp:
        scratch = Path(temp)
        cfg_path = scratch / "comparator.json"
        cfg_path.write_text(json.dumps(config))
        ch = export_side("Challenge", scratch / "challenge", prefix, paths, config)
        sol = export_side("Solution", scratch / "solution", prefix, paths, config)
        command([prefix / "bin/lake", "comparator", "--config", cfg_path,
                 "--challenge-from-export", ch, "--solution-from-export", sol])


if __name__ == "__main__":
    main()
