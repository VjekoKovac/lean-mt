# Full theorem verification

The target is `MT.powerlossMT : MT.PowerLoss`. The independently written specification is in `Challenge.lean`. A separate AI reviewer compared it with arXiv v1. The solution imports the two proved propositions and the deduction of Theorem 1.3. A fresh solution-only Lean process printed the target and exactly the three allowed axioms. [AI statement review](../docs/review-fidelity.md) · [Axiom report](full-direct-axioms.txt)

## From the reviewed source to the two exports

| Input | Project compilation | Export size | SHA-256 |
| --- | --- | ---: | --- |
| Challenge | `Challenge.lean` | 214,088,735 bytes | `756b704936c1a899c78e77b77d76351f638282bb728fc884e6e5f8bab4f35898` |
| Solution | 53 project modules ending with `Solution.lean` | 1,418,290,040 bytes | `e2ce5617c2cbaceb3288455a0ae7a4dc62b1eeb69fb6a42b0224d02c9afb30d0` |

Each side started in a separate source directory with an empty output directory. Each compiler could read its side's sources and the pinned dependency objects. Only the producing compiler could write its object directory. The exporters received read-only mounts of their own objects, sources and dependencies. Each ran in a separate process with `LEAN_ABORT_ON_PANIC=1`. The Challenge had no access to the Solution modules or the Nyll proof cache. The Solution had no access to the Challenge. The package pins and the archived commands identify the Lean 4.35.0 release, mathlib, Nyll and each imported dependency. [Pinned inputs](comparator-inputs.sha256) · [Challenge build and export](full-challenge-export.txt) · [Solution build and export](full-solution-export.txt) · [Export hashes](full-exports.sha256)

Run the following in the project root to verify the local files against the recorded inputs.

```sh
sha256sum --check checks/comparator-inputs.sha256
```

The export target includes the theorem, the three permitted axioms, the quotient primitives and Lean's built-in reduction primitives. The primitive list comes from `Lake/CLI/Check.lean` in pinned Lean 4.35.0. It can be seen verbatim in both export logs.

## Full Comparator results

The official `lake comparator` accepted the unconditional `MT.powerlossMT` against the independently exported Challenge. Con-ron accepted 131,949 reachable declarations in verified mode. NanoDa and the default Lean kernel also accepted the solution export. Lake then reported `Your solution is okay!` and exited 0. The command used the shipped theorem, modules and three-axiom allowlist, plus the two additional external kernel commands printed in its configuration. [Three-kernel Comparator transcript](full-comparator.txt)

A second run used a byte-for-byte copy of the shipped `comparator.json` with Lake's ordinary bubblewrap sandbox in an offline Debian guest. The guest independently checked both archive hashes. Lake reached `Running Lean default kernel on solution`. In the pinned release, `verifyMatch` first runs `compareAt` and `checkAxioms`, so this marker records successful statement and allowlist checks for the actual target. The operator then stopped the redundant emulation after the three-kernel run had completed. The stock guest produced no final kernel verdict. [Ordinary-sandbox partial transcript](full-comparator-standard-partial.txt)

## Native execution environment

The native Linux host denied the networking operation bubblewrap uses to configure loopback in a new network namespace. The native evidence run therefore placed each compiler and exporter, and later the complete official Comparator and its kernel children, in externally created bubblewrap environments. All capabilities were dropped, the environment was cleared, nested user namespaces were disabled, and the judge had a private PID, UTS, IPC and user namespace. Its files, executable tools, configuration and both exports were read-only. Each sandbox had disposable temporary storage. The host denied socket creation, socket connection and communication syscalls, and io_uring through a libseccomp filter. The checker log includes the complete outer command, its task-specific mount paths, and Lake's warning that its internal per-child sandbox was disabled. The outer enclosure is distinct from Lake's default sandbox.

The following recreates the x86-64 seccomp program. The two native builds and the checker used an identical filter. Binary digests, the host networking diagnostic, and the regenerated filter digest are in [the toolchain transcript](full-toolchain.txt). Open the binary on the file descriptor named by `--seccomp` when replaying the archived bubblewrap invocation.

```sh
python3 checks/make-native-network-filter.py /tmp/mt-network-denied.bpf
sha256sum /tmp/mt-network-denied.bpf
# 02b378ee4adcd8e0fd419e1276a6b22d350967d22e08e6fe1098ff12f30f24f7
```

## Reproduce with ordinary Linux isolation

Use an x86-64 Linux system with unprivileged user namespaces and bubblewrap, Python 3, git and the pinned Lean toolchain. From the project root, run these commands.

```sh
lake exe cache get
./scripts/fetch-tower-cache.sh
python3 scripts/verify-from-exports.py
```

The script compiles and exports both sides in separate default Linux namespaces, then runs the official Comparator with its ordinary per-child sandbox and the bundled con-ron, NanoDa and Lean kernels. The temporary exports are removed automatically. A small arithmetic fixture exercised this public script end to end, including all three kernels, under ordinary bubblewrap in an offline Debian guest. The fixture's transcript identifies its elementary theorem separately from the paper's full target. [Public runner fixture](from-exports-runner-smoke.txt)
