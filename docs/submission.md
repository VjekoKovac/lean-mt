# From the working project to a Palomar submission

The root configuration selects the theorem labelled `thm:powerlossMT` in arXiv:2611.22465v1. The [verification record](verification.md) gives the status of the proof, axiom report and external checks at this snapshot. Before submitting the theorem to the registry, inspect the **full** comparison at the commit you intend to cite.

The official Comparator accepted the full theorem on the separately built Challenge and Solution exports. Its output records acceptance by con-ron (131,949 declarations), NanoDa and the default Lean kernel, followed by `Your solution is okay!` and exit status 0. This run used an outer read-only bubblewrap sandbox with network access blocked. Lake’s internal child sandbox was disabled, and the corresponding warning is preserved in the log. Consult the evidence before selecting a submission commit. [Full verification scope](../checks/full-verification.md) · [Comparator output](../checks/full-comparator.txt)

## Reading a comparison

`Challenge.lean` is the mathematical specification. Read its definitions as well as the final declaration. A deliberate `by sorry` in this file tells Lean to display the intended theorem before any proof has been supplied. Open `Solution.lean` separately to see the proofs and their imports. The solution must be independent of the Challenge. The two files describe the same named theorem in *different* environments. Importing both into the same file would cause their declarations to collide.

The repository's ordinary `lake build` can succeed during development even when a target is absent. A declaration of type `Prop` defines a sentence. A theorem whose type is that sentence supplies a proof. The root `comparator.json` names `MT.powerlossMT`, so its check requires a solution proof of that very sentence. The optional local milestone check selects three theorems. `MT.localConstant_mono` proves that enlarging the permitted weight radius increases the supremum. `MT.Seed.exists_bounded_seed` constructs the bounded integer seed whose subset sums are noncollinear in triples. `MT.powerLoss_of_transfer_and_amplification` proves the conclusion assuming the two paper propositions. The milestone comparison establishes those three declarations. Replaying the main theorem requires full mode.

## Run the checks

Install VS Code and the official Lean 4 extension (`leanprover.lean4`), then complete the setup guide to install Elan. Open the unpacked *folder* containing `lean-toolchain` and `lakefile.toml`. Elan uses that folder's Lean version. For Comparator, use Linux with functional bubblewrap namespaces. GitHub Actions supplies a Linux runner if you develop on Windows or macOS. The commands below use Bash. In VS Code, open **Terminal → New Terminal** in the project folder. WSL is convenient on Windows. [Official Lean installation guide](https://lean-lang.org/install/)

```bash
lean --version
lake --version
lake exe cache get
lake build @Nyll/+Nyll.SawinTotallyRealTowers.SawinTotallyRealTower
python3 scripts/check-lean-sources.py
lake build MT Solution Challenge
```

Mathlib’s precompiled modules require several GiB. The exact Nyll input for the number-field tower has a much larger first source build, so let it finish before building the project. The repository’s CI builds this dependency once and shares its exact-key cache among the verification jobs. Warm runs may reuse earlier checked modules. See the [tower setup](tower.md) for the separately downloadable proof cache and its contents. The Challenge produces intentional specification-placeholder warnings. Open the files from the project root so editor imports resolve. In a proof, place the cursor after a tactic to read the current assumptions and goal in the Lean Infoview.

To see a verified result before attempting the full target, run the following in the same terminal. The first line after the import asks Lean to display the seed theorem's type. The second displays its axiom dependencies.

```bash
lake env lean --stdin <<'LEAN'
import Solution
#check MT.Seed.exists_bounded_seed
#print axioms MT.Seed.exists_bounded_seed
LEAN
```

Use these two **separate** Comparator commands.

```bash
./scripts/verify-comparator.sh milestone
./scripts/verify-comparator.sh full
```

The runner reads the same checked-in config in each mode, prints all theorem names it will compare and writes a temporary configuration to register the bundled NanoDa and con-ron kernels, following the official template. It invokes `lake comparator` in its normal sandbox. The three permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. The solution must have no transitive dependency on any other axiom. Lean tactics such as `norm_num`, `omega` and `ring` generate proof terms checked by the kernel.

In VS Code, `#print axioms MT.localConstant_mono` displays the assumptions used by the monotonicity proof. Inspect the full target in a fresh file importing the solution, or paste the following into the terminal.

```bash
lake env lean --stdin <<'LEAN'
import Solution
#print axioms MT.powerlossMT
LEAN
```

Consult the [verification record](verification.md) to distinguish runs at different stages of the development. Keep the exit status and complete output of the actual commands used for release. With shells that support it, start with `set -o pipefail` before piping output into `tee`. A failed comparison due to a missing solution theorem is an open mathematical obligation. A failure to launch bubblewrap is a host problem and makes no judgment about the mathematics.

For a second reading of the mathematics, run these short reviewer files after the build. The main review first expands the statement, then extracts an individual integrable function and weight at each sufficiently large radius.

```bash
lake env lean checks/AnalyticReview.lean
lake env lean checks/ArithmeticReview.lean
lake env lean checks/MainReview.lean
```

### Rebuilding and comparing proof exports

On x86_64 Linux an additional script can avoid rebuilding the Nyll dependency from source. Use a clean checkout and a host that permits bubblewrap namespaces. After the two cache downloads below, it copies current project sources into independent Challenge and Solution builds, exports the selected theorem from each, records their hashes, and passes both files to the official Comparator. The kernels check the exported proof terms. Archive hashes alone only identify the downloaded files.

```bash
lake exe cache get
./scripts/fetch-tower-cache.sh
python3 scripts/verify-from-exports.py full
```

Use the normal source-build command above when following registry instructions. The [verification record](verification.md) identifies which checking route ran locally.

The metadata can be checked independently against the pinned community schema. In a Python virtual environment, run `python -m pip install PyYAML==6.0.3 jsonschema==4.26.0`, then `python scripts/verify-metadata.py`. This checks YAML structure; the review record and the Lean logs supply the evidence for its mathematical claims.

## Publish and submit the finished theorem

1. Review the definitions in `Challenge.lean` directly against the versioned source. Record the reviewer's identity, whether the reviewer was human or AI, the commit, the questions checked and any remaining qualifications.
2. Inspect the proof of the full theorem through `Solution.lean` with the exact signature in the Challenge. Run the full build, the axiom report and the **full** Comparator command. Record the names of the kernels that actually accepted the export.
3. Update `formalization.yaml` to describe the verified mathematical result, actual coverage, source, authorship and reviews. The draft names the six authors in the arXiv ordering and proposes Vjekoslav Kovač as the maintainer. Confirm the maintainer and repository licence before public release. The draft uses the template's Apache-2.0 for the new code. The arXiv source is cited separately under CC BY 4.0.
4. Create an empty public GitHub repository in the intended account or organization. On GitHub choose **Add file → Upload files**, or commit the unpacked project with Git from its root. Include the hidden `.github/workflows/` and the checked-in `lake-manifest.json`. Exclude `.lake/` and all generated binaries. A command-line upload to a newly created empty repository can use `git init -b main`, `git add .`, `git commit -m "Formalize the local MT power-loss theorem"`, `git remote add origin <the URL copied from GitHub>`, and `git push -u origin main`. Replace the angle-bracketed text with the real repository URL.
5. On the GitHub **Actions** tab inspect the independent build and the full Comparator job for the commit to submit. Run `git rev-parse HEAD` to obtain its full 40-character SHA. Record the commit, build log, axiom output and full comparison. A code or metadata change requires checking and using the new SHA.
6. At the submission form, enter the public repository as `owner/name`, paste the exact commit SHA and select the repository-relative path `comparator.json`. Complete the authorship/authorization questions as the submitting maintainer. Review the preflight, mechanical verification and editorial results before choosing whether to register the result. The example entry's identifier belongs to a different paper.

[Palomar submission form](https://submit.palomar-registry.org/) · [Current submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md) · [Reference registration](https://palomar-registry.org/entry?id=PALOMAR-2026-10-21-000004&version=1)

## Reused code and layout

The source-file preflight `scripts/check-lean-sources.py` is from PalomarTemplate at commit `2891de4c48955af824969a263d31b25e7a9a1406`, Apache-2.0. The Comparator runner adapts the same template's verifier to offer an explicitly named milestone and to leave cache retrieval to the caller. The workflow uses the template's pinned Lean/Linux setup and adds an exact-key cache for its pinned Nyll dependency. The DFR repository motivated keeping the statement, proof and blueprint separately readable. No DFR theorem is used in this project.

[Template at the cited commit](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406) · [DFR repository](https://github.com/roos-j/lean-dfr) · [Metadata schema](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e) · [Versioned paper](https://arxiv.org/abs/2611.22465v1)
