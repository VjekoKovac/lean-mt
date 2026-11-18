# What the checks establish

The paper’s main target is `MT.powerlossMT : MT.PowerLoss`. The independently reviewed `Challenge.lean` states it. The locally compiled `Solution.lean` proves the unconditional theorem by applying the checked Section 5 deduction to `MT.analyticTransfer` and `MT.arithmeticAmplification`. The local elaboration and the separate comparison against the independent specification have distinct verification records. [Main-theorem check](../checks/main-axioms.txt)

Lean reports that `MT.powerlossMT` depends on exactly `propext`, `Classical.choice`, and `Quot.sound`. The broader axiom scan accepted 432 exported local theorem and axiom declarations. The proof-source scan found the four intentional placeholders in `Challenge.lean`.

**Full Comparator verdict: accepted (exit 0).** The official Comparator matched the unconditional solution declaration against the separately reviewed Challenge under the configured axiom policy. Con-ron accepted 131,949 declarations in verified mode. NanoDa and Lean's default kernel also accepted. The host run enclosed the judge in a read-only, network-denied outer sandbox and disabled Lake's nested sandbox. The command, warning and verdict are preserved together. [Raw transcript](../checks/full-comparator.txt) · [Environment and export details](../checks/full-verification.md)

A supplementary offline Linux run used the byte-identical shipped `comparator.json` and Lake’s standard child sandboxes. After verifying both archive hashes it passed statement matching and the permitted-axiom test, and printed `Running Lean default kernel on solution`. This additional, emulated replay was stopped at that point. The completed three-kernel verdict above concerns the same exported proof. No destination GitHub Actions run or Palomar registration has been performed.

The complete local build of `Solution.lean` used the pinned toolchain and upstream’s source-matched proof cache for Nyll. A separate source checkout and export of each side give the Comparator evidence described below. The standalone [Lean axiom report](../checks/axioms.txt) and the [expanded theorem and witness check](../checks/main-review.txt) concern the unconditional theorem.

## Reproduce the evidence

The ordinary build below recompiles any missing parts of the pinned upstream number-field development. For the shorter beginner example in the README, only the Mathlib cache and the `MT.Constant` target are required.

```bash
lean --version
lake --version
lake exe cache get
lake build MT Solution Challenge
lake env lean Audit.lean
lake env lean checks/AllAxioms.lean
./scripts/verify-comparator.sh full
```

On x86-64 Linux with working bubblewrap, this alternative fetches the published, hash-checked proof artifacts for the tower, compiles the project sources independently on each side, exports only the requested theorem and its transitive dependencies, then invokes the bundled Comparator. The generated NDJSON files are temporary. The `full` mode requests the unconditional theorem.

```bash
lake exe cache get
./scripts/fetch-tower-cache.sh
python3 scripts/verify-from-exports.py full
```

The exact commands used on the verification host, and the containment settings for each run, are given in the [full verification transcripts](../checks/full-verification.md). The source and NDJSON SHA-256 digests identify the proofs that were actually checked.

`Audit.lean` issues individual `#print axioms` commands on the principal mathematical declarations in the solution environment. `checks/AllAxioms.lean` also enumerates the exported theorem and axiom declarations originating in the imported project modules and rejects any transitive axiom outside the allowlist. The independent `Challenge` is absent from their imports. The tower has its own script, archive identity check, and axiom reports. The standalone tower-only replay was interrupted. Its proofs are transitive dependencies of the main theorem.

| Evidence | Scope |
| --- | --- |
| [Independent challenge and solution exports](../checks/full-verification.md) | Separate compilation, exported theorem, exact configuration, and individual checker outputs. [Archive hashes](../checks/full-exports.sha256) |
| [Project build](../checks/build.txt) | Build of the supporting modules and independent Challenge from the pinned sources. The final solution is compiled and queried in [the main axiom report](../checks/main-axioms.txt). |
| [Project theorem audit](../checks/all-axioms.txt) | Programmatically checks the transitive axioms for all exported theorem and axiom declarations originating in the project modules that MT and Solution import. |
| [Local proof-source scan](../checks/source-policy.txt) | Source requirements, text scan of proof markers, and the four intentional specification placeholders. |
| [Exact inputs](../checks/sources.sha256) | Run `sha256sum --check checks/sources.sha256` from the project root to identify the delivered Lean and Lake files. |
| [Source comparison](../checks/source.txt) | The attached TeX is byte-identical to the versioned manuscript retrieved from arXiv. |
| [Beginner example](../checks/first-example.txt) | The exact bounded-seed statement and its transitive axioms, from the solution environment. |
| [Tower reports](../checks/tower-kernel.txt) | Upstream inputs and the local theorem for every exact dyadic degree. See the [tower guide](tower.md) for the compiled archive and independent replay. |
| [Poisson proof](../checks/poisson-build-and-axioms.txt) | Multidimensional lattice Poisson summation for Schwartz functions, ported with attribution. |
| [Metadata validation](../checks/metadata.txt) | YAML syntax and the pinned public schema. This checks the structure of the metadata file. |
| [Analytic proof and independent type reconstruction](review-analytic.md) | Proposition 3.1, including the general affine chart and the fixed positive constants. The [actual output](../checks/analytic-review.txt) shows the reported axioms. |
| [Arithmetic proof and independent restatement](review-arithmetic.md) | Proposition 4.1 with the denominator cleared, its positivity proved, the two sets retained, every dyadic degree, and every test strip. [Actual output](../checks/arithmetic-review.txt) |
| [Expanded main theorem](../checks/MainReview.lean) | The surface, X-ray and extension conventions are expanded, and individual test-pair witnesses are extracted. [Actual output](../checks/main-review.txt) |
| [Statement, proof and clarity review](review-fidelity.md) | An independent AI review of the challenge definitions, Section 5 and the beginner instructions. No human review is recorded. |

The three-axiom policy permits `propext`, `Classical.choice` and `Quot.sound`. Among the numerical steps, `norm_num` checks rational coefficients, `omega` checks integer inequalities, and `ring` and `nlinarith` produce polynomial identities and estimates. The dyadic bracketing, infinite Fourier integrals, real powers and logarithms are exact statements over the corresponding Lean types. No floating-point experiment is used to substantiate them.

## What the Comparator checks

An ordinary module build typechecks the declarations supplied by the developer. The root Comparator additionally requires that the independent challenge and the solution export the named unconditional theorem. The milestone run requests radius monotonicity, the bounded seed lemma, and the conditional Section 5 deduction. The milestone includes none of the later optional supporting lemmas. These have their own build and axiom evidence. Only dependencies used transitively by the main theorem enter its full proof export. The supporting-module build and the broader axiom audit also cover additional lemmas.

## Mathematical decisions for an author to review

* The chart and measure conventions, and the absolute-integrability core used to prove a lower bound for the full extension operator, are in the [statement guide](statement.md).
* The analytic development uses constant-amplitude indicators on small surface patches. Bi-Lipschitz chart estimates bound their normalized surface areas in both directions. This avoids an exact graph Jacobian computation. [Analytic proof ledger](analysis.md)
* The proof of a sufficient field supply uses a uniform upper bound for root discriminants at all dyadic degrees. The source uses Martinet's tower. This project reuses Yamaguchi's proof of Sawin's construction. [Arithmetic ledger](arithmetic.md) · [Tower proof and attribution](tower.md)
* Within the overlap argument full side lengths must be converted back to half-widths before applying the box count. The ledger specifies where a fixed factor of two is absorbed. [Arithmetic ledger](arithmetic.md)
* The authors in the metadata match arXiv v1 as requested. Vjekoslav Kovač is the proposed repository maintainer and Apache-2.0 the proposed project license. A human maintainer should confirm these publication choices. [Submission guide](submission.md)
