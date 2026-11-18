# A checked field supply for the arithmetic amplification

The paper uses totally real fields of dyadic degree with one fixed root discriminant. Its constants in the lattice count and the embedding-gap argument require only a uniform upper bound on root discriminant. The module MT/Tower.lean proves an unconditional supply in this form. For **every** natural n there is a totally real number field K with

$$
 [K:\mathbb Q]=2^n,\qquad |\operatorname{disc}(K)|\le 255255^{\,2^n}.
$$

The absolute bound 255255 is independent of n. Taking the positive degree-th root gives the uniform bound for the root discriminant. The fields can be chosen separately for each n. The formal statement does not claim that their root discriminants are exactly equal or that the chosen fields form a nested tower. For the lattice argument use 255255 in all bounds for the actual root discriminant. For example, dual separation by the inverse discriminant then gives a product lower bound of 255255⁻ᵏ. Thus this result supplies the degrees and estimates needed for the paper's argument. MT.FieldIntersections combines the lattice counts into the finite-set size and return estimates of Section 4.3.

## Where the dyadic degrees come from

The public Sawin theorem gives arbitrarily large degrees. An arbitrarily sparse sequence of degrees would be inadequate for the final all-radii lower bound. Its actual construction gives more information.

1. In Naganori Yamaguchi's formalization, the theorem ClassFieldTower.Sawin.exists_sawinInfinite_totallyReal_split_field supplies one infinite Galois extension inside the maximal totally real pro-2 extension with controlled ramification. Select a finite Galois layer E with degree at least 2ⁿ. Its admissibility gives a 2-group of automorphisms, total reality, and the finite-ramification hypotheses for the bound |disc(E)|≤255255^[E:ℚ]. MT/Tower.lean adapts this extraction from the proof of sawin_totally_real_tower. [Pinned upstream source](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/blob/2df65101324c0625904b6becbff317df88d8c3de/Nyll/SawinTotallyRealTowers/SawinTotallyRealTower.lean)
2. Write |Gal(E/ℚ)|=2ʲ, with j≥n. Mathlib's Sylow.exists_subgroup_card_pow_prime_of_le_card yields a subgroup H of order 2^(j−n). By the fixed-field theorem [E:Eᴴ]=|H|, so the fixed field F=Eᴴ has [F:ℚ]=2ⁿ. Total reality descends to an intermediate field. This is MT.Tower.exists_dyadic_subfield.
3. The relative different-ideal formula shows that |disc(F)|^[E:F] divides |disc(E)|. Since [E:F]>0 and [E:ℚ]=[F:ℚ][E:F], taking powers gives |disc(F)|≤255255^[F:ℚ]. This is MT.Tower.subfield_discr_bound. [Mathlib discriminant and different](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/NumberTheory/NumberField/Discriminant/Different.lean)
4. MT.Tower.dyadic_totally_real_fields combines these results. The import uses Yamaguchi's Apache-2.0 project, written with OpenAI Codex, at commit 2df65101324c0625904b6becbff317df88d8c3de. The MT-specific descent and its explanatory material were developed by AI. The Formal Conjectures file for Erdős Problem 90 points to an earlier verified submission and itself contains placeholder proofs. This project imports the underlying proof library. [Benchmark source](https://github.com/google-deepmind/formal-conjectures/blob/8323e878b83fcd7f4a448256069352a265460d75/FormalConjectures/ErdosProblems/90.lean) · [Upstream authorship and license](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/tree/2df65101324c0625904b6becbff317df88d8c3de)

## Reproduce the tower check

The upstream and MT repositories use Lean 4.35.0 and mathlib commit 56a005855ea17e0b0958f73ec801ae140b0a1679. From the project root on Linux x86-64 (including WSL), with Lean, Lake, Python 3, Git and curl installed, run

```sh
lake exe cache get
./scripts/fetch-tower-cache.sh
./scripts/verify-tower.sh --replay
```

The first command obtains mathlib. The second downloads the exact Nyll release, verifies the three archive and manifest digests, and invokes upstream's source- and compiler-matched cache validation. A test on a separate clean worktree restored 19,467 compiler artifacts. The third command compiles MT/Tower.lean, prints the actual axiom dependencies, and with the replay flag exports the transitive proof for additional kernel checks. The printed declarations are listed in checks/TowerAxioms.lean. See the local axiom output in [checks/tower-kernel.txt](../checks/tower-kernel.txt), the cache receipts in [checks/tower-cache.txt](../checks/tower-cache.txt) and [checks/tower-cache-clean.txt](../checks/tower-cache-clean.txt), and [the full verification record](verification.md). The local tower-only export was interrupted with exit status 130 before it produced output. Neither standalone checker replayed a tower-only export in this run. The exact command and interruption are recorded in [checks/tower-export.txt](../checks/tower-export.txt). The complete main-theorem proof imports this same dependency, so a successful independent replay of the main proof also checks the tower proof used here. Cache metadata and hashes establish archive and source identity; the replay checks address proof validity. The upstream verification job also used the Lean kernel and NanoDa. [Upstream run for the pinned commit](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/actions/runs/43177526584)

## Ordinary Lake build from pinned source

In a fresh clone, open a terminal in the directory that contains `lean-toolchain` and `lake-manifest.json`. Run these commands in order. The middle command isolates the large number-field dependency. Lake can reuse its outputs for the project build and for subsequent edits to `Solution.lean`.

```sh
lake exe cache get
lake build @Nyll/+Nyll.SawinTotallyRealTowers.SawinTotallyRealTower
lake build MT Solution Challenge
```

The first command fetches Mathlib's precompiled modules for the pinned revision. The second builds the exact import used in `MT/Tower.lean`, including its transitive Nyll modules. The third checks this project's sources. `lake build` alone selects the configured default target, `Solution`. The explicit final command also builds the development library and the independent statement. Keep the committed manifest to reproduce the dependency revisions.

The Linux proof release includes 19,467 validated files. Its packaging rules omit the Lean 4.35.0 compiler outputs `.ir` and `.ir.sig` under `.lake/build/lib/lean`. Lake normally regenerates missing compiler outputs when building a module. The time saved by importing a published proof directly therefore differs from the time for an ordinary source build. Upstream's Actions cache contains more files, but access uses GitHub's repository-scoped cache service. Its separately downloadable workflow artifacts contain verification reports. The local tower compilation and axiom report used the exact publisher release. The separate tower-only replay attempt is documented above. [Upstream export rules](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/blob/2df65101324c0625904b6becbff317df88d8c3de/.github/scripts/cache-export.py) · [Published assets](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/releases/tag/cache-2df65101324c0625904b6becbff317df88d8c3de-linux-x86_64) · [GitHub cache access](https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching#restrictions-for-accessing-a-cache)

## GitHub build time and caching

Budget several hours for the first hosted source build. The upstream run on the pinned revision completed in 2 h 02 min 41 s and reused incremental library outputs. For a heavier observed workload on 11 November, three upstream source-build stages took 44 min 20 s, 1 h 53 min 38 s and 14 min 12 s. With setup and verification, that workflow took 3 h 43 min 12 s. Those measurements describe upstream runs with their own source and cache histories. They give a planning range for a first build on comparable hardware. [Pinned run](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/actions/runs/43177526584) · [Longer build](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/actions/runs/42962107161) · [Stage timestamps](https://api.github.com/repos/n-yamaguchi-0729/SawinTotallyRealTowers/actions/runs/42962107161/jobs?per_page=100)

The workflow allows six hours for the dependency job. On a cache miss it builds the Nyll source import closure with the upstream thread setting, then saves the complete `.lake/packages/Nyll/.lake/build` directory. Its cache key covers the runner family, architecture, toolchain, Lake manifest and package configuration. The build and Comparator jobs restore exactly that dependency cache and build this project's Lean files in their own checkouts. The workflow also runs the publisher's release replay independently. The new workflow must run on the destination repository to establish its actual cold time and hosted verification result. [Workflow](../.github/workflows/lean.yml) · [Dependency setup](../.github/actions/lean-dependencies/action.yml)

The workflow and composite action parsed locally as YAML. Running `actionlint -no-color .github/workflows/lean.yml` (actionlint 1.7.7) exited 0 with no diagnostics. This was a static check of the workflow configuration.
