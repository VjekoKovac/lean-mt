# Proof sources and attribution

The mathematical source for the MT theorem and its proof order is the six-author paper arXiv:2611.22465v1. The code credits below distinguish an imported or ported Lean argument from the paper's construction. [Paper](https://arxiv.org/abs/2611.22465v1)

## Multidimensional lattice Poisson summation

`MT/Upstream/Poisson.lean` ports the Formal Frontier Team's `DedekindZeta/PoissonSummation.lean` from `mathlib-initiative/sum_product` at commit `80e4127a67742659d521466204c6d2d7e0ca2b3f`. The upstream copyright and Apache-2.0 notice are retained; the repository root contains the Apache-2.0 licence. The source snapshot used Lean `v4.31.0-rc1`. The port uses Lean `v4.35.0`, module visibility for the declarations, updated measure-map and fundamental-domain arguments, and the same mathematical theorem name and formula. [Upstream file at the cited commit](https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean) · [Upstream licence](https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/LICENSE)

For a full-rank discrete lattice $L$ in a finite-dimensional real inner-product space and a complex-valued Schwartz function $f$, `DedekindZeta.PoissonSummation.tsum_eq_tsum_fourier` identifies $\sum_{v\in L} f(v)$ with $\operatorname{covol}(L)^{-1}\sum_{w\in L^*}\widehat f(w)$. The Fourier transform uses the $-2\pi i$ convention. Section 4 applies precisely this identity to a translated, anisotropically dilated product of bumps. A smooth compactly supported normalized bump is an allowed choice in the paper and is Schwartz. The triangular-bump example itself requires a nonsmooth extension or limiting argument. Positivity, summability of the relevant majorant, the number-field dual product bound, the dyadic estimate and the comparison to the indicator of a box are additional ingredients in the source's lattice count.

## Mathlib and Lean

Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0); its transitive pins are recorded in `lake-manifest.json`. The geometric model reuses `Measure.euclideanHausdorffMeasure`, volume in Euclidean space, the Fréchet derivative, complex Bochner integration, nonnegative integration, essential suprema and $L^p$ seminorms. The reference measures, graph hypotheses and the curvature hypothesis are reviewed in [the statement audit](review-fidelity.md). [Mathlib snapshot](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)

The seed argument uses Mathlib's finite-grid polynomial evaluation and degree bounds. The appendix norm argument uses Mathlib's product over infinite places for number field embeddings and the integral norm in the ring of integers. Source theorem names and their roles are recorded in [the seed blueprint](seed.md) and [the arithmetic blueprint](arithmetic.md). Section 5 uses Mathlib's `exists_nat_pow_near` to bracket a real number between successive dyadic powers and `Real.rpow_def_of_pos` for the exponent calculation. The verification scripts' provenance is in [the submission guide](submission.md).

## Totally real tower

The arithmetic development also reuses Naganori Yamaguchi's Apache-2.0 `Nyll.SawinTotallyRealTowers.SawinTotallyRealTower`, written with OpenAI Codex assistance. The dependency is pinned at `2df65101324c0625904b6becbff317df88d8c3de`. The resulting fields have dyadic degrees and bounded root discriminant, using a different tower from the concrete Martinet example. See [the tower verification and its exact scope](tower.md). [Upstream source snapshot](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers/tree/2df65101324c0625904b6becbff317df88d8c3de)
