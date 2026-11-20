# Power loss for the local Mizohata–Takeuchi estimate

This Lean 4 project formalizes Theorem 1.3 of Hannah Cairo, Inbo Gottlieb Fenves, Vjekoslav Kovač, Itamar Oliveira, Dmitrii Zakharov and Ruixiang Zhang, *Power loss for the local Mizohata–Takeuchi estimate on smooth hypersurfaces*. The formalization authors are the same six authors, as requested. The proof implementation and the independent reviews in this repository used AI. [Versioned paper](https://arxiv.org/abs/2611.22465v1)

**Main declaration:** `MT.powerlossMT : MT.PowerLoss` in [Solution.lean](Solution.lean). For every $0<\beta\le1$ there is a **single** $\alpha_\beta>0$ such that every eligible $C^{2,\beta}$ hypersurface $\Sigma\subset\mathbb R^{d+1}$ whose second fundamental form is nonzero at some point satisfies
$$
\mathcal C_\Sigma(R)\ge c_\Sigma R^{\alpha_\beta}\qquad (R\ge R_\Sigma).
$$
The exponent is chosen before the dimension and before the surface. The multiplier and threshold may depend on the surface. The independent specification is in [Challenge.lean](Challenge.lean). Start with the [statement guide](docs/statement.md) and [verification report](docs/verification.md) for its definitions and evidence.

**Verification.** The full theorem passed the official Lean Comparator. The three allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. [Full Comparator transcript](checks/full-comparator.txt) · [Main-theorem axiom report](checks/main-axioms.txt)

## Following the proof

| Source | Where to read | What is proved |
| --- | --- | --- |
| §1, Theorem 1.3 | [Challenge.lean](Challenge.lean) and [the statement guide](docs/statement.md) | Quantifier order, local graph curvature, normalized surface measure, positive-sign extension, X-ray norm and all sufficiently large real radii. |
| §3, Proposition 3.1 | [AnalyticTransfer.lean](MT/AnalyticTransfer.lean), [analytic ledger](docs/analysis.md), [physical coordinate change](docs/physical-change.md) | A chart cap input and a nonnegative weight transfer every finite configuration of sufficient gain to a lower bound on the given surface. |
| §4.1 and Appendix A | [tower](docs/tower.md), [box count](docs/box-count.md), [FieldBox.lean](MT/FieldBox.lean) | Totally real fields at each exact dyadic degree, product separation for integers and their trace dual, and uniform bounds for translated boxes. |
| §4.2 | [seed ledger](docs/seed.md) and [SeedPolynomial.lean](MT/SeedPolynomial.lean) | A bounded integer seed for every $m\ge2$, noncollinear subset sums, their energy and thickened rectangles. |
| §§4.3–4.4, Proposition 4.1 | [arithmetic ledger](docs/arithmetic.md), [Amplification.lean](MT/Amplification.lean), [ArithmeticAmplification.lean](MT/ArithmeticAmplification.lean) | Counts of actual algebraic integers and returning pairs, uniform line occupancy, projection preserving every energy collision, and one absolute scale base $C>1$. |
| §5 | [Solution.lean](Solution.lean), [Transfer.lean](MT/Transfer.lean) | The choice $\alpha_\beta=\log 2/[2(1+2/\beta)\log C]$ and the passage from dyadic degree scales to **every** sufficiently large radius. |

Read the [numbered proof map](docs/proof-map.md) for the finer claims. The [statement review](docs/review-fidelity.md), [analytic review](docs/review-analytic.md), and [arithmetic review](docs/review-arithmetic.md) identify the AI reviewers' scope and the places where the implementation chooses an equivalent or sufficient argument. The [attribution ledger](docs/dependencies.md) identifies the reused proofs. Publication and registry metadata are in [formalization.yaml](formalization.yaml).
