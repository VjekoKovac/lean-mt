# AI review of arithmetic amplification

An AI reviewer who did not implement the arithmetic proof compared §§4.1–4.4 and Appendix A of arXiv v1 with the Lean proof bodies. The question was whether one scale base $C>1$ works for **every** degree $k=2^n$, including $k=1$, with the full strip and energy conclusions of Proposition 4.1. The fields used here are totally real finite extensions of $\mathbb Q$. The configurations in them are finite sets of algebraic integers. [Manuscript, §4](https://arxiv.org/html/2611.22465v1#S4) · [Appendix A](https://arxiv.org/html/2611.22465v1#A1)

## From lattices to the gain

| Source step | Independent check of the Lean argument |
| --- | --- |
| §4.1, fields and embeddings | `MT.Tower.dyadic_totally_real_fields` supplies $[K:\mathbb Q]=2^n$ and $|\operatorname{disc}K|\le255255^{2^n}$ for every $n$. It takes a fixed field of the appropriate subgroup of a finite Galois 2-extension, proves the exact degree, and descends the discriminant bound. This reuses Yamaguchi’s proof of Sawin’s tower. The counting proof needs a common upper bound. The source cites Martinet and gives a common root discriminant for its chosen tower. |
| §4.1, primal and dual separation | The integer norm of each nonzero algebraic integer gives $\prod_i |\sigma_i(x)|\ge1$. For the dual, the real inner product is the trace pairing and the trace-dual basis represents every geometric dual point. The fractional ideal argument gives $\prod_i |\xi_i|\ge1/|\operatorname{disc}K|$. Both inequalities apply to differences of distinct points. The dual argument also treats a single nonzero point in a dyadic cell. |
| §4.1, translated rectangles | For arbitrary center and half-widths $M_i\ge48K_0D$, the normalized smooth tensor cutoff has zero Fourier coefficient $\prod_i M_i$. Here $K_0\ge1$ is the fixed one-dimensional Fourier decay constant. Poisson summation and a dyadic count bound the nonzero-frequency error by half that zero mode. Thus the lattice contains at least $\prod_iM_i/(2\sqrt{|\operatorname{disc}K|})$ points in the box. Packing gives an upper bound $1+2^k\prod_i M_i$. In particular a cube of half-width $r\ge1$ has at most $(4r)^k$ points. |
| §4.2, seed and thickening | The nonzero determinant polynomial gives $m$ integer labels in $[1,2^{3m}]$ whose $2^m$ parabolic subset sums are all distinct and have no collinear triple. The explicit perturbation bounds yield pairwise disjoint horizontal intervals, pairwise disjoint planar rectangles and at most two rectangles meeting any line. The dilation $\rho$ is fixed after the seed size and horizontal width, before the degree. |
| §4.3, sizes and returns | A tuple of generator labels prescribes one translated horizontal box in all $k$ embeddings. These boxes are disjoint. For a fixed $a$ and a subset tuple omitting its local generator labels, the midpoint construction leaves horizontal and vertical **half-widths** $H_*/2$ and $\rho^{3/2}/2$ in the overlap. The $2^{(m-1)k}$ resulting product boxes are pairwise disjoint and every counted point $z$ satisfies $z,P(a)+z\in B_K$. Integrality is retained in both coordinates. |
| §4.3, lines | Each of the $k$ embeddings of a nonvertical field line meets at most two seed rectangles. Each rectangle tuple permits at most $(4H_*)^k$ first coordinates by the lattice upper bound. Projection onto the first coordinate is injective along the field line. Thus $L=(8H_*)^k$ bounds its occupancy. Here $H_*$ denotes the fixed horizontal half-width, distinct from the eventual real-configuration scale $H=C^k$. |
| §4.4, projection and strips | A fixed bound $M\ge1$ controls every conjugate of every input coordinate, independently of $k$. The injection uses $\sigma(a)/M$ horizontally and $\sigma(\tau)/M^2$ vertically. Coordinate differences are bounded by $2M$ before projection, and doubled areas by $8M^2$. The norm gap and the $M^3$ determinant scaling give the common base $C=100M^3(8M^2)$. The determinant and ordinate gaps imply that every point in any projected strip of vertical width $C^{-k}$ lifts to one nonvertical field line. Vertical coincidence, empty and singleton cases are covered. Injective parabolic projection preserves the two cardinalities and the full ordered energy. |

The proof bodies for these steps include `MT.Arithmetic.fieldRect_lower`, `MT.Arithmetic.fieldRect_upper`, `MT.Seed.exists_seed_rectangles`, `MT.Intersections.field_intersection_estimates`, `MT.Seed.field_line_count`, `MT.Intersections.field_sets_geometry` and `MT.Arithmetic.configuration_of_bounded_field_sets`. [Field box counts](../MT/FieldBox.lean) · [Returns in the actual field](../MT/FieldIntersections.lean) · [Projection](../MT/FieldProjection.lean)

## Why the loss constants must precede the seed

Let $A_K,B_K$ denote the field sets, and $T_a=\#\{z\in B_K:P(a)+z\in B_K\}$. The three constants used by `MT.Arithmetic.configuration_of_field_bounds` enter different inequalities.

| Constant | Value used | Verified role |
| --- | --- | --- |
| $c_A$ | $2$ | $\#A_K\ge(m/c_A)^k$ from the lower lattice count for $m^k$ disjoint boxes. |
| $c_R$ | $512D$ | $\#B_K\le c_R^kT_a$ for every $a\in A_K$. The covolume appears twice, and its square is $|\operatorname{disc}K|\le D^k$. |
| $c_L$ | $8H_*$ | $L=c_L^k$ bounds nonvertical line occupancy. Choosing integer $H_* = \lceil96K_0D\rceil+1$ gives $H_*/2\ge48K_0D$. |

Cauchy–Schwarz for the representation counts and the return bound give
$$
 (\#A_K)^2\#B_K\le c_R^{2k}E(A_K,B_K).
$$
Choose $m\ge2c_Ac_R^2c_L$ after fixing $D,H_*$. Consequently $2^kc_R^{2k}L\le\#A_K$, and the displayed inequality gives $2^kL\#A_K\#B_K\le E(A_K,B_K)$. Both finite sets are nonempty by strictly positive lower counts in the actual lattice. Since $L\ge1$, $L\#A_K\#B_K$ is strictly positive. This justifies the quotient in the source. The positivity of the analytic denominator, which involves the X-ray and input norms, is proved separately in Proposition 3.1. The occupancy exponential uses the one fixed coefficient $b=\log c_L>0$. All these choices precede $n$. [Gain proof](../MT/FieldGain.lean) · [Independent analytic review](review-analytic.md)

## Replaying the result

`checks/ArithmeticReview.lean` imports the solution and spells out the proposition again using finite sets, both nonemptiness conditions, the unit boxes, all real slopes and intercepts, and every dyadic degree. It clears the positive denominator and obtains the energy inequality in multiplicative form. This independently exercises the interfaces between the field construction, the projected configuration, and the statement. It also prints the transitive axioms for the principal arithmetic lemmas and the top-level theorem. The unconditional theorem uses the proven arithmetic and analytic propositions in the Section 5 interpolation. [Review input](../checks/ArithmeticReview.lean)

In the recorded run, Lean 4.35.0 accepted the expanded proposition and all ten axiom queries. Each reports exactly `propext`, `Classical.choice`, and `Quot.sound`, including `MT.arithmeticAmplification` and `MT.powerlossMT`. The log shows the object directory used in this session. On an ordinary source build, run the following from the project root. [Actual command and output](../checks/arithmetic-review.txt)

```bash
lake build Solution
lake env lean -j1 checks/ArithmeticReview.lean
```

This source review is separate from the kernel check and from the independent statement comparison. The proof of Martinet’s particular tower and its quoted numerical discriminant is outside this implementation. The explicit large choices above establish existence of a positive power exponent. They provide no estimate of $10^{-5}$ for the separate $C^3$ remark.
