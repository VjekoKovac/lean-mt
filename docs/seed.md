# Integer seed and energy

The source is §4, “Product 0 and Product”, of [arXiv:2611.22465v1](https://arxiv.org/abs/2611.22465v1). Variables in the following construction are integers unless specified. Lean indexes the generators by `Fin m`, starting at zero.

## Choosing the seed

For each integer $m ≥ 2$ choose $a_1,…,a_m$ in $[1,2^{3m}]$. Put $P(t)=(t,t^2)$, let $A_0$ be the set of generators, and let $ζ_J=(b_J,τ_J)$ be the sum of $P(a_j)$ over $j∈J$, including $ζ_∅=(0,0)$. Let $B_0$ consist of all $ζ_J$. The choice must make both maps $j↦a_j$ and $J↦ζ_J$ injective and the affine determinant of every three distinct subset sums nonzero. In particular, vertical collinearity is excluded. The determinant has absolute value at least one because it is a nonzero integer. In particular $|A_0|=m$, $|B_0|=2^m$, $0 ≤ b_J ≤ m2^{3m}$, and $0 ≤ τ_J ≤ m2^{6m}$.

1. For distinct subsets $S,T,U$, their three Boolean incidence columns have two rows whose $2×2$ minor after subtracting the third column is nonzero. Choose a row distinguishing $S,T$. In that row $U$ agrees with exactly one of them. A second row distinguishes $U$ from the one it agrees with. Lean checks the possible Boolean cases using kernel reduction with `decide`.
2. Let $F_{S,T,U}$ be the affine determinant of the three formal subset sums. The source expands its coefficients. In Lean we evaluate at $X_i=1,X_j=2$ and the other variables zero for the two rows just found. The determinant is twice the signed minor, so $F$ is nonzero. This isolates the same two-coordinate contribution. Its total degree is at most three.
3. Form $G$ by choosing one ordering of each three-element set of subsets and multiplying the corresponding factors. All factors are nonzero. With $N=2^m$, the degree is at most three times the number of triples, which is strictly less than $N^3=2^{3m}$. The proof uses that six times the number of triples is $N(N-1)(N-2)≤N^3$.
4. The integer grid has $2^{3m}$ choices per coordinate. Apply mathlib's grid-vanishing theorem contrapositively to find a point where $G$ is nonzero. Permuting three columns preserves nonvanishing. If two subset sums coincided, complete those two subsets to a triple and contradict nonvanishing. The number of subsets is at least four. Distinct singleton points force distinct generators.

## Counting the gain

For $j∉J$, inserting $j$ adds $P(a_j)$ to $ζ_J$. There are exactly $m2^{m-1}$ such labelled edges because removing one element from the index set leaves $m-1$ elements. Injectivity sends the edges to distinct geometric pairs in $P(A_0)×B_0$. Other representations are possible, so this gives a lower bound. Define $r(z)$ as the number of pairs giving sum $z$, and $E$ as the sum of all $r(z)^2$, equivalently the number of ordered equal-sum quadruples. Cauchy–Schwarz on $B_0$ gives $(m2^{m-1})^2≤|B_0|E$, hence $4E≥m^2|B_0|$. Every nonvertical line contains at most two elements of $B_0$. Thus $E/(L_0|A_0||B_0|)≥m/8$, where $L_0$ is the maximum occupancy of a nonvertical line.

## Moving from the seed to the lattice

Take the Cartesian powers $A_0^k,B_0^k$ and identify the product of $k$ planes with two copies of $k$-dimensional Euclidean space by grouping horizontal and vertical coordinates. For root discriminant $D$, box constant $C_0$, and sufficiently large positive $ρ$ depending only on $m,D$, use

- $I_j=ρa_j+[-C_0D,C_0D]$;
- $R_J=(ρb_J+[-C_0D,C_0D])×(ρ^2τ_J+[-ρ^{3/2},ρ^{3/2}])$;
- $U$ the union of all $I_j$, $V$ the union of all $R_J$, followed by $U^k,V^k$.

The choices include $ρ≥\max(2^{3m},2C_0D,2)$, with strict further enlargement where disjointness requires it. Undoing the dilation gives horizontal half-width $C_0D/ρ$ and vertical half-height $1/√ρ$. Distinct centers are distinct integer points. Nonzero integer triple determinants and continuity imply that for sufficiently small half-widths no three chosen points, one in each of three distinct boxes, are collinear. It follows that the intervals and the corresponding rectangles in their respective families are disjoint and every affine line meets at most two rectangles. For fixed $D$ the required size can be bounded by $\exp(O(m))$. The center coordinates grow at most $m2^{6m}$, and a determinant changes by at most a fixed multiple of the maximum coordinate magnitude times the maximum displacement when the displacement is at most one. The paper uses these geometric facts to intersect with the arithmetic lattice. See [the arithmetic ledger](arithmetic.md) for this step, including the box half-width convention.

## Lean declarations and provenance

| Declaration in `MT.Seed` | Scope |
| --- | --- |
| `exists_nonzero_minor` | Nonzero incidence minor for every triple of distinct Boolean-valued functions. |
| `exists_bounded_seed` | Full grid bound, both injectivity properties, and every triple determinant. |
| `point_insert`, `card_edgeLabels`, `count_translations` | Exact count of the labels and the lower bound on actual geometric pairs. |
| `seed_energy`, `four_energy`, `exists_seed_energy` | Finset energy of the parabolic generators and their full set of subset sums. The final existence theorem discharges the genericity assumption. |
| `determinant_stability`, `thickened_determinant_ne` | Moving each coordinate by at most $δ≤1$ changes the determinant by at most $16(B+1)δ$, where all center coordinates have absolute value at most $B$. |
| `intervals_disjoint`, `rectangles_disjoint`, `card_meetingLine_le_two` | Pairwise disjointness and the all-line intersection bound for the actual real rectangles of vertical half-height $ρ^{3/2}$. |
| `exists_seed_rectangles` | The three geometric conclusions for the seed constructed in Lean, uniform in the line. With $B=m(2^{3m})^2$, it suffices to take $ρ≥\max((32(B+1))^2,32C_0D(B+1))$. |
| `card_overlap_labels` | Exactly $(2^{m-1})^k$ label tuples for fixed coordinates $j_1,…,j_k$. |

Mathlib's `Finset.card_sq_le_card_mul_addEnergy` (Yaël Dillies and Ella Yu, `Mathlib/Combinatorics/Additive/Energy.lean`) supplies the representation-count/Cauchy–Schwarz inequality with energy defined by quadruples. `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` (Antoine Chambert-Loir, `Mathlib/Combinatorics/Nullstellensatz.lean`) supplies the integer-grid argument. The proof also uses mathlib's finite powersets, binomial coefficients, degree bounds and integer intervals. The files contain the mathematical proofs generated for this project. All names here are in the pinned mathlib version. This component covers the integer seed before lattice intersection. The overlap-label count alone gives no lower bound on lattice population.

