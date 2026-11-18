# Counting points in a box

This is the finite packing and dyadic summation in the proof of Lemma 4.3, labelled `lemma:structureintersection`. The space can be indexed by any nonempty finite type of cardinality $k$. For a number field one may use its real embeddings directly. The estimates begin with the product-separation inequalities proved for the primal or trace-dual lattice in the arithmetic part.

## A translated box

Fix positive full side lengths $W_i$, arbitrary lower endpoints $a_i$, and a finite indexed family of points $f(x)$. Every coordinate lies in $[a_i,a_i+W_i]$. Suppose the product of the absolute coordinate differences between any two distinct labels is at least $δ>0$. Choose one coordinate $i_0$. Distinct points are separated in that coordinate by at least $s=δ/P$, where $P$ is the product of the other full side lengths. The floor of $(f(x)_{i_0}-a_{i_0})/s$ is injective on the points: equal floors imply distance strictly less than $s$. Counting integer buckets gives

$$
|X| ≤ 1 + (∏_i W_i)/δ.
$$

This holds for translated boxes even if one contains a single point and has arbitrarily small volume. For a centered box with half-widths $M_i$, suppose also that each point's own absolute coordinate product is at least $δ$. If the box is nonempty, one point gives $δ ≤ ∏_i M_i$. Therefore

$$
|X| ≤ (1+2^k)(∏_i M_i)/δ.
$$

The empty case is immediate. This supplies the one-point case omitted in the source's nearest-pair pigeonhole argument. For nonzero dual points take $δ=D^{-k}$, with $D$ the root discriminant. The pairwise version applies to differences of distinct dual points.

## The Fourier remainder

Let the $M_i$ now denote the source rectangle's half-widths, and let the dual cell have coordinate upper bounds $|M_if(x)_i|≤2^{j_i+1}$. Applying the centered estimate with half-widths $2·2^{j_i}/M_i$ yields

$$
|X| ≤ 2·4^k(∏_i2^{j_i})/[δ(∏_i M_i)].
$$

Only the upper endpoints are needed in this estimate. In the sum the lower endpoints control the Fourier decay. The Lean proof uses the dyadic logarithm and makes the lower endpoint closed and upper endpoint open. The source uses the opposite endpoint convention. Both partition all positive magnitudes and give the same estimate.

Assume the nonzero dual frequencies are indexed by $x$, their coordinates satisfy both product-separation conditions, and a nonnegative real quantity $F(x)$ obeys

$$
F(x) ≤ K^k (∏_i M_i) ∏_i \min(1,|M_if(x)_i|^{-2})
$$

with $K≥0$. If a factor $M_i f(x)_i$ vanished, the origin gap would fail. At $j_i$ the binary logarithm rounded down, the scalar majorant after counting points is $2^{j_i-2\max(j_i,0)}=2^{-|j_i|}$. On the integers this has sum $3$, since the nonnegative indices contribute $2$ and the strictly negative indices contribute $1$. A finite family of cells embeds in the product of its coordinate projections, so its product weights sum to at most $3^k$. All finite partial sums consequently satisfy

$$
\sum_x F(x) ≤ 2(12K)^k/δ.
$$

The nonnegative-series criterion proves summability and the same upper bound for the full series, with no assumption of convergence. If $V=∏_iM_i$, the scale inequality $4(12K)^k≤Vδ$ makes the remainder at most $V/2$. A separately proved Poisson estimate $V-R≤\operatorname{covol}(Λ)·|Λ∩Q|$ then gives $V/(2\operatorname{covol}(Λ))≤|Λ∩Q|$.

## Lean declarations and dependencies

- `MT.BoxCounting.interval_count` and `box_count` are the translated-box estimates.
- `centered_box_count` and `dyadic_cell_count` absorb the singleton term using the origin gap.
- `geomWeight_hasSum`, `product_geomWeight_sum`, and `finite_remainder` give the finite dyadic estimate.
- `remainder_bound` proves absolute convergence for nonnegative majorants and the explicit full-series estimate.
- `tailNorm_of_product_decay` gives absolute summability of the complex coefficient norms with the zero mode restored, and bounds the exact `MT.tailNorm` used by the Poisson count.
- `scale_of_halfSides` shows that choosing every half-side $M_i≥48KD$ suffices when $δ=D^{-k}$.
- `lower_bound_of_poisson` handles the scalar comparison; `count_of_poisson_and_decay` derives the lower count from the Poisson identity, cutoff and algebraic separation bounds, without a summability or remainder hypothesis.

These proofs use Lean's integer floors and mathlib's finite-product expansions, geometric series, integer binary logarithm, and summability criteria. They apply to actual coordinate data. `MT.BoxCutoff.fourier_boxSchwartz_zero` and `fourier_boxSchwartz_decay` provide the matching majorant and zero coefficient for the explicit cutoff constructed below. The trace-pairing identification in `MT/NumberFieldDual.lean` supplies the resulting geometric dual for totally real number fields.


## Constructing the cutoff

Use a fixed smooth real bump centered at zero. Give it inner radius one half and outer radius one, and normalize it to have integral one. The inner plateau has length one, so the integral before normalization is at least one. The resulting function $ψ$ is still bounded by one and vanishes outside $[-1,1]$. It defines a complex-valued Schwartz function by real inclusion. The constant $K$ can be taken to be the maximum of one and the order-zero and order-two polynomially weighted Schwartz seminorms of its Fourier transform. This constant is independent of the field, the dimension, the center and the side lengths.

For each coordinate, set $f_i(t)=ψ((t-a_i)/M_i)$. Translation contributes a phase of absolute value one to the Fourier transform, and the positive dilation contributes $M_i$. At nonzero frequency $u$, the absolute value is at most $KM_i\min(1,|M_i u|^{-2})$, and at zero its value is exactly $M_i$. Distinguishing zero here is important in Lean because reciprocal is a total operation.

The multidimensional cutoff $f(x)=∏_i f_i(x_i)$ is smooth, is bounded by one, and has support in the translated closed box. The coordinate identification from finite-dimensional Euclidean space to the product of copies of the real line preserves Lebesgue measure. Its inner product is the sum of the coordinate products, so the Fourier character factors. Finite-dimensional Fubini gives the product of one-dimensional transforms. Hence the zero coefficient is exactly $∏_i M_i$ in magnitude and the nonzero-coordinate coefficients satisfy the majorant used in the lattice count. Every coordinate of a nonzero dual vector is nonzero whenever there is a positive lower bound on its coordinate product.

## The actual lattice intersection

`MT.BoxCutoff.latticeBox L M a` is the finite set of lattice points with $|x_i-a_i|≤M_i$ for every coordinate. Its membership theorem identifies it with the intersection of the translated closed box and the lattice. The proof of finiteness uses discreteness of the lattice and compactness of the box.

In `MT.BoxCutoff.lattice_box_lower`, the lattice has full rank, its Euclidean dual has nonzero coordinate products at least $D^{-k}$, and each half-side is at least $48KD$. Applying Poisson summation to the constructed cutoff gives at least $(∏_i M_i)/(2\operatorname{covol} Λ)$ points. In terms of the full volume of the box this is $2^{-k-1}\operatorname{vol}(Q)/\operatorname{covol}(Λ)$. In `lattice_box_upper`, if nonzero primal coordinate products are at least one, every positive choice of half-sides gives at most $1+2^k∏_iM_i$ points. Both bounds hold for every center in positive dimension. The field specialization below identifies the Euclidean lattice and its dual, bounds their multiplicative minima, and inserts the covolume. The lower estimate uses the primal and dual supplied to the checked Poisson formula.


## Integral field elements in arbitrary translated boxes

Let $K$ be totally real of degree $k$, with absolute discriminant $d_K$ and $d_K≤D^k$. The reindexed orthonormal coordinates of the mixed Minkowski space are exactly its real places. The isometry preserves the scalar product and covolume. The lattice of integers in these coordinates has covolume $√{d_K}$. The rational norm of a nonzero integral element gives primal coordinate product at least one. The trace pairing with the integer basis identifies each point of the geometric dual as the image of a field element in the codifferent, so nonzero dual vectors have coordinate product at least $1/d_K$.

`MT.Arithmetic.fieldRect K c M` is a finite set of **field elements**, obtained by transporting the lattice intersection along the inverse of the Minkowski bijection on the integers. Its membership theorem gives integrality over $ℤ$ and all signed inequalities $|σ_i(x)-c_i|≤M_i$. For every center, the lower estimate is $(∏_i M_i)/(2√{d_K})$ provided $M_i≥48 C D$, where $C$ is the fixed bump constant. The upper estimate is $1+2^k∏_i M_i$ for positive half-widths. For the cube with every $M_i=r$ and $D≥1$, `fieldBox_uniform` gives $(r/(2D))^k≤\# Q≤(4r)^k$ at the same lower threshold. For §4.3 the sharper `fieldBox_lower` and `fieldBox_upper` retain the exact covolume and singleton summand.

The lower bound is exactly $2^{-(k+1)}$ times the box volume divided by the covolume. The upper bound gives the exponential comparison in Lemma 4.3 for bounded root discriminant. The stronger discriminant-independent upper constant in the remark after Lemma 4.3 is not needed for the main theorem and is not claimed by this proof. [Lean implementation](../MT/FieldBox.lean) · [Build transcript](../checks/field-box.txt)
