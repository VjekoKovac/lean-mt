module

public import MT.BoxCutoffTensor
public import MT.BoxCounting
public import MT.Upstream.Poisson

/-! Translated box counts for Euclidean lattices with multiplicative minima. -/

@[expose] public section
noncomputable section

open MeasureTheory Set DedekindZeta.PoissonSummation
open scoped FourierTransform

namespace MT.BoxCutoff

variable {ι : Type*} [Fintype ι]

/-- Actual lattice intersection with the closed translated box as a finite set. -/
def latticeBox (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] (M a : ι → ℝ) :
    Finset L := by
  classical
  have hs : IsClosed (L : Set (EuclideanSpace ℝ ι)) := L.toAddSubgroup.isClosed_of_discreteTopology
  have hf : ((closedBox M a) ∩ (L : Set (EuclideanSpace ℝ ι))).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete (compact_box M a).isBounded hs
  have hb : {x : L | (x : EuclideanSpace ℝ ι) ∈ closedBox M a}.Finite := by
    apply (hf.preimage_embedding (Function.Embedding.subtype _)).subset
    intro x hx
    exact ⟨hx,x.property⟩
  exact hb.toFinset

@[simp] theorem mem_latticeBox (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L]
    (M a : ι → ℝ) (x : L) : x ∈ latticeBox L M a ↔ (x : EuclideanSpace ℝ ι) ∈ closedBox M a := by
  classical
  simp [latticeBox]

/-- The lower half of the structure-intersection lemma for a lattice.
The only arithmetic hypothesis is the nonzero-point product gap in its *actual Euclidean dual*. -/
theorem lattice_box_lower (i₀ : ι) (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (M a : ι → ℝ) (D : ℝ) (hD : 0 < D) (hM : ∀ i, 48*constant*D ≤ M i)
    (hdual : ∀ x : dualLattice L, x ≠ 0 →
      1/D^(Fintype.card ι) ≤ ∏ i, |(x : EuclideanSpace ℝ ι) i|) :
    (∏ i, M i)/(2*ZLattice.covolume L) ≤ (latticeBox L M a).card := by
  classical
  have hK := zero_lt_one.trans_le constant_one_le
  have hMpos (i : ι) : 0 < M i := (by positivity : 0 < 48*constant*D).trans_le (hM i)
  let V := EuclideanSpace ℝ ι
  let δ := 1/D^(Fintype.card ι)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let w := boxSchwartz M a hMpos
  let g (x : dualLattice L) := 𝓕 (w : V → ℂ) (x : V)
  have hsep (x y : dualLattice L) (hxy : x ≠ y) :
      δ ≤ ∏ i, |(x : V) i - (y : V) i| := hdual (x-y) (sub_ne_zero.mpr hxy)
  have hdec (x : dualLattice L) (hx : x ≠ 0) :
      ‖g x‖ ≤ constant^(Fintype.card ι)*(∏ i, M i)*(∏ i, min 1 ((|M i*(x:V) i|^2)⁻¹)) := by
    apply fourier_boxSchwartz_decay M a hMpos
    intro i h
    have hz : (∏ j, |(x : V) j|) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])
    have hsep' : δ ≤ ∏ j, |(x : V) j| := hdual x hx
    linarith
  exact BoxCounting.count_of_poisson_and_decay i₀ (latticeBox L M a)
    (fun x : L => w (x : V)) g (fun x : dualLattice L => WithLp.ofLp (x : V))
    M constant D (ZLattice.covolume L volume) hMpos hK.le hD (ZLattice.covolume_pos L volume)
    hM hsep hdual hdec (fourier_boxSchwartz_zero M a hMpos)
    (fun x hx => tensor_zero M a hMpos (by simpa using hx)) (fun x _ => tensor_bound M a x)
    (tsum_eq_tsum_fourier L w)

/-- Packing gives the upper half for a primal lattice with algebraic
norm gap one, with full side lengths `2 Mᵢ` and arbitrary translate. -/
theorem lattice_box_upper (i₀ : ι) (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] (M a : ι → ℝ) (hM : ∀ i, 0 < M i)
    (hprimal : ∀ x : L, x ≠ 0 → 1 ≤ ∏ i, |(x : EuclideanSpace ℝ ι) i|) :
    ((latticeBox L M a).card : ℝ) ≤ 1 + 2^(Fintype.card ι) * ∏ i, M i := by
  have hbox (x : L) (hx : x ∈ latticeBox L M a) (i : ι) :
      (a i-M i) ≤ (x : EuclideanSpace ℝ ι) i ∧
      (x : EuclideanSpace ℝ ι) i ≤ (a i-M i) + 2*M i := by
    obtain ⟨hl,hu⟩ := abs_le.mp ((mem_latticeBox L M a x).mp hx i)
    constructor <;> linarith
  have hs (x y : L) (hxy : x ≠ y) :
      1 ≤ ∏ i, |(x : EuclideanSpace ℝ ι) i - (y : EuclideanSpace ℝ ι) i| :=
    hprimal (x-y) (sub_ne_zero.mpr hxy)
  simpa [Finset.prod_mul_distrib] using
    BoxCounting.box_count i₀ (latticeBox L M a) (fun x : L => WithLp.ofLp (x : EuclideanSpace ℝ ι))
      (fun i => a i-M i) (fun i => 2*M i) 1 (fun i => mul_pos (by norm_num) (hM i))
      zero_lt_one hbox (fun x _ y _ => hs x y)

end MT.BoxCutoff
