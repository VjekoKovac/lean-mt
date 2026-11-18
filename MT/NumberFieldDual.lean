module

public import MT.Upstream.Poisson
public import MT.Arithmetic
public import MT.TracePairing
public import MT.NumberFieldLattice
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-! The geometric dual of the Euclidean lattice of integers in a totally real
number field consists exactly of the Minkowski images of trace-dual elements.
This is the dual-lattice identification used before Poisson summation in §4.1. -/

@[expose] public section
noncomputable section
open MeasureTheory NumberField NumberField.InfinitePlace Module
open NumberField.mixedEmbedding DedekindZeta.PoissonSummation
open scoped Classical InnerProductSpace NumberField nonZeroDivisors

namespace MT.Arithmetic

/-- Euclidean realization of the mixed embedding. -/
abbrev minkowskiVector {K : Type*} [Field K] [NumberField K] (x : K) : euclidean.mixedSpace K :=
  (euclidean.toMixed K).symm (mixedEmbedding K x)

theorem minkowskiVector_mem {K : Type*} [Field K] [NumberField K] (a : 𝓞 K) :
    minkowskiVector (a : K) ∈ euclidean.integerLattice K := by
  change (euclidean.toMixed K) ((euclidean.toMixed K).symm _) ∈ mixedEmbedding.integerLattice K
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact ⟨a, rfl⟩

/-- Identifies every geometric dual-lattice point by its integer pairings
with the integral basis. The trace pairing supplies the rational field element. -/
theorem exists_element_of_minkowski_dual {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    (w : euclidean.mixedSpace K) (hw : w ∈ dualLattice (euclidean.integerLattice K)) :
    ∃ x : K, minkowskiVector x = w ∧
      ∀ a : 𝓞 K, ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ K (x * (a : K)) := by
  classical
  have hpair (x y : K) : ⟪minkowskiVector x, minkowskiVector y⟫_ℝ = (Algebra.trace ℚ K (x * y) : ℝ) :=
    MT.TracePairing.inner_embedding x y
  have hwZ (a : 𝓞 K) : ∃ n : ℤ, (n : ℝ) = ⟪w, minkowskiVector (a : K)⟫_ℝ :=
    Submodule.mem_one.mp (mem_dualLattice.mp hw _ (minkowskiVector_mem a))
  let r := integralBasis K
  choose n hn using fun i => hwZ (RingOfIntegers.basis K i)
  let φ : K →ₗ[ℚ] ℚ := r.constr ℚ (fun i => (n i : ℚ))
  let T := (Algebra.traceForm ℚ K).toDual (traceForm_nondegenerate ℚ K)
  let x := T.symm φ
  have hx (i) : Algebra.trace ℚ K (x * r i) = n i := by
    change (T x) (r i) = _
    rw [show T x = φ from T.apply_symm_apply φ]
    exact r.constr_basis ℚ _ i
  let b := (mixedEmbedding.latticeBasis K).map (euclidean.toMixed K).symm.toLinearEquiv
  have beq (i) : b i = minkowskiVector (r i) := by
    change (euclidean.toMixed K).symm (mixedEmbedding.latticeBasis K i) = _
    rw [mixedEmbedding.latticeBasis_apply]
  have eqB : (innerₗ (euclidean.mixedSpace K)) (minkowskiVector x) = (innerₗ _) w := by
    apply b.ext
    intro i
    change ⟪minkowskiVector x, b i⟫_ℝ = ⟪w, b i⟫_ℝ
    rw [beq, hpair, hx]
    simpa [r, integralBasis_apply] using hn i
  have he : minkowskiVector x = w :=
    LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp
      (innerₗ_nondegenerate (V := euclidean.mixedSpace K)).1) eqB
  refine ⟨x, he, ?_⟩
  intro a
  obtain ⟨z,hz⟩ := hwZ a
  refine ⟨z, ?_⟩
  rw [← he, hpair] at hz
  exact_mod_cast hz

/-- Exact trace-dual characterization, with the standard integral lattice
and the dual lattice used by Poisson summation. -/
theorem mem_minkowski_dual_iff {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    (w : euclidean.mixedSpace K) :
    w ∈ dualLattice (euclidean.integerLattice K) ↔
      ∃ x : K, minkowskiVector x = w ∧
        ∀ a : 𝓞 K, ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ K (x * (a : K)) := by
  refine ⟨exists_element_of_minkowski_dual w, ?_⟩
  rintro ⟨x, rfl, hx⟩
  apply mem_dualLattice.mpr
  intro y hy
  change ∃ a : 𝓞 K, mixedEmbedding K (a : K) = euclidean.toMixed K y at hy
  obtain ⟨a, ha⟩ := hy
  have hya : minkowskiVector (a : K) = y :=
    (euclidean.toMixed K).symm_apply_eq.mpr ha
  rw [← hya, MT.TracePairing.inner_embedding]
  obtain ⟨n, hn⟩ := hx a
  apply Submodule.mem_one.mpr
  refine ⟨n, ?_⟩
  change (n : ℝ) = (Algebra.trace ℚ K (x * (a : K)) : ℝ)
  exact_mod_cast hn

/-- The product gap directly for every nonzero geometric dual-lattice
point, expressed in its real embedding coordinates. -/
theorem minkowski_dual_coordinate_gap {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    {w : euclidean.mixedSpace K} (hw : w ∈ dualLattice (euclidean.integerLattice K))
    (hne : w ≠ 0) :
    1 / ((discr K).natAbs : ℝ) ≤
      ∏ v : InfinitePlace K, |((euclidean.toMixed K) w).1 ⟨v, IsTotallyReal.isReal v⟩| := by
  obtain ⟨x, rfl, hx⟩ := (mem_minkowski_dual_iff w).mp hw
  have hn : x ≠ 0 := by
    intro h
    apply hne
    simp [h, minkowskiVector]
  have hgap := dual_product_gap hn hx
  simpa only [minkowskiVector, ContinuousLinearEquiv.apply_symm_apply,
    mixedEmbedding_apply_isReal, ← Real.norm_eq_abs, norm_embedding_of_isReal] using hgap

end MT.Arithmetic
