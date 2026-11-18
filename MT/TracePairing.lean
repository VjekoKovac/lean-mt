module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Tactic

/-! # The Euclidean trace pairing for totally real fields -/

@[expose] public section

namespace MT.TracePairing

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped InnerProductSpace Classical

/-- The trace is the sum over the real places, with each embedding occurring once. -/
theorem sum_real_embeddings {K : Type*} [Field K] [NumberField K] [IsTotallyReal K] (z : K) :
    (∑ w : {w : InfinitePlace K // IsReal w}, embedding_of_isReal w.2 z) =
      (Algebra.trace ℚ K z : ℝ) := by
  classical
  let e : (K →+* ℂ) ≃ {w : InfinitePlace K // IsReal w} :=
    (Equiv.subtypeUnivEquiv (fun φ : K →+* ℂ => IsTotallyReal.complexEmbedding_isReal φ)).symm.trans mkReal
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_ratCast]
  change _ = algebraMap ℚ ℂ (Algebra.trace ℚ K z)
  rw [trace_eq_sum_embeddings]
  calc
    _ = ∑ φ : K →+* ℂ, φ z := by
      symm
      apply Fintype.sum_equiv e
      intro φ
      rw [embedding_of_isReal_apply]
      change φ z = embedding (mk φ) z
      rw [embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)]
    _ = _ := Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _
      (fun φ => by simp [RingHom.equivRatAlgHom_apply])

/-- On Minkowski-embedded elements the Euclidean scalar product equals the
field trace of the product, for a totally real number field. -/
theorem inner_embedding {K : Type*} [Field K] [NumberField K] [IsTotallyReal K] (x y : K) :
    ⟪(euclidean.toMixed K).symm (mixedEmbedding K x),
      (euclidean.toMixed K).symm (mixedEmbedding K y)⟫_ℝ = (Algebra.trace ℚ K (x * y) : ℝ) := by
  classical
  let : IsEmpty {w : InfinitePlace K // IsComplex w} :=
    ⟨fun w => (not_isReal_iff_isComplex.mpr w.2) (IsTotallyReal.isReal w.1)⟩
  rw [WithLp.prod_inner_apply]
  have hzero : (WithLp.ofLp ((euclidean.toMixed K).symm (mixedEmbedding K x))).2 = 0 :=
    Subsingleton.elim _ _
  rw [hzero, inner_zero_left, add_zero, PiLp.inner_apply, ← sum_real_embeddings (x*y)]
  apply Finset.sum_congr rfl
  intro w _
  change ⟪embedding_of_isReal w.2 x, embedding_of_isReal w.2 y⟫_ℝ = _
  rw [map_mul, Real.inner_apply]

end MT.TracePairing
