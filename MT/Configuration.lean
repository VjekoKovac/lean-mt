module

public import MT.Definitions
public import Mathlib.Tactic

/-! # Parabolic energy and real configurations
Definitions for Propositions 3.1 and 4.1 of arXiv:2611.22465v1. The last
theorem proves the preservation of the full count in §4.4, including
both directions of the equality test on ordered representations.
-/

@[expose] public section
noncomputable section

namespace MT

/-- Coordinate x ↦ σ(x)/S. -/
def projectedCoordinate {K : Type*} [Field K] (σ : K →+* ℝ) (S : ℝ) (hS : S ≠ 0) :
    K ↪ ℝ where
  toFun x := σ x / S
  inj' _ _ h := σ.injective ((div_left_inj' hS).mp h)

/-- (b,τ) ↦ (σ(b)/S,σ(τ)/S²). -/
def projectedPoint {K : Type*} [Field K] (σ : K →+* ℝ) (S : ℝ) (hS : S ≠ 0) :
    (K × K) ↪ (ℝ × ℝ) :=
  (projectedCoordinate σ S hS).prodMap (projectedCoordinate σ (S ^ 2) (pow_ne_zero _ hS))

theorem parabolicSum_project {K : Type*} [Field K] (σ : K →+* ℝ) (S : ℝ) (hS : S ≠ 0)
    (p : K × (K × K)) :
    parabolicSum (((projectedCoordinate σ S hS).prodMap (projectedPoint σ S hS)) p) =
      projectedPoint σ S hS (parabolicSum p) := by
  apply Prod.ext
  · change σ p.1 / S + σ p.2.1 / S = σ (p.1 + p.2.1) / S
    rw [map_add, add_div]
  · change (σ p.1 / S) ^ 2 + σ p.2.2 / S ^ 2 = σ (p.1 ^ 2 + p.2.2) / S ^ 2
    rw [map_add, map_pow, add_div, div_pow]

/-- Both set sizes and their unnormalized parabolic energy are exactly preserved. -/
theorem project_preserves_counts {K : Type*} [Field K] (σ : K →+* ℝ)
    (S : ℝ) (hS : S ≠ 0) (A : Finset K) (B : Finset (K × K)) :
    (A.map (projectedCoordinate σ S hS)).card = A.card ∧
    (B.map (projectedPoint σ S hS)).card = B.card ∧
    energy (A.map (projectedCoordinate σ S hS)) (B.map (projectedPoint σ S hS)) = energy A B := by
  classical
  refine ⟨Finset.card_map _, Finset.card_map _, ?_⟩
  simp only [energy, ← Finset.prodMap_map_product, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro q _
  let e := (projectedCoordinate σ S hS).prodMap (projectedPoint σ S hS)
  change (parabolicSum (e q.1) = parabolicSum (e q.2)) ↔ _ 
  dsimp only [e]
  rw [parabolicSum_project, parabolicSum_project, (projectedPoint σ S hS).injective.eq_iff]

end MT
