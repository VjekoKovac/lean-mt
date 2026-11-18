module

import Solution

/-! Independent restatement of Proposition 4.1. This imports the proof,
expands its configuration data, and clears its strictly positive denominator.
It never imports the specification module. -/

open MT

example : ∃ C : ℝ, 1 < C ∧ ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ,
    let k : ℕ := 2^n
    ∃ (A : Finset ℝ) (B : Finset (ℝ × ℝ)) (L : ℝ),
      A.Nonempty ∧ B.Nonempty ∧
      (∀ a ∈ A, |a| ≤ 1) ∧ (∀ z ∈ B, |z.1| ≤ 1 ∧ |z.2| ≤ 1) ∧
      1 ≤ L ∧ L ≤ Real.exp (b * (k : ℝ)) ∧
      (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → (C^k)⁻¹ ≤ |a-a'|) ∧
      (∀ slope intercept : ℝ, ((B.filter (fun z =>
        z.2 - 2*slope*z.1 ∈ Set.Icc intercept (intercept+(C^k)⁻¹))).card : ℝ) ≤ L) ∧
      (2:ℝ)^k * (L * A.card * B.card) ≤ (energy A B : ℝ) := by
  obtain ⟨C,hC,b,hb,h⟩ := arithmeticAmplification
  refine ⟨C,hC,b,hb,?_⟩
  intro n
  obtain ⟨L,hL,hsize,Q,hgain⟩ := h n
  have ha : (0:ℝ) < Q.A.card := by exact_mod_cast Q.nonemptyA.card_pos
  have hB : (0:ℝ) < Q.B.card := by exact_mod_cast Q.nonemptyB.card_pos
  have hden : (0:ℝ) < L*Q.A.card*Q.B.card :=
    mul_pos (mul_pos (zero_lt_one.trans_le hL) ha) hB
  exact ⟨Q.A,Q.B,L,Q.nonemptyA,Q.nonemptyB,Q.inBoxA,Q.inBoxB,hL,hsize,Q.separated,
    Q.strip,(le_div_iff₀ hden).mp hgain⟩

#print axioms MT.Seed.exists_bounded_seed
#print axioms MT.Arithmetic.minkowski_dual_coordinate_gap
#print axioms MT.Arithmetic.fieldRect_lower
#print axioms MT.Arithmetic.fieldRect_upper
#print axioms MT.Intersections.field_intersection_estimates
#print axioms MT.Intersections.field_sets_geometry
#print axioms MT.Arithmetic.configuration_of_field_bounds
#print axioms MT.Tower.dyadic_totally_real_fields
#print axioms MT.arithmeticAmplification
#print axioms MT.powerlossMT
