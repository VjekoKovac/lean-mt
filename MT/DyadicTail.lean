module

public import MT.Configuration

/-! # Completing a dyadic tail
The cited bounded-root-discriminant tower can start above the smallest
degrees. A finite initial segment of Proposition 4.1 is recovered by reusing
one finite configuration and increasing the absolute base C.
-/

@[expose] public section
noncomputable section
namespace MT

/-- At a larger H the separation requirement decreases and every test strip
is contained in the strip of the old width with the same lower intercept. -/
def Configuration.raiseScale {H H' L : ℝ} (Q : Configuration H L) (hH : 0 < H)
    (h : H ≤ H') : Configuration H' L where
  A := Q.A
  B := Q.B
  nonemptyA := Q.nonemptyA
  nonemptyB := Q.nonemptyB
  inBoxA := Q.inBoxA
  inBoxB := Q.inBoxB
  separated a ha a' ha' hne := (inv_anti₀ hH h).trans (Q.separated a ha a' ha' hne)
  strip s u := by
    apply le_trans _ (Q.strip s u)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hzB, hzlo, hzhi⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hzB, hzlo, hzhi.trans (add_le_add_right (inv_anti₀ hH h) u)⟩

/-- It suffices for the arithmetic construction to deliver the stated bounds
from any fixed dyadic index onwards. All constants here are absolute. -/
theorem arithmeticAmplification_of_tail {C b : ℝ} (hC : 1 < C) (hb : 0 < b)
    (N : ℕ) (tail : ∀ n : ℕ, N ≤ n →
      ∃ L : ℝ, 1 ≤ L ∧ L ≤ Real.exp (b * (2 ^ n : ℕ)) ∧
        ∃ Q : Configuration (C ^ (2 ^ n : ℕ)) L, (2 : ℝ) ^ (2 ^ n : ℕ) ≤ Q.gain) :
    ArithmeticAmplification := by
  let k₀ : ℕ := 2 ^ N
  have hk₀ : 0 < k₀ := pow_pos (by decide) _
  refine ⟨C ^ k₀, one_lt_pow₀ hC hk₀.ne', b * k₀, by positivity, ?_⟩
  intro n
  let j := max N n
  have hj : 2 ^ j ≤ k₀ * 2 ^ n := by
    dsimp [j, k₀]
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨L, hL, hsize, Q, hgain⟩ := tail j (le_max_left _ _)
  have hscale : C ^ (2 ^ j : ℕ) ≤ (C ^ k₀) ^ (2 ^ n : ℕ) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hC.le hj
  refine ⟨L, hL, hsize.trans (Real.exp_le_exp.mpr ?_), Q.raiseScale (by positivity) hscale, ?_⟩
  · rw [mul_assoc, ← Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hb.le
  · exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.pow_le_pow_right (by decide) (le_max_right N n))).trans hgain

end MT
