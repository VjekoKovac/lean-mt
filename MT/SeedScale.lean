module

public import MT.Overlap

/-! # Uniform choice of the parabolic dilation for the arithmetic construction
Choose a single ρ after the horizontal half-width and the seed size, before
the field dimension. It controls both opposite-face overlaps and the geometric
threshold for disjointness and line occupancy.
-/

@[expose] public section
noncomputable section
namespace MT.Seed

/-- The scale can be fixed before choosing any number field. The vertical
half-width dominates twice H. Every point in a horizontal generator interval
displaces the center of the vertical interval by at most its half-width. -/
theorem exists_overlap_scale (m : ℕ) (H : ℝ) (hH : 1 ≤ H) :
    ∃ ρ : ℝ, 16 ≤ ρ ∧ dilationThreshold m H ≤ ρ ∧ 2*H ≤ ρ^(3/2 : ℝ) ∧
      ∀ a : ℤ, 1 ≤ a → a ≤ (2:ℤ)^(3*m) → ∀ x : ℝ, |x-ρ*a| ≤ H →
        |x^2-ρ^2*(a:ℝ)^2| ≤ ρ^(3/2 : ℝ) := by
  let A := (2 : ℝ)^(3*m)
  let T := 2*H*A + H^2
  let ρ := max (max 16 (dilationThreshold m H)) (max (2*H) (T^2))
  have h16 : 16 ≤ ρ := (le_max_left _ _).trans (le_max_left _ _)
  have hr : 1 ≤ ρ := le_trans (by norm_num) h16
  have hr' : 0 < ρ := lt_of_lt_of_le zero_lt_one hr
  have hT : T ≤ Real.sqrt ρ := Real.le_sqrt_of_sq_le
    ((le_max_right _ _).trans (le_max_right _ _))
  have hV : ρ^(3/2 : ℝ) = ρ * Real.sqrt ρ := by
    rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add hr', Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hs : 1 ≤ Real.sqrt ρ := Real.le_sqrt_of_sq_le (by simpa using hr)
  have hrV : ρ ≤ ρ^(3/2 : ℝ) := by rw [hV]; exact le_mul_of_one_le_right hr'.le hs
  refine ⟨ρ, h16, (le_max_right _ _).trans (le_max_left _ _),
    ((le_max_left _ _).trans (le_max_right _ _)).trans hrV, ?_⟩
  intro a ha ha' x hx
  have hA : (a : ℝ) ≤ A := by dsimp [A]; exact_mod_cast ha'
  have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast (show (0:ℤ) ≤ a by omega)
  have habs : |ρ*(a:ℝ)| = ρ*a := abs_of_nonneg (mul_nonneg hr'.le ha0)
  have hh := vertical_shift_le hx
  rw [habs, mul_pow] at hh
  rw [hV]
  apply hh.trans
  calc
    H*(2*(ρ*a)+H) ≤ H*(2*(ρ*A)+H) := by gcongr
    _ ≤ ρ*T := by dsimp [T]; nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg H)]
    _ ≤ ρ*Real.sqrt ρ := mul_le_mul_of_nonneg_left hT hr'.le

end MT.Seed
