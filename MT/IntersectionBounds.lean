module

public import Mathlib.Tactic

/-! # Uniform constants for the arithmetic configuration
The two factors of the field covolume in the return estimate multiply to the
absolute discriminant. Hence the loss depends only on its root and is
independent of the seed size, dilation, or degree.
-/

@[expose] public section
namespace MT.Intersections

/-- Absorb the additive packing error and the factor 2 into the k-th power. -/
theorem upper_base {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 1 ≤ r) :
    1 + 2^k*r^k ≤ (4*r)^k := by
  have h : 1 ≤ 2^k*r^k := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num) ) (one_le_pow₀ hr)
  have h' : (2 : ℝ) ≤ 2^k := le_self_pow₀ (by norm_num) hk.ne'
  calc
    _ ≤ 2*(2^k*r^k) := by linarith
    _ ≤ 2^k*(2^k*r^k) := mul_le_mul_of_nonneg_right h' (by positivity)
    _ = _ := by rw [show (4:ℝ)*r = 2*(2*r) by ring, mul_pow, mul_pow]

/-- Normalize the lower count for generator intervals with loss cA=2. -/
theorem lower_A_base {m k : ℕ} (hk : 0 < k) {H D s A : ℝ} (hH : 1 ≤ H)
    (hD : 0 ≤ D) (hDH : D ≤ H) (hs : 0 < s) (hsq : s^2 ≤ D^k)
    (ha : (m:ℝ)^k*(H^k/(2*s)) ≤ A) : ((m:ℝ)/2)^k ≤ A := by
  have hHs := pow_le_pow_left₀ hD hDH k
  have hsH : s ≤ H^k := by
    rcases le_total s 1 with h | h
    · exact h.trans (one_le_pow₀ hH)
    · nlinarith [mul_nonneg hs.le (sub_nonneg.mpr h)]
  have h' : (2 : ℝ) ≤ 2^k := le_self_pow₀ (by norm_num) hk.ne'
  apply le_trans _ ha
  rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    _ ≤ (m:ℝ)^k*(2*H^k) := by gcongr
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left h' (show 0 ≤ (m:ℝ)^k*H^k by positivity)]

/-- Normalize the upper count of B and the lower count of returning points.
Here V denotes the vertical half-width and s is the covolume of the field. -/
theorem return_base {m k : ℕ} (hk : 0 < k) (hm : 0 < m) {H V D s B T : ℝ}
    (hH : 0 < H) (hV : 0 < V) (hD : 0 < D) (hs : 0 < s) (hsq : s^2 ≤ D^k)
    (hb : B ≤ ((2:ℝ)^m)^k * ((4*H)^k * (4*V)^k))
    (ht : ((2:ℝ)^(m-1))^k * (((H/2)^k / (2*s)) * ((V/2)^k / (2*s))) ≤ T) :
    B ≤ (512*D)^k*T := by
  have h' : (4 : ℝ) ≤ 4^k := le_self_pow₀ (by norm_num) hk.ne'
  have h1 : 4*s^2 ≤ (4*D)^k := by
    rw [mul_pow]
    exact mul_le_mul h' hsq (sq_nonneg _) (by positivity)
  have hm' : (2:ℝ)^m = 2*2^(m-1) := by
    conv_lhs => rw [show m=(m-1)+1 by omega, pow_succ]
    ring
  have ht' : ((2:ℝ)^(m-1)*(H/2)*(V/2))^k ≤ T*(4*s^2) := by
    rw [← div_le_iff₀ (by positivity : 0 < 4*s^2)]
    convert ht using 1
    rw [mul_pow, mul_pow]
    field_simp
    ring
  apply le_of_mul_le_mul_right (a := 4*s^2)
  · calc
      B*(4*s^2) ≤ (((2:ℝ)^m)^k*((4*H)^k*(4*V)^k))*(4*s^2) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ ≤ (((2:ℝ)^m)^k*((4*H)^k*(4*V)^k))*(4*D)^k := by gcongr
      _ = (512*D)^k*((2^(m-1)*(H/2)*(V/2))^k) := by
        simp only [← mul_pow, hm']
        congr 1
        ring
      _ ≤ (512*D)^k*(T*(4*s^2)) := mul_le_mul_of_nonneg_left ht' (by positivity)
      _ = _ := by ring
  · positivity

end MT.Intersections
