module

public import MT.LineEstimates

/-! Explicit constants for the scales in (3.1). -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace MT

/-- Frequency scale h, spatial length Y, time length T and cube half-width ε.
The constants c and δ can be made small before H is chosen. -/
structure TransferScales where
  h : ℝ
  Y : ℝ
  T : ℝ
  ε : ℝ

def transferScales (β H c δ : ℝ) : TransferScales :=
  let h := c / H ^ (1 / β)
  ⟨h, H/h, H/h^2, δ*h/H⟩

theorem transferScales_bounds {β H c δ : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hH : 1 ≤ H)
    (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ) :
    let s := transferScales β H c δ
    0 < s.h ∧ 0 < s.Y ∧ 0 < s.T ∧ 0 < s.ε ∧
    s.h*H ≤ c ∧ s.Y ≤ s.T ∧ s.Y*H ≤ s.T ∧
    s.T*s.h^2 = H ∧ s.T = H^(1+2/β)/c^2 ∧ s.Y*s.ε = δ ∧
    s.T*(s.h*s.ε) = δ ∧ s.T*s.ε^2 = δ^2/H ∧ s.T*s.h^(2+β) = c^β := by
  let a := H^(1/β)
  let h := c/a
  have hH₀ : 0 < H := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hha : 0 < h := div_pos hc ha
  have hHle : H ≤ a := by
    calc H = H^(1:ℝ) := (Real.rpow_one H).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH ((le_div_iff₀ hβ).2 (by linarith))
  have hsmall : h*H ≤ c := by
    dsimp [h]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ ha).2 (mul_le_mul_of_nonneg_left hHle hc.le)
  have hle : h ≤ 1 := (le_mul_of_one_le_right hha.le hH).trans (hsmall.trans hc1)
  have hrate : H^(1+2/β) = H*a^2 := by
    rw [Real.rpow_add hH₀, Real.rpow_one, show 2/β = (1/β)*(2:ℝ) by ring,
      Real.rpow_mul hH₀.le, Real.rpow_two]
  have hpow : h ^ β = c ^ β / H := by
    dsimp [h,a]
    rw [Real.div_rpow hc.le (by positivity), ← Real.rpow_mul hH₀.le,
      show 1 / β * β = 1 by field_simp, Real.rpow_one]
  change 0 < h ∧ 0 < H/h ∧ 0 < H/h^2 ∧ 0 < δ*h/H ∧ h*H ≤ c ∧
    H/h ≤ H/h^2 ∧ H/h*H ≤ H/h^2 ∧ H/h^2*h^2 = H ∧ H/h^2 = H^(1+2/β)/c^2 ∧
    H/h*(δ*h/H) = δ ∧ H/h^2*(h*(δ*h/H)) = δ ∧ H/h^2*(δ*h/H)^2 = δ^2/H ∧
    H/h^2*h^(2+β) = c^β
  refine ⟨hha, by positivity, by positivity, by positivity, hsmall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply div_le_div_of_nonneg_left hH₀.le (by positivity)
    nlinarith [mul_nonneg hha.le (sub_nonneg.mpr hle)]
  · field_simp
    nlinarith [mul_nonneg hH₀.le (sub_nonneg.mpr (hsmall.trans hc1))]
  · field_simp
  · rw [hrate]
    dsimp [h]
    field_simp
  · field_simp
  · field_simp
  · field_simp
  · rw [Real.rpow_add hha, Real.rpow_two, hpow]
    field_simp

/-- The weight from (3.1) is admissible at exactly the claimed radius scale,
and its X-ray norm has a strictly positive, finite bound. -/
theorem counterWeight_at_transfer_scale {d : ℕ} {β H L c δ : ℝ}
    (Q : Configuration H L) (p q : Fin (d+1))
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hH : 1 ≤ H) (hL : 0 ≤ L)
    (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ) :
    let s := transferScales β H c δ
    let w := counterWeight Q.B p q s.h s.Y s.T
    let κ := (Real.sqrt (d+1 : ℝ)+1)/c^2
    Continuous w ∧ AdmissibleWeight (κ * H^(1+2/β)) w ∧
      0 < xrayNorm w ∧ xrayNorm w ≤ ENNReal.ofReal (12*(d+1 : ℝ)*s.T*L*Q.B.card) := by
  let s := transferScales β H c δ
  obtain ⟨hh,hY,hT,hε,hhH,hYT,hYH,hTH,hrate,_⟩ := transferScales_bounds hβ hβ1 hH hc hc1 hδ
  have hrad : (Real.sqrt (d+1 : ℝ)+1)/c^2 * H^(1+2/β) =
      (Real.sqrt (d+1 : ℝ)+1)*s.T := by rw [show s.T = _ from hrate]; ring
  refine ⟨continuous_counterWeight .., ?_, counterWeight_xrayNorm_pos _ Q.nonemptyB ..,
    counterWeight_xrayNorm Q p q hH hL hh hY hT hTH hYH⟩
  rw [hrad]
  exact admissible_counterWeight Q.B p q hY hYT

end MT
