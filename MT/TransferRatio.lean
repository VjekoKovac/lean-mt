module

public import MT.Constant
public import MT.Configuration
public import MT.Transfer

/-! The last step of Proposition 3.1, in the analytic definitions of §1. -/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace MT

/-- For an actual test pair, the lower bound for the weighted extension mass
(Lemma 3.4), the upper bound for the squared input norm (the estimate for the cubes immediately
before Lemma 3.4), and the uniform X-ray bound (Lemma 3.5) imply the
energy-to-occupancy lower bound. The existence and the three estimates for the
paper's particular pair remain separate obligations. -/
theorem localConstant_of_transfer_estimates {d : ℕ} (S : Set (Space (d + 1)))
    {R H L T cE cF cX : ℝ} (Q : Configuration H L)
    (f : Space (d + 1) → ℂ) (w : Space (d + 1) → ℝ)
    (hf : Integrable f (surfaceMeasure S)) (h₂ : MemLp f 2 (surfaceMeasure S))
    (hwB : Measurable w) (hw : AdmissibleWeight R w) (hd : 0 < denominator S f w)
    (hL : 1 ≤ L) (hT : 0 < T) (hcE : 0 < cE) (hcF : 0 < cF) (hcX : 0 < cX)
    (hmass : ENNReal.ofReal (cE * T * (energy Q.A Q.B : ℝ)) ≤
      weightedMass (extension S f) w)
    (hinput : (eLpNorm f 2 (surfaceMeasure S)) ^ 2 ≤ ENNReal.ofReal (cF * Q.A.card))
    (hxray : xrayNorm w ≤ ENNReal.ofReal (cX * (L * T * Q.B.card))) :
    ENNReal.ofReal (cE / (cF * cX) * Q.gain) ≤ localConstant S R := by
  have ha : (0 : ℝ) < Q.A.card := by exact_mod_cast Finset.card_pos.mpr Q.nonemptyA
  have hb : (0 : ℝ) < Q.B.card := by exact_mod_cast Finset.card_pos.mpr Q.nonemptyB
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let F := cF * (Q.A.card : ℝ)
  let X := cX * (L * T * (Q.B.card : ℝ))
  have hF : 0 < F := mul_pos hcF ha
  have hX : 0 < X := mul_pos hcX (mul_pos (mul_pos hLpos hT) hb)
  have hden : denominator S f w ≤ ENNReal.ofReal (F * X) := by
    rw [ENNReal.ofReal_mul hF.le]
    exact mul_le_mul' hinput hxray
  have hscalar := transfer_quotient (E := (energy Q.A Q.B : ℝ))
    (N := cE * T * (energy Q.A Q.B : ℝ)) (by positivity) hF hX hT hLpos ha hb
    hcE hcF hcX le_rfl le_rfl le_rfl
  calc
    _ ≤ ENNReal.ofReal ((cE * T * (energy Q.A Q.B : ℝ)) / (F * X)) :=
      ENNReal.ofReal_le_ofReal hscalar
    _ ≤ weightedMass (extension S f) w / denominator S f w := by
      rw [ENNReal.ofReal_div_of_pos (mul_pos hF hX)]
      exact ENNReal.div_le_div hmass hden
    _ ≤ _ := le_sSup (show _ ∈ ratios S R (extension S)
        (fun g v => Integrable g (surfaceMeasure S) ∧ Measurable v) from
      ⟨f, w, ⟨hf, hwB⟩, h₂, hw, hd, hden.trans_lt ENNReal.ofReal_lt_top, rfl⟩)

end MT
