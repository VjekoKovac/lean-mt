module

public import MT.Definitions

/-! Basic comparison principles for the constants in §1. -/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace MT

/-- Enlarging the ball keeps every previously admissible test weight. -/
theorem localConstant_mono {d : ℕ} (S : Set (Space (d + 1))) :
    Monotone (localConstant S) := by
  intro R R' hR
  apply sSup_le_sSup
  rintro q ⟨f, w, h₁, h₂, ⟨hw, hwloc, hsupp⟩, hpos, hfin, hq⟩
  exact ⟨f, w, h₁, h₂, ⟨hw, hwloc, hsupp.trans (Metric.ball_subset_ball hR)⟩,
    hpos, hfin, hq⟩

/-- The test-class constant gives a lower bound for every full L² constant. -/
theorem localConstant_le_full {d : ℕ} (S : Set (Space (d + 1))) (R : ℝ)
    (E : (Space (d + 1) → ℂ) → Space (d + 1) → ℂ) (hE : AgreesOnCore S E) :
    localConstant S R ≤ fullLocalConstant S R E := by
  apply sSup_le_sSup
  rintro q ⟨f, w, ⟨hint, _⟩, hmem, hw, hpos, hfin, hq⟩
  refine ⟨f, w, trivial, hmem, hw, hpos, hfin, ?_⟩
  have hmass : weightedMass (E f) w = weightedMass (extension S f) w := by
    apply lintegral_congr_ae
    filter_upwards [hE f hint hmem] with x hx
    simp only [hx]
  simpa only [hmass] using hq

/-- The integral itself supplies one realization, so the agreement condition in
the statement cannot be vacuous. -/
theorem extension_agreesOnCore {d : ℕ} (S : Set (Space (d + 1))) :
    AgreesOnCore S (extension S) := by
  intro f hf h₂
  exact Filter.EventuallyEq.rfl

/-- Suffices to construct the lower bound with the integrable tests of §3. -/
theorem powerLoss_of_core
    (h : ∀ β : ℝ, 0 < β → β ≤ 1 →
      ∃ α : ℝ, 0 < α ∧ ∀ (d : ℕ), 0 < d → ∀ S : Set (Space (d + 1)),
        IsHypersurface β S → HasCurvature β S →
          EventuallyPowerBound α (localConstant S)) : PowerLoss := by
  intro β hβ₀ hβ₁
  obtain ⟨α, hα, hs⟩ := h β hβ₀ hβ₁
  refine ⟨α, hα, ?_⟩
  intro d hd S hS hcurv
  obtain ⟨c, R₀, hc, hR₀, hh⟩ := hs d hd S hS hcurv
  exact ⟨c, R₀, hc, hR₀, fun R hR E hE =>
    (hh R hR).trans (localConstant_le_full S R E hE)⟩

/-- The source permits the exponent to be chosen small. Once the radius is at
least one, any smaller positive exponent keeps the same coefficient and
threshold. Thus the existential positivity in `PowerLoss` retains this feature. -/
theorem eventuallyPowerBound_mono_exponent {α γ : ℝ} {C : ℝ → ℝ≥0∞}
    (hγα : γ ≤ α) (h : EventuallyPowerBound α C) : EventuallyPowerBound γ C := by
  obtain ⟨c, R₀, hc, h₀, hb⟩ := h
  refine ⟨c, R₀, hc, h₀, ?_⟩
  intro R hR
  exact (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (h₀.trans hR) hγα) hc.le)).trans
    (hb R hR)

end MT
