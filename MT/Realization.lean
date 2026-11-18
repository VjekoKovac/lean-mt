module

public import MT.Constant

/-!
# Comparing the full L² statement to the integrable tests
The proof of Theorem 1.3 uses integrable data on a single patch. Quantifying
over all extensions agreeing on such data preserves exactly that lower-bound
problem. This module supplies the reverse implication as a statement audit.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MT

/-- An extension of the integral on its absolutely convergent data. Its
choice of value on the complement is used only for comparing suprema. -/
def zeroOutsideCore {d : ℕ} (S : Set (Space (d + 1)))
    (f : Space (d + 1) → ℂ) : Space (d + 1) → ℂ := by
  classical
  exact if Integrable f (surfaceMeasure S) then extension S f else 0

theorem zeroOutsideCore_agrees {d : ℕ} (S : Set (Space (d + 1))) :
    AgreesOnCore S (zeroOutsideCore S) := by
  intro f hf _
  simp [zeroOutsideCore, hf]

/-- The L¹ ∩ L² supremum with exactly the weight class of the full problem.
The transfer construction can use the smaller Borel-weight test family. -/
def integrableDataConstant {d : ℕ} (S : Set (Space (d + 1))) (R : ℝ) : ℝ≥0∞ :=
  sSup (ratios S R (extension S) (fun f _ => Integrable f (surfaceMeasure S)))

/-- For this realization, every test outside the integrable class contributes
a zero ratio. The weight class is identical on both sides of the equality. -/
theorem fullLocalConstant_zeroOutsideCore {d : ℕ} (S : Set (Space (d + 1))) (R : ℝ) :
    fullLocalConstant S R (zeroOutsideCore S) = integrableDataConstant S R := by
  classical
  apply le_antisymm
  · apply sSup_le
    rintro q ⟨f, w, _, hmem, hw, hpos, hfin, hq⟩
    by_cases hf : Integrable f (surfaceMeasure S)
    · apply le_sSup
      exact ⟨f, w, hf, hmem, hw, hpos, hfin, by simpa [zeroOutsideCore, hf] using hq⟩
    · simp [hq, zeroOutsideCore, hf, weightedMass]
  · apply sSup_le_sSup
    rintro q ⟨f, w, hf, hmem, hw, hpos, hfin, hq⟩
    exact ⟨f, w, trivial, hmem, hw, hpos, hfin, by simpa [zeroOutsideCore, hf] using hq⟩

/-- At fixed S, R and weight class, the full lower bound uniform over
realizations is equivalent to the lower bound on integrable data. -/
theorem full_lower_bound_iff_integrable {d : ℕ} (S : Set (Space (d + 1))) (R : ℝ)
    (B : ℝ≥0∞) :
    (∀ E, AgreesOnCore S E → B ≤ fullLocalConstant S R E) ↔
      B ≤ integrableDataConstant S R := by
  constructor
  · intro h
    simpa only [fullLocalConstant_zeroOutsideCore] using h (zeroOutsideCore S) (zeroOutsideCore_agrees S)
  · intro h E hE
    apply h.trans
    apply sSup_le_sSup
    rintro q ⟨f, w, hf, hmem, hw, hpos, hfin, hq⟩
    refine ⟨f, w, trivial, hmem, hw, hpos, hfin, ?_⟩
    have hmass : weightedMass (E f) w = weightedMass (extension S f) w := by
      apply lintegral_congr_ae
      filter_upwards [hE f hf hmem] with x hx
      simp only [hx]
    simpa only [hmass] using hq

/-- Once a power works at all sufficiently large radii, it can be replaced
by any prescribed smaller exponent. This spells out the source's choice of
a small positive exponent. -/
theorem EventuallyPowerBound.of_exponent_le {C : ℝ → ℝ≥0∞} {α γ : ℝ}
    (h : EventuallyPowerBound α C) (hγα : γ ≤ α) : EventuallyPowerBound γ C := by
  obtain ⟨c, R₀, hc, hR₀, hr⟩ := h
  refine ⟨c, R₀, hc, hR₀, ?_⟩
  intro R hR
  have hp := Real.rpow_le_rpow_of_exponent_le (hR₀.trans hR) hγα
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp hc.le)).trans (hr R hR)

end MT
