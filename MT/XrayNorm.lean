module

public import MT.Definitions

/-! From uniform line integrals (Lemma 3.5) to the X-ray norm in §1. -/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace MT

/-- Apply Lemma 3.5 to each unit direction and each perpendicular offset.
Line integrability is stated explicitly as weights can have exceptional traces. -/
theorem xrayNorm_le_of_line_bound {d : ℕ} {w : Space (d + 1) → ℝ} {M : ℝ}
    (_hw : Continuous w) (hw₀ : ∀ x, 0 ≤ w x)
    (hint : ∀ ν : Space (d + 1), ‖ν‖ = 1 → ∀ y : Space (d + 1),
      Integrable (fun s : ℝ => w (y + s • ν)))
    (hbound : ∀ ν : Space (d + 1), ‖ν‖ = 1 → ∀ y : Space (d + 1),
      (∫ s : ℝ, w (y + s • ν)) ≤ M) : xrayNorm w ≤ ENNReal.ofReal M := by
  refine essSup_le_of_ae_le _ ?_
  apply (ae_restrict_iff' Metric.isClosed_sphere.measurableSet).2
  filter_upwards with ν hν
  have hunit : ‖ν‖ = 1 := by simpa [Metric.mem_sphere] using hν
  apply iSup_le
  intro y
  apply iSup_le
  intro _
  rw [← ofReal_integral_eq_lintegral_ofReal (hint ν hunit y) (ae_of_all _ fun s => hw₀ _)]
  exact ENNReal.ofReal_le_ofReal (hbound ν hunit y)

/-- A continuous weight positive at the origin has positive X-ray norm.
The sphere area hypothesis is separated here from the one-dimensional
argument; no integrability assumption on the individual slices is needed. -/
theorem xrayNorm_pos {d : ℕ} {w : Space (d + 1) → ℝ}
    (hw : Continuous w) (hw₀ : 0 < w 0)
    (hσ : 0 < (Measure.euclideanHausdorffMeasure d) (Metric.sphere (0 : Space (d+1)) 1)) :
    0 < xrayNorm w := by
  let S := Metric.sphere (0 : Space (d + 1)) 1
  let μ := surfaceMeasure S
  have hμ : μ Set.univ ≠ 0 := by
    simpa [μ, S, surfaceMeasure] using hσ.ne'
  let : NeZero μ := ⟨fun h => hμ (by simp [h])⟩
  have hlines (ν : Space (d + 1)) : 0 < xray w ν := by
    let F (t : ℝ) := ENNReal.ofReal (w (0 + t • ν))
    have hc : Continuous F := ENNReal.continuous_ofReal.comp
      (hw.comp (continuous_const.add (continuous_id.smul continuous_const)))
    have hm : 0 < (∫⁻ t : ℝ, F t) :=
      (lintegral_pos_iff_support hc.measurable).mpr <|
        hc.isOpen_support.measure_pos volume ⟨0, by simpa [F] using hw₀⟩
    exact hm.trans_le ((le_iSup_of_le (0 : Space (d+1))
      (le_iSup_of_le (show ⟪(0 : Space (d+1)), ν⟫_ℝ = 0 by simp) le_rfl)))
  by_contra! h
  have he : essSup (xray w) μ = 0 := bot_unique h
  obtain ⟨ν, hν⟩ := (ENNReal.essSup_eq_zero_iff.mp he).exists
  exact (hlines ν).ne' hν

end MT
