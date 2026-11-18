module

public import MT.LineEstimates
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Physical change of variables for the chart normalization in §3.
The source applies an invertible linear map in frequency, so the physical
variable changes by its adjoint. The statements below apply to every
invertible physical linear map, including these adjoints. -/

public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MT

/-- A continuous linear equivalence in positive dimension has positive operator norm. -/
theorem equiv_opNorm_pos {d : ℕ} (A : Space (d+1) ≃L[ℝ] Space (d+1)) :
    0 < ‖A.toContinuousLinearMap‖ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Space (d+1))
  have hAv : A v ≠ 0 := by simpa using A.injective.ne hv
  exact pos_of_mul_pos_left ((norm_pos_iff.mpr hAv).trans_le (A.toContinuousLinearMap.le_opNorm v)) (norm_nonneg _)

/-- The pullback of an admissible continuous weight is supported in the
open ball whose radius is multiplied by the inverse operator norm. -/
theorem admissibleWeight_comp {d : ℕ} (A : Space (d+1) ≃L[ℝ] Space (d+1))
    {w : Space (d+1) → ℝ} {R : ℝ} (hw : Continuous w) (ha : AdmissibleWeight R w) :
    AdmissibleWeight (‖A.symm.toContinuousLinearMap‖ * R) (fun x => w (A x)) := by
  refine ⟨fun x => ha.1 (A x), (hw.comp A.continuous).locallyIntegrable, ?_⟩
  intro x hx
  have hs := tsupport_comp_subset_preimage (f := A) w A.continuous hx
  have hR : ‖A x‖ < R := by simpa [Metric.mem_ball] using ha.2.2 hs
  have hx' : ‖x‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A x‖ := by
    simpa using A.symm.toContinuousLinearMap.le_opNorm (A x)
  simpa [Metric.mem_ball] using hx'.trans_lt (mul_lt_mul_of_pos_left hR (equiv_opNorm_pos A.symm))

/-- Change the speed on an arbitrary line after applying an invertible linear
map. All offsets are retained because a perpendicular offset can cease to be
perpendicular after the map. -/
theorem line_bound_comp {n : ℕ} (A : Space n ≃L[ℝ] Space n)
    {w : Space n → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hline : ∀ u y : Space n, ‖u‖ = 1 →
      Integrable (fun t : ℝ => w (y+t•u)) ∧ (∫ t : ℝ, w (y+t•u)) ≤ M)
    (v y : Space n) (hv : ‖v‖ = 1) :
    Integrable (fun t : ℝ => w (A (y+t•v))) ∧
      (∫ t : ℝ, w (A (y+t•v))) ≤ ‖A.symm.toContinuousLinearMap‖ * M := by
  have hv' : v ≠ 0 := norm_pos_iff.mp (hv ▸ zero_lt_one)
  have hAv : A v ≠ 0 := by simpa using A.injective.ne hv'
  let r := ‖A v‖
  have hr : 0 < r := norm_pos_iff.mpr hAv
  let u := r⁻¹ • A v
  have hu : ‖u‖ = 1 := by
    change ‖r⁻¹ • A v‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  have hback (t : ℝ) : (r*t) • u = t • A v := by
    dsimp only [u]
    rw [smul_smul, mul_comm r t, mul_assoc, mul_inv_cancel₀ hr.ne', mul_one]
  let F (s : ℝ) := w (A y+s•u)
  have heq : (fun t : ℝ => w (A (y+t•v))) = fun t => F (r*t) := by
    funext t
    simp [F, hback]
  have hinv : r⁻¹ ≤ ‖A.symm.toContinuousLinearMap‖ := by
    rw [← one_div, div_le_iff₀ hr]
    simpa [r, hv] using A.symm.toContinuousLinearMap.le_opNorm (A v)
  obtain ⟨hint, hb⟩ := hline u (A y) hu
  rw [heq]
  refine ⟨(integrable_comp_mul_left_iff F hr.ne').2 hint, ?_⟩
  rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hr), smul_eq_mul]
  exact (mul_le_mul_of_nonneg_left hb (inv_pos.mpr hr).le).trans
    (mul_le_mul_of_nonneg_right hinv hM)

/-- The essential supremum over unit directions after changing physical
coordinates, derived from a uniform bound for every original line. -/
theorem xrayNorm_comp_le {d : ℕ} (A : Space (d+1) ≃L[ℝ] Space (d+1))
    {w : Space (d+1) → ℝ} {M : ℝ} (hw : Continuous w) (hw₀ : ∀ x, 0 ≤ w x)
    (hM : 0 ≤ M) (hline : ∀ u y : Space (d+1), ‖u‖ = 1 →
      Integrable (fun t : ℝ => w (y+t•u)) ∧ (∫ t : ℝ, w (y+t•u)) ≤ M) :
    xrayNorm (fun x => w (A x)) ≤ ENNReal.ofReal (‖A.symm.toContinuousLinearMap‖ * M) := by
  exact xrayNorm_le_of_line_bound (hw.comp A.continuous) (fun x => hw₀ (A x))
    (fun u hu y => (line_bound_comp A hM hline u y hu).1)
    (fun u hu y => (line_bound_comp A hM hline u y hu).2)

/-- Strict positivity of the essential X-ray norm for the pulled weight. -/
theorem xrayNorm_comp_pos {d : ℕ} (A : Space (d+1) ≃L[ℝ] Space (d+1))
    {w : Space (d+1) → ℝ} (hw : Continuous w) (h₀ : 0 < w 0) :
    0 < xrayNorm (fun x => w (A x)) :=
  xrayNorm_pos (hw.comp A.continuous) (by simpa using h₀) (sphereArea_pos d)

/-- The two factors in the weighted numerator change together. The
absolute determinant enters to the first power, in every dimension. -/
theorem weightedMass_comp_linearEquiv {n : ℕ} (A : Space n ≃L[ℝ] Space n)
    (g : Space n → ℂ) (w : Space n → ℝ) :
    weightedMass (fun x => g (A x)) (fun x => w (A x)) =
      ENNReal.ofReal |LinearMap.det (A.symm : Space n →ₗ[ℝ] Space n)| * weightedMass g w := by
  let f (x : Space n) := ENNReal.ofReal (‖g x‖ ^ 2) * ENNReal.ofReal (w x)
  change (∫⁻ x, f (A.toHomeomorph.toMeasurableEquiv x)) = _ * ∫⁻ x, f x
  rw [← lintegral_map_equiv (μ := volume) f A.toHomeomorph.toMeasurableEquiv]
  have hmap : Measure.map (A.toHomeomorph.toMeasurableEquiv) volume =
      ENNReal.ofReal |LinearMap.det (A.symm : Space n →ₗ[ℝ] Space n)| • volume := by
    ext s hs
    change (Measure.map (A : Space n → Space n) volume) s = _
    rw [Measure.map_apply A.continuous.measurable hs]
    exact Measure.addHaar_preimage_continuousLinearEquiv volume A s
  rw [hmap, lintegral_smul_measure]
  rfl

/-- Undo a physical map in the argument of the extension operator by
pulling back the weight along its inverse. -/
theorem weightedMass_inverse_weight {n : ℕ} (A : Space n ≃L[ℝ] Space n)
    (g : Space n → ℂ) (w : Space n → ℝ) :
    weightedMass g (fun x => w (A.symm x)) =
      ENNReal.ofReal |LinearMap.det (A : Space n →ₗ[ℝ] Space n)| *
        weightedMass (fun y => g (A y)) w := by
  simpa using weightedMass_comp_linearEquiv A.symm (fun y => g (A y)) w

/-- All weight estimates for the actual construction after the physical
map is undone. The same fixed operator norm multiplies the support radius
and the X-ray upper bound. -/
theorem inverse_counterWeight_estimates {d : ℕ} (A : Space (d+1) ≃L[ℝ] Space (d+1))
    {H L T Y h : ℝ} (Q : Configuration H L) (p q : Fin (d+1))
    (hH : 1 ≤ H) (hL : 0 ≤ L) (hh : 0 < h) (hY : 0 < Y) (hYT : Y ≤ T)
    (hscaleT : T*h^2 = H) (hscaleY : Y*H ≤ T) :
    let w := fun x => counterWeight Q.B p q h Y T (A.symm x)
    Continuous w ∧ AdmissibleWeight (‖A.toContinuousLinearMap‖ * ((Real.sqrt (d+1 : ℝ)+1)*T)) w ∧
      0 < xrayNorm w ∧
      xrayNorm w ≤ ENNReal.ofReal (‖A.toContinuousLinearMap‖ * (12*(d+1 : ℝ)*T*L*Q.B.card)) := by
  have hw := continuous_counterWeight Q.B p q h Y T
  have hT : 0 < T := hY.trans_le hYT
  refine ⟨hw.comp A.symm.continuous,
    admissibleWeight_comp A.symm hw (admissible_counterWeight Q.B p q hY hYT),
    xrayNorm_comp_pos A.symm hw ?_, xrayNorm_comp_le A.symm hw (counterWeight_nonneg Q.B p q h Y T) (by positivity) ?_⟩
  · rw [counterWeight_at_zero]
    have hc := Finset.card_pos.mpr Q.nonemptyB
    positivity
  · exact counterWeight_line_bound Q p q hH hL hh hY hT hscaleT hscaleY

end MT
