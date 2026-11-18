module

public import MT.Definitions
public import Mathlib.Tactic

/-! Positivity of the d-dimensional area of the unit sphere, including d = 0. -/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace MT

/-- The projection onto the first d coordinates maps the unit sphere onto a
set containing the open unit ball. In particular the sphere has positive
normalized Hausdorff area. -/
theorem sphereArea_pos (d : ℕ) :
    0 < (Measure.euclideanHausdorffMeasure d) (Metric.sphere (0 : Space (d+1)) 1) := by
  let P : Space (d+1) →L[ℝ] Space d :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i : Fin d =>
        PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d+1) => ℝ) i.castSucc))
  let S := Metric.sphere (0 : Space (d+1)) 1
  have hcover : Metric.ball (0 : Space d) 1 ⊆ P '' S := by
    intro x hx
    let a := Real.sqrt (1-‖x‖^2)
    let y : Space (d+1) := WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => x i) a)
    have hnorm : ‖x‖ < 1 := by simpa using hx
    have ha : a^2 = 1-‖x‖^2 := Real.sq_sqrt (by nlinarith [norm_nonneg x])
    have hy : ‖y‖^2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
      simp only [y, Fin.snoc_castSucc, Fin.snoc_last]
      rw [← EuclideanSpace.real_norm_sq_eq, ha]
      ring
    refine ⟨y, ?_, ?_⟩
    · change y ∈ Metric.sphere 0 1
      rw [Metric.mem_sphere, dist_zero_right]
      nlinarith [norm_nonneg y]
    · ext i
      change Fin.snoc (α := fun _ => ℝ) (fun j => x j) a i.castSucc = x i
      simp
  have hball : 0 < (Measure.hausdorffMeasure (d : ℝ)) (Metric.ball (0 : Space d) 1) := by
    have hh := Metric.isOpen_ball.measure_pos
      (Measure.hausdorffMeasure (Module.finrank ℝ (Space d) : ℝ))
      (Metric.nonempty_ball.mpr (show (0:ℝ) < 1 by norm_num) :
        (Metric.ball (0 : Space d) 1).Nonempty)
    simpa [Space] using hh
  have himage := P.lipschitzWith.hausdorffMeasure_image_le
    (show 0 ≤ (d : ℝ) by positivity) S
  have hraw : (Measure.hausdorffMeasure (d : ℝ)) S ≠ 0 :=
    (ENNReal.mul_pos_iff.mp (hball.trans_le ((measure_mono hcover).trans himage))).2.ne'
  change 0 < (Measure.euclideanHausdorffMeasure d) S
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  apply ENNReal.mul_pos
  · exact_mod_cast Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
  · exact hraw

end MT
