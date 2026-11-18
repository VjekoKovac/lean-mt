module

public import MT.Taylor
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-! # Surface area on a local graph patch
Section 3 uses uniform upper and lower bounds for graph area on sufficiently
small parameter cubes. The normalization of Hausdorff area makes the lower
bound exactly Lebesgue volume. The upper constant is common to all compact
subsets of a fixed chart neighborhood.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped Topology NNReal ENNReal

namespace MT

theorem GraphChart.dist_sq {d : ℕ} (g : GraphChart d) (x y : Space d) :
    dist (g.point x) (g.point y) ^ 2 =
      dist x y ^ 2 + dist (g.height x) (g.height y) ^ 2 := by
  simp only [GraphChart.point, IsometryEquiv.dist_eq, EuclideanSpace.dist_sq_eq]
  rw [Fin.sum_univ_castSucc]
  simp

/-- Orthogonal projection back to the base coordinates does not expand distances. -/
theorem GraphChart.antilipschitz {d : ℕ} (g : GraphChart d) : AntilipschitzWith 1 g.point := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one, one_mul]
  exact (sq_le_sq₀ dist_nonneg dist_nonneg).mp
    ((g.dist_sq x y).symm ▸ le_add_of_nonneg_right (sq_nonneg _))

theorem GraphChart.lipschitzOn {d : ℕ} (g : GraphChart d) {T : Set (Space d)} {K : ℝ≥0}
    (h : LipschitzOnWith K g.height T) : LipschitzOnWith (1 + K) g.point T := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hh := h.dist_le_mul x hx y hy
  apply (sq_le_sq₀ dist_nonneg (mul_nonneg (by positivity) dist_nonneg)).mp
  rw [g.dist_sq]
  push_cast
  have hs := (sq_le_sq₀ dist_nonneg (mul_nonneg K.coe_nonneg dist_nonneg)).mpr hh
  nlinarith [mul_nonneg K.coe_nonneg (sq_nonneg (dist x y))]

/-- Uniform comparability for compact parameter sets in one fixed neighborhood. -/
theorem GraphChart.local_area_bounds {d : ℕ} {β : ℝ} {g : GraphChart d}
    {S : Set (Space (d+1))} (hg : g.ValidFor β S) {u : Space d}
    (hu : u ∈ g.domain) (hu' : g.point u ∈ g.region) :
    ∃ K : ℝ≥0, ∃ U ∈ 𝓝 u, ∀ T ⊆ U, IsCompact T →
      volume T ≤ surfaceMeasure S (g.point '' T) ∧
        surfaceMeasure S (g.point '' T) ≤ (K : ℝ≥0∞) ^ d * volume T := by
  have hc : ContDiffAt ℝ 1 g.height u :=
    (hg.2.2.2.1.contDiffAt (hg.1.mem_nhds hu)).of_le (by norm_num)
  obtain ⟨K, U, hU, hLip⟩ := hc.exists_lipschitzOnWith
  refine ⟨1+K, U ∩ {x | g.point x ∈ S}, Filter.inter_mem hU (GraphChart.eventually_point_mem hg hu hu'), ?_⟩
  intro T hT ht
  have lip := (g.lipschitzOn hLip).mono (hT.trans inter_subset_left)
  have hi : g.point '' T ⊆ S := by rintro _ ⟨x, hx, rfl⟩; exact (hT hx).2
  have hm := (ht.image_of_continuousOn lip.continuousOn).measurableSet
  rw [surfaceMeasure, Measure.restrict_apply hm, inter_eq_left.mpr hi,
    ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume d]
  have low := g.antilipschitz.le_hausdorffMeasure_image (Nat.cast_nonneg d) T
  have up := lip.hausdorffMeasure_image_le (Nat.cast_nonneg d)
  simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at low
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  constructor
  · exact mul_le_mul_of_nonneg_left low bot_le
  · rw [← mul_left_comm]
    exact mul_le_mul_of_nonneg_left (by simpa using up) bot_le

end MT
