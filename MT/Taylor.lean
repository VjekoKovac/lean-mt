module

public import MT.Definitions
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Tactic

/-! Quadratic approximation used in Lemma 3.3 of arXiv:2611.22465v1. -/

public section
noncomputable section
open Set Filter
open scoped Topology

namespace MT

/-- Taylor approximation along any straight segment in an open graph chart.
This is the order-(2+β) remainder in Lemma 3.3 *before* diagonalizing its
quadratic form. The estimate uses the Hessian operator norm in `ValidFor`. -/
theorem graph_taylor_remainder {d : ℕ} {φ : Space d → ℝ} {U : Set (Space d)}
    {K β : ℝ} (p : Space d) (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U) (hK : 0 ≤ K)
    (hβ : 0 ≤ β) (hH : ∀ y ∈ U, ‖hessian φ y - hessian φ p‖ ≤ K * ‖y - p‖ ^ β)
    (x : Space d) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p + t • x ∈ U) :
    |φ (p + x) - φ p - fderiv ℝ φ p x - hessian φ p x x / 2| ≤ K * ‖x‖ ^ (2 + β) := by
  let b := fderiv ℝ φ p x
  let a := hessian φ p x x
  let r (t : ℝ) := φ (p + t • x) - φ p - t * b - t ^ 2 / 2 * a
  let r' (t : ℝ) := fderiv ℝ φ (p + t • x) x - b - t * a
  let r'' (t : ℝ) := (hessian φ (p + t • x) - hessian φ p) x x
  have hpath (t : ℝ) : HasDerivAt (fun s : ℝ => p + s • x) x t := by
    simpa using ((hasDerivAt_id t).smul_const x).const_add p
  have dφ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 2 φ (p + t • x) := hφ.contDiffAt (hU.mem_nhds (hseg t ht))
  have dr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt r (r' t) t := by
    have h := ((dφ t ht).differentiableAt (by decide)).hasFDerivAt.comp_hasDerivAt t (hpath t)
    have hh := (((h.sub_const (φ p)).sub ((hasDerivAt_id t).mul_const b)).sub
      ((((hasDerivAt_id t).pow 2).div_const 2).mul_const a))
    change HasDerivAt r _ t at hh
    convert hh using 1
    dsimp [r', id]
    ring
  have dr' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt r' (r'' t) t := by
    have h : ContDiffAt ℝ 1 (fderiv ℝ φ) (p + t • x) := (dφ t ht).fderiv_right (by decide)
    have hg : HasDerivAt (fun s : ℝ => fderiv ℝ φ (p + s • x))
        (hessian φ (p + t • x) x) t :=
      h.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t (hpath t)
    have hh : HasDerivAt (fun s : ℝ => fderiv ℝ φ (p + s • x) x)
        (hessian φ (p + t • x) x x) t := by
      simpa only [map_zero, add_zero] using hg.clm_apply (hasDerivAt_const t x)
    have hhh := (hh.sub_const b).sub ((hasDerivAt_id t).mul_const a)
    change HasDerivAt r' _ t at hhh
    simpa [r'', a] using hhh
  let M := K * ‖x‖ ^ β * ‖x‖ * ‖x‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have d2bound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖r'' t‖ ≤ M := by
    let D := hessian φ (p + t • x) - hessian φ p
    have htx : ‖t • x‖ ≤ ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have hbnd : ‖D‖ ≤ K * ‖x‖ ^ β := by
      have hh := hH _ (hseg t ht)
      simp only [add_sub_cancel_left] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) htx hβ) hK)
    calc
      ‖r'' t‖ ≤ ‖D x‖ * ‖x‖ := (D x).le_opNorm x
      _ ≤ (‖D‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (D.le_opNorm x) (norm_nonneg _)
      _ ≤ M := by dsimp [M]; gcongr
  have d1bound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖r' t‖ ≤ M := by
    have hh := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs => (dr' s hs).hasDerivWithinAt)
      (fun s hs => d2bound s (Ico_subset_Icc_self hs)) t (Ico_subset_Icc_self ht)
    have hr'₀ : r' 0 = 0 := by simp [r', b]
    rw [hr'₀, sub_zero, sub_zero] at hh
    exact hh.trans (mul_le_of_le_one_right hM ht.2.le)
  have bound := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (dr t ht).hasDerivWithinAt) d1bound
  have hpow : M = K * ‖x‖ ^ (2 + β) := by
    rw [Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) hβ,
      Real.rpow_ofNat]
    dsimp [M]
    ring
  simpa [r, Real.norm_eq_abs, b, a, hpow, div_mul_eq_mul_div] using bound

/-- At every point of a valid chart the Hölder Hessian estimate gives one
constant and a whole positive-radius ball on which the Taylor bound holds. -/
theorem GraphChart.exists_taylor_bound {d : ℕ} {g : GraphChart d} {β : ℝ}
    {S : Set (Space (d + 1))} (hg : g.ValidFor β S) (hβ : 0 ≤ β)
    (p : Space d) (hp : p ∈ g.domain) :
    ∃ K ρ : ℝ, 0 ≤ K ∧ 0 < ρ ∧ ∀ x : Space d, ‖x‖ < ρ →
      |g.height (p + x) - g.height p - fderiv ℝ g.height p x - hessian g.height p x x / 2| ≤
        K * ‖x‖ ^ (2 + β) := by
  obtain ⟨hopen, _, _, hφ, K, hK, hholder⟩ := hg
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp hopen p hp
  refine ⟨K, ρ, hK, hρ, ?_⟩
  intro x hx
  apply graph_taylor_remainder p hopen hφ hK hβ
  · intro y hy
    simpa only [dist_eq_norm] using hholder y hy p hp
  · intro t ht
    apply hsub
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hx

/-- Somewhere nonzero curvature supplies a direction with nonzero quadratic
coefficient. Schwarz symmetry is essential to this polarization argument. -/
theorem HasCurvature.exists_direction {d : ℕ} {β : ℝ} {S : Set (Space (d + 1))}
    (h : HasCurvature β S) :
    ∃ g : GraphChart d, g.ValidFor β S ∧ ∃ u ∈ g.domain, g.point u ∈ g.region ∧
      ∃ v : Space d, hessian g.height u v v ≠ 0 := by
  obtain ⟨g, hg, u, hu, him, hn⟩ := h
  refine ⟨g, hg, u, hu, him, ?_⟩
  by_contra! hzero
  apply hn
  have hC : ContDiffAt ℝ 2 g.height u := hg.2.2.2.1.contDiffAt (hg.1.mem_nhds hu)
  have hsym : ∀ v w, hessian g.height u v w = hessian g.height u w v :=
    hC.isSymmSndFDerivAt (by simp)
  ext v w
  have hsum := hzero (v + w)
  simp only [map_add, add_apply] at hsum
  simp only [zero_apply]
  linarith [hzero v, hzero w, hsym v w]

/-- A graph parameter close enough to an interior chart point still belongs
to the represented surface, even if the graph describes only a local patch. -/
theorem GraphChart.eventually_point_mem {d : ℕ} {β : ℝ} {g : GraphChart d}
    {S : Set (Space (d + 1))} (hg : g.ValidFor β S)
    {u : Space d} (hu : u ∈ g.domain) (him : g.point u ∈ g.region) :
    ∀ᶠ y in 𝓝 u, g.point y ∈ S := by
  obtain ⟨hopen, hreg, himage, hφ, _⟩ := hg
  have hc : ContinuousAt g.point u := by
    apply g.rigid.continuous.continuousAt.comp
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) => ℝ)).continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using (hφ.contDiffAt (hopen.mem_nhds hu)).continuousAt
    · simpa using (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).continuousAt (x := u)
  filter_upwards [hopen.mem_nhds hu, hc (hreg.mem_nhds him)] with y hy hiy
  have hh : g.point y ∈ (g.point '' g.domain) ∩ g.region := ⟨⟨y, hy, rfl⟩, hiy⟩
  rw [← himage] at hh
  exact hh.1

/-- The parabolic slice used in the paper's first reduction. Subtracting the
tangent line and dividing by the nonzero quadratic coefficient gives the
standard parabola up to a uniform order-(2+β) error for small signed t. -/
theorem HasCurvature.exists_parabolic_slice {d : ℕ} {β : ℝ} {S : Set (Space (d + 1))}
    (h : HasCurvature β S) (hβ : 0 ≤ β) :
    ∃ g : GraphChart d, g.ValidFor β S ∧ ∃ u ∈ g.domain, g.point u ∈ g.region ∧
      ∃ v : Space d, let q := hessian g.height u v v / 2
        q ≠ 0 ∧ ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ ∀ t : ℝ, |t| < δ →
          g.point (u + t • v) ∈ S ∧
          |(g.height (u + t • v) - g.height u - t * fderiv ℝ g.height u v) / q - t ^ 2| ≤
            K * |t| ^ (2 + β) := by
  obtain ⟨g, hg, u, hu, him, v, hv⟩ := h.exists_direction
  let q := hessian g.height u v v / 2
  have hq : q ≠ 0 := div_ne_zero hv (by norm_num)
  have hv₀ : v ≠ 0 := by
    intro hz
    apply hv
    simp [hz]
  have hnv := norm_pos_iff.mpr hv₀
  obtain ⟨K, ρ, hK, hρ, hbound⟩ := GraphChart.exists_taylor_bound hg hβ u hu
  have path : ContinuousAt (fun t : ℝ => u + t • v) 0 := by fun_prop
  have hpatch : ∀ᶠ t : ℝ in 𝓝 0, g.point (u + t • v) ∈ S := by
    have hm : Tendsto (fun t : ℝ => u + t • v) (𝓝 0) (𝓝 u) := by simpa using path.tendsto
    exact hm.eventually (GraphChart.eventually_point_mem hg hu him)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hpatch
  refine ⟨g, hg, u, hu, him, v, hq, K * ‖v‖ ^ (2 + β) / |q|, min (ρ / ‖v‖) ε,
    by positivity, lt_min (div_pos hρ hnv) hε, ?_⟩
  intro t ht
  refine ⟨hsub (show t ∈ Metric.ball (0 : ℝ) ε by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using
      ht.trans_le (min_le_right _ _)), ?_⟩
  have hn : ‖t • v‖ < ρ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (lt_div_iff₀ hnv).mp (ht.trans_le (min_le_left _ _))
  have hh := hbound (t • v) hn
  rw [norm_smul, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)] at hh
  simp only [map_smul, smul_apply, smul_eq_mul] at hh
  change |(g.height (u + t • v) - g.height u - t * fderiv ℝ g.height u v) / q - t ^ 2| ≤ _
  let z := g.height (u + t • v) - g.height u - t * fderiv ℝ g.height u v
  have heq : z / q - t ^ 2 = (z - t * (t * hessian g.height u v v) / 2) / q := by
    field_simp
    dsimp [q]
    ring
  change |z / q - t ^ 2| ≤ _
  rw [heq, abs_div]
  calc
    _ ≤ (K * (|t| ^ (2 + β) * ‖v‖ ^ (2 + β))) / |q| := by
      apply div_le_div_of_nonneg_right _ (abs_nonneg _)
      exact hh
    _ = _ := by ring

end MT
