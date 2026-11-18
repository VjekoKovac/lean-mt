module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Tactic

/-! A fixed, smooth, compactly supported one-dimensional cutoff for the
tensor-product minorant in Lemma 4.3. -/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped FourierTransform Real ContDiff

namespace MT.BoxCutoff

def bump : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩

def ψ (x : ℝ) : ℂ := bump.normed volume x

theorem ψ_smooth : ContDiff ℝ ∞ ψ :=
  Complex.ofRealCLM.contDiff.comp (bump.contDiff_normed (μ := volume))

theorem ψ_compact : HasCompactSupport ψ :=
  (bump.hasCompactSupport_normed (μ := volume)).comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)

def ψSchwartz : SchwartzMap ℝ ℂ := ψ_compact.toSchwartzMap ψ_smooth

theorem ψ_bound (x : ℝ) : ‖ψ x‖ ≤ 1 := by
  rw [ψ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bump.nonneg_normed x)]
  have h := bump.normed_le_div_measure_closedBall_rIn (μ := volume) x
  simpa [bump, Real.volume_real_closedBall (by norm_num : 0 ≤ (1/2:ℝ))] using h

theorem ψ_zero {x : ℝ} (h : 1 ≤ |x|) : ψ x = 0 := by
  have ho : x ∉ Function.support (bump.normed volume) := by
    rw [bump.support_normed_eq]
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, bump, not_lt] using h
  simpa only [ψ, Complex.ofReal_eq_zero] using (Function.notMem_support.mp ho)

theorem integral_ψ : ∫ x, ψ x = 1 := by
  change (∫ x : ℝ, ((bump.normed volume x : ℝ):ℂ)) = 1
  rw [integral_complex_ofReal, bump.integral_normed]; norm_num

/-- One universal Fourier-decay constant, shared by all coordinates. -/
def constant : ℝ :=
  max 1 (max (SchwartzMap.seminorm ℂ 0 0 (𝓕 ψSchwartz)) (SchwartzMap.seminorm ℂ 2 0 (𝓕 ψSchwartz)))

theorem constant_one_le : 1 ≤ constant := le_max_left _ _

theorem fourier_ψ_decay {t : ℝ} (ht : t ≠ 0) :
    ‖𝓕 ψ t‖ ≤ constant * min 1 ((|t|^2)⁻¹) := by
  have hc : 0 ≤ constant := zero_le_one.trans constant_one_le
  have hzero := SchwartzMap.norm_le_seminorm ℂ (𝓕 ψSchwartz) t
  have htwo := SchwartzMap.norm_pow_mul_le_seminorm ℂ (𝓕 ψSchwartz) 2 t
  change ‖𝓕 ψ t‖ ≤ _ at hzero
  change ‖t‖^2 * ‖𝓕 ψ t‖ ≤ _ at htwo
  have hz : ‖𝓕 ψ t‖ ≤ constant := hzero.trans ((le_max_left ..).trans (le_max_right ..))
  have htw : |t|^2 * ‖𝓕 ψ t‖ ≤ constant := by
    rw [← Real.norm_eq_abs]
    exact htwo.trans ((le_max_right ..).trans (le_max_right ..))
  rw [mul_min_of_nonneg _ _ hc, mul_one, ← div_eq_mul_inv]
  exact le_min hz ((le_div_iff₀ (sq_pos_of_pos (abs_pos.mpr ht))).mpr (by linarith))

def affine (M a x : ℝ) : ℂ := ψ ((x-a)/M)

private theorem integral_affine (g : ℝ → ℂ) (M a : ℝ) (hM : 0 < M) :
    (∫ x : ℝ, g ((x-a)/M)) = (M:ℂ) * ∫ x, g x := calc
  _ = ∫ x : ℝ, g (x/M) := integral_sub_right_eq_self (fun y => g (y/M)) a
  _ = _ := by
    simpa [div_eq_mul_inv, abs_of_pos hM, Complex.real_smul] using
      Measure.integral_comp_inv_mul_right g M

theorem fourier_affine (M a ξ : ℝ) (hM : 0 < M) :
    𝓕 (affine M a) ξ = (𝐞 (-(a*ξ)) : ℂ) * (M:ℂ) * 𝓕 ψ (M*ξ) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  let g (t : ℝ) : ℂ := (𝐞 (-(t*(M*ξ))) : ℂ) * ψ t
  have he (x : ℝ) : 𝐞 (-(x*ξ)) • affine M a x = (𝐞 (-(a*ξ)) : ℂ) * g ((x-a)/M) := by
    rw [show -(x*ξ) = -(a*ξ) + -(((x-a)/M)*(M*ξ)) by field_simp; ring]
    simp [g, affine, AddChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul, mul_assoc]
  simp only [he, integral_const_mul, integral_affine g M a hM]
  simp [mul_assoc, g, Circle.smul_def, smul_eq_mul]

theorem fourier_ψ_zero : 𝓕 ψ 0 = 1 := by simp [Real.fourier_real_eq, integral_ψ]

theorem fourier_affine_zero (M a : ℝ) (hM : 0 < M) : 𝓕 (affine M a) 0 = (M : ℂ) := by
  simp [fourier_affine M a 0 hM, fourier_ψ_zero]

theorem fourier_affine_decay (M a ξ : ℝ) (hM : 0 < M) (hξ : ξ ≠ 0) :
    ‖𝓕 (affine M a) ξ‖ ≤ (constant*M) * min 1 ((|M*ξ|^2)⁻¹) := by
  rw [fourier_affine M a ξ hM, norm_mul, norm_mul, Circle.norm_coe, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  calc
    _ ≤ M*(constant * min 1 ((|M*ξ|^2)⁻¹)) :=
      mul_le_mul_of_nonneg_left (fourier_ψ_decay (mul_ne_zero hM.ne' hξ)) hM.le
    _ = _ := by ring

end MT.BoxCutoff
