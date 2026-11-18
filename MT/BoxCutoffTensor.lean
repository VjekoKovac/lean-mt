module

public import MT.BoxCutoff
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Pi

/-! The tensor-product minorant of a real Euclidean box. Fourier factorization
uses the volume-preserving coordinate map followed by finite-dimensional Fubini. -/

@[expose] public section
noncomputable section

open MeasureTheory Set Finset
open scoped FourierTransform Real InnerProductSpace ContDiff

namespace MT.BoxCutoff

variable {ι : Type*} [Fintype ι]

def closedBox (M a : ι → ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, |x i-a i| ≤ M i}

omit [Fintype ι] in
theorem compact_box (M a : ι → ℝ) : IsCompact (closedBox M a) := by
  let I := Set.univ.pi fun i => Icc (a i-M i) (a i+M i)
  have hc : IsCompact I := isCompact_univ_pi fun i => isCompact_Icc
  have he : closedBox M a = WithLp.toLp 2 '' I := by
    ext x
    constructor
    · intro hx
      refine ⟨WithLp.ofLp x, ?_, rfl⟩
      intro i _
      obtain ⟨hl,hu⟩ := abs_le.mp (hx i)
      change a i-M i ≤ x i ∧ x i ≤ a i+M i
      constructor <;> linarith
    · rintro ⟨y,hy,rfl⟩ i
      obtain ⟨hl,hu⟩ := hy i (Set.mem_univ _)
      change |y i-a i| ≤ M i
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [he]
  exact hc.image (PiLp.continuous_toLp 2 _)

def tensor (M a : ι → ℝ) (x : EuclideanSpace ℝ ι) : ℂ :=
  ∏ i, affine (M i) (a i) (x i)

theorem tensor_zero (M a : ι → ℝ) (hM : ∀ i, 0 < M i) {x : EuclideanSpace ℝ ι}
    (hx : x ∉ closedBox M a) : tensor M a x = 0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, M i < |x i-a i| := by simpa [closedBox] using hx
  apply prod_eq_zero (mem_univ i)
  apply ψ_zero
  rw [abs_div, abs_of_pos (hM i)]
  exact (le_div_iff₀ (hM i)).mpr (by linarith)

theorem tensor_bound (M a : ι → ℝ) (x : EuclideanSpace ℝ ι) : ‖tensor M a x‖ ≤ 1 := by
  rw [tensor, norm_prod]
  exact prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => ψ_bound _)

theorem tensor_smooth (M a : ι → ℝ) : ContDiff ℝ ∞ (tensor M a) := by
  apply contDiff_prod
  intro i _
  apply ψ_smooth.comp
  apply ContDiff.div_const
  apply ContDiff.sub _ contDiff_const
  exact contDiff_piLp_apply 2

theorem tensor_compact (M a : ι → ℝ) (hM : ∀ i, 0 < M i) : HasCompactSupport (tensor M a) :=
  HasCompactSupport.intro' (compact_box M a) (compact_box M a).isClosed
    (fun _ hx => tensor_zero M a hM hx)

def boxSchwartz (M a : ι → ℝ) (hM : ∀ i, 0 < M i) : SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
  (tensor_compact M a hM).toSchwartzMap (tensor_smooth M a)

omit [Fintype ι] in
private theorem char_sum (s : Finset ι) (t : ι → ℝ) :
    (𝐞 (∑ i ∈ s, t i) : ℂ) = ∏ i ∈ s, (𝐞 (t i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, AddChar.map_add_eq_mul, ih]

/-- Fourier transform of a product in Euclidean coordinates, including noncentered factors. -/
theorem fourier_tensor (M a : ι → ℝ) (ξ : EuclideanSpace ℝ ι) :
    𝓕 (tensor M a) ξ = ∏ i, 𝓕 (affine (M i) (a i)) (ξ i) := by
  let h (i : ι) (u : ℝ) := (𝐞 (-(u*ξ i)) : ℂ) * affine (M i) (a i) u
  have he (x : EuclideanSpace ℝ ι) : 𝐞 (-⟪x,ξ⟫_ℝ) • tensor M a x = ∏ i, h i (x i) := by
    rw [PiLp.inner_apply, ← sum_neg_distrib, Circle.smul_def, smul_eq_mul, char_sum]
    simp only [tensor, h, prod_mul_distrib, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [Real.fourier_eq]
  simp only [he]
  calc
    _ = ∫ x : ι → ℝ, ∏ i, h i (x i) :=
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).integral_comp'
        (fun x : ι → ℝ => ∏ i, h i (x i))
    _ = ∏ i, ∫ u, h i u := integral_fintype_prod_volume_eq_prod h
    _ = _ := prod_congr rfl fun i _ => by simp [h, Real.fourier_real_eq, Circle.smul_def]

theorem fourier_boxSchwartz_zero (M a : ι → ℝ) (hM : ∀ i, 0 < M i) :
    ‖𝓕 (boxSchwartz M a hM : EuclideanSpace ℝ ι → ℂ) 0‖ = ∏ i, M i := by
  change ‖𝓕 (tensor M a) 0‖ = _
  rw [fourier_tensor, norm_prod]
  apply prod_congr rfl
  intro i _
  change ‖𝓕 (affine (M i) (a i)) 0‖ = M i
  rw [fourier_affine_zero _ _ (hM i), Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hM i)]

theorem fourier_boxSchwartz_decay (M a : ι → ℝ) (hM : ∀ i, 0 < M i)
    (ξ : EuclideanSpace ℝ ι) (hξ : ∀ i, ξ i ≠ 0) :
    ‖𝓕 (boxSchwartz M a hM : EuclideanSpace ℝ ι → ℂ) ξ‖ ≤
      constant^(Fintype.card ι)*(∏ i, M i)*(∏ i, min 1 ((|M i*ξ i|^2)⁻¹)) := by
  change ‖𝓕 (tensor M a) ξ‖ ≤ _
  rw [fourier_tensor, norm_prod]
  calc
    _ ≤ ∏ i, (constant*M i) * min 1 ((|M i*ξ i|^2)⁻¹) :=
      prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => fourier_affine_decay _ _ _ (hM i) (hξ i)
    _ = _ := by simp [prod_mul_distrib]

end MT.BoxCutoff
