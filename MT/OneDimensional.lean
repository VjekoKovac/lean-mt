module

public import MT.KernelRow

/-! The one-dimensional exponential-sum estimate in the proof of Lemma 3.5. -/

public section
noncomputable section
open MeasureTheory Set
open scoped FourierTransform Real ComplexConjugate

namespace MT

private theorem char_pair (u v : ℝ) :
    (𝐞 u : ℂ) * conj (𝐞 v : ℂ) = (𝐞 (u - v) : ℂ) := by
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    Circle.coe_mul, Circle.coe_inv_eq_conj]

private theorem tent_compact : HasCompactSupport tent := by
  apply HasCompactSupport.intro' (K := Icc (-1 : ℝ) 1) isCompact_Icc isClosed_Icc
  intro x hx
  have h : 1 ≤ |x| := by
    by_contra! hh
    exact hx ⟨(abs_lt.mp hh).1.le, (abs_lt.mp hh).2.le⟩
  exact max_eq_right (sub_nonpos.mpr h)

theorem integral_tent_char (u : ℝ) :
    (∫ t : ℝ, (tent t : ℂ) * (𝐞 (t * u) : ℂ)) =
      ((Real.sinc (Real.pi * u)) ^ 2 : ℝ) := by
  calc
    _ = 𝓕 (fun x : ℝ => (tent x : ℂ)) (-u) := by
      rw [Real.fourier_real_eq]
      simp [Circle.smul_def, smul_eq_mul, mul_comm]
    _ = _ := by rw [fourier_tent, mul_neg, Real.sinc_neg]

/-- Unit-scale form of the one-dimensional estimate in Lemma 3.5. The family
is indexed to retain repeated frequencies after projection. -/
theorem unit_tent_large_sieve {ι : Type*} (B : Finset ι) (ω : ι → ℝ)
    (c : ι → ℂ) (L : ℝ) (hLpos : 0 ≤ L)
    (hL : ∀ t : ℝ, ((B.filter (fun j => ω j ∈ Icc t (t+1))).card : ℝ) ≤ L)
    (hc : ∀ j ∈ B, ‖c j‖ = 1) :
    (∫ t : ℝ, tent t * ‖∑ j ∈ B, c j * (𝐞 (t * ω j) : ℂ)‖ ^ 2) ≤
      12 * L * B.card := by
  classical
  let F (j k : ι) (t : ℝ) := (c j * conj (c k)) *
    ((tent t : ℂ) * (𝐞 (t * (ω j - ω k)) : ℂ))
  let D (j k : ι) := (c j * conj (c k)) *
    ((((Real.sinc (Real.pi * (ω j - ω k)))^2 : ℝ)) : ℂ)
  have hF (j k : ι) : Integrable (F j k) := by
    have hct : Continuous (fun t : ℝ => (tent t : ℂ)) := by unfold tent; fun_prop
    have hcc : HasCompactSupport (fun t : ℝ => (tent t : ℂ)) :=
      tent_compact.comp_left (g := Complex.ofReal) (by simp)
    apply Continuous.integrable_of_hasCompactSupport
    · dsimp [F]
      exact continuous_const.mul (hct.mul (continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const))))
    · exact (hcc.mul_right (f' := fun t : ℝ => (𝐞 (t * (ω j - ω k)) : ℂ))).mul_left
  have hFint (j k : ι) : ∫ t, F j k t = D j k := by
    dsimp [F, D]
    rw [integral_const_mul, integral_tent_char]
  have hpoint (t : ℝ) :
      (((tent t * ‖∑ j ∈ B, c j * (𝐞 (t * ω j) : ℂ)‖^2 : ℝ)) : ℂ) =
        ∑ j ∈ B, ∑ k ∈ B, F j k t := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [F]
    rw [mul_sub, ← char_pair]
    ring
  have heq : ((∫ t : ℝ, tent t * ‖∑ j ∈ B, c j * (𝐞 (t * ω j) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ B, ∑ k ∈ B, D j k := by
    rw [← integral_complex_ofReal]
    simp_rw [hpoint]
    rw [integral_finsetSum B (fun j _ => integrable_finsetSum B (fun k _ => hF j k))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finsetSum B (fun k _ => hF j k)]
    simp_rw [hFint]
  have hD (j k : ι) (hj : j ∈ B) (hk : k ∈ B) :
      ‖D j k‖ = Real.sinc (Real.pi*(ω j-ω k))^2 := by
    simp [D, hc j hj, hc k hk]
  calc
    _ ≤ |∫ t : ℝ, tent t * ‖∑ j ∈ B, c j * (𝐞 (t * ω j) : ℂ)‖ ^ 2| := le_abs_self _
    _ = ‖∑ j ∈ B, ∑ k ∈ B, D j k‖ := by rw [← heq, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ j ∈ B, ∑ k ∈ B, ‖D j k‖ := (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ = ∑ k ∈ B, ∑ j ∈ B, Real.sinc (Real.pi*(ω j-ω k))^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_congr rfl fun j hj => hD j k hj hk
    _ ≤ ∑ _k ∈ B, 12*L := Finset.sum_le_sum fun k _ => sinc_row_le B ω (ω k) L hLpos hL
    _ = _ := by simp [mul_comm]

/-- The integral estimate used in Lemma 3.5, including the scale Z.
The bound counts indices, so equal projected frequencies are permitted. -/
theorem tent_large_sieve {ι : Type*} (B : Finset ι) (ω : ι → ℝ)
    (c : ι → ℂ) {Z L : ℝ} (hZ : 0 < Z) (hLpos : 0 ≤ L)
    (hL : ∀ t : ℝ, ((B.filter (fun j => ω j ∈ Icc t (t + Z⁻¹))).card : ℝ) ≤ L)
    (hc : ∀ j ∈ B, ‖c j‖ = 1) :
    (∫ t : ℝ, tent (t/Z) * ‖∑ j ∈ B, c j * (𝐞 (t * ω j) : ℂ)‖ ^ 2) ≤
      12 * Z * L * B.card := by
  classical
  have hs (t : ℝ) :
      ((B.filter (fun j => Z * ω j ∈ Icc t (t + 1))).card : ℝ) ≤ L := by
    apply le_trans _ (hL (t / Z))
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro j hj
    obtain ⟨hj, hlo, hhi⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨hj, (div_le_iff₀ hZ).2 (by linarith), ?_⟩
    calc
      ω j ≤ (t+1)/Z := (le_div_iff₀ hZ).2 (by linarith)
      _ = _ := by ring
  let G (t : ℝ) := tent t * ‖∑ j ∈ B, c j * (𝐞 (t * (Z * ω j)) : ℂ)‖ ^ 2
  have heq (t : ℝ) :
      tent (t/Z) * ‖∑ j ∈ B, c j * (𝐞 (t * ω j) : ℂ)‖ ^ 2 = G (t / Z) := by
    dsimp [G]
    have h (j : ι) : t / Z * (Z * ω j) = t * ω j := by field_simp
    simp only [h]
  simp_rw [heq]
  rw [Measure.integral_comp_div G Z, abs_of_pos hZ, smul_eq_mul]
  calc
    _ ≤ Z * (12*L*B.card) := mul_le_mul_of_nonneg_left
      (unit_tent_large_sieve B (fun j => Z*ω j) c L hLpos hs hc) hZ.le
    _ = _ := by ring

end MT
