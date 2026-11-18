module

public import MT.Configuration
public import MT.Tent
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The resonant-box lower bound in Lemma 3.4 of arXiv:2611.22465v1. -/

@[expose] public section
noncomputable section
open MeasureTheory Set FourierTransform
open scoped ENNReal

namespace MT

/-- Real part of the Fourier transform of the paper's tent. -/
def tentFactor (z : ℝ) : ℝ := (𝓕 (fun x : ℝ => (tent x : ℂ)) z).re

theorem tentFactor_nonneg (z : ℝ) : 0 ≤ tentFactor z := by
  simp only [tentFactor, fourier_tent, Complex.ofReal_re]
  exact sq_nonneg _

/-- An explicit kernel lower bound near resonance: |z| ≤ 1/3 suffices. -/
theorem tentFactor_lower {z : ℝ} (hz : |z| ≤ 1 / 3) : 1 / 4 ≤ tentFactor z := by
  have hp := Real.pi_pos
  have ha : |Real.pi * z| ≤ Real.pi / 3 := by
    rw [abs_mul, abs_of_pos hp]
    linarith [mul_le_mul_of_nonneg_left hz hp.le]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (Real.pi * z))
    (by linarith : Real.pi / 3 ≤ Real.pi) ha
  rw [Real.cos_pi_div_three, Real.cos_abs] at hc
  have hs := hc.trans (Real.cos_le_sinc (by linarith : |Real.pi * z| < Real.pi / 2))
  simp only [tentFactor, fourier_tent, Complex.ofReal_re]
  nlinarith [sq_nonneg (Real.sinc (Real.pi * z) - 1 / 2)]

/-- Parameter cube centered at ha in coordinate j. The finite function space
has product Lebesgue measure, so its cubical volumes are literal products. -/
def parameterCube {d : ℕ} (j : Fin d) (h ε a : ℝ) : Set (Fin d → ℝ) :=
  Icc (fun i => (if i = j then h * a else 0) - ε)
    (fun i => (if i = j then h * a else 0) + ε)

theorem volume_parameterCube {d : ℕ} (j : Fin d) (h ε a : ℝ) :
    volume (parameterCube j h ε a) = (ENNReal.ofReal (2 * ε)) ^ d := by
  simp only [parameterCube, Real.volume_Icc_pi]
  simp [show ∀ t : ℝ, (t + ε) - (t - ε) = 2 * ε by intro t; ring]

/-- The d spatial phases together with the single time phase. The latter is
the last coordinate in the tuple of length d+1. -/
def boxPhases {d : ℕ} (j : Fin d) (φ : (Fin d → ℝ) → ℝ) (Y T h : ℝ)
    (p p' : ℝ × (ℝ × ℝ)) (ξ ξ' : Fin d → ℝ) : Fin (d+1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ)
    (fun i => Y * (ξ i - ξ' i + if i = j then h * (p.2.1 - p'.2.1) else 0))
    (T * (φ ξ - φ ξ' + h ^ 2 * (p.2.2 - p'.2.2)))

/-- Resonance cancels the two center coordinates exactly. The analytic
inputs left here are uniform approximation of the height on each cube and
the two choices of Fourier scales. -/
theorem boxPhases_small_of_height {d : ℕ} {j : Fin d} {φ : (Fin d → ℝ) → ℝ}
    {Y T h ε e : ℝ} {p p' : ℝ × (ℝ × ℝ)} {ξ ξ' : Fin d → ℝ}
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hspace : Y * (2 * ε) ≤ 1 / 3)
    (htime : T * (2 * e) ≤ 1 / 3)
    (hξ : ξ ∈ parameterCube j h ε p.1) (hξ' : ξ' ∈ parameterCube j h ε p'.1)
    (heq : parabolicSum p = parabolicSum p')
    (hφ : |φ ξ - (h * p.1) ^ 2| ≤ e) (hφ' : |φ ξ' - (h * p'.1) ^ 2| ≤ e) :
    ∀ i, |boxPhases j φ Y T h p p' ξ ξ' i| ≤ 1 / 3 := by
  have eq₁ : p.1 + p.2.1 = p'.1 + p'.2.1 := congrArg Prod.fst heq
  have eq₂ : p.1 ^ 2 + p.2.2 = p'.1 ^ 2 + p'.2.2 := congrArg Prod.snd heq
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [boxPhases, Fin.snoc_last, abs_mul, abs_of_nonneg hT]
    have hid : φ ξ - φ ξ' + h ^ 2 * (p.2.2 - p'.2.2) =
        (φ ξ - (h * p.1) ^ 2) - (φ ξ' - (h * p'.1) ^ 2) := by
      linear_combination h ^ 2 * eq₂
    rw [hid]
    apply le_trans (mul_le_mul_of_nonneg_left _ hT) htime
    exact (abs_sub _ _).trans (by linarith)
  · simp only [boxPhases, Fin.snoc_castSucc, abs_mul, abs_of_nonneg hY]
    apply le_trans (mul_le_mul_of_nonneg_left _ hY) hspace
    have hu := hξ.1 k
    have hv := hξ.2 k
    have hu' := hξ'.1 k
    have hv' := hξ'.2 k
    by_cases hk : k = j
    · simp [hk] at hu hv hu' hv' ⊢
      have hcenter : h * p.1 + h * p.2.1 = h * p'.1 + h * p'.2.1 := by
        linear_combination h * eq₁
      apply abs_le.mpr
      constructor <;> linarith
    · simp [hk] at hu hv hu' hv' ⊢
      apply abs_le.mpr
      constructor <;> linarith

/-- Nonnegative form of the kernel displayed in §3, with factor Y^d T.
The squaring identity for the tent shows its real factors are nonnegative. -/
def boxKernel {d : ℕ} (Y T : ℝ) (θ : Fin (d+1) → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Y ^ d * T) * ∏ i, ENNReal.ofReal (tentFactor (θ i))

/-- Area-measure version of the positive-kernel argument. Each localized patch
may carry its actual surface measure. Only its lower mass bound and control of
the phases enter. This avoids identifying its density with a graph Jacobian. -/
theorem resonant_patch_mass {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (W : ℝ → Set Z) (hW : ∀ a, MeasurableSet (W a)) {d : ℕ} (Y T : ℝ)
    (A : Finset ℝ) (B : Finset (ℝ × ℝ)) (V : ℝ≥0∞) (hV : ∀ a ∈ A, V ≤ μ (W a))
    (θ : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) → Z → Z → Fin (d+1) → ℝ)
    (hphase : ∀ p ∈ A ×ˢ B, ∀ p' ∈ A ×ˢ B, parabolicSum p = parabolicSum p' →
      ∀ ξ ∈ W p.1, ∀ ξ' ∈ W p'.1, ∀ i, |θ p p' ξ ξ' i| ≤ 1 / 3) :
    let m := ENNReal.ofReal (Y ^ d * T) * (ENNReal.ofReal (1/4)) ^ (d+1)
    (energy A B : ℝ≥0∞) * (m * V * V) ≤
      ∑ q ∈ (A ×ˢ B) ×ˢ (A ×ˢ B),
        ∫⁻ ξ in W q.1.1, ∫⁻ ξ' in W q.2.1, boxKernel Y T (θ q.1 q.2 ξ ξ') ∂μ ∂μ := by
  classical
  let P := A ×ˢ B
  let G := (P ×ˢ P).filter (fun q => parabolicSum q.1 = parabolicSum q.2)
  let m := ENNReal.ofReal (Y ^ d * T) * (ENNReal.ofReal (1/4)) ^ (d+1)
  let mass (q : (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) : ℝ≥0∞ :=
    ∫⁻ ξ in W q.1.1, ∫⁻ ξ' in W q.2.1,
      boxKernel Y T (θ q.1 q.2 ξ ξ') ∂μ ∂μ
  change (G.card : ℝ≥0∞) * (m * V * V) ≤ ∑ q ∈ P ×ˢ P, mass q
  calc
    _ = ∑ _q ∈ G, m * V * V := by simp
    _ ≤ ∑ q ∈ G, mass q := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hqP, heq⟩ := Finset.mem_filter.mp hq
      obtain ⟨hp, hp'⟩ := Finset.mem_product.mp hqP
      have hm (ξ) (hξ : ξ ∈ W q.1.1)
          (ξ') (hξ' : ξ' ∈ W q.2.1) :
          m ≤ boxKernel Y T (θ q.1 q.2 ξ ξ') := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [show (ENNReal.ofReal (1/4)) ^ (d+1) = ∏ _i : Fin (d+1), ENNReal.ofReal (1/4) by simp]
        apply Finset.prod_le_prod
        intro i _
        exact ENNReal.ofReal_le_ofReal (tentFactor_lower (hphase _ hp _ hp' heq ξ hξ ξ' hξ' i))
      have hconst (a : ℝ) (ha : a ∈ A) (z : ℝ≥0∞) :
          z * V ≤ ∫⁻ _ξ in W a, z ∂μ := by
        simp only [lintegral_const, Measure.restrict_apply_univ]
        exact mul_le_mul_of_nonneg_left (hV a ha) (by positivity)
      refine (hconst _ (Finset.mem_product.mp hp).1 (m * V)).trans ?_
      apply setLIntegral_mono' (hW _)
      intro ξ hξ
      refine (hconst _ (Finset.mem_product.mp hp').1 m).trans ?_
      exact setLIntegral_mono' (hW _) (hm ξ hξ)
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- After Fourier expansion, nonresonant boxes can be discarded. If all d+1
arguments of the tent transforms stay within 1/3 on each resonant product of
cubes, the remaining double integrals give exactly the energy multiplicity
times a common lower bound. -/
theorem resonant_box_mass {d : ℕ} (j : Fin d) (φ : (Fin d → ℝ) → ℝ)
    (Y T h ε : ℝ) (A : Finset ℝ) (B : Finset (ℝ × ℝ))
    (hphase : ∀ p ∈ A ×ˢ B, ∀ p' ∈ A ×ˢ B, parabolicSum p = parabolicSum p' →
      ∀ ξ ∈ parameterCube j h ε p.1, ∀ ξ' ∈ parameterCube j h ε p'.1,
        ∀ i, |boxPhases j φ Y T h p p' ξ ξ' i| ≤ 1 / 3) :
    let V := (ENNReal.ofReal (2 * ε)) ^ d
    let m := ENNReal.ofReal (Y ^ d * T) * (ENNReal.ofReal (1/4)) ^ (d+1)
    (energy A B : ℝ≥0∞) * (m * V * V) ≤
      ∑ q ∈ (A ×ˢ B) ×ˢ (A ×ˢ B),
        ∫⁻ ξ in parameterCube j h ε q.1.1, ∫⁻ ξ' in parameterCube j h ε q.2.1,
          boxKernel Y T (boxPhases j φ Y T h q.1 q.2 ξ ξ') := by
  exact resonant_patch_mass volume (parameterCube j h ε) (fun _ => measurableSet_Icc)
    Y T A B _ (fun a _ => (volume_parameterCube j h ε a).ge) (boxPhases j φ Y T h) hphase

end MT
