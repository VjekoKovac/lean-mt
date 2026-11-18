module

public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

/-! # The nonnegative Fourier kernel in §3

The tent is the convolution square of the centered interval of length one.
The real sinc normalization here is `sin x / x` (with value 1 at zero).
-/

@[expose] public section
noncomputable section
open MeasureTheory Set FourierTransform
open scoped Convolution

namespace MT

def intervalPulse : ℝ → ℂ :=
  (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => 1)

def tent (x : ℝ) : ℝ := max (1 - |x|) 0

theorem integrable_intervalPulse : Integrable intervalPulse := by
  rw [intervalPulse, integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (IsCompact.measure_lt_top isCompact_Icc).ne

/-- Length of the overlap of two unit intervals. -/
theorem pulse_convolution (x : ℝ) :
    (intervalPulse ⋆[ContinuousLinearMap.mul ℂ ℂ] intervalPulse) x = (tent x : ℂ) := by
  let a := max (-(1/2 : ℝ)) (x - 1/2)
  let b := min (1/2 : ℝ) (x + 1/2)
  have hmem (y : ℝ) : (y ∈ Icc a b) ↔
      y ∈ Icc (-(1/2 : ℝ)) (1/2) ∧ (x-y) ∈ Icc (-(1/2 : ℝ)) (1/2) := by
    simp only [a, b, mem_Icc, max_le_iff, le_min_iff]
    constructor <;> intro h <;> (rcases h with ⟨⟨h₁,h₂⟩,h₃,h₄⟩; refine ⟨⟨?_,?_⟩,?_,?_⟩ <;> linarith)
  change (∫ y, intervalPulse y * intervalPulse (x-y)) = _
  have heq : (fun y => intervalPulse y * intervalPulse (x-y)) =
      (Icc a b).indicator (fun _ => (1 : ℂ)) := by
    funext y
    by_cases h₁ : y ∈ Icc (-(1/2 : ℝ)) (1/2) <;>
      by_cases h₂ : x-y ∈ Icc (-(1/2 : ℝ)) (1/2) <;>
      simp only [intervalPulse, indicator_apply, hmem y, h₁, h₂, and_self,
        and_false, and_true, ite_true, ite_false, mul_one, mul_zero]
  rw [heq, integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
  simp only [Complex.real_smul, mul_one]
  congr 1
  dsimp [a,b,tent]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, min_eq_left (show (1/2 : ℝ) ≤ x + 1/2 by linarith),
      max_eq_right (show -(1/2 : ℝ) ≤ x - 1/2 by linarith)]
    congr 1
    ring
  · rw [abs_of_nonpos hx, min_eq_right (show x + 1/2 ≤ (1/2 : ℝ) by linarith),
      max_eq_left (show x - 1/2 ≤ -(1/2 : ℝ) by linarith)]
    congr 1
    ring

/-- Scaled version of mathlib's interval integral of the exponential. -/
theorem pulse_integral (z : ℝ) :
    (∫ t in -(1/2 : ℝ)..(1/2 : ℝ), Complex.exp (((t * (2*z) : ℝ) : ℂ) * Complex.I)) =
      (Real.sinc z : ℂ) := by
  by_cases hz : z = 0
  · subst z
    norm_num
  have h2 : 2 * z ≠ 0 := mul_ne_zero (by norm_num) hz
  have h := intervalIntegral.integral_comp_mul_right
    (a := -(1/2 : ℝ)) (b := 1/2) (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) h2
  rw [show -(1/2 : ℝ) * (2*z) = -z by ring,
      show (1/2 : ℝ) * (2*z) = z by ring, integral_exp_mul_I_eq_sinc] at h
  rw [h, Complex.real_smul]
  push_cast
  field_simp [show (z : ℂ) ≠ 0 by exact_mod_cast hz]

/-- The Fourier transform in the convention with phase −2πi xξ. -/
theorem fourier_intervalPulse (ξ : ℝ) :
    𝓕 intervalPulse ξ = (Real.sinc (Real.pi * ξ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hfun : (fun v : ℝ => Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) •
      intervalPulse v) = (Icc (-(1/2 : ℝ)) (1/2)).indicator (fun v : ℝ =>
        Complex.exp (((v * (2 * (-(Real.pi * ξ))) : ℝ) : ℂ) * Complex.I)) := by
    funext v
    by_cases h : v ∈ Icc (-(1/2 : ℝ)) (1/2) <;>
      simp only [intervalPulse, indicator_apply, h, ite_true, ite_false,
        smul_eq_mul, mul_one, mul_zero]
    congr 3
    ring
  rw [hfun, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : -(1/2 : ℝ) ≤ 1/2),
    pulse_integral, Real.sinc_neg]

/-- The identity η = sinc² used in both analytic lemmas of the source. -/
theorem fourier_tent (ξ : ℝ) :
    𝓕 (fun x : ℝ => (tent x : ℂ)) ξ =
      ((Real.sinc (Real.pi * ξ)) ^ 2 : ℝ) := by
  have hfun : (fun x : ℝ => (tent x : ℂ)) =
      (intervalPulse ⋆[ContinuousLinearMap.mul ℂ ℂ] intervalPulse) :=
    funext fun x => (pulse_convolution x).symm
  rw [hfun, Real.fourier_mul_convolution_eq integrable_intervalPulse integrable_intervalPulse,
    fourier_intervalPulse]
  push_cast
  ring

end MT
