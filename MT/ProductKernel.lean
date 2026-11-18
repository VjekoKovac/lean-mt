module

public import MT.WeightedKernel
public import MT.OneDimensional
public import Mathlib.MeasureTheory.Integral.Pi

/-! The physical-space integral defining the product kernel in Lemma 3.4. -/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform Real

namespace MT

/-- The exact positive-sign integral for a rescaled tent. -/
theorem scaled_tent_char (u : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ, (tent (t / s) : ℂ) * (𝐞 (t * u) : ℂ)) =
      ((s * tentFactor (s * u) : ℝ) : ℂ) := by
  let G (t : ℝ) := (tent t : ℂ) * (𝐞 (t * (s * u)) : ℂ)
  have heq (t : ℝ) : (tent (t / s) : ℂ) * (𝐞 (t * u) : ℂ) = G (t / s) := by
    dsimp [G]
    rw [show t / s * (s * u) = t * u by field_simp]
  simp_rw [heq]
  rw [Measure.integral_comp_div G s, abs_of_pos hs]
  dsimp [G]
  rw [integral_tent_char]
  rw [show tentFactor (s * u) = Real.sinc (Real.pi * (s * u)) ^ 2 by
    simp only [tentFactor, fourier_tent, Complex.ofReal_re]]
  simp only [Complex.ofReal_mul]

/-- The complex integral equals a nonnegative real number for all signed
frequencies. The separate coordinate factors can have any positive scales. -/
theorem product_tent_char {n : ℕ} (scale : Fin n → ℝ) (hs : ∀ i, 0 < scale i)
    (ω : Fin n → ℝ) :
    (∫ x : Fin n → ℝ, ∏ i, (tent (x i / scale i) : ℂ) * (𝐞 (x i * ω i) : ℂ)) =
      ((∏ i, scale i * tentFactor (scale i * ω i) : ℝ) : ℂ) := by
  rw [integral_fintype_prod_volume_eq_prod (E := fun _ : Fin n => ℝ)
    (fun i t => (tent (t / scale i) : ℂ) * (𝐞 (t * ω i) : ℂ))]
  simp_rw [fun i => scaled_tent_char (ω i) (hs i)]
  rw [Complex.ofReal_prod]

/-- Physical-space computation of the anisotropic Fourier kernel. The d
spatial scales are Y and the time scale is T. Multiplying the characters
coordinatewise gives the phase of the full dot product. -/
theorem product_tent_kernel {d : ℕ} {Y T : ℝ} (hY : 0 < Y) (hT : 0 < T)
    (ω : Fin (d+1) → ℝ) :
    let scale : Fin (d+1) → ℝ := Fin.snoc (α := fun _ => ℝ) (fun _ => Y) T
    ENNReal.ofReal ((∫ x : Fin (d+1) → ℝ, ∏ i,
      (tent (x i / scale i) : ℂ) * (𝐞 (x i * ω i) : ℂ)).re) =
      boxKernel Y T (fun i => scale i * ω i) := by
  let scale : Fin (d+1) → ℝ := Fin.snoc (α := fun _ => ℝ) (fun _ => Y) T
  have hs (i : Fin (d+1)) : 0 < scale i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [scale, Fin.snoc_last] using hT
    · simpa only [scale, Fin.snoc_castSucc] using hY
  change ENNReal.ofReal ((∫ x : Fin (d+1) → ℝ, ∏ i,
      (tent (x i / scale i) : ℂ) * (𝐞 (x i * ω i) : ℂ)).re) = _
  rw [product_tent_char scale hs, Complex.ofReal_re, Finset.prod_mul_distrib,
    ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => (hs i).le)]
  rw [show ∏ i, scale i = Y ^ d * T by simp [scale, Fin.prod_univ_castSucc]]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => tentFactor_nonneg _)]
  rfl

end MT
