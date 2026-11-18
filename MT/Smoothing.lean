module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Tactic

/-! # The zero-frequency contribution in the lattice count
Lemma 4.3 sums a bounded compactly supported cutoff on a lattice and separates
its zero Fourier coefficient. The estimates here use complex absolute values
so the cutoff may be translated without any sign assumption on its transform.
-/

@[expose] public section
noncomputable section

namespace MT

/-- Remove the zero frequency before summing absolute values. -/
def tailNorm {ι : Type*} [Zero ι] (g : ι → ℂ) : ℝ := by
  classical
  exact ∑' i, if i = 0 then 0 else ‖g i‖

/-- If Poisson summation relates two sums and the nonzero frequencies have
total absolute value at most E, the zero frequency minus E gives a lower
bound for the count after dividing by the covolume. -/
theorem count_from_zero_frequency {ι ν : Type*} [Zero ν] (B : Finset ι)
    (f : ι → ℂ) (g : ν → ℂ) (c E : ℝ) (hc : 0 < c)
    (hsupp : ∀ i ∉ B, f i = 0) (hbump : ∀ i ∈ B, ‖f i‖ ≤ 1)
    (hsum : Summable (fun j => ‖g j‖))
    (hpoisson : (∑' i, f i) = (c : ℂ)⁻¹ * ∑' j, g j)
    (htail : tailNorm g ≤ E) :
    (‖g 0‖ - E) / c ≤ B.card := by
  classical
  have hcount : ‖∑' i, f i‖ ≤ (B.card : ℝ) := by
    rw [tsum_eq_sum hsupp]
    calc
      _ ≤ ∑ i ∈ B, ‖f i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ B, (1 : ℝ) := Finset.sum_le_sum hbump
      _ = _ := by simp
  let tail : ν → ℂ := fun i => if i = 0 then 0 else g i
  have htnorm : Summable (fun i => ‖tail i‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hsum
    by_cases hi : i = 0 <;> simp [tail, hi]
  have hrest : ‖∑' i, tail i‖ ≤ E := by
    apply (norm_tsum_le_tsum_norm htnorm).trans
    simpa [tailNorm, tail, apply_ite] using htail
  have hsplit : (∑' i, g i) = g 0 + ∑' i, tail i :=
    hsum.of_norm.tsum_eq_add_tsum_ite 0
  have hfreq : (∑' j, g j) = (c : ℂ) * ∑' i, f i := by
    rw [hpoisson, ← mul_assoc, mul_inv_cancel₀, one_mul]
    exact_mod_cast hc.ne'
  have hz : g 0 = (∑' j, g j) - ∑' j, tail j := by rw [hsplit, add_sub_cancel_right]
  have hh : ‖g 0‖ ≤ c * B.card + E := by
    calc
      _ ≤ ‖∑' j, g j‖ + ‖∑' j, tail j‖ := hz ▸ norm_sub_le _ _
      _ ≤ c * B.card + E := by
        rw [hfreq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
        exact add_le_add (mul_le_mul_of_nonneg_left hcount hc.le) hrest
  apply (div_le_iff₀ hc).mpr
  linarith

end MT
