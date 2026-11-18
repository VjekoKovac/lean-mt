module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Tactic

/-! # Scalar steps of the transfer argument and dyadic interpolation

Source: Cairo, Fenves, Kovač, Oliveira, Zakharov, Zhang, arXiv:2611.22465v1,
§§3, 5. The sample estimate in the last theorem is an explicit hypothesis.
-/

public section
open scoped ENNReal BigOperators

namespace MT

/-- On a resonant energy quadruple the spatial centre frequencies cancel, as
do the quadratic centre frequencies. Only the displacements remain. -/
theorem resonant_phase {a a' b b' τ τ' : ℝ} (h u u' : ℝ)
    (h₁ : a + b = a' + b') (h₂ : a ^ 2 + τ = a' ^ 2 + τ') :
    (h * a + u) - (h * a' + u') + h * (b - b') = u - u' ∧
    (h * a + u) ^ 2 - (h * a' + u') ^ 2 + h ^ 2 * (τ - τ') =
      2 * h * (a * u - a' * u') + u ^ 2 - u' ^ 2 := by
  constructor
  · linear_combination h * h₁
  · linear_combination (h ^ 2) * h₂

/-- The shells in a row of the one-dimensional kernel of Lemma 3.5.
The map `shell` is defined on the index set, so coincident frequencies
keep their multiplicities. -/
theorem kernel_shell_sum {ι : Type*} (B : Finset ι) (N : ℕ) (shell : ι → ℕ)
    (K : ι → ℝ) (w : ℕ → ℝ) (L : ℝ)
    (hn : ∀ y ∈ B, shell y < N)
    (hcount : ∀ n < N, ((B.filter (fun y => shell y = n)).card : ℝ) ≤ L)
    (hw : ∀ n < N, 0 ≤ w n) (hK : ∀ y ∈ B, K y ≤ w (shell y)) :
    ∑ y ∈ B, K y ≤ L * ∑ n ∈ Finset.range N, w n := by
  classical
  calc
    _ = ∑ n ∈ Finset.range N, ∑ y ∈ B, if shell y = n then K y else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      simp [Finset.mem_range.mpr (hn y hy)]
    _ ≤ ∑ n ∈ Finset.range N, L * w n := by
      apply Finset.sum_le_sum
      intro n hn'
      have hnN := Finset.mem_range.mp hn'
      rw [← Finset.sum_filter]
      calc
        _ ≤ ∑ _y ∈ B.filter (fun y => shell y = n), w n := by
          apply Finset.sum_le_sum
          intro y hy
          obtain ⟨hyB, hys⟩ := Finset.mem_filter.mp hy
          simpa [hys] using hK y hyB
        _ = ((B.filter (fun y => shell y = n)).card : ℝ) * w n := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcount n hnN) (hw n hnN)
    _ = _ := (Finset.mul_sum ..).symm

/-- Finite majorant sum for the tail of each row, uniformly bounded by 1. -/
theorem shell_tail_sum (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) =
      1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Scalar division step of Proposition 3.1. Here E is the energy, N the
weighted extension mass, F the squared input norm, and X the X-ray norm. -/
theorem transfer_quotient {E N F X T L na nb cE cF cX : ℝ}
    (hE : 0 ≤ E) (hF : 0 < F) (hX : 0 < X) (hT : 0 < T)
    (hL : 0 < L) (ha : 0 < na) (hb : 0 < nb)
    (hpE : 0 < cE) (hpF : 0 < cF) (hpX : 0 < cX)
    (hlower : cE * T * E ≤ N) (hfupper : F ≤ cF * na)
    (hxupper : X ≤ cX * (L * T * nb)) :
    cE / (cF * cX) * (E / (L * na * nb)) ≤ N / (F * X) := by
  have hden := mul_le_mul hfupper hxupper hX.le
    (show (0 : ℝ) ≤ cF * na by positivity)
  calc
    _ = (cE * T * E) / ((cF * na) * (cX * (L * T * nb))) := by
      field_simp [ne_of_gt hT, ne_of_gt hL, ne_of_gt ha, ne_of_gt hb,
        ne_of_gt hpF, ne_of_gt hpX]
    _ ≤ _ := by
      apply (div_le_div_iff₀ (show 0 < (cF * na) * (cX * (L * T * nb)) by positivity)
        (mul_pos hF hX)).2
      exact (mul_le_mul_of_nonneg_left hden (by positivity)).trans
        (mul_le_mul_of_nonneg_right hlower (by positivity))

/-- Formula (5.1). The parameters are the Hölder exponent and the absolute
base in the arithmetic amplification. -/
noncomputable def paperExponent (β C : ℝ) : ℝ :=
  Real.log 2 / (2 * ((1 + 2 / β) * Real.log C))

theorem paperExponent_pos {β C : ℝ} (hβ : 0 < β) (hC : 1 < C) :
    0 < paperExponent β C := by
  have hl := Real.log_pos hC
  have h₂ := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  unfold paperExponent
  positivity

/-- Section 5. Samples may start at any dyadic index N. The lower-bound
coefficient and starting radius may depend on the surface through b and κ.
The exponent depends only on β and the universal C. -/
theorem powerLoss_of_dyadic_samples {M : ℝ → ℝ≥0∞} {β C κ b : ℝ} {N : ℕ}
    (hM : Monotone M) (hβ : 0 < β) (hC : 1 < C)
    (hκ : 0 < κ) (hb : 0 < b)
    (sample : ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal (b * (2 : ℝ) ^ (2 ^ n : ℕ)) ≤
        M (κ * C ^ ((1 + 2 / β) * (2 : ℝ) ^ n))) :
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ENNReal.ofReal (c * R ^ paperExponent β C) ≤ M R := by
  let a := (1 + 2 / β) * Real.log C
  have hCpos : 0 < C := by linarith
  have hClog := Real.log_pos hC
  have ha : 0 < a := by dsimp [a]; positivity
  have htwo := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  refine ⟨b / κ ^ paperExponent β C, by positivity,
    κ * Real.exp (a * (2 : ℝ) ^ N), by positivity, ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hnorm : 0 < R / κ := div_pos hRpos hκ
  have hstart : Real.exp (a * (2 : ℝ) ^ N) ≤ R / κ :=
    (le_div_iff₀ hκ).2 (by simpa [mul_comm] using hR)
  have hlogStart := Real.log_le_log (Real.exp_pos _) hstart
  rw [Real.log_exp] at hlogStart
  have hx : (2 : ℝ) ^ N ≤ Real.log (R / κ) / a :=
    (le_div_iff₀ ha).2 (by simpa [mul_comm] using hlogStart)
  have hone : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  obtain ⟨n, hn, hnext⟩ := exists_nat_pow_near (hone.trans hx)
    (show (1 : ℝ) < 2 by norm_num)
  have hnN : N ≤ n := by
    by_contra! hsmall
    have hp : (2 : ℝ) ^ (n + 1) ≤ 2 ^ N :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact (not_lt_of_ge (hp.trans hx)) hnext
  have hradius : κ * C ^ ((1 + 2 / β) * (2 : ℝ) ^ n) ≤ R := by
    rw [mul_comm κ]
    apply (le_div_iff₀ hκ).1
    rw [Real.rpow_def_of_pos hCpos]
    calc
      _ ≤ Real.exp (Real.log (R / κ)) := by
        apply Real.exp_le_exp.mpr
        have hh := (le_div_iff₀ ha).1 hn
        calc
          _ = (2 : ℝ) ^ n * a := by dsimp [a]; ring
          _ ≤ _ := hh
      _ = _ := Real.exp_log hnorm
  have hhalf : Real.log (R / κ) / (2 * a) ≤ (2 : ℝ) ^ n := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * a)).2
    have hu := (div_lt_iff₀ ha).1 hnext
    rw [pow_succ] at hu
    calc
      _ ≤ ((2 : ℝ) ^ n * 2) * a := hu.le
      _ = _ := by ring
  have hgain : (R / κ) ^ paperExponent β C ≤ (2 : ℝ) ^ (2 ^ n : ℕ) := by
    rw [Real.rpow_def_of_pos hnorm]
    calc
      _ ≤ Real.exp (((2 : ℝ) ^ n) * Real.log 2) := by
        apply Real.exp_le_exp.mpr
        change Real.log (R / κ) * (Real.log 2 / (2 * a)) ≤ _
        calc
          _ = (Real.log (R / κ) / (2 * a)) * Real.log 2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hhalf htwo.le
      _ = Real.exp (Real.log 2 * (((2 ^ n : ℕ) : ℝ))) := by
        push_cast
        rw [mul_comm]
      _ = _ := by
        rw [← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  calc
    _ = ENNReal.ofReal (b * (R / κ) ^ paperExponent β C) := by
      rw [Real.div_rpow hRpos.le hκ.le]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hgain hb.le)
    _ ≤ _ := sample n hnN
    _ ≤ _ := hM hradius

end MT
