module

public import MT.Transfer
public import MT.Tent
public import Mathlib.Analysis.Real.Pi.Bounds

/-! The uniformly summable Fourier-kernel row in the proof of Lemma 3.5.
Frequencies are scaled so the occupancy intervals have length one. -/

public section
open scoped BigOperators
namespace MT

private theorem unit_shell_count {ι : Type*} (B : Finset ι) (ω : ι → ℝ)
    (x L : ℝ) (n : ℕ)
    (hL : ∀ t : ℝ, ((B.filter (fun j => ω j ∈ Set.Icc t (t+1))).card : ℝ) ≤ L) :
    ((B.filter (fun j => ⌊|ω j - x|⌋₊ = n)).card : ℝ) ≤ 2*L := by
  classical
  let strip (t : ℝ) := B.filter (fun j => ω j ∈ Set.Icc t (t+1))
  have hcover : B.filter (fun j => ⌊|ω j - x|⌋₊ = n) ⊆
      strip (x+n) ∪ strip (x-n-1) := by
    intro j hj
    obtain ⟨hjB, hjn⟩ := Finset.mem_filter.mp hj
    have hlo := Nat.floor_le (abs_nonneg (ω j - x))
    have hhi := Nat.lt_floor_add_one |ω j - x|
    rw [hjn] at hlo hhi
    rcases le_total x (ω j) with hx | hx
    · rw [abs_of_nonneg (sub_nonneg.mpr hx)] at hlo hhi
      exact Finset.mem_union.mpr (.inl (Finset.mem_filter.mpr
        ⟨hjB, (by constructor <;> linarith : ω j ∈ Set.Icc (x+n) (x+n+1))⟩))
    · rw [abs_of_nonpos (sub_nonpos.mpr hx)] at hlo hhi
      exact Finset.mem_union.mpr (.inr (Finset.mem_filter.mpr
        ⟨hjB, (by constructor <;> linarith : ω j ∈ Set.Icc (x-n-1) (x-n-1+1))⟩))
  have hcards := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  calc
    _ ≤ ((strip (x+n)).card : ℝ) + ((strip (x-n-1)).card : ℝ) := by exact_mod_cast hcards
    _ ≤ L + L := add_le_add (hL _) (hL _)
    _ = _ := by ring

private theorem sinc_shell_majorant (z : ℝ) (n : ℕ) (hn : (n : ℝ) ≤ |z|) :
    Real.sinc (Real.pi*z)^2 ≤ 6 * (1/((n : ℝ)+1) - 1/((n : ℝ)+2)) := by
  cases n with
  | zero =>
    have h := Real.abs_sinc_le_one (Real.pi*z)
    have hs := (sq_le_sq.mpr (by simpa using h) : Real.sinc (Real.pi*z)^2 ≤ 1^2)
    norm_num only [Nat.cast_zero, zero_add, one_div_one, one_pow] at hs ⊢
    linarith only [hs]
  | succ m =>
    let n : ℝ := (m : ℝ) + 1
    have hnpos : 1 ≤ n := by dsimp [n]; linarith [Nat.cast_nonneg (α := ℝ) m]
    have habs : n ≤ |z| := by simpa [n] using hn
    have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hnorm : n ≤ |Real.pi*z| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      calc
        n ≤ |z| := habs
        _ ≤ Real.pi * |z| := le_mul_of_one_le_left (abs_nonneg _) hπ
    have hden : 0 < |Real.pi*z| := by linarith
    have hsin := Real.abs_sin_le_one (Real.pi*z)
    have hdecay : |Real.sinc (Real.pi*z)| ≤ 1/n := by
      rw [Real.sinc_of_ne_zero (abs_pos.mp hden), abs_div]
      exact div_le_div₀ (by norm_num) hsin (by linarith) hnorm
    have hsquare : Real.sinc (Real.pi*z)^2 ≤ (1/n)^2 := by
      apply sq_le_sq.mpr
      rwa [abs_of_nonneg (by positivity : 0 ≤ 1/n)]
    change _ ≤ 6 * (1 / ((m.succ : ℝ) + 1) - 1 / ((m.succ : ℝ) + 2))
    push_cast
    change _ ≤ 6 * (1/(n+1) - 1/(n+2))
    apply hsquare.trans
    have hp : 0 < n := by linarith
    have h1 : 0 < n+1 := by linarith
    have h2 : 0 < n+2 := by linarith
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hnpos) (show 0 ≤ 5*n+2 by positivity)]

/-- All unit intervals contain at most L indexed frequencies. Then the
sum of the squared sinc kernel in every row is at most 12L. -/
theorem sinc_row_le {ι : Type*} (B : Finset ι) (ω : ι → ℝ)
    (x L : ℝ) (hLpos : 0 ≤ L)
    (hL : ∀ t : ℝ, ((B.filter (fun j => ω j ∈ Set.Icc t (t+1))).card : ℝ) ≤ L) :
    ∑ j ∈ B, Real.sinc (Real.pi * (ω j-x)) ^ 2 ≤ 12*L := by
  classical
  let s (j : ι) := ⌊|ω j - x|⌋₊
  let N := B.sup s + 1
  let w (n : ℕ) : ℝ := 6 * (1/((n : ℝ)+1) - 1/((n : ℝ)+2))
  have hw (n : ℕ) : 0 ≤ w n := by
    dsimp [w]
    have h := one_div_le_one_div_of_le (show 0 < (n : ℝ) + 1 by positivity)
      (show (n : ℝ) + 1 ≤ n + 2 by linarith)
    linarith
  have hs := kernel_shell_sum B N s (fun j => Real.sinc (Real.pi * (ω j-x))^2) w (2*L)
    (fun j hj => Nat.lt_succ_of_le (Finset.le_sup hj))
    (fun n _ => unit_shell_count B ω x L n hL) (fun n _ => hw n)
    (fun j _ => sinc_shell_majorant (ω j-x) (s j) (Nat.floor_le (abs_nonneg _)))
  apply hs.trans
  have hwN : ∑ n ∈ Finset.range N, w n ≤ 6 := by
    simp only [w, ← Finset.mul_sum, shell_tail_sum]
    have hr : 0 ≤ 1 / ((N : ℝ)+1) := by positivity
    linarith
  calc
    _ ≤ (2*L)*6 := mul_le_mul_of_nonneg_left hwN (by positivity)
    _ = _ := by ring

end MT
