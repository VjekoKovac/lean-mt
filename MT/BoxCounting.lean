module

public import MT.Smoothing
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Data.Int.Log
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-! Finite packing for the primal and dual boxes of Lemma 4.3. -/

@[expose] public section
noncomputable section
namespace MT.BoxCounting
open Finset

/-- At most `1 + W/s` points of an `s`-separated family fit in a closed interval
of length `W`. The lower endpoint can be arbitrary. -/
theorem interval_count {α : Type*} (X : Finset α) (f : α → ℝ) (a W s : ℝ)
    (hW : 0 ≤ W) (hs : 0 < s) (hbox : ∀ x ∈ X, a ≤ f x ∧ f x ≤ a+W)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → s ≤ |f x-f y|) :
    (X.card : ℝ) ≤ 1 + W/s := by
  let g (x : α) := (f x-a)/s
  let ix (x : α) := ⌊g x⌋₊
  have hpos (x hx) : 0 ≤ g x := div_nonneg (sub_nonneg.mpr (hbox x hx).1) hs.le
  have hcount : X.card ≤ (range (⌊W/s⌋₊+1)).card := by
    apply card_le_card_of_injOn ix
    · intro x hx
      apply mem_range.mpr
      exact Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right
        (by linarith [(hbox x hx).2] : f x-a ≤ W) hs.le))
    · intro x hx y hy he
      by_contra hne
      have hlo := Nat.floor_le (hpos x hx)
      have hhi := Nat.lt_floor_add_one (g x)
      have hlo' := Nat.floor_le (hpos y hy)
      have hhi' := Nat.lt_floor_add_one (g y)
      change ⌊g x⌋₊ = ⌊g y⌋₊ at he
      rw [he] at hlo hhi
      have hd : |g x-g y| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
      have heq : g x-g y = (f x-f y)/s := by dsimp [g]; ring
      rw [heq, abs_div, abs_of_pos hs] at hd
      have := (div_lt_iff₀ hs).mp hd
      linarith [hsep x hx y hy hne]
  have h := Nat.floor_le (div_nonneg hW hs.le)
  simp only [card_range] at hcount
  have : (X.card : ℝ) ≤ (⌊W/s⌋₊ : ℝ)+1 := by exact_mod_cast hcount
  linarith

variable {ι α : Type*} [Fintype ι]

/-- The separation of coordinate products controls any translated box.
The distinguished coordinate is the one pigeonholed in the source. -/
theorem box_count (i₀ : ι) (X : Finset α) (f : α → ι → ℝ) (a W : ι → ℝ) (δ : ℝ)
    (hW : ∀ i, 0 < W i) (hδ : 0 < δ)
    (hbox : ∀ x ∈ X, ∀ i, a i ≤ f x i ∧ f x i ≤ a i+W i)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ ∏ i, |f x i-f y i|) :
    (X.card : ℝ) ≤ 1+(∏ i, W i)/δ := by
  classical
  let P := ∏ i ∈ univ.erase i₀, W i
  have hP : 0 < P := prod_pos fun i _ => hW i
  have hsum := interval_count X (fun x => f x i₀) (a i₀) (W i₀) (δ/P) (hW _).le
    (div_pos hδ hP) (fun x hx => hbox x hx i₀) (by
      intro x hx y hy hne
      apply (div_le_iff₀ hP).mpr
      calc
        δ ≤ ∏ i, |f x i-f y i| := hsep x hx y hy hne
        _ = |f x i₀-f y i₀| * ∏ i ∈ univ.erase i₀, |f x i-f y i| :=
          (mul_prod_erase _ _ (mem_univ i₀)).symm
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply prod_le_prod₀ (fun i _ => abs_nonneg _)
          intro i _
          obtain ⟨hx₁,hx₂⟩ := hbox x hx i
          obtain ⟨hy₁,hy₂⟩ := hbox y hy i
          exact abs_le.mpr ⟨by linarith, by linarith⟩)
  have hvol : W i₀ * P = ∏ i, W i := mul_prod_erase _ _ (mem_univ i₀)
  rwa [div_div_eq_mul_div, hvol] at hsum

/-- For a box centered at the origin containing only nonzero vectors with
coordinate product at least δ, absorb the isolated `+1` in the packing estimate.
The empty box also satisfies the inequality. -/
theorem centered_box_count (i₀ : ι) (X : Finset α) (f : α → ι → ℝ) (M : ι → ℝ) (δ : ℝ)
    (hM : ∀ i, 0 < M i) (hδ : 0 < δ)
    (hbox : ∀ x ∈ X, ∀ i, |f x i| ≤ M i)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ ∏ i, |f x i-f y i|)
    (hzero : ∀ x ∈ X, δ ≤ ∏ i, |f x i|) :
    (X.card : ℝ) ≤ (1 + 2^(Fintype.card ι))*(∏ i, M i)/δ := by
  classical
  have hp : 0 < ∏ i, M i := prod_pos fun i _ => hM i
  obtain h | h := X.eq_empty_or_nonempty
  · subst X
    simp only [card_empty, Nat.cast_zero]
    positivity
  obtain ⟨x,hx⟩ := h
  have hδM := (hzero x hx).trans (prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hbox x hx i))
  have hc := box_count i₀ X f (-M) (fun i => 2*M i) δ (fun i => mul_pos (by norm_num) (hM i)) hδ
    (fun y hy i => by
      obtain ⟨h₁,h₂⟩ := abs_le.mp (hbox y hy i)
      exact ⟨h₁, by dsimp; linarith⟩) hsep
  simp only [prod_mul_distrib, prod_const, card_univ] at hc
  apply (le_div_iff₀ hδ).mpr
  have he := (le_div_iff₀ hδ).mp (show (X.card : ℝ)-1 ≤
      2^(Fintype.card ι)*(∏ i, M i)/δ by linarith)
  linarith

/-- Dyadic annulus count in the exact coordinate variables of the paper.
Only its upper radius is needed. The constant is at most `2 · 4^k`. -/
theorem dyadic_cell_count (i₀ : ι) (X : Finset α) (f : α → ι → ℝ)
    (M : ι → ℝ) (j : ι → ℤ) (δ : ℝ) (hM : ∀ i, 0 < M i) (hδ : 0 < δ)
    (hbox : ∀ x ∈ X, ∀ i, |M i * f x i| ≤ (2:ℝ)^(j i + 1))
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ ∏ i, |f x i-f y i|)
    (hzero : ∀ x ∈ X, δ ≤ ∏ i, |f x i|) :
    (X.card : ℝ) ≤ 2 * 4^(Fintype.card ι) * (∏ i, (2:ℝ)^(j i)) / ((∏ i, M i)*δ) := by
  let k := Fintype.card ι
  have U (x : α) (hx : x ∈ X) (i : ι) : |f x i| ≤ 2*(2:ℝ)^(j i)/M i := by
    have hh := hbox x hx i
    rw [abs_mul, abs_of_pos (hM i), zpow_add_one₀ (by norm_num)] at hh
    exact (le_div_iff₀ (hM i)).mpr (by linarith)
  have h := centered_box_count i₀ X f (fun i => 2*(2:ℝ)^(j i)/M i) δ
    (fun i => div_pos (mul_pos (by norm_num) (zpow_pos (by norm_num) _)) (hM i)) hδ U hsep hzero
  simp only [prod_div_distrib, prod_mul_distrib, prod_const, card_univ] at h
  have hMk : 0 < ∏ i, M i := prod_pos fun i _ => hM i
  have hJ : 0 < ∏ i, (2:ℝ)^(j i) := prod_pos fun _ _ => by positivity
  have hC : (1+(2:ℝ)^k)*2^k ≤ 2*4^k := by
    rw [show (4:ℝ) = 2*2 by norm_num, mul_pow]
    have ht : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (pow_nonneg (by norm_num : (0:ℝ)≤2) k)]
  calc
    _ ≤ _ := h
    _ = (1+2^k)*2^k*(∏ i, (2:ℝ)^(j i))/((∏ i, M i)*δ) := by ring
    _ ≤ _ := by gcongr

/-- The exact one-dimensional majorant in the geometric series of the paper. -/
def geomWeight (j : ℤ) : ℝ := (1/2:ℝ)^j.natAbs

theorem geomWeight_hasSum : HasSum geomWeight 3 := by
  have hn : HasSum (fun n : ℕ => geomWeight (n:ℤ)) 2 := by
    simpa only [geomWeight, Int.natAbs_natCast] using hasSum_geometric_two
  have hp : HasSum (fun n : ℕ => geomWeight (-(n+1 : ℤ))) 1 := by
    have h : ∀ n : ℕ, (-(n+1 : ℤ)).natAbs = n+1 := fun n => by
      rw [Int.natAbs_neg]
      exact Int.natAbs_natCast (n+1)
    simpa only [geomWeight, h, pow_succ, show (2:ℝ)*(1/2) = 1 by norm_num]
      using hasSum_geometric_two.mul_right (1/2:ℝ)
  convert HasSum.of_nat_of_neg_add_one hn hp using 1; norm_num

theorem product_geomWeight_sum (J : Finset (ι → ℤ)) :
    ∑ j ∈ J, ∏ i, geomWeight (j i) ≤ 3^(Fintype.card ι) := by
  classical
  let S (i : ι) := J.image (fun j => j i)
  have hs : J ⊆ Fintype.piFinset S := fun j hj =>
    Fintype.mem_piFinset.mpr fun i => mem_image_of_mem _ hj
  calc
    _ ≤ ∑ j ∈ Fintype.piFinset S, ∏ i, geomWeight (j i) :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => prod_nonneg fun _ _ => by
        dsimp [geomWeight]; positivity)
    _ = ∏ i, ∑ j ∈ S i, geomWeight j := (prod_univ_sum S fun _ => geomWeight).symm
    _ ≤ ∏ _i : ι, (3 : ℝ) := by
      apply prod_le_prod₀ (fun _ _ => sum_nonneg fun _ _ => by dsimp [geomWeight]; positivity)
      intro i _
      rw [← geomWeight_hasSum.tsum_eq]
      exact geomWeight_hasSum.summable.sum_le_tsum _ fun _ _ => by dsimp [geomWeight]; positivity
    _ = _ := by simp

/-- The shellwise Fourier decay `min(1,2^(-2j))`. -/
def decay (j : ℤ) : ℝ := (2:ℝ)^(-2 * max j 0)

theorem dyadic_factor (j : ℤ) : (2:ℝ)^j * decay j = geomWeight j := by
  rw [decay, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  have he : j + -2*max j 0 = -(j.natAbs:ℤ) := by
    cases j <;> simp <;> omega
  rw [he, zpow_neg, zpow_natCast, geomWeight, one_div, inv_pow]

/-- Every finite partial sum of a dyadically bounded nonzero-frequency
remainder is bounded uniformly in the side lengths and the number of cells. -/
theorem finite_remainder (i₀ : ι) (X : Finset α) (f : α → ι → ℝ)
    (M : ι → ℝ) (j : α → ι → ℤ) (K δ : ℝ) (hM : ∀ i, 0 < M i) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hbox : ∀ x ∈ X, ∀ i, |M i * f x i| ≤ (2:ℝ)^(j x i + 1))
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ ∏ i, |f x i-f y i|)
    (hzero : ∀ x ∈ X, δ ≤ ∏ i, |f x i|)
    (F : α → ℝ) (hF : ∀ x ∈ X, F x ≤ K^(Fintype.card ι)*(∏ i,M i)*(∏ i, decay (j x i))) :
    ∑ x ∈ X, F x ≤ 2*(12*K)^(Fintype.card ι)/δ := by
  classical
  let k := Fintype.card ι
  let J := X.image j
  let A := ∏ i, M i
  have hA : 0 < A := prod_pos fun i _ => hM i
  let d (t : ι → ℤ) := ∏ i, decay (t i)
  have hd (t : ι → ℤ) : 0 ≤ d t := prod_nonneg fun i _ => zpow_nonneg (by norm_num) _
  let P (t : ι → ℤ) := ∏ i, (2:ℝ)^(t i)
  let C := 2*(4*K)^k/δ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgroup (t : ι → ℤ) :
      ((X.filter fun x => j x = t).card : ℝ) * (K^k*A*d t) ≤ C*∏ i, geomWeight (t i) := by
    have hb := dyadic_cell_count i₀ (X.filter fun x => j x = t) f M t δ hM hδ
      (fun x hx i => (mem_filter.mp hx).2 ▸ hbox x (mem_filter.mp hx).1 i)
      (fun x hx y hy => hsep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1)
      (fun x hx => hzero x (mem_filter.mp hx).1)
    have hid : P t * d t = ∏ i, geomWeight (t i) := by
      dsimp [P,d]
      rw [← prod_mul_distrib]
      exact prod_congr rfl fun i _ => dyadic_factor (t i)
    calc
      _ ≤ (2*4^k*P t/(A*δ))*(K^k*A*d t) :=
        mul_le_mul_of_nonneg_right hb (mul_nonneg (mul_nonneg (pow_nonneg hK _) hA.le) (hd t))
      _ = C*(P t*d t) := by dsimp [C]; rw [mul_pow]; field_simp
      _ = _ := by rw [hid]
  calc
    _ ≤ ∑ x ∈ X, K^k*A*d (j x) := sum_le_sum hF
    _ = ∑ t ∈ J, ((X.filter fun x => j x = t).card : ℝ) * (K^k*A*d t) := by
      simpa only [sum_const, nsmul_eq_mul] using
        (sum_fiberwise_of_maps_to' (fun x hx => mem_image_of_mem j hx)
          (fun t => K^k*A*d t)).symm
    _ ≤ ∑ t ∈ J, C*∏ i, geomWeight (t i) := sum_le_sum fun t _ => hgroup t
    _ = C*(∑ t ∈ J, ∏ i, geomWeight (t i)) := (mul_sum ..).symm
    _ ≤ C*3^k := mul_le_mul_of_nonneg_left (product_geomWeight_sum J) hC
    _ = _ := by
      change (2*(4*K)^k/δ)*3^k = 2*(12*K)^k/δ
      rw [show (12:ℝ)*K = (4*K)*3 by ring, mul_pow (4*K) 3 k]
      ring

private theorem decay_log {t : ℝ} (ht : 0 < t) : min 1 (t^2)⁻¹ ≤ decay (Int.log 2 t) := by
  let j := Int.log 2 t
  have hlo : (2:ℝ)^j ≤ t := Int.zpow_log_le_self (by decide : 1 < 2) ht
  by_cases hj : j ≤ 0
  · change min 1 (t^2)⁻¹ ≤ (2:ℝ)^(-2*max j 0)
    simp [max_eq_right hj]
  · change min 1 (t^2)⁻¹ ≤ (2:ℝ)^(-2*max j 0)
    rw [max_eq_left (le_of_not_ge hj), show -2*j = -(j+j) by ring, zpow_neg,
      zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    apply (min_le_right ..).trans
    apply inv_anti₀ (mul_pos (zpow_pos (by norm_num) _) (zpow_pos (by norm_num) _))
    rw [sq]; gcongr

/-- Absolute convergence and uniform bound for the full dual remainder, from
product separation and product decay only. Take `α` to be the nonzero dual
lattice points and `δ` the reciprocal of the absolute discriminant. -/
theorem remainder_bound (i₀ : ι) (f : α → ι → ℝ) (M : ι → ℝ) (K δ : ℝ)
    (hM : ∀ i, 0 < M i) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ ∏ i, |f x i-f y i|)
    (hzero : ∀ x, δ ≤ ∏ i, |f x i|)
    (F : α → ℝ) (hFnon : ∀ x, 0 ≤ F x)
    (hF : ∀ x, F x ≤ K^(Fintype.card ι)*(∏ i,M i)*
      (∏ i, min 1 ((|M i*f x i|^2)⁻¹))) :
    Summable F ∧ ∑' x, F x ≤ 2*(12*K)^(Fintype.card ι)/δ := by
  classical
  let j (x : α) (i : ι) := Int.log 2 |M i*f x i|
  have hpos (x : α) (i : ι) : 0 < |M i*f x i| := by
    apply abs_pos.mpr
    apply mul_ne_zero (hM i).ne'
    intro he
    have hz : (∏ v, |f x v|) = 0 := prod_eq_zero (mem_univ i) (by simp [he])
    linarith [hzero x]
  have hfin (X : Finset α) : ∑ x ∈ X, F x ≤ 2*(12*K)^(Fintype.card ι)/δ := by
    apply finite_remainder i₀ X f M j K δ hM hK hδ
      (fun x _ i => (Int.lt_zpow_succ_log_self (by decide : 1 < 2) |M i*f x i|).le)
      (fun x _ y _ => hsep x y) (fun x _ => hzero x) F
    intro x _
    apply (hF x).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hK _) (prod_nonneg fun i _ => (hM i).le))
    apply prod_le_prod₀ (fun i _ => le_min zero_le_one (by positivity))
    exact fun i _ => decay_log (hpos x i)
  exact ⟨summable_of_sum_le hFnon hfin, Real.tsum_le_of_sum_le hFnon hfin⟩

/-- The lower-bound step after Poisson summation. In the application the
zero-mode term is the product of the half-widths and the error satisfies
`remainder_bound`. The explicit scale condition makes the error at most half
of the zero-mode term. -/
theorem lower_bound_of_poisson {V δ D K R count : ℝ} {k : ℕ} (hδ : 0 < δ) (hD : 0 < D)
    (herr : R ≤ 2*(12*K)^k/δ) (hscale : 4*(12*K)^k ≤ V*δ)
    (hpoisson : V - R ≤ D*count) :
    V/(2*D) ≤ count := by
  have hr : R ≤ V/2 := by
    calc
      R ≤ 2*(12*K)^k/δ := herr
      _ = (4*(12*K)^k/δ)/2 := by ring
      _ ≤ _ := by gcongr; exact (div_le_iff₀ hδ).mpr hscale
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hD)).mpr
  nlinarith

/-- Specialize the remainder estimate to an actual complex dual function.
This is the tail and summability input used by `MT.count_from_zero_frequency`;
its second projection is also the tail input to the lattice Poisson theorem. -/
theorem tailNorm_of_product_decay {ν : Type*} [Zero ν] (i₀ : ι)
    (f : ν → ι → ℝ) (M : ι → ℝ) (K δ : ℝ)
    (hM : ∀ i, 0 < M i) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ ∏ i, |f x i-f y i|)
    (hzero : ∀ x, x ≠ 0 → δ ≤ ∏ i, |f x i|)
    (g : ν → ℂ) (hg : ∀ x, x ≠ 0 → ‖g x‖ ≤ K^(Fintype.card ι)*(∏ i,M i)*
      (∏ i, min 1 ((|M i*f x i|^2)⁻¹))) :
    Summable (fun x => ‖g x‖) ∧ tailNorm g ≤ 2*(12*K)^(Fintype.card ι)/δ := by
  classical
  let S : Set ν := {x | x ≠ 0}
  obtain ⟨hs,ht⟩ := remainder_bound i₀ (fun x : S => f x) M K δ hM hK hδ
    (fun x y h => hsep x y (Subtype.val_injective.ne h))
    (fun x => hzero x x.property) (fun x => ‖g x‖) (fun x => norm_nonneg _)
    (fun x => hg x x.property)
  have he (x : ν) : S.indicator (fun x => ‖g x‖) x = if x=0 then 0 else ‖g x‖ := by
    by_cases hx : x=0 <;> simp [S, Set.indicator, hx]
  have hs' : Summable (S.indicator (fun x => ‖g x‖)) := summable_subtype_iff_indicator.mp hs
  have hsingle : Summable (fun x : ν => if x=0 then ‖g x‖ else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun x hx => by
      have hx₀ : x ≠ 0 := by simpa only [mem_singleton] using hx
      simp [hx₀]
  constructor
  · apply (hsingle.add hs').congr
    intro x
    rw [he]
    by_cases hx : x=0 <;> simp [hx]
  · change (∑' x : S, ‖g (x:ν)‖) ≤ _ at ht
    rw [tsum_subtype S (fun x : ν => ‖g x‖)] at ht
    simpa only [he, tailNorm] using ht

/-- The requested physical scale suffices as soon as each half-side
dominates `48 K D`, with `δ = 1/D^k`. -/
theorem scale_of_halfSides (i₀ : ι) (M : ι → ℝ) (K D : ℝ)
    (hK : 0 ≤ K) (hD : 0 < D) (hM : ∀ i, 48*K*D ≤ M i) :
    4*(12*K)^(Fintype.card ι) ≤ (∏ i, M i)*(1/D^(Fintype.card ι)) := by
  let k := Fintype.card ι
  have hk : 1 ≤ k := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have h₄ : (4 : ℝ) ≤ 4^k := by simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤4) hk
  have hside : (48*K*D)^k ≤ ∏ i, M i := by
    calc
      _ = ∏ _i : ι, 48*K*D := by simp [k]
      _ ≤ _ := prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hM i)
  rw [← div_eq_mul_one_div, le_div_iff₀ (pow_pos hD _)]
  calc
    _ ≤ 4^k*(12*K)^k*D^k := by gcongr
    _ = (48*K*D)^k := by rw [← mul_pow, ← mul_pow]; congr 1; ring
    _ ≤ _ := hside

/-- Deduce a primal count from a Poisson identity, support and size bounds
on the primal cutoff, and pointwise product decay and algebraic separation
on the dual side. The count uses the product of half-side lengths. -/
theorem count_of_poisson_and_decay {ν : Type*} [Zero ν] (i₀ : ι)
    (B : Finset α) (w : α → ℂ) (g : ν → ℂ) (f : ν → ι → ℝ)
    (M : ι → ℝ) (K D c : ℝ) (hM : ∀ i, 0 < M i) (hK : 0 ≤ K) (hD : 0 < D) (hc : 0 < c)
    (hsize : ∀ i, 48*K*D ≤ M i)
    (hsep : ∀ x y, x ≠ y → 1/D^(Fintype.card ι) ≤ ∏ i, |f x i-f y i|)
    (hzero : ∀ x, x ≠ 0 → 1/D^(Fintype.card ι) ≤ ∏ i, |f x i|)
    (hg : ∀ x, x ≠ 0 → ‖g x‖ ≤ K^(Fintype.card ι)*(∏ i,M i)*
      (∏ i, min 1 ((|M i*f x i|^2)⁻¹)))
    (hz : ‖g 0‖ = ∏ i, M i)
    (hsupp : ∀ i ∉ B, w i = 0) (hbump : ∀ i ∈ B, ‖w i‖ ≤ 1)
    (hpoisson : (∑' i, w i) = (c : ℂ)⁻¹ * ∑' x, g x) :
    (∏ i, M i)/(2*c) ≤ B.card := by
  let δ := 1/D^(Fintype.card ι)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨hs,ht⟩ := tailNorm_of_product_decay i₀ f M K δ hM hK hδ hsep hzero g hg
  have h := count_from_zero_frequency B w g c (tailNorm g) hc hsupp hbump hs hpoisson le_rfl
  rw [hz, div_le_iff₀ hc] at h
  exact lower_bound_of_poisson hδ hc ht (scale_of_halfSides i₀ M K D hK hD hsize)
    (by simpa only [mul_comm c] using h)

end MT.BoxCounting
