module

public import MT.SeedPolynomial
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Thickening a seed

Undoing parabolic dilation changes the horizontal and vertical half-widths to
`H / ρ` and `1 / √ρ`. A quantitative determinant perturbation estimate
keeps all distinct triples noncollinear, uniformly over the chosen points.
-/

@[expose] public section
noncomputable section

namespace MT.Seed

open Finset

abbrev Plane := ℝ × ℝ

def toPlane (p : ℤ × ℤ) : Plane := ((p.1 : ℝ), (p.2 : ℝ))

/-- Axis-aligned rectangles with center `(ρ b,ρ² τ)` and half-widths
`H` and `ρ^(3/2)`. -/
def rectangle (H ρ : ℝ) (p : ℤ × ℤ) : Set Plane :=
  {q | |q.1 - ρ * p.1| ≤ H ∧ |q.2 - ρ ^ 2 * p.2| ≤ ρ ^ (3/2 : ℝ)}

def close (δ : ℝ) (q p : Plane) : Prop := |q.1-p.1| ≤ δ ∧ |q.2-p.2| ≤ δ

private theorem diff_error {x y X Y δ : ℝ} (hx : |x-X| ≤ δ) (hy : |y-Y| ≤ δ) :
    |(x-y)-(X-Y)| ≤ 2*δ := calc
  _ = |(x-X)-(y-Y)| := by ring_nf
  _ ≤ |x-X| + |y-Y| := abs_sub .. 
  _ ≤ _ := by linarith

private theorem prod_error {x y X Y B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hx : |x-X| ≤ 2*δ) (hy : |y-Y| ≤ 2*δ) (hX : |X| ≤ 2*B) (hY : |Y| ≤ 2*B) :
    |x*y-X*Y| ≤ 8*(B+1)*δ := by
  have hy' : |y| ≤ 2*(B+1) := calc
    _ = |(y-Y)+Y| := by ring_nf
    _ ≤ |y-Y|+|Y| := abs_add_le .. 
    _ ≤ _ := by linarith
  calc
    _ = |(x-X)*y + X*(y-Y)| := by ring_nf
    _ ≤ |(x-X)*y| + |X*(y-Y)| := abs_add_le .. 
    _ = |x-X| * |y| + |X| * |y-Y| := by rw [abs_mul, abs_mul]
    _ ≤ (2*δ)*(2*(B+1)) + (2*B)*(2*δ) := by gcongr
    _ ≤ _ := by nlinarith

/-- If the seed coordinates have magnitude at most `B` and each coordinate moves
by at most `δ ≤ 1`, the signed double area changes by at most `16(B+1)δ`. -/
theorem determinant_stability {p q r p' q' r' : Plane} {B δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hp : close B p 0) (hq : close B q 0) (hr : close B r 0)
    (hP : close δ p' p) (hQ : close δ q' q) (hR : close δ r' r) :
    |determinant p' q' r' - determinant p q r| ≤ 16*(B+1)*δ := by
  have bd {x y : ℝ} (hx : |x| ≤ B) (hy : |y| ≤ B) : |x-y| ≤ 2*B :=
    (abs_sub ..).trans (by linarith)
  simp [close] at hp hq hr
  let e₁ := (p'.1-r'.1)*(q'.2-r'.2) - (p.1-r.1)*(q.2-r.2)
  let e₂ := (q'.1-r'.1)*(p'.2-r'.2) - (q.1-r.1)*(p.2-r.2)
  have h₁ : |e₁| ≤ 8*(B+1)*δ := prod_error hB hδ hδ₁ (diff_error hP.1 hR.1)
    (diff_error hQ.2 hR.2) (bd hp.1 hr.1) (bd hq.2 hr.2)
  have h₂ : |e₂| ≤ 8*(B+1)*δ := prod_error hB hδ hδ₁ (diff_error hQ.1 hR.1)
    (diff_error hP.2 hR.2) (bd hq.1 hr.1) (bd hp.2 hr.2)
  calc
    _ = |e₁-e₂| := by dsimp [e₁, e₂, determinant]; ring_nf
    _ ≤ |e₁|+|e₂| := abs_sub .. 
    _ ≤ _ := by linarith

/-- Undo parabolic dilation. -/
def unscale (ρ : ℝ) (p : Plane) : Plane := (p.1/ρ, p.2/ρ^2)

private theorem unscale_close {p : ℤ × ℤ} {q : Plane} {ρ H δ : ℝ} (hρ : 0 < ρ)
    (hH : H/ρ ≤ δ) (hV : 1/Real.sqrt ρ ≤ δ) (hq : q ∈ rectangle H ρ p) :
    close δ (unscale ρ q) (toPlane p) := by
  obtain ⟨hx,hy⟩ := hq
  have hs := Real.sq_sqrt hρ.le
  have ht : ρ^(3/2 : ℝ) = ρ * Real.sqrt ρ := by
    rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hρ, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  constructor
  · change |q.1/ρ - p.1| ≤ δ
    calc
      _ = |q.1 - ρ*p.1| / ρ := by
        rw [show q.1/ρ - p.1 = (q.1 - ρ*p.1)/ρ by field_simp, abs_div, abs_of_pos hρ]
      _ ≤ H/ρ := by gcongr
      _ ≤ _ := hH
  · change |q.2/ρ^2 - p.2| ≤ δ
    calc
      _ = |q.2 - ρ^2*p.2| / ρ^2 := by
        rw [show q.2/ρ^2 - p.2 = (q.2 - ρ^2*p.2)/ρ^2 by field_simp, abs_div, abs_of_pos (sq_pos_of_pos hρ)]
      _ ≤ ρ^(3/2 : ℝ)/ρ^2 := by gcongr
      _ = 1 / Real.sqrt ρ := by rw [ht]; field_simp; nlinarith
      _ ≤ _ := hV

private theorem cast_det (p q r : ℤ × ℤ) :
    determinant (toPlane p) (toPlane q) (toPlane r) = ((determinant p q r : ℤ) : ℝ) := by
  simp [determinant, toPlane]

private theorem unscale_det {ρ : ℝ} (hρ : ρ ≠ 0) (p q r : Plane) :
    determinant (unscale ρ p) (unscale ρ q) (unscale ρ r) = determinant p q r / ρ^3 := by
  dsimp [determinant, unscale]
  field_simp

/-- The paper's no-three-rectangles conclusion, in its determinant form.
The threshold is uniform in all three labels and all points in their rectangles.
The right side is polynomial in the coordinate bound and in the horizontal half-width. -/
theorem thickened_determinant_ne {ι : Type*} (z : ι → ℤ × ℤ) (B H ρ : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ i, close B (toPlane (z i)) 0)
    (htrip : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → determinant (z i) (z j) (z k) ≠ 0)
    (h₁ : (32*(B+1))^2 ≤ ρ) (h₂ : H*(32*(B+1)) ≤ ρ)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {p q r : Plane} (hp : p ∈ rectangle H ρ (z i)) (hq : q ∈ rectangle H ρ (z j))
    (hr : r ∈ rectangle H ρ (z k)) :
    determinant p q r ≠ 0 := by
  let N := 32*(B+1)
  have hN : 1 ≤ N := by dsimp [N]; linarith
  have hNpos : 0 < N := by linarith
  have hρ : 0 < ρ := (sq_pos_of_pos hNpos).trans_le h₁
  have hδ : 0 < 1/N := by positivity
  have hδ₁ : 1/N ≤ 1 := (div_le_iff₀ hNpos).mpr (by linarith)
  have hH : H/ρ ≤ 1/N := (div_le_div_iff₀ hρ hNpos).mpr (by simpa [N] using h₂)
  have hV : 1/Real.sqrt ρ ≤ 1/N :=
    one_div_le_one_div_of_le hNpos (Real.le_sqrt_of_sq_le h₁)
  have herr := determinant_stability hB hδ.le hδ₁ (hbound i) (hbound j) (hbound k)
    (unscale_close hρ hH hV hp) (unscale_close hρ hH hV hq) (unscale_close hρ hH hV hr)
  intro he
  rw [unscale_det hρ.ne', he, zero_div, zero_sub, abs_neg, cast_det, ← Int.cast_abs] at herr
  have hunit : (1:ℤ) ≤ |determinant (z i) (z j) (z k)| := by
    have := abs_pos.mpr (htrip i j k hij hik hjk)
    omega
  have hu : (1:ℝ) ≤ ((|determinant (z i) (z j) (z k)| : ℤ):ℝ) := by exact_mod_cast hunit
  have hf : 16*(B+1)*(1/N) = (1/2 : ℝ) := by
    dsimp [N]; field_simp; ring
  linarith

private theorem determinant_zero_of_line {p q r : Plane} {u v c : ℝ}
    (huv : u ≠ 0 ∨ v ≠ 0)
    (hp : u*p.1+v*p.2 = c) (hq : u*q.1+v*q.2 = c) (hr : u*r.1+v*r.2 = c) :
    determinant p q r = 0 := by
  rcases huv with hu | hv
  · apply (mul_eq_zero.mp (show u*determinant p q r = 0 by
      unfold determinant
      linear_combination (q.2-r.2)*(hp-hr) - (p.2-r.2)*(hq-hr))).resolve_left hu
  · apply (mul_eq_zero.mp (show v*determinant p q r = 0 by
      unfold determinant
      linear_combination (p.1-r.1)*(hq-hr) - (q.1-r.1)*(hp-hr))).resolve_left hv

/-- All labels of rectangles intersecting the affine line `ux + vy = c`. -/
def meetingLine {ι : Type*} [Fintype ι] (z : ι → ℤ × ℤ) (H ρ u v c : ℝ) : Finset ι := by
  classical
  exact univ.filter fun i => ∃ p ∈ rectangle H ρ (z i), u*p.1 + v*p.2 = c

/-- Every affine line meets at most two distinct rectangles, also for vertical lines. -/
theorem card_meetingLine_le_two {ι : Type*} [Fintype ι]
    (z : ι → ℤ × ℤ) (B H ρ : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ i, close B (toPlane (z i)) 0)
    (htrip : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → determinant (z i) (z j) (z k) ≠ 0)
    (h₁ : (32*(B+1))^2 ≤ ρ) (h₂ : H*(32*(B+1)) ≤ ρ)
    (u v c : ℝ) (huv : u ≠ 0 ∨ v ≠ 0) :
    (meetingLine z H ρ u v c).card ≤ 2 := by
  classical
  by_contra! ht
  obtain ⟨i,j,k,hi,hj,hk,hij,hik,hjk⟩ := two_lt_card_iff.mp ht
  obtain ⟨p,hp,hlp⟩ := (mem_filter.mp hi).2
  obtain ⟨q,hq,hlq⟩ := (mem_filter.mp hj).2
  obtain ⟨r,hr,hlr⟩ := (mem_filter.mp hk).2
  exact thickened_determinant_ne z B H ρ hB hbound htrip h₁ h₂ hij hik hjk hp hq hr
    (determinant_zero_of_line huv hlp hlq hlr)

private theorem integer_eq_of_close {x : ℝ} {a b : ℤ} (ha : |x-a| ≤ 1/4) (hb : |x-b| ≤ 1/4) :
    a = b := by
  have hab : |((a-b : ℤ):ℝ)| < 1 := calc
    _ = |(x-b) - (x-a)| := by push_cast; ring_nf
    _ ≤ |x-b| + |x-a| := abs_sub .. 
    _ < _ := by linarith
  rw [← Int.cast_abs] at hab
  have h : |a-b| < 1 := by exact_mod_cast hab
  have hz : |a-b| = 0 := by have := abs_nonneg (a-b); omega
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

/-- The intervals of horizontal half-width `H` around distinct scaled integer
generators are disjoint. -/
theorem intervals_disjoint {a b : ℤ} {H ρ : ℝ}
    (hρ : 0 < ρ) (hH : 4*H ≤ ρ) (hab : a ≠ b) :
    Disjoint {x : ℝ | |x-ρ*a| ≤ H} {x : ℝ | |x-ρ*b| ≤ H} := by
  apply Set.disjoint_left.mpr
  intro x ha hb
  have hclose (c : ℤ) (hc : |x-ρ*c| ≤ H) : |x/ρ-c| ≤ 1/4 := calc
    _ = |x-ρ*c| /ρ := by
      rw [show x/ρ-c = (x-ρ*c)/ρ by field_simp, abs_div, abs_of_pos hρ]
    _ ≤ H/ρ := by gcongr
    _ ≤ _ := (div_le_iff₀ hρ).mpr (by linarith)
  exact hab (integer_eq_of_close (hclose a ha) (hclose b hb))

/-- Rectangles around different integer centers are disjoint. -/
theorem rectangles_disjoint {p q : ℤ × ℤ} {H ρ : ℝ}
    (hρ : 16 ≤ ρ) (hH : 4*H ≤ ρ) (hpq : p ≠ q) :
    Disjoint (rectangle H ρ p) (rectangle H ρ q) := by
  have hρ' : 0 < ρ := by linarith
  have hα : H/ρ ≤ 1/4 := (div_le_iff₀ hρ').mpr (by linarith)
  have hβ : 1/Real.sqrt ρ ≤ 1/4 :=
    one_div_le_one_div_of_le (by norm_num) (Real.le_sqrt_of_sq_le (by norm_num; linarith))
  apply Set.disjoint_left.mpr
  intro x hp hq
  have hu := unscale_close hρ' hα hβ hp
  have hw := unscale_close hρ' hα hβ hq
  exact hpq (Prod.ext (integer_eq_of_close hu.1 hw.1) (integer_eq_of_close hu.2 hw.2))

/-- Upper bound on both coordinates of any bounded integer subset-sum seed. -/
def coordinateBound (m : ℕ) : ℕ := m * (2^(3*m))^2

theorem seedPoint_bounded {m : ℕ} {a : Fin m → ℤ}
    (ha : ∀ i, 1 ≤ a i ∧ a i ≤ (2:ℤ)^(3*m)) (s : Finset (Fin m)) :
    close (coordinateBound m) (toPlane (seedPoint a s)) 0 := by
  let M : ℤ := 2^(3*m)
  have hM : 1 ≤ M := by dsimp [M]; exact one_le_pow₀ (by norm_num)
  have hM' : M ≤ M^2 := by nlinarith only [hM, mul_nonneg (sub_nonneg.mpr hM) (by omega : 0 ≤ M)]
  have sums (f : Fin m → ℤ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ M^2) :
      |∑ i ∈ s, f i| ≤ (m:ℤ)*M^2 := calc
    _ = ∑ i ∈ s, f i := abs_of_nonneg (sum_nonneg fun i _ => (hf i).1)
    _ ≤ ∑ _i ∈ s, M^2 := sum_le_sum fun i _ => (hf i).2
    _ = (s.card:ℤ)*M^2 := by simp
    _ ≤ _ := by
      gcongr
      exact_mod_cast card_finset_fin_le s
  have h₁ := sums a fun i => ⟨by linarith [(ha i).1], (ha i).2.trans hM'⟩
  have h₂ := sums (fun i => (a i)^2) fun i =>
    ⟨sq_nonneg _, pow_le_pow_left₀ (by linarith [(ha i).1]) (ha i).2 _⟩
  change |((∑ i ∈ s, a i : ℤ):ℝ) - 0| ≤ (coordinateBound m : ℝ) ∧
    |((∑ i ∈ s, (a i)^2 : ℤ):ℝ) - 0| ≤ (coordinateBound m : ℝ)
  simp only [sub_zero, ← Int.cast_abs, coordinateBound]
  constructor
  · exact_mod_cast h₁
  · exact_mod_cast h₂

/-- An explicit sufficient value of the dilation parameter in the paper. -/
def dilationThreshold (m : ℕ) (H : ℝ) : ℝ :=
  max ((32*((coordinateBound m:ℝ)+1))^2) (H*(32*((coordinateBound m:ℝ)+1)))

/-- Simultaneous bounded integer seed and all three clauses of the rectangle lemma.
The dilation threshold is independent of the chosen line and of the product dimension. -/
theorem exists_seed_rectangles (m : ℕ) (hm : 2 ≤ m) :
    ∃ a : Fin m → ℤ, (∀ i, 1 ≤ a i ∧ a i ≤ (2:ℤ)^(3*m)) ∧
      ∀ H : ℝ, 0 ≤ H → ∀ ρ : ℝ, dilationThreshold m H ≤ ρ →
      (∀ i j, i ≠ j → Disjoint {x : ℝ | |x-ρ*a i| ≤ H} {x : ℝ | |x-ρ*a j| ≤ H}) ∧
      (∀ s t, s ≠ t → Disjoint (rectangle H ρ (seedPoint a s)) (rectangle H ρ (seedPoint a t))) ∧
      (∀ u v c : ℝ, u ≠ 0 ∨ v ≠ 0 → (meetingLine (seedPoint a) H ρ u v c).card ≤ 2) := by
  obtain ⟨a,ha,hinj,hseed,htrip⟩ := exists_bounded_seed m hm
  refine ⟨a,ha,?_⟩
  intro H hH ρ hρ
  let B : ℝ := coordinateBound m
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h₁ : (32*(B+1))^2 ≤ ρ := (le_max_left _ _).trans hρ
  have h₂ : H*(32*(B+1)) ≤ ρ := (le_max_right _ _).trans hρ
  have h16 : 16 ≤ ρ := by nlinarith [sq_nonneg B]
  have hh : 4*H ≤ ρ := by nlinarith [mul_nonneg hB hH]
  refine ⟨fun i j h => intervals_disjoint (by linarith) hh (hinj.ne h),
    fun s t h => rectangles_disjoint h16 hh (hseed.ne h), ?_⟩
  exact card_meetingLine_le_two (seedPoint a) B H ρ hB (seedPoint_bounded ha) htrip h₁ h₂

end MT.Seed
