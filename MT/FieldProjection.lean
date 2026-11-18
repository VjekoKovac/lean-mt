module

public import MT.Arithmetic
public import MT.Energy

/-! # From bounded algebraic integers to a real configuration
This is the final projection of §4.4. It uses the uniform size of the original
coordinates at *all* infinite places and the field line occupancy. It produces
a real configuration with the same energy ratio at an explicit exponential
scale. The earlier lattice-intersection construction supplies its inputs.
-/

@[expose] public section
noncomputable section
namespace MT.Arithmetic

open NumberField NumberField.InfinitePlace
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]

/-- The first coordinate records algebraic integrality, the second the
absolute value of every real conjugate. -/
def boundedInteger (M : ℝ) (x : K) : Prop :=
  IsIntegral ℤ x ∧ ∀ v : InfinitePlace K, v x ≤ M

private theorem bounded_sub {M : ℝ} {a b : K}
    (ha : boundedInteger M a) (hb : boundedInteger M b) :
    boundedInteger (2 * M) (a - b) := by
  refine ⟨ha.1.sub hb.1, fun v => ?_⟩
  let σ := embedding_of_isReal (IsTotallyReal.isReal v)
  have hn (x : K) : |σ x| = v x := norm_embedding_of_isReal _ x
  rw [← hn, map_sub]
  calc
    _ ≤ |σ a| + |σ b| := abs_sub _ _
    _ ≤ M + M := add_le_add (hn a ▸ ha.2 v) (hn b ▸ hb.2 v)
    _ = _ := by ring

omit [NumberField K] [IsTotallyReal K] in
private theorem bounded_mul {M : ℝ} {a b : K} (hM : 0 ≤ M)
    (ha : boundedInteger M a) (hb : boundedInteger M b) :
    boundedInteger (M * M) (a * b) :=
  ⟨ha.1.mul hb.1, fun v => (map_mul v a b).le.trans
    (mul_le_mul (ha.2 v) (hb.2 v) (apply_nonneg _ _) hM)⟩

private theorem bounded_det {M : ℝ} (hM : 0 ≤ M) {p q r : K × K}
    (hp : boundedInteger M p.1 ∧ boundedInteger M p.2)
    (hq : boundedInteger M q.1 ∧ boundedInteger M q.2)
    (hr : boundedInteger M r.1 ∧ boundedInteger M r.2) :
    boundedInteger (8 * M ^ 2) (det₂ p q r) := by
  have hh : 0 ≤ 2 * M := by positivity
  convert bounded_sub (bounded_mul hh (bounded_sub hq.1 hp.1) (bounded_sub hr.2 hp.2))
    (bounded_mul hh (bounded_sub hr.1 hp.1) (bounded_sub hq.2 hp.2)) using 1 <;> first | rfl | ring

private theorem gap {M S : ℝ} (hS : 1 ≤ S) (hM : 1 ≤ M) {x : K}
    (hx : boundedInteger M x) (v : InfinitePlace K) {d : ℕ} (hd : d ≤ 3) (h : x ≠ 0) :
    100 / (100 * S ^ 3 * M) ^ Module.finrank ℚ K ≤
      |embedding_of_isReal (IsTotallyReal.isReal v) x / S ^ d| := by
  let a : 𝓞 K := ⟨x, hx.1⟩
  have hne : a ≠ 0 := fun e => h (congrArg (fun t : 𝓞 K => (t : K)) e)
  exact normalized_integral_gap hne hS hM v (fun w _ => hx.2 w) hd

/-- Construction of A and B and the final three bounds in Proposition 4.1.
The uniform coordinate bound M≥1 also suffices for the parabolic scaling S=M.
The output ratio is exactly the field energy divided by L·|A|·|B|. -/
theorem configuration_of_bounded_field_sets [DecidableEq K]
    (v : InfinitePlace K) (A : Finset K) (B : Finset (K × K)) (L : ℕ)
    (M : ℝ) (hM : 1 ≤ M) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAb : ∀ a ∈ A, boundedInteger M a)
    (hBb : ∀ p ∈ B, boundedInteger M p.1 ∧ boundedInteger M p.2)
    (hline : ∀ u z : K, (B.filter fun p => p.2 = u * p.1 + z).card ≤ L) :
    ∃ Q : Configuration ((100 * M^3 * (8 * M^2)) ^ Module.finrank ℚ K) L,
      Q.gain = (energy A B : ℝ) / (L * A.card * B.card : ℝ) := by
  classical
  let σ := embedding_of_isReal (IsTotallyReal.isReal v)
  let T := 8 * M ^ 2
  let H := (100 * M ^ 3 * T) ^ Module.finrank ℚ K
  have hm : 0 < M := by linarith
  have hT : 1 ≤ T := by dsimp [T]; nlinarith [one_le_pow₀ hM (n:=2)]
  have hscale : 0 < H := by dsimp [H, T]; positivity
  have h2 : 2*M ≤ T := by dsimp [T]; nlinarith [mul_nonneg (sub_nonneg.mpr hM) hm.le]
  have hn (x : K) : |σ x| = v x := norm_embedding_of_isReal _ x
  have hcoord {a b : K} (ha : boundedInteger M a) (hb : boundedInteger M b)
      (d : ℕ) (hd : d ≤ 3) (hne : a ≠ b) :
      100 * H⁻¹ ≤ |σ a / M^d - σ b / M^d| := by
    have hu := bounded_sub ha hb
    have hg := gap hM hT (x := a-b) ⟨hu.1, fun w => (hu.2 w).trans h2⟩ v hd (sub_ne_zero.mpr hne)
    simpa only [H, σ, div_eq_mul_inv, map_sub, sub_mul] using hg
  have hor {a : K} (ha : boundedInteger M a) : |σ a / M| ≤ 1 := by
    rw [abs_div, abs_of_pos hm, div_le_one hm, hn]
    exact ha.2 v
  have vert {a : K} (ha : boundedInteger M a) : |σ a / M^2| ≤ 1 := by
    rw [abs_div, abs_of_pos (pow_pos hm 2), div_le_one (pow_pos hm 2), hn]
    exact (ha.2 v).trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hM) hm.le])
  let aE := projectedCoordinate σ M hm.ne'
  let bE := projectedPoint σ M hm.ne'
  let Q : Configuration H L := {
    A := A.map aE
    B := B.map bE
    nonemptyA := hA.map
    nonemptyB := hB.map
    inBoxA := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
      exact hor (hAb x hx)
    inBoxB := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hp
      exact ⟨hor (hBb x hx).1, vert (hBb x hx).2⟩
    separated := by
      intro a ha b hb hne
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
      have hh := hcoord (hAb x hx) (hAb y hy) 1 (by decide) (fun h => hne (congrArg aE h))
      simp only [pow_one] at hh
      change H⁻¹ ≤ |σ x / M - σ y / M|
      linarith [inv_pos.mpr hscale]
    strip := by
      intro s c
      apply Nat.cast_le.mpr
      apply projected_strip_card_le σ M hm.ne' B (inv_pos.mpr hscale) L
        (fun p hp => hor (hBb p hp).1) _ _ hline s c
      · intro p hp q hq hne
        apply hcoord (hBb p hp).2 (hBb q hq).2 2 (by decide)
        exact fun h => hne (congrArg (fun x => σ x / M^2) h)
      · intro p hp q hq r hr hne
        rw [projected_det σ hm.ne'] at hne ⊢
        have hD := bounded_det hm.le (hBb p hp) (hBb q hq) (hBb r hr)
        have hdet : det₂ p q r ≠ 0 := by
          intro h
          simp [h] at hne
        simpa only [H, σ, div_eq_mul_inv] using gap hM hT hD v (by decide : 3 ≤ 3) hdet }
  refine ⟨Q, ?_⟩
  obtain ⟨h₁,h₂,h₃⟩ := project_preserves_counts σ M hm.ne' A B
  change (energy (A.map aE) (B.map bE) : ℝ) / _ = _
  simp [Q, aE, bE, h₁, h₂, h₃]

end MT.Arithmetic
