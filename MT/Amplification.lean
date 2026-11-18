module

public import MT.FieldSets
public import MT.FieldIntersections
public import MT.SeedScale

/-! # Proposition 4.1 from a uniform supply of totally real fields
D is chosen first. All constants in the box counts depend only on D and a
one-dimensional cutoff. Next come the integer half-width H, the seed size m,
one seed, the dilation ρ and the uniform projection bound M. Only now choose
the dyadic degree and the field. Thus the same C works in all dimensions.
-/

@[expose] public section
noncomputable section
namespace MT
open NumberField NumberField.InfinitePlace
open scoped NumberField Classical

/-- A bounded-root-discriminant field of every exact dyadic degree is sufficient.
The tower module provides this premise with D=255255. -/
theorem arithmeticAmplification_of_dyadic_fields (D : ℕ) (hDnat : 1 ≤ D)
    (fields : ∀ n : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsTotallyReal K),
      Module.finrank ℚ K = 2^n ∧ (discr K).natAbs ≤ D^(2^n)) : ArithmeticAmplification := by
  classical
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast hDnat
  have hD' : (0 : ℝ) < D := by linarith
  let N : ℕ := ⌈96*BoxCutoff.constant*(D:ℝ)⌉₊ + 1
  let H : ℝ := N
  have hNH : 96*BoxCutoff.constant*(D:ℝ) ≤ H := by
    apply (Nat.le_ceil _).trans
    dsimp [H,N]
    push_cast
    linarith
  have hlarge : 48*BoxCutoff.constant*(D:ℝ) ≤ H/2 := by linarith
  have hDH : (D:ℝ) ≤ H := by
    have h := mul_le_mul_of_nonneg_right BoxCutoff.constant_one_le hD'.le
    linarith
  have hH : 1 ≤ H := hD.trans hDH
  obtain ⟨m,hm,hsize⟩ := choose_seed_size 2 (512*(D:ℝ)) (8*H)
  obtain ⟨a,ha,seed⟩ := Seed.exists_seed_rectangles m hm
  obtain ⟨ρ,hρ,hcut,hV,hshift⟩ := Seed.exists_overlap_scale m H hH
  obtain ⟨haDis,hbDis,hmeet⟩ := seed H (by linarith) ρ hcut
  let M := Intersections.projectionSize m H ρ
  have hM : 1 ≤ M := Intersections.projectionSize_ge_one .. 
  let C := 100*M^3*(8*M^2)
  have hC : 1 < C := by
    have h2 : 1 ≤ M^2 := one_le_pow₀ hM
    have h3 : 1 ≤ M^3 := one_le_pow₀ hM
    dsimp [C]
    nlinarith [mul_le_mul h2 h3 (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ M^2)]
  have hL : 1 < 8*H := by linarith
  refine ⟨C,hC,Real.log (8*H),Real.log_pos hL,?_⟩
  intro n
  let k : ℕ := 2^n
  obtain ⟨K, iF, iN, iT, hdeg, hdisc⟩ := fields n
  change Module.finrank ℚ K = k at hdeg
  let box := Arithmetic.fieldBox K
  let A := Intersections.ATotal box a H ρ
  let B := Intersections.BTotal box a H ρ
  have hdisk : ((discr K).natAbs : ℝ) ≤ (D:ℝ)^Module.finrank ℚ K := by
    rw [hdeg]; exact_mod_cast hdisc
  obtain ⟨hA,hB,hAc,hret⟩ := Intersections.field_intersection_estimates K a H ρ D (by omega)
    hD hH hDH (by linarith) hlarge hdisk haDis hbDis
    (fun j => hshift (a j) (ha j).1 (ha j).2)
  have hcard : Fintype.card (InfinitePlace K) = k := (Arithmetic.card_places_eq_degree K).trans hdeg
  have hN : 0 < N := Nat.zero_lt_succ _
  let L : ℕ := (8*N)^k
  have hLn : 0 < L := pow_pos (by omega) _
  have hLr : (L : ℝ) = (8*H)^k := by simp [L,H]
  have hcap (c : InfinitePlace K → ℝ) : (box c H).card ≤ (4*N)^k := by
    apply (Nat.cast_le (α := ℝ)).mp
    have hb := (Arithmetic.fieldBox_uniform K c hD hdisk (r:=H) (by linarith)).2
    simpa only [hdeg, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using hb
  obtain ⟨hAb,hBb,hline⟩ := Intersections.field_sets_geometry box a H ρ (by linarith)
    ((4*N)^k) ha (Arithmetic.mem_fieldBox K) hcap
    (fun u v => hmeet u (-1) v (Or.inr (by norm_num)))
  have hline' (u v : K) : (B.filter fun p => p.2=u*p.1+v).card ≤ L := by
    apply (hline u v).trans_eq
    rw [hcard, ← mul_pow]
    dsimp [L]
    ring
  let w : InfinitePlace K := Classical.arbitrary _
  obtain ⟨Q,hgain⟩ := Arithmetic.configuration_of_field_bounds w A B L m k M 2
    (512*(D:ℝ)) (8*H) hdeg hM (by norm_num) (by positivity) (by linarith)
    hsize hLn hA hB hAb hBb hline' (by simpa only [hdeg] using hAc)
    hLr.le (by simpa only [hdeg] using hret)
  refine ⟨L, by exact_mod_cast hLn, ?_, Q, hgain⟩
  change (L : ℝ) ≤ Real.exp (Real.log (8*H) * (k : ℝ))
  rw [hLr, mul_comm (Real.log (8*H)), Real.exp_nat_mul, Real.exp_log (by linarith)]

end MT
