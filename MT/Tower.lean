module

public import Nyll.SawinTotallyRealTowers.SawinTotallyRealTower
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic

/-!
# Fields of every dyadic degree with bounded root discriminant

The source paper uses Martinet's tower. We use Naganori Yamaguchi's
Apache-2.0 formalization of Sawin's totally real pro-2 tower. The finite-layer
extraction at the end adapts the proof of
`ClassFieldTower.Sawin.sawin_totally_real_tower`, copyright 2026 Naganori
Yamaguchi (assisted by OpenAI Codex), pinned in `lake-manifest.json`.
Only an upper bound on root discriminant is required by the box-count argument.
-/

@[expose] public section

namespace MT.Tower

open NumberField
open scoped NumberField

/-- An exponential discriminant bound descends to any intermediate field. -/
theorem subfield_discr_bound {E : Type*} [Field E] [NumberField E]
    (F : IntermediateField ℚ E) {D : ℕ}
    (he : (NumberField.discr E).natAbs ≤ D ^ Module.finrank ℚ E) :
    (NumberField.discr F).natAbs ≤ D ^ Module.finrank ℚ F := by
  have h := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    F (𝓞 F) E (𝓞 E)
  have hdvd : (NumberField.discr F).natAbs ^ Module.finrank F E ∣ (NumberField.discr E).natAbs :=
    Dvd.intro_left _ h.symm
  have hle := (Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)) hdvd).trans he
  rw [← Module.finrank_mul_finrank ℚ F E, pow_mul] at hle
  exact le_of_pow_le_pow_left₀ (Module.finrank_pos.ne') (Nat.zero_le _) hle

/-- The fixed field of a subgroup of the appropriate order has exactly the desired degree. -/
theorem exists_dyadic_subfield (n : ℕ) (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    [NumberField.IsTotallyReal E] (hp : IsPGroup 2 (E ≃ₐ[ℚ] E))
    (hsize : 2 ^ n ≤ Module.finrank ℚ E) {D : ℕ}
    (he : (NumberField.discr E).natAbs ≤ D ^ Module.finrank ℚ E) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
      Module.finrank ℚ K = 2 ^ n ∧ (NumberField.discr K).natAbs ≤ D ^ (2 ^ n) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hp.exists_card_eq
  have hdeg : Module.finrank ℚ E = 2 ^ j := (IsGalois.card_aut_eq_finrank ℚ E).symm.trans hj
  have hnj : n ≤ j := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (hsize.trans_eq hdeg)
  have hsmall : 2 ^ (j - n) ≤ Nat.card (E ≃ₐ[ℚ] E) := by
    rw [hj]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hp hsmall
  let F := IntermediateField.fixedField H
  have hrel : Module.finrank F E = 2 ^ (j - n) :=
    (IntermediateField.finrank_fixedField_eq_card H).trans hH
  have hmul : Module.finrank ℚ F * (2 ^ (j - n)) = (2 ^ n) * (2 ^ (j - n)) := by
    rw [← pow_add, Nat.add_sub_of_le hnj, ← hrel, Module.finrank_mul_finrank, hdeg]
  have hF := Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ (j - n)) hmul
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF, hF ▸ subfield_discr_bound F he⟩

open ClassFieldTower.Sawin

/-- Exact dyadic degrees and a common root-discriminant upper bound, sufficient
for the arithmetic argument. The fields need not be nested for the MT proof. -/
theorem dyadic_totally_real_fields (n : ℕ) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsTotallyReal K),
      Module.finrank ℚ K = 2 ^ n ∧ (NumberField.discr K).natAbs ≤ 255255 ^ (2 ^ n) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, L, hGal, _, hInfinite, hL, _, _, _⟩ :=
    exists_sawinInfinite_totallyReal_split_field
  obtain ⟨E, hE, hsize⟩ :=
    @AlgebraicNumberTheory.exists_finiteGaloisIntermediateField_le_finrank_ge_of_infinite_aut
      ℚ (AlgebraicClosure ℚ) _ _ _ L hGal hInfinite (2 ^ n)
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : IsGalois ℚ E := E.isGalois
  have hadm := (isAdmissibleFiniteLayer_iff_le_maximalRealProPOutside
      2 sawinRationalPrimeSupport E).mpr (hE.trans hL)
  let : IsTotallyReal E := (isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal E).mp hadm.2.2
  exact exists_dyadic_subfield n E hadm.1 hsize
    (discr_natAbs_le_of_sawin_ramification E hadm.1 hadm.2.1)

end MT.Tower
