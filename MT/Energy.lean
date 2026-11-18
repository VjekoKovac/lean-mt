module

public import MT.Configuration
public import Mathlib.Combinatorics.Additive.Energy

/-! # Parabolic counts and mathlib's additive energy
The map a ↦ (a,a²) is injective. This identifies the two counts of ordered
quadruples exactly, and makes mathlib's Cauchy–Schwarz theorem directly
applicable to the paper's configurations, both over ℤ and over a field.
-/

@[expose] public section
noncomputable section
namespace MT

def parabolaEmbedding {K : Type*} [Semiring K] : K ↪ K × K :=
  ⟨fun a => (a, a ^ 2), fun _ _ h => congrArg Prod.fst h⟩

theorem energy_eq_addEnergy {K : Type*} [Semiring K] [DecidableEq K]
    (A : Finset K) (B : Finset (K × K)) :
    energy A B = (A.map parabolaEmbedding).addEnergy B := by
  classical
  rw [Finset.addEnergy_eq_card_filter]
  let e := (parabolaEmbedding (K := K)).prodMap (Function.Embedding.refl (K × K))
  have hp : A.map parabolaEmbedding ×ˢ B = (A ×ˢ B).map e := by
    rw [Finset.prodMap_map_product, Finset.map_refl]
  rw [hp, ← Finset.prodMap_map_product, Finset.filter_map, Finset.card_map]
  unfold energy
  apply congrArg Finset.card
  ext q
  simp only [Finset.mem_filter]
  rfl

/-- The number of representations returning to the test set U, squared,
is at most its cardinality times the parabolic energy. For U=B this is the
Cauchy–Schwarz estimate used in both the seed and the field-energy claim in §4.3. -/
theorem returning_pairs_sq_le {K : Type*} [Semiring K] [DecidableEq K]
    (A : Finset K) (B U : Finset (K × K)) :
    ((A ×ˢ B).filter fun ab => parabolicSum ab ∈ U).card ^ 2 ≤ U.card * energy A B := by
  classical
  rw [energy_eq_addEnergy]
  have h := Finset.card_sq_le_card_mul_addEnergy (A.map parabolaEmbedding) B U
  let e := (parabolaEmbedding (K := K)).prodMap (Function.Embedding.refl (K × K))
  have hp : A.map parabolaEmbedding ×ˢ B = (A ×ˢ B).map e := by
    rw [Finset.prodMap_map_product, Finset.map_refl]
  rw [hp, Finset.filter_map, Finset.card_map] at h
  exact h

/-- Claim on field energy in §4.3. If every parabolic shift returns at least
a 1/D proportion of B to B, Cauchy–Schwarz gives the squared-proportion
lower bound for energy. The integral formulation avoids all divisions. -/
theorem energy_of_return_proportion {K : Type*} [Semiring K] [DecidableEq K]
    (A : Finset K) (B : Finset (K × K)) (D : ℕ) (hB : B.Nonempty)
    (h : ∀ a ∈ A, B.card ≤ D * (B.filter fun z => parabolicSum (a,z) ∈ B).card) :
    A.card ^ 2 * B.card ≤ D ^ 2 * energy A B := by
  classical
  let hits := ((A ×ˢ B).filter fun ab => parabolicSum ab ∈ B).card
  have hsum : hits = ∑ a ∈ A, (B.filter fun z => parabolicSum (a,z) ∈ B).card := by
    simp only [hits, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  have hcount : A.card * B.card ≤ D * hits := by
    simpa [hsum, Finset.mul_sum] using Finset.sum_le_sum h
  have hsquare := Nat.pow_le_pow_left hcount 2
  have hc : hits ^ 2 ≤ B.card * energy A B := returning_pairs_sq_le A B B
  apply Nat.le_of_mul_le_mul_left _ hB.card_pos
  calc
    B.card * (A.card ^ 2 * B.card) = (A.card * B.card) ^ 2 := by ring
    _ ≤ (D * hits) ^ 2 := hsquare
    _ = D ^ 2 * hits ^ 2 := mul_pow _ _ _
    _ ≤ D ^ 2 * (B.card * energy A B) := Nat.mul_le_mul_left _ hc
    _ = B.card * (D ^ 2 * energy A B) := by ring

end MT
