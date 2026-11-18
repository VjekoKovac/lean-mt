module

public import MT.SeedGeometry

/-! # Nonvertical field lines through the product of rectangles
Claim 4 of Section 4.3. The input X j is the set of possible first
coordinates in a product box. The same bound N is used for every box.
-/

@[expose] public section
noncomputable section
namespace MT.Seed
open Finset

theorem field_line_count {K ι J : Type*} [Field K] [Fintype ι] [Fintype J]
    [DecidableEq K] (σ : ι → K →+* ℝ) (z : J → ℤ × ℤ) (H ρ : ℝ)
    (B : Finset (K × K)) (X : (ι → J) → Finset K) (N : ℕ)
    (hcover : ∀ p ∈ B, ∀ i, ∃ j, (σ i p.1, σ i p.2) ∈ rectangle H ρ (z j))
    (hX : ∀ p ∈ B, ∀ j : ι → J, (∀ i, |σ i p.1 - ρ * (z (j i)).1| ≤ H) → p.1 ∈ X j)
    (hcount : ∀ j, (X j).card ≤ N)
    (hlines : ∀ u v : ℝ, (meetingLine z H ρ u (-1) v).card ≤ 2)
    (u v : K) :
    (B.filter fun p => p.2 = u*p.1+v).card ≤ 2^Fintype.card ι * N := by
  classical
  let hits := B.filter fun p => p.2 = u*p.1+v
  let choices (i : ι) := meetingLine z H ρ (σ i u) (-1) (-σ i v)
  let tags := Fintype.piFinset choices
  let piece (j : ι → J) := hits.filter fun p =>
    ∀ i, (σ i p.1, σ i p.2) ∈ rectangle H ρ (z (j i))
  have hsub : hits ⊆ tags.biUnion piece := by
    intro p hp
    obtain ⟨hpB,heq⟩ := mem_filter.mp hp
    choose j hj using hcover p hpB
    apply mem_biUnion.mpr
    refine ⟨j, Fintype.mem_piFinset.mpr (fun i => ?_), mem_filter.mpr ⟨hp,hj⟩⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _, (σ i p.1, σ i p.2), hj i, ?_⟩
    change σ i u * σ i p.1 + -1 * σ i p.2 = -σ i v
    rw [heq, map_add, map_mul]
    ring
  have hf (j : ι → J) : (piece j).card ≤ N := by
    apply le_trans _ (hcount j)
    apply card_le_card_of_injOn Prod.fst
    · intro p hp
      obtain ⟨hh, hbox⟩ := mem_filter.mp hp
      exact hX p (mem_filter.mp hh).1 j (fun i => (hbox i).1)
    · intro p hp q hq h
      obtain ⟨_,hp'⟩ := mem_filter.mp (mem_filter.mp hp).1
      obtain ⟨_,hq'⟩ := mem_filter.mp (mem_filter.mp hq).1
      exact Prod.ext h (by rw [hp', hq', h])
  have htags : tags.card ≤ 2 ^ Fintype.card ι := by
    rw [Fintype.card_piFinset]
    calc
      _ ≤ ∏ _i : ι, 2 := Finset.prod_le_prod (fun i _ => hlines _ _)
      _ = _ := by simp
  calc
    hits.card ≤ (tags.biUnion piece).card := card_le_card hsub
    _ ≤ ∑ j ∈ tags, (piece j).card := card_biUnion_le
    _ ≤ ∑ _j ∈ tags, N := sum_le_sum (fun j _ => hf j)
    _ = tags.card*N := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ htags

end MT.Seed
