module

public import MT.FieldProjection
public import MT.DyadicTail

/-! # Choosing the seed size and preserving its gain under projection
This is the last numerical argument of Section 4.3 and the output of Section 4.4.
The losses in the earlier box estimates must be independent of m. The lemma
`choose_seed_size` chooses m only after those losses have been fixed.
-/

@[expose] public section
noncomputable section
namespace MT
open Finset

/-- Real-valued version of the returning-pair estimate. The denominator D
need not be an integer and can in particular be an exact k-th power. -/
theorem energy_of_returns {K : Type*} [Semiring K] [DecidableEq K]
    (A : Finset K) (B : Finset (K × K)) (D : ℝ) (hB : B.Nonempty)
    (h : ∀ a ∈ A, (B.card : ℝ) ≤ D * ((B.filter fun z => parabolicSum (a,z) ∈ B).card : ℝ)) :
    (A.card : ℝ)^2 * B.card ≤ D^2 * energy A B := by
  classical
  let hits := ((A ×ˢ B).filter fun ab => parabolicSum ab ∈ B).card
  have hsum : hits = ∑ a ∈ A, (B.filter fun z => parabolicSum (a,z) ∈ B).card := by
    simp only [hits, card_eq_sum_ones, sum_filter, sum_product]
  have hr : (A.card : ℝ)*B.card ≤ D*hits := by
    simpa [hsum, mul_sum] using Finset.sum_le_sum h
  have hc : (hits : ℝ)^2 ≤ B.card * (energy A B : ℝ) := by
    exact_mod_cast returning_pairs_sq_le A B B
  apply le_of_mul_le_mul_left (a := (B.card : ℝ))
  · calc
      _ = ((A.card : ℝ)*B.card)^2 := by ring
      _ ≤ (D*hits)^2 := pow_le_pow_left₀ (by positivity) hr _
      _ = D^2*(hits : ℝ)^2 := mul_pow .. 
      _ ≤ D^2*(B.card*(energy A B : ℝ)) := mul_le_mul_of_nonneg_left hc (sq_nonneg _)
      _ = _ := by ring
  · exact_mod_cast hB.card_pos

theorem choose_seed_size (cA cR cL : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ 2*cA*cR^2*cL ≤ (m : ℝ) := by
  obtain ⟨m,hm⟩ := exists_nat_ge (2*cA*cR^2*cL)
  exact ⟨max 2 m, le_max_left _ _, hm.trans (by exact_mod_cast le_max_right 2 m)⟩

namespace Arithmetic
open NumberField
open scoped NumberField

/-- Apply the three quantitative field estimates. M may depend on the chosen
seed and dilation. The base in the configuration scale is independent of k. -/
theorem configuration_of_field_bounds {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    [DecidableEq K] (v : InfinitePlace K) (A : Finset K) (B : Finset (K × K))
    (L m k : ℕ) (M cA cR cL : ℝ) (hdeg : Module.finrank ℚ K = k)
    (hM : 1 ≤ M) (hcA : 0 < cA) (hcR : 0 < cR) (hcL : 0 < cL)
    (hm : 2*cA*cR^2*cL ≤ (m : ℝ)) (hL : 0 < L)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAb : ∀ a ∈ A, boundedInteger M a)
    (hBb : ∀ p ∈ B, boundedInteger M p.1 ∧ boundedInteger M p.2)
    (hline : ∀ u z : K, (B.filter fun p => p.2 = u * p.1 + z).card ≤ L)
    (hAc : ((m : ℝ) / cA)^k ≤ (A.card : ℝ)) (hLc : (L : ℝ) ≤ cL^k)
    (hret : ∀ a ∈ A, (B.card : ℝ) ≤ cR^k * ((B.filter fun z => parabolicSum (a,z) ∈ B).card : ℝ)) :
    ∃ Q : Configuration ((100*M^3*(8*M^2))^k) L, (2 : ℝ)^k ≤ Q.gain := by
  classical
  obtain ⟨Q,hQ⟩ := configuration_of_bounded_field_sets v A B L M hM hA hB hAb hBb hline
  subst k
  refine ⟨Q, ?_⟩
  rw [hQ, le_div_iff₀ (by positivity)]
  have he := energy_of_returns A B (cR ^ Module.finrank ℚ K) hB hret
  have hm' : 2*cR^2*cL ≤ (m : ℝ)/cA := (le_div_iff₀ hcA).mpr (by linarith only [hm])
  let k := Module.finrank ℚ K
  have hsmall : (2:ℝ)^k * (cR^k)^2 * L ≤ (A.card : ℝ) := calc
    _ ≤ (2:ℝ)^k * (cR^k)^2 * cL^k := mul_le_mul_of_nonneg_left hLc (by positivity)
    _ = (2*cR^2*cL)^k := by simp [mul_pow, ← pow_mul, Nat.mul_comm k 2]
    _ ≤ ((m : ℝ)/cA)^k := pow_le_pow_left₀ (by positivity) hm' k
    _ ≤ _ := hAc
  have ha : (0:ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hb : (0:ℝ) < B.card := by exact_mod_cast hB.card_pos
  apply le_of_mul_le_mul_left (a := (cR^k)^2)
  · calc
      _ = ((2:ℝ)^k * (cR^k)^2 * L) * ((A.card : ℝ) * B.card) := by ring
      _ ≤ (A.card : ℝ)*((A.card : ℝ)*B.card) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = (A.card : ℝ)^2 * B.card := by ring
      _ ≤ _ := he
  · positivity

end Arithmetic
end MT
