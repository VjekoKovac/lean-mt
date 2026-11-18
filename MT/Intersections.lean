module

public import MT.Overlap
public import MT.Energy
public import Mathlib.NumberTheory.NumberField.Basic

/-! # Intersection of the thickened seed products with the integer lattice
A box query returns the elements of the field whose embeddings lie in one
specified box. The two finite unions below count the actual elements without
multiplicity. The return estimate uses a disjoint family of midpoint boxes.
-/

@[expose] public section
noncomputable section

namespace MT.Intersections

open Finset
open scoped Classical

variable {ι K : Type*} [Fintype ι] [Field K] {m : ℕ}
variable (box : (ι → ℝ) → ℝ → Finset K) (a : Fin m → ℤ) (H ρ : ℝ)

/-- Integer points with the prescribed tuple of generator-interval labels. -/
def genBox (j : ι → Fin m) : Finset K := box (fun i => ρ * a (j i)) H

/-- Product of the horizontal and vertical integer boxes for fixed subset labels. -/
def rectBox (J : ι → Finset (Fin m)) : Finset (K × K) :=
  (box (fun i => ρ * (Seed.seedPoint a (J i)).1) H) ×ˢ
  (box (fun i => ρ^2 * (Seed.seedPoint a (J i)).2) (ρ^(3/2 : ℝ)))

/-- The first component of the intersection called 𝒜 in Section 4.3. -/
def ATotal : Finset K := univ.biUnion (genBox box a H ρ)

/-- The second component ℬ, after grouping horizontal and vertical coordinates. -/
def BTotal : Finset (K × K) := univ.biUnion (rectBox box a H ρ)

/-- For each embedding, the cardinality of its seed index set is m. -/
theorem card_A_lower (σ : ι → K →+* ℝ)
    (hbox : ∀ c r x, x ∈ box c r ↔ IsIntegral ℤ x ∧ ∀ i, |σ i x - c i| ≤ r)
    (hdis : ∀ j j', j ≠ j' →
      Disjoint {x : ℝ | |x-ρ*a j| ≤ H} {x : ℝ | |x-ρ*a j'| ≤ H})
    (lo : ℝ) (hlo : ∀ c, lo ≤ ((box c H).card : ℝ)) :
    (m : ℝ) ^ Fintype.card ι * lo ≤ ((ATotal box a H ρ).card : ℝ) := by
  have hd : (↑(univ : Finset (ι → Fin m)) : Set _).PairwiseDisjoint (genBox box a H ρ) := by
    intro j _ l _ hne
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (hdis _ _ hi)
      (((hbox _ _ x).mp hx).2 i) (((hbox _ _ x).mp hy).2 i)
  unfold ATotal
  rw [Finset.card_biUnion hd, Nat.cast_sum]
  calc
    _ = ∑ _j : ι → Fin m, lo := by simp [nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun j _ => hlo _

omit [Field K] in
/-- The upper cardinality estimate for the second component. -/
theorem card_B_upper {U V : ℝ}
    (hU : 0 ≤ U) (hu : ∀ c, ((box c H).card : ℝ) ≤ U)
    (hv : ∀ c, ((box c (ρ^(3/2 : ℝ))).card : ℝ) ≤ V) :
    ((BTotal box a H ρ).card : ℝ) ≤ ((2 : ℝ)^m)^Fintype.card ι * (U*V) := by
  unfold BTotal
  calc
    _ ≤ (∑ J : ι → Finset (Fin m), ((rectBox box a H ρ J).card : ℝ)) := by
      exact_mod_cast (Finset.card_biUnion_le (s := univ) (t := rectBox box a H ρ))
    _ ≤ ∑ _J : ι → Finset (Fin m), U*V := by
      apply Finset.sum_le_sum
      intro J _
      simp only [rectBox, card_product, Nat.cast_mul]
      exact mul_le_mul (hu _) (hv _) (Nat.cast_nonneg _) hU
    _ = _ := by simp [Fintype.card_finset, nsmul_eq_mul]

omit [Fintype ι] in
/-- Characterize both integer coordinates of a single product box. -/
theorem mem_rectBox (σ : ι → K →+* ℝ)
    (hbox : ∀ c r x, x ∈ box c r ↔ IsIntegral ℤ x ∧ ∀ i, |σ i x - c i| ≤ r)
    (J : ι → Finset (Fin m)) (p : K × K) :
    p ∈ rectBox box a H ρ J ↔ IsIntegral ℤ p.1 ∧ IsIntegral ℤ p.2 ∧
      ∀ i, (σ i p.1, σ i p.2) ∈ Seed.rectangle H ρ (Seed.seedPoint a (J i)) := by
  simp only [rectBox, mem_product, hbox, Seed.rectangle, Set.mem_ofPred_eq]
  aesop

private theorem seed_insert (j : Fin m) (J : Finset (Fin m)) (hj : j ∉ J) :
    Seed.seedPoint a J + Seed.parabola (a j) = Seed.seedPoint a (insert j J) := by
  ext <;> simp [Seed.seedPoint, Seed.parabola, hj, add_comm]

/-- Claim on the returning points for each a ∈ 𝒜. The two lower bounds
apply to boxes with half-widths H/2 and ρ^(3/2)/2, respectively. -/
theorem card_return_lower (σ : ι → K →+* ℝ)
    (hbox : ∀ c r x, x ∈ box c r ↔ IsIntegral ℤ x ∧ ∀ i, |σ i x - c i| ≤ r)
    (hdis : ∀ J J' : Finset (Fin m), J ≠ J' →
      Disjoint (Seed.rectangle H ρ (Seed.seedPoint a J))
        (Seed.rectangle H ρ (Seed.seedPoint a J')))
    (hshift : ∀ j x, |x-ρ*a j| ≤ H → |x^2-ρ^2*(a j : ℝ)^2| ≤ ρ^(3/2 : ℝ))
    {u v : ℝ} (hv0 : 0 ≤ v)
    (hu : ∀ c, u ≤ ((box c (H/2)).card : ℝ))
    (hv : ∀ c, v ≤ ((box c (ρ^(3/2 : ℝ)/2)).card : ℝ))
    {x : K} (hx : x ∈ ATotal box a H ρ) :
    ((2:ℝ)^(m-1))^Fintype.card ι * (u*v) ≤
      (((BTotal box a H ρ).filter fun z => parabolicSum (x,z) ∈ BTotal box a H ρ).card : ℝ) := by
  obtain ⟨j,_,hxj⟩ := mem_biUnion.mp hx
  have hxi := ((hbox _ _ x).mp hxj).1
  have hloc (i : ι) : |σ i x-ρ*a (j i)| ≤ H := ((hbox _ _ x).mp hxj).2 i
  let S := Fintype.piFinset fun i => (univ.erase (j i)).powerset
  choose center hc using fun (J : ι → Finset (Fin m)) (i : ι) =>
    Seed.returning_rectangle (Seed.seedPoint a (J i)) (a (j i)) H ρ
      (σ i x) (hloc i) (hshift _ _ (hloc i))
  let innerBox (J : ι → Finset (Fin m)) : Finset (K × K) :=
    box (fun i => (center J i).1) (H/2) ×ˢ
    box (fun i => (center J i).2) (ρ^(3/2 : ℝ)/2)
  have hmember {J : ι → Finset (Fin m)} {z : K × K} (hz : z ∈ innerBox J) (i : ι) :
      (σ i z.1, σ i z.2) ∈ Seed.rectangle H ρ (Seed.seedPoint a (J i)) ∧
      (σ i z.1 + σ i x, σ i z.2 + (σ i x)^2) ∈
        Seed.rectangle H ρ (Seed.seedPoint a (J i) + Seed.parabola (a (j i))) := by
    apply hc J i (σ i z.1, σ i z.2)
    · exact ((hbox _ _ _).mp (mem_product.mp hz).1).2 i
    · exact ((hbox _ _ _).mp (mem_product.mp hz).2).2 i
  have hsub : S.biUnion innerBox ⊆
      (BTotal box a H ρ).filter fun z => parabolicSum (x,z) ∈ BTotal box a H ρ := by
    intro z hz
    obtain ⟨J,hJ,hz⟩ := mem_biUnion.mp hz
    have hz₁ := ((hbox _ _ _).mp (mem_product.mp hz).1).1
    have hz₂ := ((hbox _ _ _).mp (mem_product.mp hz).2).1
    apply mem_filter.mpr
    constructor
    · apply mem_biUnion.mpr
      exact ⟨J,mem_univ _, (mem_rectBox box a H ρ σ hbox J z).mpr
        ⟨hz₁,hz₂,fun i => (hmember hz i).1⟩⟩
    · apply mem_biUnion.mpr
      let J' (i : ι) := insert (j i) (J i)
      refine ⟨J',mem_univ _, (mem_rectBox box a H ρ σ hbox J' _).mpr
        ⟨hxi.add hz₁,(hxi.pow 2).add hz₂,?_⟩⟩
      intro i
      have hj' : j i ∉ J i := fun e =>
        (Finset.mem_erase.mp ((Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hJ i)) e)).1 rfl
      have h := (hmember hz i).2
      rw [seed_insert a _ _ hj'] at h
      simpa only [J', parabolicSum, map_pow, map_add, add_comm] using h
  have hpd : (↑S : Set _).PairwiseDisjoint innerBox := by
    intro J _ J' _ hj
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hj
    exact Finset.disjoint_left.mpr fun z h₁ h₂ =>
      (Set.disjoint_left.mp (hdis _ _ hi)) (hmember h₁ i).1 (hmember h₂ i).1
  calc
    _ = ∑ _J ∈ S, u*v := by
      have hs : S.card = (2^(m-1))^Fintype.card ι := by
        simp [S, Fintype.card_piFinset, Finset.card_erase_of_mem, Finset.card_powerset]
      simp [hs,nsmul_eq_mul]
    _ ≤ ∑ J ∈ S, ((innerBox J).card : ℝ) := by
      refine sum_le_sum fun J _ => ?_
      simp only [innerBox, card_product, Nat.cast_mul]
      exact mul_le_mul (hu _) (hv _) hv0 (Nat.cast_nonneg _)
    _ = ((S.biUnion innerBox).card : ℝ) := by rw [card_biUnion hpd, Nat.cast_sum]
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

end MT.Intersections
