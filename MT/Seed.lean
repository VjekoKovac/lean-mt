module

public import Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Tactic

/-!
# The finite seed

For vectors `v j`, let `A` be their image and `B` the image of the subset-sum map.
In the paper one takes `v j = (a j, a j ^ 2)`. After establishing injectivity of the
subset-sum map, inserting a missing index gives distinct pairs in `A × B` whose
sums land inside `B`. Mathlib already proves the energy estimate needed to turn
this count into the paper's gain: see `Finset.card_sq_le_card_mul_addEnergy`.
-/

@[expose] public section

namespace MT.Seed

open Finset

/-- Coordinatewise integer form of the paper's parabola. -/
def parabola (x : ℤ) : ℤ × ℤ := (x, x ^ 2)

section Counting

variable {G : Type*} [AddCommMonoid G] [DecidableEq G] {m : ℕ}

/-- The sum of the seed vectors with labels in a subset. -/
def point (v : Fin m → G) (J : Finset (Fin m)) : G := ∑ j ∈ J, v j

def generators (v : Fin m → G) : Finset G := univ.image v

def points (v : Fin m → G) : Finset G := univ.image (point v)

omit [DecidableEq G] in
theorem point_insert (v : Fin m → G) {j : Fin m} {J : Finset (Fin m)}
    (hj : j ∉ J) : v j + point v J = point v (insert j J) := by
  simp [point, hj]

omit [DecidableEq G] in
theorem generators_injective {v : Fin m → G} (hv : Function.Injective (point v)) :
    Function.Injective v := by
  intro i j h
  have hs : ({i} : Finset (Fin m)) = {j} := hv (by simpa [point] using h)
  simpa using hs

theorem card_generators {v : Fin m → G} (hv : Function.Injective (point v)) :
    (generators v).card = m := by
  rw [generators, card_image_of_injective _ (generators_injective hv)]
  simp

theorem card_points {v : Fin m → G} (hv : Function.Injective (point v)) :
    (points v).card = 2 ^ m := by
  rw [points, card_image_of_injective _ hv]
  simp [Fintype.card_finset]

/-- Labels `(j, J)` for which inserting `j` produces a known seed translation. -/
def edgeLabels (m : ℕ) : Finset (Σ _j : Fin m, Finset (Fin m)) :=
  univ.sigma fun j => (univ.erase j).powerset

theorem card_edgeLabels (m : ℕ) : (edgeLabels m).card = m * 2 ^ (m - 1) := by
  simp [edgeLabels, card_sigma, card_erase_of_mem, card_powerset]

/-- Lower bound for genuine pairs of points. Other representations may also occur. -/
theorem count_translations {v : Fin m → G} (hv : Function.Injective (point v)) :
    m * 2 ^ (m - 1) ≤
      (((generators v) ×ˢ (points v)).filter fun p => p.1 + p.2 ∈ points v).card := by
  rw [← card_edgeLabels]
  apply card_le_card_of_injOn (fun p => (v p.1, point v p.2))
  · rintro ⟨j, J⟩ he
    have hs : J ⊆ univ.erase j := mem_powerset.mp (mem_sigma.mp he).2
    have hj : j ∉ J := fun h => (mem_erase.mp (hs h)).1 rfl
    refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_image_of_mem _ (mem_univ _),
      mem_image_of_mem _ (mem_univ _)⟩, ?_⟩
    rw [point_insert v hj]
    exact mem_image_of_mem _ (mem_univ _)
  · rintro ⟨i, I⟩ _ ⟨j, J⟩ _ h
    have hij : i = j := generators_injective hv (congrArg Prod.fst h)
    have hIJ : I = J := hv (congrArg Prod.snd h)
    subst j
    subst J
    rfl

/-- The Cauchy–Schwarz step, with additive energy defined by actual quadruples. -/
theorem seed_energy {v : Fin m → G} (hv : Function.Injective (point v)) :
    (m * 2 ^ (m - 1)) ^ 2 ≤
      2 ^ m * (generators v).addEnergy (points v) := by
  rw [← card_points hv]
  exact (Nat.pow_le_pow_left (count_translations hv) 2).trans
    (card_sq_le_card_mul_addEnergy _ _ _)

/-- The seed lower bound without division: `m² |B| ≤ 4 E(A,B)`. -/
theorem four_energy {v : Fin m → G} (hv : Function.Injective (point v)) :
    m ^ 2 * (points v).card ≤ 4 * (generators v).addEnergy (points v) := by
  rw [card_points hv]
  cases m with
  | zero => simp
  | succ n =>
    have h := seed_energy hv
    rw [Nat.succ_sub_one, pow_succ 2 n] at h
    let E := (generators v).addEnergy (points v)
    have hp : 0 < 2 ^ n := by positivity
    have hc : 2 ^ n * ((n+1)^2 * 2^n) ≤ 2^n * (2*E) := by
      convert h using 1 <;> ring
    have h' := Nat.le_of_mul_le_mul_left hc hp
    rw [pow_succ]
    change (n+1)^2 * (2^n * 2) ≤ 4*E
    nlinarith

/-- Choices of absent-index subsets in `k` specified coordinates, as used
when counting the disjoint overlap boxes. -/
theorem card_overlap_labels {k : ℕ} (j : Fin k → Fin m) :
    (Fintype.piFinset fun i => (univ.erase (j i)).powerset).card = (2 ^ (m - 1)) ^ k := by
  simp [Fintype.card_piFinset, card_erase_of_mem, card_powerset]

end Counting

/-- Convert a Boolean incidence entry into an integer. -/
def bit (b : Bool) : ℤ := if b then 1 else 0

/-- The determinant of these two incidence rows and the row of ones. -/
def bitMinor (a b c d e f : Bool) : ℤ :=
  (bit a - bit c) * (bit e - bit f) - (bit b - bit c) * (bit d - bit f)

/-- Three distinct incidence columns admit a nonzero minor with the row of ones.
The finite Boolean identities in the proof use kernel reduction via `decide`. -/
theorem exists_nonzero_minor {ι : Type*} {x y z : ι → Bool}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ i j : ι, i ≠ j ∧ bitMinor (x i) (y i) (z i) (x j) (y j) (z j) ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  by_cases h : x i = z i
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hxz
    refine ⟨i, j, fun e => hj (e ▸ h), ?_⟩
    have ht : ∀ a b c d e f : Bool, a ≠ b → a = c → d ≠ f →
        bitMinor a b c d e f ≠ 0 := by decide
    exact ht _ _ _ _ _ _ hi h hj
  · have h' : y i = z i := by
      have hbool : ∀ a b c : Bool, a ≠ b → a ≠ c → b = c := by decide
      exact hbool _ _ _ hi h
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hyz
    refine ⟨i, j, fun e => hj (e ▸ h'), ?_⟩
    have ht : ∀ a b c d e f : Bool, a ≠ b → b = c → e ≠ f →
        bitMinor a b c d e f ≠ 0 := by decide
    exact ht _ _ _ _ _ _ hi h' hj

end MT.Seed
