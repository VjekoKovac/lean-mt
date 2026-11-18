module

public import MT.Seed
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.Data.Int.Interval

/-!
# A generic bounded integer seed

The proof uses the product of all triple determinants on the grid
`{1, …, 2^(3m)}^m`. To show that a determinant polynomial is nonzero,
evaluate on two coordinates only. This picks out the nonzero Boolean minor
from the paper, with a nonzero scalar factor.
-/

@[expose] public section
namespace MT.Seed

open Finset MvPolynomial

variable {m : ℕ}

def seedPoint {R : Type*} [CommRing R] (a : Fin m → R) (s : Finset (Fin m)) : R × R :=
  (∑ i ∈ s, a i, ∑ i ∈ s, (a i)^2)

/-- The determinant with last row equal to `(1,1,1)`. -/
def determinant {R : Type*} [CommRing R] (p q r : R × R) : R :=
  (p.1-r.1)*(q.2-r.2) - (q.1-r.1)*(p.2-r.2)

def tripleDet {R : Type*} [CommRing R] (a : Fin m → R) (s t u : Finset (Fin m)) : R :=
  determinant (seedPoint a s) (seedPoint a t) (seedPoint a u)

private noncomputable def detPoly (s t u : Finset (Fin m)) : MvPolynomial (Fin m) ℤ :=
  tripleDet X s t u

private theorem eval_detPoly (a : Fin m → ℤ) (s t u : Finset (Fin m)) :
    eval a (detPoly s t u) = tripleDet a s t u := by
  simp [detPoly, tripleDet, determinant, seedPoint, map_sum]

private theorem degree_detPoly (s t u : Finset (Fin m)) :
    (detPoly s t u).totalDegree ≤ 3 := by
  let f := fun s : Finset (Fin m) => seedPoint (X (R := ℤ)) s
  have h₁ (s : Finset (Fin m)) : (f s).1.totalDegree ≤ 1 :=
    totalDegree_finsetSum_le (by simp)
  have h₂ (s : Finset (Fin m)) : (f s).2.totalDegree ≤ 2 :=
    totalDegree_finsetSum_le (by simp)
  have hp (s t u : Finset (Fin m)) :
      (((f s).1 - (f u).1) * ((f t).2 - (f u).2)).totalDegree ≤ 3 := by
    exact (totalDegree_mul ..).trans (add_le_add
      ((totalDegree_sub ..).trans (max_le (h₁ s) (h₁ u)))
      ((totalDegree_sub ..).trans (max_le (h₂ t) (h₂ u))))
  exact (totalDegree_sub ..).trans (max_le (hp s t u) (hp t s u))

private def incidence (s : Finset (Fin m)) (i : Fin m) : Bool := decide (i ∈ s)

private theorem incidence_injective :
    Function.Injective (incidence (m := m)) := by
  intro s t h
  ext i
  simpa [incidence] using congrFun h i

private theorem detPoly_ne_zero {s t u : Finset (Fin m)}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) : detPoly s t u ≠ 0 := by
  obtain ⟨i, j, hij, hminor⟩ := exists_nonzero_minor
    (incidence_injective.ne hst) (incidence_injective.ne hsu) (incidence_injective.ne htu)
  let a (l : Fin m) : ℤ := (if l = i then 1 else 0) + (if l = j then 2 else 0)
  have ha (l : Fin m) : (a l)^2 = (if l=i then 1 else 0) + (if l=j then 4 else 0) := by
    by_cases h : l = i <;> by_cases h' : l = j <;> simp_all [a]
  have hx (s : Finset (Fin m)) :
      (seedPoint a s).1 = bit (incidence s i) + 2 * bit (incidence s j) := by
    simp [seedPoint, a, sum_add_distrib, incidence, bit, mul_ite]
  have hy (s : Finset (Fin m)) :
      (seedPoint a s).2 = bit (incidence s i) + 4 * bit (incidence s j) := by
    simp [seedPoint, ha, sum_add_distrib, incidence, bit, mul_ite]
  intro hz
  have he : tripleDet a s t u = 0 := by rw [← eval_detPoly, hz, map_zero]
  simp only [tripleDet, determinant, hx, hy] at he
  apply hminor
  unfold bitMinor
  linarith only [he]

private theorem nonzero_reorder {α : Type*} [DecidableEq α] {R : Type*} [CommRing R]
    (f : α → R × R) {a b c x y z : α} (h : determinant (f a) (f b) (f c) ≠ 0)
    (hx : x ∈ ({a,b,c} : Finset α)) (hy : y ∈ ({a,b,c} : Finset α))
    (hz : z ∈ ({a,b,c} : Finset α)) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    determinant (f x) (f y) (f z) ≠ 0 := by
  simp only [mem_insert, mem_singleton] at hx hy hz
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;> try contradiction
  all_goals
    intro he
    apply h
    unfold determinant at *
    first | linear_combination he | linear_combination -he

private theorem degree_budget (m : ℕ) :
    ((2^m).choose 3) * 3 < 2^(3*m) := by
  have h := Nat.descFactorial_le_pow (2^m) 3
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  norm_num [Nat.factorial] at h
  rw [mul_comm 3 m, pow_mul]
  have : 0 < (2 ^ m : ℕ) ^ 3 := by positivity
  omega

/-- Paper's bounded integer seed (Lemma `lemma:seednoncollinearity`).
All distinct triples of subset sums have nonzero affine determinant. -/
theorem exists_bounded_seed (m : ℕ) (hm : 2 ≤ m) :
    ∃ a : Fin m → ℤ, (∀ i, 1 ≤ a i ∧ a i ≤ (2:ℤ)^(3*m)) ∧
      Function.Injective a ∧ Function.Injective (seedPoint a) ∧
      ∀ s t u : Finset (Fin m), s ≠ t → s ≠ u → t ≠ u → tripleDet a s t u ≠ 0 := by
  classical
  let T := {S : Finset (Finset (Fin m)) // S.card = 3}
  have decomp (S : T) := Finset.card_eq_three.mp S.property
  choose x y z hxy hxz hyz hset using decomp
  let G := ∏ S : T, detPoly (x S) (y S) (z S)
  have hG : G ≠ 0 := Finset.prod_ne_zero_iff.mpr
    fun S _ => detPoly_ne_zero (hxy S) (hxz S) (hyz S)
  have hdeg : G.totalDegree < 2^(3*m) := calc
    _ ≤ ∑ S : T, (detPoly (x S) (y S) (z S)).totalDegree := totalDegree_finsetProd .. 
    _ ≤ ∑ _S : T, 3 := sum_le_sum fun S _ => degree_detPoly (x S) (y S) (z S)
    _ = ((2^m).choose 3)*3 := by simp [T, Fintype.card_finset_len, Fintype.card_finset]
    _ < _ := degree_budget m
  let grid := Finset.Icc (1:ℤ) (2^(3*m))
  have hgrid : grid.card = 2^(3*m) := by
    simp [grid, Int.card_Icc]
    exact_mod_cast Int.toNat_natCast (2^(3*m))
  obtain ⟨a, ha, hval⟩ : ∃ a : Fin m → ℤ, (∀ i, a i ∈ grid) ∧ eval a G ≠ 0 := by
    by_contra! hall
    exact hG (eq_zero_of_eval_zero_at_prod_finset G (fun _ => grid)
      (fun i => (degreeOf_le_totalDegree G i).trans_lt (hgrid ▸ hdeg)) hall)
  have hd (S : T) : tripleDet a (x S) (y S) (z S) ≠ 0 := by
    change eval a (∏ S : T, detPoly (x S) (y S) (z S)) ≠ 0 at hval
    rw [map_prod] at hval
    rw [← eval_detPoly]
    exact Finset.prod_ne_zero_iff.mp hval S (mem_univ S)
  have htriple (s t u : Finset (Fin m)) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
      tripleDet a s t u ≠ 0 := by
    let S : T := ⟨{s,t,u}, by simp [hst, hsu, htu]⟩
    have he : ({s,t,u} : Finset _) = {x S, y S, z S} := hset S
    exact nonzero_reorder (seedPoint a) (hd S)
      (he ▸ by simp) (he ▸ by simp) (he ▸ by simp) hst hsu htu
  have hinj : Function.Injective (seedPoint a) := by
    intro s t heq
    by_contra hst
    obtain ⟨u, hus, hut⟩ : ∃ u : Finset (Fin m), u ≠ s ∧ u ≠ t := by
      by_contra! h
      have hsub : (univ : Finset (Finset (Fin m))) ⊆ {s,t} := by
        intro u _
        by_cases hs : u = s
        · simp [hs]
        · simp [h u hs]
      have hcard := card_le_card hsub
      simp [Fintype.card_finset, hst] at hcard
      have hh : (2:ℕ)^2 ≤ 2^m := Nat.pow_le_pow_right (by decide) hm
      omega
    apply htriple s t u hst hus.symm hut.symm
    simp [tripleDet, heq, determinant]
  refine ⟨a, fun i => Finset.mem_Icc.mp (ha i), ?_, hinj, htriple⟩
  intro i j heq
  have h : ({i} : Finset (Fin m)) = {j} := hinj (by simp [seedPoint, heq])
  simpa using h

/-- The polynomial lemma discharges the injectivity hypothesis of the counting theorem.
This yields actual integer parabolic configurations for every `m ≥ 2`. -/
theorem exists_seed_energy (m : ℕ) (hm : 2 ≤ m) :
    ∃ a : Fin m → ℤ, (∀ i, 1 ≤ a i ∧ a i ≤ (2:ℤ)^(3*m)) ∧
      (generators (parabola ∘ a)).card = m ∧ (points (parabola ∘ a)).card = 2^m ∧
      m^2 * 2^m ≤ 4 * (generators (parabola ∘ a)).addEnergy (points (parabola ∘ a)) ∧
      ∀ s t u : Finset (Fin m), s ≠ t → s ≠ u → t ≠ u → tripleDet a s t u ≠ 0 := by
  obtain ⟨a, ha, _, hseed, htriple⟩ := exists_bounded_seed m hm
  have heq (s : Finset (Fin m)) : point (parabola ∘ a) s = seedPoint a s := by
    ext <;> simp [point, parabola, seedPoint, Prod.fst_sum, Prod.snd_sum]
  have hv : Function.Injective (point (parabola ∘ a)) := by
    intro s t h
    exact hseed (by simpa only [heq] using h)
  refine ⟨a, ha, card_generators hv, card_points hv, ?_, htriple⟩
  simpa [card_points hv] using four_energy hv

end MT.Seed
