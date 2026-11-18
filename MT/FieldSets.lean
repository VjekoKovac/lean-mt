module

public import MT.FieldGain
public import MT.FieldLines
public import MT.Intersections

/-! # Geometry of the two actual field sets
This module applies the counting of field lines to the finite unions of §4.3
and puts every conjugate of every input coordinate under one scale. Both the
dilation and this scale are chosen independently of the number-field degree.
-/

@[expose] public section
noncomputable section
namespace MT.Intersections
open Finset NumberField NumberField.InfinitePlace
open scoped NumberField Classical

def projectionSize (m : ℕ) (H ρ : ℝ) : ℝ :=
  max 1 (max (ρ*(2:ℝ)^(3*m)+H)
    (max (ρ*Seed.coordinateBound m+H) (ρ^2*Seed.coordinateBound m+ρ^(3/2 : ℝ))))

theorem projectionSize_ge_one (m : ℕ) (H ρ : ℝ) : 1 ≤ projectionSize m H ρ := le_max_left .. 

private theorem abs_of_close {x c W : ℝ} (hx : |x-c| ≤ W) : |x| ≤ |c| + W := calc
  _ = |c+(x-c)| := by rw [show c+(x-c)=x by ring]
  _ ≤ |c|+|x-c| := abs_add_le .. 
  _ ≤ _ := by linarith

variable {K : Type*} [Field K] [NumberField K] [IsTotallyReal K] {m : ℕ}

def placeEmbedding (w : InfinitePlace K) : K →+* ℝ := embedding_of_isReal (IsTotallyReal.isReal w)

theorem field_sets_geometry (box : (InfinitePlace K → ℝ) → ℝ → Finset K)
    (a : Fin m → ℤ) (H ρ : ℝ) (hρ : 0 ≤ ρ) (N : ℕ)
    (ha : ∀ i, 1 ≤ a i ∧ a i ≤ (2:ℤ)^(3*m))
    (hbox : ∀ c r x, x ∈ box c r ↔ IsIntegral ℤ x ∧ ∀ i, |placeEmbedding i x-c i| ≤ r)
    (hN : ∀ c, (box c H).card ≤ N)
    (hlines : ∀ u v : ℝ, (Seed.meetingLine (Seed.seedPoint a) H ρ u (-1) v).card ≤ 2) :
    let M := projectionSize m H ρ
    let A := ATotal box a H ρ
    let B := BTotal box a H ρ
    (∀ x ∈ A, Arithmetic.boundedInteger M x) ∧
    (∀ p ∈ B, Arithmetic.boundedInteger M p.1 ∧ Arithmetic.boundedInteger M p.2) ∧
    ∀ u z : K, (B.filter fun p => p.2 = u*p.1+z).card ≤ 2^Fintype.card (InfinitePlace K)*N := by
  let B := BTotal box a H ρ
  let M := projectionSize m H ρ
  have hnorm (w : InfinitePlace K) (x : K) : |placeEmbedding w x| = w x := norm_embedding_of_isReal _ _
  have hz (J : Finset (Fin m)) :
      |((Seed.seedPoint a J).1 : ℝ)| ≤ Seed.coordinateBound m ∧
      |((Seed.seedPoint a J).2 : ℝ)| ≤ Seed.coordinateBound m := by
    simpa [Seed.close, Seed.toPlane] using Seed.seedPoint_bounded ha J
  have hg : ρ*(2:ℝ)^(3*m)+H ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hh : ρ*Seed.coordinateBound m+H ≤ M :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hv : ρ^2*Seed.coordinateBound m+ρ^(3/2 : ℝ) ≤ M :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have htag {p : K × K} (hp : p ∈ B) :
      IsIntegral ℤ p.1 ∧ IsIntegral ℤ p.2 ∧
      ∃ J : InfinitePlace K → Finset (Fin m), ∀ i,
        (placeEmbedding i p.1,placeEmbedding i p.2) ∈ Seed.rectangle H ρ (Seed.seedPoint a (J i)) := by
    obtain ⟨J,_,hJ⟩ := mem_biUnion.mp hp
    obtain ⟨hx,hy⟩ := mem_product.mp hJ
    obtain ⟨ix,bx⟩ := (hbox _ _ _).mp hx
    obtain ⟨iy,by'⟩ := (hbox _ _ _).mp hy
    exact ⟨ix,iy,J, fun i => ⟨bx i,by' i⟩⟩
  refine ⟨?_,?_,?_⟩
  · intro x hx
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hx
    obtain ⟨ix,bx⟩ := (hbox _ _ _).mp hj
    refine ⟨ix, fun w => ?_⟩
    have h := abs_of_close (bx w)
    rw [← hnorm]
    have hapos : (0:ℝ) ≤ a (j w) := by
      exact_mod_cast (show (0:ℤ) ≤ a (j w) by linarith [(ha (j w)).1])
    have hlim : (a (j w) : ℝ) ≤ (2:ℝ)^(3*m) := by exact_mod_cast (ha (j w)).2
    rw [abs_mul, abs_of_nonneg hρ, abs_of_nonneg hapos] at h
    exact h.trans ((add_le_add_left (mul_le_mul_of_nonneg_left hlim hρ) H).trans hg)
  · intro p hp
    obtain ⟨ix, iy, J, hJ⟩ := htag hp
    refine ⟨⟨ix, fun w => ?_⟩, ⟨iy, fun w => ?_⟩⟩
    · rw [← hnorm]
      have h := abs_of_close (hJ w).1
      rw [abs_mul, abs_of_nonneg hρ] at h
      exact h.trans ((add_le_add_left (mul_le_mul_of_nonneg_left (hz _).1 hρ) H).trans hh)
    · rw [← hnorm]
      have h := abs_of_close (hJ w).2
      rw [abs_mul, abs_of_nonneg (sq_nonneg ρ)] at h
      exact h.trans ((add_le_add_left (mul_le_mul_of_nonneg_left (hz _).2 (sq_nonneg ρ)) _).trans hv)
  · intro u v
    apply Seed.field_line_count placeEmbedding (Seed.seedPoint a) H ρ B
      (fun J => box (fun i => ρ*(Seed.seedPoint a (J i)).1) H) N
    · intro p hp i
      obtain ⟨_,_,J,hJ⟩ := htag hp
      exact ⟨J i,hJ i⟩
    · intro p hp J b
      exact (hbox _ _ _).mpr ⟨(htag hp).1, b⟩
    · exact fun J => hN _
    · exact hlines

end MT.Intersections
