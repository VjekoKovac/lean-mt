module

public import MT.FieldBox
public import MT.IntersectionBounds
public import MT.Intersections

/-! # Cardinality and return estimates over a totally real number field
Combine the translated-box bounds with the disjoint labeled products of
Section 4.3. The normalized constants are independent of the dilation and m.
-/

@[expose] public section
noncomputable section
namespace MT.Intersections
open NumberField NumberField.InfinitePlace Finset
open scoped NumberField Classical

/-- Sizes and return proportion of the actual intersections with 𝒪_K and 𝒪_K². -/
theorem field_intersection_estimates (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    {m : ℕ} (a : Fin m → ℤ) (H ρ D : ℝ) (hm : 0 < m) (hD : 1 ≤ D)
    (hH : 1 ≤ H) (hDH : D ≤ H) (hV : H ≤ ρ^(3/2 : ℝ))
    (hlarge : 48*BoxCutoff.constant*D ≤ H/2)
    (hdisc : ((discr K).natAbs : ℝ) ≤ D^Module.finrank ℚ K)
    (hdisA : ∀ j j', j ≠ j' →
      Disjoint {x : ℝ | |x-ρ*a j| ≤ H} {x : ℝ | |x-ρ*a j'| ≤ H})
    (hdisB : ∀ J J' : Finset (Fin m), J ≠ J' →
      Disjoint (Seed.rectangle H ρ (Seed.seedPoint a J))
        (Seed.rectangle H ρ (Seed.seedPoint a J')))
    (hshift : ∀ j x, |x-ρ*a j| ≤ H → |x^2-ρ^2*(a j : ℝ)^2| ≤ ρ^(3/2 : ℝ)) :
    let A := ATotal (Arithmetic.fieldBox K) a H ρ
    let B := BTotal (Arithmetic.fieldBox K) a H ρ
    let k := Module.finrank ℚ K
    A.Nonempty ∧ B.Nonempty ∧ ((m:ℝ)/2)^k ≤ A.card ∧ ∀ x ∈ A,
      (B.card : ℝ) ≤ (512*D)^k*((B.filter fun z => parabolicSum (x,z) ∈ B).card : ℝ) := by
  let k := Module.finrank ℚ K
  let V := ρ^(3/2 : ℝ)
  let s := Real.sqrt ((discr K).natAbs : ℝ)
  let box := Arithmetic.fieldBox K
  let σ (i : InfinitePlace K) := embedding_of_isReal (IsTotallyReal.isReal i)
  let A := ATotal box a H ρ
  let B := BTotal box a H ρ
  change A.Nonempty ∧ B.Nonempty ∧ _ ∧ _
  have hk : 0 < k := Module.finrank_pos
  have hdpos : (0 : ℝ) < (discr K).natAbs := by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)
  have hs : 0 < s := Real.sqrt_pos.mpr hdpos
  have hsD : s^2 ≤ D^k := by
    rw [show s^2=((discr K).natAbs : ℝ) from Real.sq_sqrt hdpos.le]
    exact hdisc
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hV0 : 0 < V := hH0.trans_le hV
  have hposD := zero_lt_one.trans_le hD
  have hbox := Arithmetic.mem_fieldBox K
  have hcard : Fintype.card (InfinitePlace K) = k := Arithmetic.card_places_eq_degree K
  have hlower (r : ℝ) (hr : 48*BoxCutoff.constant*D ≤ r) (c : InfinitePlace K → ℝ) :
      r^k/(2*s) ≤ ((box c r).card : ℝ) :=
    Arithmetic.fieldBox_lower K c hposD hdisc hr
  have hupper (r : ℝ) (hr : 1 ≤ r) (c : InfinitePlace K → ℝ) :
      ((box c r).card : ℝ) ≤ (4*r)^k :=
    (Arithmetic.fieldBox_upper K c (zero_lt_one.trans_le hr)).trans (upper_base hk hr)
  have ha := card_A_lower box a H ρ σ hbox hdisA (H^k/(2*s)) (hlower H (by linarith))
  rw [hcard] at ha
  have ha' : ((m:ℝ)/2)^k ≤ (A.card : ℝ) := lower_A_base hk hH hposD.le hDH hs hsD ha
  have hane : A.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast ((by positivity : 0 < ((m:ℝ)/2)^k).trans_le ha'))
  have hb : (B.card : ℝ) ≤ ((2:ℝ)^m)^k*((4*H)^k*(4*V)^k) := by
    simpa only [hcard] using card_B_upper box a H ρ
      (by positivity : 0 ≤ (4*H)^k) (hupper H hH) (hupper V (hH.trans hV))
  have hret (x : K) (hx : x ∈ A) :
      ((2:ℝ)^(m-1))^k*(((H/2)^k/(2*s))*((V/2)^k/(2*s))) ≤
        ((B.filter fun z => parabolicSum (x,z) ∈ B).card : ℝ) := by
    simpa only [hcard] using card_return_lower box a H ρ σ hbox hdisB hshift
      (by positivity : 0 ≤ (V/2)^k/(2*s))
      (hlower (H/2) hlarge) (hlower (V/2) (hlarge.trans (by dsimp [V]; linarith))) hx
  have hbne : B.Nonempty := by
    obtain ⟨x,hx⟩ := hane
    have hit := hret x hx
    have hp : (0:ℝ) < ((2:ℝ)^(m-1))^k*(((H/2)^k/(2*s))*((V/2)^k/(2*s))) := by positivity
    exact (Finset.card_pos.mp (by exact_mod_cast hp.trans_le hit)).mono (Finset.filter_subset _ _)
  exact ⟨hane, hbne, ha', fun x hx => return_base hk hm hH0 hV0 hposD hs hsD hb (hret x hx)⟩

end MT.Intersections
