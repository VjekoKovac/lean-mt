module

public import MT.ChartPhase
public import MT.SurfacePackets
public import Mathlib.Analysis.Normed.Affine.MazurUlam

/-! Straightening a curved chart and the corresponding Fourier adjoint. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace Topology

namespace MT

/-- Split off the height coordinate. The Euclidean product and the usual
product norm are linearly homeomorphic in finite dimensions. -/
def splitHeight (d : ℕ) : Space (d+1) ≃ₗ[ℝ] Space d × ℝ where
  toFun z := (WithLp.toLp 2 (fun i => z i.castSucc), z (Fin.last d))
  invFun p := WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => p.1 i) p.2)
  left_inv z := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by
    apply Prod.ext
    · ext i
      simp
    · simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Horizontal rotation, subtraction of the tangent plane, and division
by the nonzero signed quadratic coefficient. -/
def tangentShear {d : ℕ} (E : Space d ≃ₗᵢ[ℝ] Space d)
    (ℓ : Space d →L[ℝ] ℝ) (q : ℝ) (hq : q ≠ 0) :
    (Space d × ℝ) ≃ₗ[ℝ] (Space d × ℝ) where
  toFun p := (E.symm p.1, (p.2 - ℓ p.1)/q)
  invFun p := (E p.1, q*p.2 + ℓ (E p.1))
  left_inv p := by
    apply Prod.ext <;> simp
    field_simp
    ring
  right_inv p := by
    apply Prod.ext <;> simp [hq]
  map_add' p p' := by
    apply Prod.ext <;> simp
    ring
  map_smul' a p := by
    apply Prod.ext <;> simp
    ring

def GraphChart.frequencyCoordinates {d : ℕ} (g : GraphChart d) (u : Space d)
    (E : Space d ≃ₗᵢ[ℝ] Space d) (j : Fin d)
    (hq : curvatureCoefficient g u E j ≠ 0) : Space (d+1) ≃L[ℝ] Space (d+1) :=
  (((g.rigid.symm.toRealLinearIsometryEquiv.toLinearEquiv.trans (splitHeight d)).trans
    (tangentShear E (fderiv ℝ g.height u) (curvatureCoefficient g u E j) hq)).trans
    (splitHeight d).symm).toContinuousLinearEquiv

/-- Translation by the negative image of the base point yields exactly
the graph of the normalized height. All translations cancel in the
frequency differences of paired packets. -/
theorem GraphChart.frequencyCoordinates_point {d : ℕ} (g : GraphChart d) (u : Space d)
    (E : Space d ≃ₗᵢ[ℝ] Space d) (j : Fin d) (hq : curvatureCoefficient g u E j ≠ 0)
    (ξ : Fin d → ℝ) :
    let L := g.frequencyCoordinates u E j hq
    L (g.point (u + E (WithLp.toLp 2 ξ))) - L (g.point u) =
      WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) ξ (normalizedHeight g u E j ξ)) := by
  let x := E (WithLp.toLp 2 ξ)
  let M := g.rigid.symm.toRealLinearIsometryEquiv
  let D := tangentShear E (fderiv ℝ g.height u) (curvatureCoefficient g u E j) hq
  let F := splitHeight d
  change F.symm (D (F (M (g.point (u + x))))) - F.symm (D (F (M (g.point u)))) = _
  rw [← map_sub, ← map_sub, ← map_sub]
  simp only [M, IsometryEquiv.toRealLinearIsometryEquiv_apply, GraphChart.point,
    IsometryEquiv.symm_apply_apply, sub_sub_sub_cancel_right]
  have hi : ∀ v : Space d, F (WithLp.toLp 2
      (Fin.snoc (α := fun _ => ℝ) (fun i => v i) (g.height v))) = (v, g.height v) := by
    intro v
    exact F.apply_symm_apply (v, g.height v)
  rw [map_sub, hi, hi]
  suffices D ((u+x, g.height (u+x))-(u,g.height u)) =
      (WithLp.toLp 2 ξ, normalizedHeight g u E j ξ) from congrArg F.symm this
  change (E.symm (u+x-u), (g.height (u+x)-g.height u - fderiv ℝ g.height u (u+x-u)) /
    curvatureCoefficient g u E j) = (WithLp.toLp 2 ξ, normalizedHeight g u E j ξ)
  simp [x, normalizedHeight]

/-- The base-coordinate isometry locates each parameter cube at its
corresponding cap in the original chart. -/
def chartOriented {d : ℕ} (u : Space d) (E : Space d ≃ₗᵢ[ℝ] Space d) : Space d ≃ᵢ Space d :=
  E.toIsometryEquiv.trans (IsometryEquiv.addLeft u)

@[simp] theorem chartOriented_apply {d : ℕ} (u : Space d) (E : Space d ≃ₗᵢ[ℝ] Space d)
    (x : Space d) : chartOriented u E x = u + E x := rfl

/-- After the shift by an arithmetic frequency, differences of graph
frequencies are exactly the scaled phases controlled by Taylor's theorem. -/
theorem GraphChart.shifted_phase {d : ℕ} (g : GraphChart d) (u : Space d)
    (E : Space d ≃ₗᵢ[ℝ] Space d) (j : Fin d) (hq : curvatureCoefficient g u E j ≠ 0)
    (h Y T : ℝ) (p q : ℝ × ℝ × ℝ) (ξ ξ' : Fin d → ℝ) (i : Fin (d+1)) :
    let L := g.frequencyCoordinates u E j hq
    let z := fun v : Fin d → ℝ => L (g.point (chartOriented u E (WithLp.toLp 2 v)))
    (if i = Fin.last d then T else Y) *
      (shiftedFrequency j.castSucc (Fin.last d) h p.2 (z ξ) i -
       shiftedFrequency j.castSucc (Fin.last d) h q.2 (z ξ') i) =
      boxPhases j (normalizedHeight g u E j) Y T h p q ξ ξ' i := by
  let L := g.frequencyCoordinates u E j hq
  let z := fun v : Fin d → ℝ => L (g.point (chartOriented u E (WithLp.toLp 2 v)))
  have hh (v : Fin d → ℝ) : z v i - L (g.point u) i =
      Fin.snoc (α := fun _ => ℝ) v (normalizedHeight g u E j v) i :=
    congrArg (fun y : Space (d+1) => y i) (g.frequencyCoordinates_point u E j hq v)
  have hd : z ξ i - z ξ' i = Fin.snoc (α := fun _ => ℝ) ξ (normalizedHeight g u E j ξ) i -
      Fin.snoc (α := fun _ => ℝ) ξ' (normalizedHeight g u E j ξ') i := by linarith [hh ξ, hh ξ']
  change (if i = Fin.last d then T else Y) * (shiftedFrequency _ _ _ _ (z ξ) i -
    shiftedFrequency _ _ _ _ (z ξ') i) = _
  simp only [shiftedFrequency]
  rw [show z ξ i + (if i = j.castSucc then h * p.2.1 else 0) +
      (if i = Fin.last d then h^2 * p.2.2 else 0) -
      (z ξ' i + (if i = j.castSucc then h * q.2.1 else 0) +
      (if i = Fin.last d then h^2 * q.2.2 else 0)) =
      (z ξ i-z ξ' i) + (if i = j.castSucc then h*(p.2.1-q.2.1) else 0) +
      (if i = Fin.last d then h^2*(p.2.2-q.2.2) else 0) by
    split <;> split <;> ring, hd]
  clear hd hh
  induction i using Fin.lastCases with
  | last => simp [boxPhases, (Fin.castSucc_ne_last j).symm]
  | cast k => simp [boxPhases]

/-- Cancellation of the normalized cap amplitude against two patch
volumes and the anisotropic Fourier kernel. -/
private theorem packet_prefactor (d : ℕ) {ε : ℝ} (hε : 0 < ε) (Y T en : ℝ) :
    (ε ^ (-(d:ℝ)/2))^2 * (en * ((∏ i : Fin (d+1),
      (if i = Fin.last d then T else Y)/4) * ((2*ε)^d)^2)) =
      ((Y*ε)^d/4)*T*en := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_ne_last, ite_false, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ite_true]
  calc
    _ = ((ε ^ (-(d:ℝ)/2))^2 * (2*ε)^d) * ((Y/4)^d * (2*ε)^d) * (T/4) * en := by ring
    _ = _ := by
      rw [amplitude_cancel d hε, ← mul_pow, ← mul_pow,
        show 2 * (Y/4 * (2*ε)) = Y*ε by ring]
      ring

/-- Lemma 3.4 for graph caps in the general chart. All quantities on
the right are the actual test function, surface area, and physical weight. -/
theorem graph_cap_weightedMass_lower {d : ℕ} (g : GraphChart d) (u : Space d)
    (E : Space d ≃ₗᵢ[ℝ] Space d) (j : Fin d) (hq : curvatureCoefficient g u E j ≠ 0)
    (S : Set (Space (d+1))) (A : Finset ℝ) (B : Finset (ℝ × ℝ)) (h ε Y T : ℝ)
    (hε : 0 < ε) (hY : 0 < Y) (hT : 0 < T)
    (hpatch : ∀ a ∈ A, let W := surfaceCap g (chartOriented u E) j h ε a
      MeasurableSet W ∧ (surfaceMeasure S) W ≠ ⊤ ∧ (ENNReal.ofReal (2*ε))^d ≤ (surfaceMeasure S) W)
    (hphase : ∀ p ∈ A ×ˢ B, ∀ q ∈ A ×ˢ B, parabolicSum p = parabolicSum q →
      ∀ ξ ∈ parameterCube j h ε p.1, ∀ ξ' ∈ parameterCube j h ε q.1,
      ∀ i, |boxPhases j (normalizedHeight g u E j) Y T h p q ξ ξ' i| ≤ 1/3) :
    let L := g.frequencyCoordinates u E j hq
    let W := surfaceCap g (chartOriented u E) j h ε
    let f := capTest A W (ε ^ (-(d:ℝ)/2))
    ENNReal.ofReal (((Y*ε)^d/4)*T*(energy A B:ℝ)) ≤
      weightedMass (fun x => extension S f (L.toContinuousLinearMap.adjoint x))
        (counterWeight B j.castSucc (Fin.last d) h Y T) := by
  let W := surfaceCap g (chartOriented u E) j h ε
  let L := g.frequencyCoordinates u E j hq
  let amp := ε ^ (-(d:ℝ)/2)
  rw [← packet_prefactor d hε]
  apply cap_weightedMass_lower_linear S A L.toContinuousLinearMap B j.castSucc (Fin.last d)
    h amp Y T ((2*ε)^d) hY hT (by positivity) W (fun a ha => (hpatch a ha).1)
    (fun a ha => (hpatch a ha).2.1)
  · intro a ha
    have hv := ENNReal.toReal_mono (hpatch a ha).2.1 (hpatch a ha).2.2
    simpa only [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*ε),
      measureReal_def] using hv
  · intro p hp q hq' he z hz z' hz' i
    obtain ⟨_, ⟨_, ⟨ξ,hξ,rfl⟩,rfl⟩,rfl⟩ := hz
    obtain ⟨_, ⟨_, ⟨ξ',hξ',rfl⟩,rfl⟩,rfl⟩ := hz'
    exact (g.shifted_phase u E j hq h Y T p q ξ ξ' i).symm ▸ hphase p hp q hq' he ξ hξ ξ' hξ' i

end MT
