module

public import MT.ChartCoordinates
public import MT.TransferRatio
public import MT.PhysicalChange
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Assembly of Proposition 3.1 of arXiv:2611.22465v1. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace MT

/-- The adjoint of the invertible frequency map, as an invertible physical map. -/
def adjointEquiv {n : ℕ} (F : Space n ≃L[ℝ] Space n) : Space n ≃L[ℝ] Space n :=
  ContinuousLinearEquiv.equivOfInverse' F.toContinuousLinearMap.adjoint
    F.symm.toContinuousLinearMap.adjoint
    (by rw [← ContinuousLinearMap.adjoint_comp]; simp [ContinuousLinearMap.adjoint_id])
    (by rw [← ContinuousLinearMap.adjoint_comp]; simp [ContinuousLinearMap.adjoint_id])

/-- This deduction records the constants after choosing a curved surface chart
and a physical coordinate map. The remaining hypothesis is precisely the
weighted mass inequality evaluated at the normalized coordinates. -/
theorem GraphChart.transfer_of_packet {d : ℕ} {β : ℝ} {S : Set (Space (d+1))}
    {g : GraphChart d} (hg : g.ValidFor β S) {u : Space d} (hu : u ∈ g.domain)
    (hur : g.point u ∈ g.region)
    (E : Space d ≃ₗᵢ[ℝ] Space d) (j : Fin d) (hq : curvatureCoefficient g u E j ≠ 0)
    (e : Space d ≃ᵢ Space d) (he : e 0 = u)
    (A : Space (d+1) ≃L[ℝ] Space (d+1)) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (packet : ∀ {H L h ε Y T : ℝ} (Q : Configuration H L),
      0 < ε → 0 < Y → 0 < T →
      let W := surfaceCap g e j h ε
      (∀ a ∈ Q.A, MeasurableSet (W a) ∧ surfaceMeasure S (W a) ≠ ⊤ ∧
        ENNReal.ofReal (2*ε)^d ≤ surfaceMeasure S (W a)) →
      (∀ p ∈ Q.A ×ˢ Q.B, ∀ p' ∈ Q.A ×ˢ Q.B, parabolicSum p = parabolicSum p' →
        ∀ ξ ∈ parameterCube j h ε p.1, ∀ ξ' ∈ parameterCube j h ε p'.1,
          ∀ i, |boxPhases j (normalizedHeight g u E j) Y T h p p' ξ ξ' i| ≤ 1/3) →
      ENNReal.ofReal (((Y*ε)^d/4)*T*(energy Q.A Q.B:ℝ)) ≤
        weightedMass (fun x => extension S (capTest Q.A W (ε^(-(d:ℝ)/2))) (A x))
          (counterWeight Q.B j.castSucc (Fin.last d) h Y T)) :
    ∃ κ b H₀ : ℝ, 0 < κ ∧ 0 < b ∧ 1 ≤ H₀ ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ L : ℝ, 1 ≤ L → ∀ Q : Configuration H L,
        ENNReal.ofReal (b * Q.gain) ≤ localConstant S (κ * H ^ (1 + 2 / β)) := by
  obtain ⟨K,R,hR,hcaps⟩ := GraphChart.cap_test_data hg e (by rwa [he]) (by rwa [he])
  obtain ⟨c,hc,hc1,hph⟩ := GraphChart.resonant_phases hg hu E j hq hβ hβ1 hR
  let N := ‖A.toContinuousLinearMap‖
  let J := |LinearMap.det (A : Space (d+1) →ₗ[ℝ] Space (d+1))|
  let κ := N*(Real.sqrt (d+1:ℝ)+1)/c^2
  let cE := J*(c^d/4)
  let cF := (K:ℝ)^d*2^d+1
  let cX := N*12*(d+1:ℝ)
  have hN : 0 < N := equiv_opNorm_pos A
  have hJ : 0 < J := abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hE : 0 < cE := by dsimp [cE]; positivity
  have hF : 0 < cF := by dsimp [cF]; positivity
  have hX : 0 < cX := by dsimp [cX]; positivity
  refine ⟨κ, cE/(cF*cX), 1, hκ, by positivity, le_rfl, ?_⟩
  intro H hH L hL Q
  let s := transferScales β H c c
  let W := surfaceCap g e j s.h s.ε
  let f := capTest Q.A W (s.ε^(-(d:ℝ)/2))
  let w₀ := counterWeight Q.B j.castSucc (Fin.last d) s.h s.Y s.T
  let w := fun x => w₀ (A.symm x)
  obtain ⟨hh,hY,hT,hε,_,hYT,hYH,hTH,hrate,hYε,_⟩ :=
    transferScales_bounds hβ hβ1 hH hc hc1 hc
  obtain ⟨hgap,hfit,hphase⟩ := hph Q hH
  obtain ⟨harea,hint,hmem,hfPos,hfBound⟩ := hcaps Q j hh.le hε hgap hfit
  obtain ⟨hwcont,hw,hwPos,hwBound⟩ := inverse_counterWeight_estimates A Q j.castSucc (Fin.last d)
    hH (zero_le_one.trans hL) hh hY hYT hTH hYH
  have hradius : N*((Real.sqrt (d+1:ℝ)+1)*s.T) = κ*H^(1+2/β) := by
    rw [show s.T = _ from hrate]
    dsimp [κ]
    ring
  change AdmissibleWeight (N*((Real.sqrt (d+1:ℝ)+1)*s.T)) w at hw
  rw [hradius] at hw
  have halower := packet Q hε hY hT harea hphase
  have hmass : ENNReal.ofReal (cE*s.T*(energy Q.A Q.B:ℝ)) ≤ weightedMass (extension S f) w := by
    rw [show w = fun x => w₀ (A.symm x) from rfl, weightedMass_inverse_weight]
    change _ ≤ ENNReal.ofReal J * _
    rw [show cE*s.T*(energy Q.A Q.B:ℝ) = J*(((s.Y*s.ε)^d/4)*s.T*(energy Q.A Q.B:ℝ)) by
      rw [show s.Y*s.ε = c from hYε]; dsimp [cE]; ring, ENNReal.ofReal_mul hJ.le]
    exact mul_le_mul_of_nonneg_left halower bot_le
  have hinput : (eLpNorm f 2 (surfaceMeasure S))^2 ≤ ENNReal.ofReal (cF * Q.A.card) := by
    apply hfBound.trans
    calc
      _ = ENNReal.ofReal (((K:ℝ)^d * 2^d) * Q.A.card) := by
        simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by dsimp [cF]; linarith) (by positivity))
  have hxray : xrayNorm w ≤ ENNReal.ofReal (cX*(L*s.T*Q.B.card)) := by
    apply hwBound.trans_eq
    congr 1
    dsimp [cX,N]
    ring
  exact localConstant_of_transfer_estimates S Q f w hint hmem hwcont.measurable hw
    (ENNReal.mul_pos hfPos.ne' hwPos.ne') hL hT hE hF hX hmass hinput hxray

/-- Proposition 3.1. For each eligible hypersurface choose all multiplicative
constants before the scale H and the arithmetic configuration. -/
theorem analyticTransfer : AnalyticTransfer := by
  intro β hβ hβ1 d hd S _ hcurv
  let j : Fin d := ⟨0,hd⟩
  obtain ⟨g,hg,u,hu,hur,E,hq⟩ := hcurv.exists_oriented_chart j
  let A := adjointEquiv (g.frequencyCoordinates u E j hq)
  apply GraphChart.transfer_of_packet hg hu hur E j hq (chartOriented u E) (by simp) A hβ hβ1
  intro H L h ε Y T Q hε hY hT W harea hphase
  exact graph_cap_weightedMass_lower g u E j hq S Q.A Q.B h ε Y T hε hY hT harea hphase

end MT
