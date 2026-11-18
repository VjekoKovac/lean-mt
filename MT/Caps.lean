module

public import MT.GraphMeasure
public import MT.WeightedKernel
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # The input test and its surface L² norm

Use the same parameter cubes as Lemma 3.4, transported into the chosen chart.
The test is constant on their graph images. Measuring the patches directly
uses the two-sided area bound of GraphMeasure in place of dividing by J.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal Topology InnerProductSpace

namespace MT

def chartCube {d : ℕ} (e : Space d ≃ᵢ Space d) (j : Fin d) (h ε a : ℝ) : Set (Space d) :=
  e '' (WithLp.toLp 2 '' parameterCube j h ε a)

def surfaceCap {d : ℕ} (g : GraphChart d) (e : Space d ≃ᵢ Space d)
    (j : Fin d) (h ε a : ℝ) : Set (Space (d+1)) := g.point '' chartCube e j h ε a

theorem chartCube_compact {d : ℕ} (e : Space d ≃ᵢ Space d) (j : Fin d) (h ε a : ℝ) :
    IsCompact (chartCube e j h ε a) :=
  (isCompact_Icc.image (by fun_prop : Continuous (@WithLp.toLp 2 (Fin d → ℝ)))).image e.continuous

theorem chartCube_volume {d : ℕ} (e : Space d ≃ᵢ Space d) (j : Fin d) (h ε a : ℝ) :
    volume (chartCube e j h ε a) = ENNReal.ofReal (2*ε)^d := by
  unfold chartCube
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume d,
    e.isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  have hi : WithLp.toLp 2 '' parameterCube j h ε a =
      (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' parameterCube j h ε a := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨x.ofLp, hx, rfl⟩
  rw [hi, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (show MeasurableSet (parameterCube j h ε a) from measurableSet_Icc).nullMeasurableSet,
    volume_parameterCube]

/-- For any fixed chart, all cubes from A fit in its neighborhood once h+ε
is sufficiently small. This radius is independent of A and of the scale. -/
theorem chartCubes_fit {d : ℕ} (e : Space d ≃ᵢ Space d) {U : Set (Space d)}
    (hU : U ∈ 𝓝 (e 0)) : ∃ r : ℝ, 0 < r ∧
    ∀ (j : Fin d) (h ε a : ℝ), 0 ≤ h → |a| ≤ 1 → h+ε < r → chartCube e j h ε a ⊆ U := by
  have hC : Continuous (fun x : Fin d → ℝ => e (WithLp.toLp 2 x)) := by fun_prop
  have hnear : (fun x : Fin d → ℝ => e (WithLp.toLp 2 x)) ⁻¹' U ∈ 𝓝 0 :=
    hC.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r,hr,?_⟩
  intro j h ε a hh ha hsmall y hy
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
  apply hball
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hr]
  intro i
  have hlo := hx.1 i
  have hhi := hx.2 i
  have hcenter : |h*a| ≤ h := by
    rw [abs_mul, abs_of_nonneg hh]
    exact mul_le_of_le_one_right hh ha
  rw [Real.norm_eq_abs, abs_lt]
  obtain ⟨hal, hau⟩ := abs_le.mp hcenter
  by_cases hi : i = j <;> simp only [hi, ite_true, ite_false] at hlo hhi <;>
    constructor <;> linarith

theorem parameterCube_disjoint {d : ℕ} {j : Fin d} {h ε a a' : ℝ} (hh : 0 ≤ h)
    (hgap : 2*ε < h*|a-a'|) :
    Disjoint (parameterCube j h ε a) (parameterCube j h ε a') := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have h₁ := hx.1 j
  have h₂ := hx.2 j
  have h₃ := hx'.1 j
  have h₄ := hx'.2 j
  simp only [ite_true] at h₁ h₂ h₃ h₄
  rw [← abs_of_nonneg hh, ← abs_mul, mul_sub] at hgap
  exact (not_le.mpr hgap) (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem surfaceCap_pairwise {d : ℕ} {H L h ε : ℝ} (Q : Configuration H L)
    (g : GraphChart d) (e : Space d ≃ᵢ Space d) (j : Fin d) (hh : 0 ≤ h)
    (hε : 2*ε < h*H⁻¹) :
    (↑Q.A : Set ℝ).PairwiseDisjoint (surfaceCap g e j h ε) := by
  intro a ha a' ha' hn
  have hp := parameterCube_disjoint (j := j) hh
    (hε.trans_le (mul_le_mul_of_nonneg_left (Q.separated a ha a' ha' hn) hh))
  apply Set.disjoint_left.mpr
  rintro z ⟨y, ⟨u, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩ ⟨y', ⟨u', ⟨v', hv', rfl⟩, rfl⟩, heq⟩
  have hh := e.injective (g.antilipschitz.injective heq)
  have hvv : v' = v := congrArg WithLp.ofLp hh
  exact Set.disjoint_left.mp hp hv (hvv ▸ hv')

/-- Choose the chart factor and neighborhood once, before the scale and cubes. -/
theorem GraphChart.cap_area {d : ℕ} {β : ℝ} {S : Set (Space (d+1))} {g : GraphChart d}
    (hg : g.ValidFor β S) {u : Space d} (hu : u ∈ g.domain) (hur : g.point u ∈ g.region) :
    ∃ K : ℝ≥0, ∃ U ∈ 𝓝 u, ∀ (e : Space d ≃ᵢ Space d) (j : Fin d) (h ε a : ℝ),
      chartCube e j h ε a ⊆ U →
      IsCompact (surfaceCap g e j h ε a) ∧
      (ENNReal.ofReal (2*ε))^d ≤ surfaceMeasure S (surfaceCap g e j h ε a) ∧
      surfaceMeasure S (surfaceCap g e j h ε a) ≤ (K : ℝ≥0∞)^d * (ENNReal.ofReal (2*ε))^d := by
  obtain ⟨K,U,hU,hm⟩ := GraphChart.local_area_bounds hg hu hur
  refine ⟨K, U ∩ g.domain, Filter.inter_mem hU (hg.1.mem_nhds hu), ?_⟩
  intro e j h ε a hsub
  have hcompact := chartCube_compact e j h ε a
  have hcont : ContinuousOn g.point g.domain := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply g.rigid.continuous.continuousAt.comp
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (d+1) => ℝ)).continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using (hg.2.2.2.1.contDiffAt (hg.1.mem_nhds hx)).continuousAt
    · simpa using (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).continuousAt (x := x)
  refine ⟨hcompact.image_of_continuousOn (hcont.mono (hsub.trans inter_subset_right)), ?_⟩
  simpa only [surfaceCap, chartCube_volume] using
    hm (chartCube e j h ε a) (hsub.trans inter_subset_left) hcompact

def capTest {X : Type*} (A : Finset ℝ) (W : ℝ → Set X) (amp : ℝ) (x : X) : ℂ :=
  ∑ a ∈ A, (W a).indicator (fun _ => (amp : ℂ)) x

theorem capTest_eq_indicator {X : Type*} (A : Finset ℝ) (W : ℝ → Set X) (amp : ℝ)
    (hdis : (A : Set ℝ).PairwiseDisjoint W) :
    capTest A W amp = (⋃ a ∈ A, W a).indicator (fun _ => (amp : ℂ)) := by
  funext x
  unfold capTest
  rw [← Finset.indicator_biUnion_apply]
  exact hdis

theorem amplitude_cancel (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (ε ^ (-(d:ℝ)/2))^2 * (2*ε)^d = (2:ℝ)^d := by
  have hh : (ε ^ (-(d:ℝ)/2))^2 = (ε^d)⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hε.le, show (-(d:ℝ)/2)*2 = -(d:ℝ) by ring,
      Real.rpow_neg hε.le, Real.rpow_natCast]
  rw [hh, mul_pow]
  field_simp

/-- Equation (3.2). The test is exactly the normalized finite indicator sum.
Two-sided area bounds give positive squared norm and a uniform upper bound. -/
theorem capTest_input {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : Finset ℝ) (hA : A.Nonempty) (W : ℝ → Set X) (d : ℕ) {ε : ℝ}
    (hε : 0 < ε) (K : ℝ≥0)
    (hM : ∀ a ∈ A, MeasurableSet (W a)) (hdis : (A : Set ℝ).PairwiseDisjoint W)
    (hlower : ∀ a ∈ A, (ENNReal.ofReal (2*ε))^d ≤ μ (W a))
    (hupper : ∀ a ∈ A, μ (W a) ≤ (K : ℝ≥0∞)^d * (ENNReal.ofReal (2*ε))^d) :
    let f := capTest A W (ε ^ (-(d:ℝ)/2))
    Integrable f μ ∧ MemLp f 2 μ ∧
      (A.card : ℝ≥0∞)*(2:ℝ≥0∞)^d ≤ (eLpNorm f 2 μ)^2 ∧
      (eLpNorm f 2 μ)^2 ≤ (A.card : ℝ≥0∞)*(K:ℝ≥0∞)^d*(2:ℝ≥0∞)^d ∧
      0 < (eLpNorm f 2 μ)^2 := by
  let amp := ε ^ (-(d:ℝ)/2)
  let U := ⋃ a ∈ A, W a
  have hU : MeasurableSet U := A.measurableSet_biUnion hM
  have heq := capTest_eq_indicator A W amp hdis
  have hUeq : μ U = ∑ a ∈ A, μ (W a) := measure_biUnion_finset hdis hM
  let V := (ENNReal.ofReal (2*ε))^d
  have hUL : (A.card : ℝ≥0∞)*V ≤ μ U := calc
    _ = ∑ _a ∈ A, V := by simp
    _ ≤ _ := hUeq ▸ Finset.sum_le_sum hlower
  have hUU : μ U ≤ (A.card : ℝ≥0∞)*((K:ℝ≥0∞)^d*V) := calc
    _ = _ := hUeq
    _ ≤ ∑ _a ∈ A, ((K:ℝ≥0∞)^d*V) := Finset.sum_le_sum hupper
    _ = _ := by simp
  have hfin : μ U ≠ ⊤ := (hUU.trans_lt (by dsimp [V]; finiteness)).ne
  have hnorm : (eLpNorm (capTest A W amp) 2 μ)^2 = ENNReal.ofReal (amp^2)*μ U := by
    rw [heq, eLpNorm_indicator_const hU.nullMeasurableSet (by norm_num) (by norm_num), mul_pow]
    have hr (z : ℝ≥0∞) : (z ^ (1 / (2 : ℝ)))^2 = z := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    simp only [ENNReal.toReal_ofNat, hr]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by dsimp [amp]; positivity),
      ENNReal.ofReal_pow (by dsimp [amp]; positivity)]
  have hc : ENNReal.ofReal (amp^2) * V = (2 : ℝ≥0∞)^d := by
    dsimp [V,amp]
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      amplitude_cancel d hε, ENNReal.ofReal_pow (by norm_num)]
    norm_num
  have hlow : (A.card : ℝ≥0∞)*(2:ℝ≥0∞)^d ≤ (eLpNorm (capTest A W amp) 2 μ)^2 := by
    rw [hnorm, ← hc, ← mul_assoc, mul_comm (A.card:ℝ≥0∞), mul_assoc]
    exact mul_le_mul_of_nonneg_left hUL bot_le
  have hup : (eLpNorm (capTest A W amp) 2 μ)^2 ≤ (A.card:ℝ≥0∞)*(K:ℝ≥0∞)^d*(2:ℝ≥0∞)^d := by
    rw [hnorm, ← hc]
    apply (mul_le_mul_of_nonneg_left hUU (a := ENNReal.ofReal (amp^2)) bot_le).trans_eq
    ring
  have hcard : 0 < (A.card : ℝ≥0∞) := by exact_mod_cast Finset.card_pos.mpr hA
  refine ⟨?_, ?_, hlow, hup, (ENNReal.mul_pos hcard.ne' (pow_ne_zero d (by norm_num))).trans_le hlow⟩
  · rw [heq]
    exact (memLp_one_iff_integrable).1 (memLp_indicator_const 1 hU.nullMeasurableSet _ (.inr hfin))
  · rw [heq]
    exact memLp_indicator_const 2 hU.nullMeasurableSet _ (.inr hfin)

/-- Choose the L² constant and chart radius once. All admissible sets and
subsequent sufficiently small separated caps can be tested in this chart. -/
theorem GraphChart.cap_test_data {d : ℕ} {β : ℝ} {S : Set (Space (d+1))} {g : GraphChart d}
    (hg : g.ValidFor β S) (e : Space d ≃ᵢ Space d)
    (hu : e 0 ∈ g.domain) (hur : g.point (e 0) ∈ g.region) :
    ∃ K : ℝ≥0, ∃ r : ℝ, 0 < r ∧ ∀ {H L : ℝ} (Q : Configuration H L)
      (j : Fin d) {h ε : ℝ}, 0 ≤ h → 0 < ε → 2*ε < h*H⁻¹ → h+ε < r →
      let W := surfaceCap g e j h ε
      let f := capTest Q.A W (ε ^ (-(d:ℝ)/2))
      (∀ a ∈ Q.A, MeasurableSet (W a) ∧ surfaceMeasure S (W a) ≠ ⊤ ∧
        (ENNReal.ofReal (2*ε))^d ≤ surfaceMeasure S (W a)) ∧
      Integrable f (surfaceMeasure S) ∧ MemLp f 2 (surfaceMeasure S) ∧
      0 < (eLpNorm f 2 (surfaceMeasure S))^2 ∧
      (eLpNorm f 2 (surfaceMeasure S))^2 ≤
        (Q.A.card:ℝ≥0∞)*(K:ℝ≥0∞)^d*(2:ℝ≥0∞)^d := by
  obtain ⟨K,U,hU,harea⟩ := GraphChart.cap_area hg hu hur
  obtain ⟨r,hr,hfit⟩ := chartCubes_fit e hU
  refine ⟨K,r,hr,?_⟩
  intro H L Q j h ε hh hε hgap hsmall
  have hcaps (a : ℝ) (ha : a ∈ Q.A) := harea e j h ε a
    (hfit j h ε a hh (Q.inBoxA a ha) hsmall)
  obtain ⟨hint,hmem,_,hup,hpos⟩ := capTest_input (surfaceMeasure S) Q.A Q.nonemptyA
    (surfaceCap g e j h ε) d hε K (fun a ha => (hcaps a ha).1.measurableSet)
    (surfaceCap_pairwise Q g e j hh hgap) (fun a ha => (hcaps a ha).2.1)
    (fun a ha => (hcaps a ha).2.2)
  refine ⟨?_,hint,hmem,hpos,hup⟩
  intro a ha
  exact ⟨(hcaps a ha).1.measurableSet, ((hcaps a ha).2.2.trans_lt (by finiteness)).ne, (hcaps a ha).2.1⟩

end MT
