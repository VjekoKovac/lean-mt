module

public import MT.Caps
public import MT.Scales
public import MT.Taylor
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! The resonant phase of Lemma 3.4 for a general curved chart.

A single nonisotropic unit direction suffices for the upper bound on a
cube. The transverse terms of the full Hessian are bounded by its operator
norm. The signed coefficient is absorbed into the final frequency coordinate.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace Topology

namespace MT

def chartAxis {d : ℕ} (j : Fin d) : Space d := EuclideanSpace.single j 1

theorem norm_chartAxis {d : ℕ} (j : Fin d) : ‖chartAxis j‖ = 1 := by
  simp [chartAxis, EuclideanSpace.single, PiLp.norm_single]

def curvatureCoefficient {d : ℕ} (g : GraphChart d) (u : Space d)
    (E : Space d ≃ₗᵢ[ℝ] Space d) (j : Fin d) : ℝ :=
  hessian g.height u (E (chartAxis j)) (E (chartAxis j)) / 2

/-- A single reflection chooses the curved direction as the distinguished
coordinate. Its coefficient may be positive or negative. -/
theorem HasCurvature.exists_oriented_chart {d : ℕ} {β : ℝ} {S : Set (Space (d+1))}
    (h : HasCurvature β S) (j : Fin d) :
    ∃ g : GraphChart d, g.ValidFor β S ∧ ∃ u ∈ g.domain, g.point u ∈ g.region ∧
      ∃ E : Space d ≃ₗᵢ[ℝ] Space d, curvatureCoefficient g u E j ≠ 0 := by
  obtain ⟨g,hg,u,hu,hur,v,hv⟩ := h.exists_direction
  have hn : ‖v‖ ≠ 0 := by
    intro hz
    apply hv
    simp [norm_eq_zero.mp hz]
  let v₀ := ‖v‖⁻¹ • v
  have hunit : ‖v₀‖ = 1 := by
    simp [v₀, norm_smul, hn]
  let E := (ℝ ∙ (chartAxis j - v₀))ᗮ.reflection
  have he : E (chartAxis j) = v₀ :=
    Submodule.reflection_sub ((norm_chartAxis j).trans hunit.symm)
  refine ⟨g,hg,u,hu,hur,E,?_⟩
  unfold curvatureCoefficient
  rw [he]
  simp [v₀, hn, hv]

/-- Subtract the tangent hyperplane and normalize the signed quadratic
coefficient. In normalized ambient coordinates a graph point is (x,Φ(x)). -/
def normalizedHeight {d : ℕ} (g : GraphChart d) (u : Space d)
    (E : Space d ≃ₗᵢ[ℝ] Space d) (j : Fin d) (ξ : Fin d → ℝ) : ℝ :=
  let x := E (WithLp.toLp 2 ξ)
  (g.height (u+x) - g.height u - fderiv ℝ g.height u x) / curvatureCoefficient g u E j

theorem norm_sub_center_le {d : ℕ} {j : Fin d} {h ε a : ℝ} {ξ : Fin d → ℝ}
    (hε : 0 ≤ ε) (hξ : ξ ∈ parameterCube j h ε a) :
    ‖WithLp.toLp 2 ξ - (h*a) • chartAxis j‖ ≤ Real.sqrt d * ε := by
  let z := WithLp.toLp 2 ξ - (h*a) • chartAxis j
  have hz (i : Fin d) : |z i| ≤ ε := by
    have hl := hξ.1 i
    have hu := hξ.2 i
    by_cases hi : i = j <;>
      simp [z, chartAxis, EuclideanSpace.single, *] at hl hu ⊢ <;>
      apply abs_le.mpr <;> constructor <;> linarith
  change ‖z‖ ≤ _
  rw [← Real.sqrt_sq (norm_nonneg z), EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ Real.sqrt (∑ _i : Fin d, ε^2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum fun i _ => sq_le_sq.mpr (by simpa [abs_of_nonneg hε] using hz i)
    _ = _ := by simp [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hε]

/-- Variation of a quadratic form on a cap, including every mixed Hessian term. -/
private theorem bilinear_diag_sub_le {d : ℕ} (D : Space d →L[ℝ] Space d →L[ℝ] ℝ)
    (x z : Space d) : |D x x - D z z| ≤ ‖D‖ * (‖x‖ + ‖z‖) * ‖x-z‖ := by
  have hid : D x x - D z z = D (x-z) x + D z (x-z) := by simp
  rw [hid]
  calc
    _ ≤ |D (x-z) x| + |D z (x-z)| := abs_add_le .. 
    _ ≤ (‖D‖*‖x-z‖)*‖x‖ + (‖D‖*‖z‖)*‖x-z‖ := by
      change ‖D (x-z) x‖ + ‖D z (x-z)‖ ≤ _
      exact add_le_add (((D (x-z)).le_opNorm x).trans (by gcongr; exact D.le_opNorm _))
        (((D z).le_opNorm (x-z)).trans (by gcongr; exact D.le_opNorm _))
    _ = _ := by ring

/-- Uniform approximation on every cube of a curved chart. P controls
the Taylor remainder and Q the variation of the quadratic form across a cap. -/
theorem GraphChart.cube_height_bound {d : ℕ} {β : ℝ} {S : Set (Space (d+1))}
    {g : GraphChart d} (hg : g.ValidFor β S) {u : Space d} (hu : u ∈ g.domain)
    (E : Space d ≃ₗᵢ[ℝ] Space d) (j : Fin d) (hq : curvatureCoefficient g u E j ≠ 0)
    (hβ : 0 ≤ β) :
    ∃ P Q r : ℝ, 0 ≤ P ∧ 0 ≤ Q ∧ 0 < r ∧ ∀ {h ε a : ℝ} {ξ : Fin d → ℝ},
      0 ≤ ε → ε ≤ h → h < r → |a| ≤ 1 → ξ ∈ parameterCube j h ε a →
      |normalizedHeight g u E j ξ - (h*a)^2| ≤ P*h^(2+β) + Q*(h*ε) := by
  let m := Real.sqrt d
  let N := 1+m
  let q := curvatureCoefficient g u E j
  let D := hessian g.height u
  have hm : 0 ≤ m := Real.sqrt_nonneg _
  have hN : 0 < N := by dsimp [N]; linarith
  obtain ⟨K,ρ,hK,hρ,ht⟩ := GraphChart.exists_taylor_bound hg hβ u hu
  refine ⟨K*N^(2+β)/|q|, ‖D‖*(N+1)*m/(2*|q|), ρ/N,
    by positivity, by positivity, by positivity,?_⟩
  intro h ε a ξ hε hεh hsmall ha hξ
  have hh := hε.trans hεh
  let x := E (WithLp.toLp 2 ξ)
  let z := E ((h*a) • chartAxis j)
  have hxz : ‖x-z‖ ≤ m*ε := by
    change ‖E (WithLp.toLp 2 ξ) - E ((h*a) • chartAxis j)‖ ≤ _
    rw [← map_sub, E.norm_map]
    exact norm_sub_center_le hε hξ
  have hzc : ‖z‖ ≤ h := by
    simp only [z, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, norm_chartAxis,
      mul_one, abs_mul, abs_of_nonneg hh]
    exact mul_le_of_le_one_right hh ha
  have hxc : ‖x‖ ≤ N*h := calc
    _ ≤ ‖x-z‖ + ‖z‖ := by simpa [add_comm] using (norm_le_norm_add_norm_sub' x z)
    _ ≤ m*h+h := add_le_add (hxz.trans (mul_le_mul_of_nonneg_left hεh hm)) hzc
    _ = _ := by dsimp [N]; ring
  have ht' := ht x (hxc.trans_lt (by simpa [mul_comm] using (lt_div_iff₀ hN).mp hsmall))
  have hquad : |D x x - D z z| ≤ ‖D‖*(N+1)*m*(h*ε) := calc
    _ ≤ ‖D‖*(‖x‖+‖z‖)*‖x-z‖ := bilinear_diag_sub_le D x z
    _ ≤ ‖D‖*(N*h+h)*(m*ε) := by gcongr
    _ = _ := by ring
  have hquad0 : D z z / 2 = q * (h*a)^2 := by
    simp only [z, q, curvatureCoefficient, D, map_smul, smul_apply, smul_eq_mul]
    ring
  let b := g.height (u+x) - g.height u - fderiv ℝ g.height u x
  have hb : |b-D x x/2| ≤ K*N^(2+β)*h^(2+β) := calc
    _ ≤ K*‖x‖^(2+β) := ht'
    _ ≤ K*(N*h)^(2+β) := by gcongr
    _ = _ := by rw [Real.mul_rpow hN.le hh]; ring
  change |b/q - (h*a)^2| ≤ _
  have heq : b/q - (h*a)^2 = ((b-D x x/2) + (D x x-D z z)/2)/q := by
    field_simp [show q ≠ 0 from hq]
    linarith [hquad0]
  rw [heq, abs_div]
  calc
    _ ≤ (|b-D x x/2| + |(D x x-D z z)/2|)/|q| :=
      div_le_div_of_nonneg_right (abs_add_le ..) (abs_nonneg _)
    _ ≤ (K*N^(2+β)*h^(2+β) + (‖D‖*(N+1)*m*(h*ε))/2)/|q| := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      gcongr
    _ = _ := by ring


/-- Choose one small positive scale multiplier for h and ε. Every scale H≥1
then works, and all caps fit an arbitrarily prescribed local chart radius. -/
theorem GraphChart.resonant_phases {d : ℕ} {β : ℝ} {S : Set (Space (d+1))}
    {g : GraphChart d} (hg : g.ValidFor β S) {u : Space d} (hu : u ∈ g.domain)
    (E : Space d ≃ₗᵢ[ℝ] Space d) (j : Fin d) (hq : curvatureCoefficient g u E j ≠ 0)
    (hβ : 0 < β) (hβ1 : β ≤ 1) {R : ℝ} (hR : 0 < R) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ {H L : ℝ} (Q : Configuration H L), 1 ≤ H →
      let s := transferScales β H c c
      2*s.ε < s.h*H⁻¹ ∧ s.h+s.ε < R ∧
      ∀ p ∈ Q.A ×ˢ Q.B, ∀ p' ∈ Q.A ×ˢ Q.B, parabolicSum p = parabolicSum p' →
        ∀ ξ ∈ parameterCube j s.h s.ε p.1, ∀ ξ' ∈ parameterCube j s.h s.ε p'.1,
          ∀ i, |boxPhases j (normalizedHeight g u E j) s.Y s.T s.h p p' ξ ξ' i| ≤ 1/3 := by
  obtain ⟨P,D,r,hP,hD,hr,happrox⟩ := GraphChart.cube_height_bound hg hu E j hq hβ.le
  let F (t : ℝ) := P*t^β + D*t
  have hF : Continuous F := (continuous_const.mul (Real.continuous_rpow_const hβ.le)).add
    (continuous_const.mul continuous_id)
  have hF0 : F 0 < 1/6 := by simp [F,Real.zero_rpow hβ.ne']
  have hV : {t : ℝ | F t < 1/6} ∈ 𝓝 0 := hF.isOpen_preimage _ isOpen_Iio |>.mem_nhds hF0
  obtain ⟨w,hw,hwb⟩ := Metric.mem_nhds_iff.mp hV
  let c := min (min (r/2) (R/3)) (min (w/2) (1/12))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcr : c ≤ r/2 := (min_le_left ..).trans (min_le_left ..)
  have hcR : c ≤ R/3 := (min_le_left ..).trans (min_le_right ..)
  have hcw : c ≤ w/2 := (min_le_right ..).trans (min_le_left ..)
  have hc12 : c ≤ 1/12 := (min_le_right ..).trans (min_le_right ..)
  have hc1 : c ≤ 1 := by linarith
  have hcF : P*c^β + D*c < 1/6 := hwb (show c ∈ Metric.ball 0 w by
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hc]; linarith)
  refine ⟨c,hc,hc1,?_⟩
  intro H L Q hH
  let s := transferScales β H c c
  obtain ⟨hh,hY,hT,hε,hhH,_,_,_,_,hYε,hThε,_,hThβ⟩ :=
    transferScales_bounds hβ hβ1 hH hc hc1 hc
  have hH0 : 0 < H := by linarith
  have hhC : s.h ≤ c := (le_mul_of_one_le_right hh.le hH).trans hhH
  have hεdef : s.ε = c*s.h/H := rfl
  have hεh : s.ε ≤ s.h := by
    rw [hεdef,div_le_iff₀ hH0]
    exact (mul_le_of_le_one_left hh.le hc1).trans (le_mul_of_one_le_right hh.le hH)
  refine ⟨?_,by linarith,?_⟩
  · rw [show s.ε = c*s.h/H from rfl, ← div_eq_mul_inv, ← mul_div_assoc, div_lt_div_iff_of_pos_right hH0]
    nlinarith [mul_pos (show 0 < 1-2*c by linarith) hh]
  intro p hp p' hp' he ξ hξ ξ' hξ'
  let err := P*s.h^(2+β) + D*(s.h*s.ε)
  have htime : s.T*(2*err) ≤ 1/3 := by
    have hte : s.T*err = P*c^β + D*c := by
      dsimp [err]
      linear_combination P * hThβ + D * hThε
    linarith
  have hspace : s.Y*(2*s.ε) ≤ 1/3 := by linarith
  have hat {a : ℝ} (ha : a ∈ Q.A) {x : Fin d → ℝ} (hx : x ∈ parameterCube j s.h s.ε a) :
      |normalizedHeight g u E j x - (s.h*a)^2| ≤ err :=
    happrox hε.le hεh (by linarith) (Q.inBoxA _ ha) hx
  exact boxPhases_small_of_height hY.le hT.le hspace htime hξ hξ' he
    (hat (Finset.mem_product.mp hp).1 hξ) (hat (Finset.mem_product.mp hp').1 hξ')

end MT
