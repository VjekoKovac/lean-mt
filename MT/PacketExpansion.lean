module

public import MT.ProductKernel
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The finite expansion and Fubini step at the start of Lemma 3.4. -/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate

namespace MT

/-- Expand the squared modulus of a finite sum of extension packets, and
integrate in physical space first. In §3 the packet index is (a,ζ), μₚ is
surface area restricted to the corresponding compact patch, the phases have
absolute value one, and b is the compactly supported product of tents. -/
theorem packet_energy_expansion {ι X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (ν : Measure X) [SigmaFinite ν] (μ : ι → Measure Z) [∀ i, IsFiniteMeasure (μ i)]
    (P : Finset ι) (b : X → ℝ) (hb : Measurable b) (hint : Integrable b ν)
    (F : ι → X → Z → ℂ)
    (hF : ∀ i ∈ P, Measurable (fun xz : X × Z => F i xz.1 xz.2))
    (habs : ∀ i ∈ P, ∀ x z, ‖F i x z‖ = 1) :
    (((∫ x, b x * ‖∑ p ∈ P, (∫ z, F p x z ∂(μ p))‖ ^ 2 ∂ν) : ℝ) : ℂ) =
      ∑ pq ∈ P ×ˢ P, ∫ zz, ∫ x, (b x : ℂ) * (F pq.1 x zz.1 * conj (F pq.2 x zz.2)) ∂ν
        ∂((μ pq.1).prod (μ pq.2)) := by
  classical
  let K (p q : ι) (x : X) (zz : Z × Z) := (b x : ℂ) * (F p x zz.1 * conj (F q x zz.2))
  have hK (p q : ι) (hp : p ∈ P) (hq : q ∈ P) :
      Integrable (Function.uncurry (K p q)) (ν.prod ((μ p).prod (μ q))) := by
    have h₁ : Measurable (fun z : X × Z × Z => F p z.1 z.2.1) := (hF p hp).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h₂ : Measurable (fun z : X × Z × Z => F q z.1 z.2.2) := (hF q hq).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    apply (hint.norm.comp_fst ((μ p).prod (μ q))).mono'
    · exact ((Complex.continuous_ofReal.measurable.comp (hb.comp measurable_fst)).mul
        (h₁.mul (Complex.continuous_conj.measurable.comp h₂))).aestronglyMeasurable
    · filter_upwards with xzz
      simp [Function.uncurry, K, habs p hp, habs q hq]
  have hpq (p q : ι) (x : X) :
      ∫ zz, K p q x zz ∂((μ p).prod (μ q)) =
        (b x : ℂ) * ((∫ z, F p x z ∂(μ p)) * conj (∫ z, F q x z ∂(μ q))) := by
    dsimp only [K]
    rw [integral_const_mul, integral_prod_mul (F p x) (fun z => conj (F q x z)), integral_conj]
  have hpoint (x : X) :
      ((b x * ‖∑ p ∈ P, ∫ z, F p x z ∂(μ p)‖ ^ 2 : ℝ) : ℂ) =
        ∑ pq ∈ P ×ˢ P, ∫ zz, K pq.1 pq.2 x zz ∂((μ pq.1).prod (μ pq.2)) := by
    simp_rw [hpq]
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum,
      Finset.sum_mul_sum, Finset.sum_product]
    simp only [Finset.mul_sum]
  rw [← integral_complex_ofReal]
  simp_rw [hpoint]
  rw [integral_finsetSum (f := fun (pq : ι × ι) x => ∫ zz, K pq.1 pq.2 x zz ∂((μ pq.1).prod (μ pq.2))) _ (fun pq hpq' =>
    (hK pq.1 pq.2 (Finset.mem_product.mp hpq').1 (Finset.mem_product.mp hpq').2).integral_prod_left)]
  refine Finset.sum_congr rfl (fun pq hpq' => ?_)
  exact integral_integral_swap
    (hK pq.1 pq.2 (Finset.mem_product.mp hpq').1 (Finset.mem_product.mp hpq').2)

end MT
