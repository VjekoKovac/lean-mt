module

public import MT.PacketExpansion
public import MT.LineEstimates

/-! Exact kernel identity for extension packets on finite patches, §3. -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Real ComplexConjugate

namespace MT

/-- Product of the one-dimensional positive-sign characters. -/
def planeWave {n : ℕ} (x ω : Fin n → ℝ) : ℂ := ∏ i, (𝐞 (x i * ω i) : ℂ)

theorem planeWave_diff {n : ℕ} (x ω ω' : Fin n → ℝ) :
    planeWave x ω * conj (planeWave x ω') = planeWave x (ω - ω') := by
  simp only [planeWave, map_prod, ← Finset.prod_mul_distrib, Pi.sub_apply, mul_sub]
  apply Finset.prod_congr rfl
  intro i _
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    Circle.coe_mul, Circle.coe_inv_eq_conj]

/-- No Fubini hypotheses are left to discharge: the packets are parametrized by
arbitrary measurable frequency maps on finite patch measures. The weight in
this identity is the product of tents; finite exponential sums are included
by indexing packets with (a,ζ) and shifting each frequency by ζ. -/
theorem packet_kernel_identity {ι Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (μ : ι → Measure Z) [∀ i, IsFiniteMeasure (μ i)]
    (P : Finset ι) (scale : Fin n → ℝ) (hs : ∀ i, 0 < scale i)
    (ω : ι → Z → Fin n → ℝ) (hω : ∀ p ∈ P, Measurable (ω p)) :
    (∫ x : Fin n → ℝ, (∏ i, tent (x i / scale i)) *
      ‖∑ p ∈ P, ∫ z, planeWave x (ω p z) ∂(μ p)‖ ^ 2) =
    ∑ pq ∈ P ×ˢ P, ∫ zz, ∏ i, scale i * tentFactor (scale i *
      (ω pq.1 zz.1 i - ω pq.2 zz.2 i)) ∂((μ pq.1).prod (μ pq.2)) := by
  let b (x : Fin n → ℝ) := ∏ i, tent (x i / scale i)
  let F (p : ι) (x : Fin n → ℝ) (z : Z) := planeWave x (ω p z)
  have hb : Continuous b := by dsimp [b]; fun_prop
  have hint : Integrable b := by
    exact Integrable.fintype_prod (μ := fun _ : Fin n => volume)
      (f := fun i t => tent (t / scale i)) (fun i => tent_integrable.comp_div (hs i).ne')
  have hF (p : ι) (hp : p ∈ P) :
      Measurable (fun xz : (Fin n → ℝ) × Z => F p xz.1 xz.2) := by
    have hw := hω p hp
    unfold F planeWave
    fun_prop
  have habs (p : ι) (_ : p ∈ P) (x : Fin n → ℝ) (z : Z) : ‖F p x z‖ = 1 := by
    simp [F, planeWave, norm_prod]
  have heq := packet_energy_expansion volume μ P b hb.measurable hint F hF habs
  have hh (p q : ι) (zz : Z × Z) :
      (∫ x : Fin n → ℝ, (b x : ℂ) * (F p x zz.1 * conj (F q x zz.2))) =
        ((∏ i, scale i * tentFactor (scale i * (ω p zz.1 i - ω q zz.2 i)) : ℝ) : ℂ) := by
    change (∫ x : Fin n → ℝ, (b x : ℂ) *
      (planeWave x (ω p zz.1) * conj (planeWave x (ω q zz.2)))) = _
    simp_rw [planeWave_diff]
    refine Eq.trans ?_ (product_tent_char scale hs (ω p zz.1 - ω q zz.2))
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [b, planeWave]
    rw [Complex.ofReal_prod, Finset.prod_mul_distrib]
  simp_rw [hh, integral_complex_ofReal] at heq
  exact_mod_cast heq

/-- Weighted extension mass from the resonant patches, with the Fourier
transforms, the two integrations over patches, and the finite energy count in
one inequality. To use it on a surface, take μ a to be area on its a-th patch,
and ω(a,ζ)(z) to be z plus the physical modulation indexed by ζ. -/
theorem packet_mass_ge_energy {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (A : Finset ℝ) (B : Finset (ℝ × ℝ)) (μ : ℝ → Measure Z) [∀ a, IsFiniteMeasure (μ a)]
    (scale : Fin n → ℝ) (hs : ∀ i, 0 < scale i)
    (ω : (ℝ × ℝ × ℝ) → Z → Fin n → ℝ) (hω : ∀ p ∈ A ×ˢ B, Measurable (ω p))
    (V : ℝ) (hV : 0 ≤ V) (harea : ∀ a ∈ A, V ≤ (μ a).real univ)
    (hphase : ∀ p ∈ A ×ˢ B, ∀ q ∈ A ×ˢ B, parabolicSum p = parabolicSum q →
      ∀ᵐ zz ∂((μ p.1).prod (μ q.1)), ∀ i, |scale i * (ω p zz.1 i - ω q zz.2 i)| ≤ 1/3) :
    (energy A B : ℝ) * ((∏ i, scale i / 4) * V ^ 2) ≤
      ∫ x : Fin n → ℝ, (∏ i, tent (x i / scale i)) *
        ‖∑ p ∈ A ×ˢ B, ∫ z, planeWave x (ω p z) ∂(μ p.1)‖ ^ 2 := by
  classical
  let P := A ×ˢ B
  let G := (P ×ˢ P).filter (fun q => parabolicSum q.1 = parabolicSum q.2)
  let D (p q : ℝ × ℝ × ℝ) (zz : Z × Z) := ∏ i, scale i *
    tentFactor (scale i * (ω p zz.1 i - ω q zz.2 i))
  let m := ∏ i, scale i / 4
  let I (pq : (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) :=
    ∫ zz, D pq.1 pq.2 zz ∂((μ pq.1.1).prod (μ pq.2.1))
  have hpos (p q) (zz : Z × Z) : 0 ≤ D p q zz :=
    Finset.prod_nonneg fun i _ => mul_nonneg (hs i).le (tentFactor_nonneg _)
  have hm : 0 ≤ m := Finset.prod_nonneg fun i _ => div_nonneg (hs i).le (by norm_num)
  have hone (z : ℝ) : tentFactor z ≤ 1 := by
    simp only [tentFactor, fourier_tent, Complex.ofReal_re]
    have hh := sq_le_sq.mpr (by simpa using Real.abs_sinc_le_one (Real.pi*z) :
      |Real.sinc (Real.pi*z)| ≤ |(1:ℝ)|)
    simpa using hh
  have hcont : Continuous tentFactor := by
    have he : tentFactor = fun z => Real.sinc (Real.pi * z) ^ 2 := by
      funext z; simp only [tentFactor, fourier_tent, Complex.ofReal_re]
    rw [he]
    fun_prop
  have hint (p q) (hp : p ∈ P) (hq : q ∈ P) : Integrable (D p q) ((μ p.1).prod (μ q.1)) := by
    apply (integrable_const (∏ i, scale i)).mono'
    · have h₁ := hω p hp
      have h₂ := hω q hq
      dsimp [D]
      fun_prop
    · filter_upwards with zz
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos p q zz)]
      apply Finset.prod_le_prod₀
      · exact fun i _ => mul_nonneg (hs i).le (tentFactor_nonneg _)
      · exact fun i _ => mul_le_of_le_one_right (hs i).le (hone _)
  have hEq := packet_kernel_identity (fun p : ℝ × ℝ × ℝ => μ p.1) P scale hs ω hω
  rw [hEq]
  change (G.card : ℝ) * (m * V ^ 2) ≤ ∑ q ∈ P ×ˢ P, I q
  calc
    _ = ∑ _q ∈ G, m * V ^ 2 := by simp
    _ ≤ ∑ q ∈ G, I q := by
      apply Finset.sum_le_sum
      intro pq hpq
      obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hpq
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hmem
      have haar := mul_le_mul (harea _ (Finset.mem_product.mp hp).1)
        (harea _ (Finset.mem_product.mp hq).1) hV (measureReal_nonneg)
      have hlower : ∀ᵐ zz ∂((μ pq.1.1).prod (μ pq.2.1)), m ≤ D pq.1 pq.2 zz := by
        filter_upwards [hphase _ hp _ hq heq] with zz hz
        apply Finset.prod_le_prod₀
        · exact fun i _ => div_nonneg (hs i).le (by norm_num)
        · intro i _
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (by simpa using tentFactor_lower (hz i)) (hs i).le
      calc
        _ ≤ ((μ pq.1.1).real univ * (μ pq.2.1).real univ) * m := by
          rw [pow_two, mul_comm m]
          exact mul_le_mul_of_nonneg_right haar hm
        _ = ∫ _zz : Z × Z, m ∂((μ pq.1.1).prod (μ pq.2.1)) := by
          rw [integral_const, smul_eq_mul, ← measureReal_prod_prod, univ_prod_univ]
        _ ≤ _ := integral_mono_ae (integrable_const _) (hint _ _ hp hq) hlower
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun pq _ _ => integral_nonneg (hpos pq.1 pq.2))

end MT
