module

public import MT.Caps
public import MT.PacketKernel
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Fourier characters and the surface cap test in §3. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Real FourierTransform InnerProductSpace

namespace MT

/-- The product character on physical coordinates is the usual dot-product
character. The same identity holds for any finite number of coordinates. -/
theorem planeWave_dot {n : ℕ} (x ξ : Fin n → ℝ) :
    planeWave x ξ = (𝐞 (∑ i, x i * ξ i) : ℂ) := by
  unfold planeWave
  generalize (Finset.univ : Finset (Fin n)) = U
  induction U using Finset.induction_on with
  | empty => simp
  | insert i U hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, AddChar.map_add_eq_mul, Circle.coe_mul]

/-- The Fourier phase in `extension` is the same character as the one in the
packet expansion, under the standard coordinate isometry. -/
theorem planeWave_euclidean {n : ℕ} (x ξ : Space n) :
    planeWave (fun i => x i) (fun i => ξ i) =
      Complex.exp (((2 * Real.pi * ⟪ξ, x⟫_ℝ : ℝ) : ℂ) * Complex.I) := by
  rw [planeWave_dot, ← Real.fourierChar_apply]
  congr 2

/-- Direct rewrite of the extension of a sum of constant indicators. This
uses surface area restricted to each patch, with finite positive area later
supplied by the chart estimates. -/
theorem extension_capTest {d : ℕ} (S : Set (Space (d+1))) (A : Finset ℝ)
    (W : ℝ → Set (Space (d+1))) (hW : ∀ a ∈ A, MeasurableSet (W a))
    (hfin : ∀ a ∈ A, (surfaceMeasure S) (W a) ≠ ⊤) (amp : ℝ) (x : Space (d+1)) :
    extension S (capTest A W amp) x =
      (amp : ℂ) * ∑ a ∈ A, ∫ ξ in W a, planeWave (fun i => x i) (fun i => ξ i)
        ∂(surfaceMeasure S) := by
  let F (ξ : Space (d+1)) := Complex.exp (((2 * Real.pi * ⟪ξ, x⟫_ℝ : ℝ) : ℂ) * Complex.I)
  have hc : Continuous F := by dsimp [F]; fun_prop
  have hp (a : ℝ) (ξ : Space (d+1)) :
      (W a).indicator (fun _ => (amp : ℂ)) ξ * F ξ =
        (W a).indicator (fun y => (amp : ℂ) * F y) ξ := by
    by_cases hz : ξ ∈ W a <;> simp [hz]
  have hi (a : ℝ) (ha : a ∈ A) :
      Integrable ((W a).indicator (fun ξ => (amp : ℂ) * F ξ)) (surfaceMeasure S) := by
    rw [integrable_indicator_iff (hW a ha)]
    have : IsFiniteMeasure ((surfaceMeasure S).restrict (W a)) :=
      ⟨by simpa using lt_top_iff_ne_top.mpr (hfin a ha)⟩
    apply (integrable_const ‖(amp : ℂ)‖).mono'
    · exact (continuous_const.mul hc).aestronglyMeasurable
    · filter_upwards with ξ
      simp [F, Complex.norm_exp]
  change ∫ ξ, (∑ a ∈ A, (W a).indicator (fun _ => (amp : ℂ)) ξ) * F ξ ∂(surfaceMeasure S) = _
  simp_rw [Finset.sum_mul, hp]
  rw [integral_finsetSum A hi, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [integral_indicator (hW a ha), integral_const_mul]
  simp_rw [planeWave_euclidean]
  rfl

/-- Frequency after the modulation indexed by (b,τ). The spatial coordinate
and time coordinate may be specified in any order. -/
def shiftedFrequency {n : ℕ} (j k : Fin n) (h : ℝ) (ζ : ℝ × ℝ) (ξ : Space n) :
    Fin n → ℝ := fun i => ξ i + (if i = j then h * ζ.1 else 0) +
      (if i = k then h ^ 2 * ζ.2 else 0)

theorem planeWave_shifted {n : ℕ} (j k : Fin n) (h : ℝ) (x ξ : Space n) (ζ : ℝ × ℝ) :
    planeWave (fun i => x i) (shiftedFrequency j k h ζ ξ) =
      planeWave (fun i => x i) (fun i => ξ i) * (𝐞 (h * ζ.1 * x j + h ^ 2 * ζ.2 * x k) : ℂ) := by
  rw [planeWave_dot, planeWave_dot, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [shiftedFrequency, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Passing from the product of the cap extension and the finite modulation sum
to a single family of packets indexed by (a,ζ). This is a pointwise identity
on physical space. -/
theorem modulated_cap_extension {d : ℕ} (S : Set (Space (d+1))) (A : Finset ℝ)
    (B : Finset (ℝ × ℝ)) (j k : Fin (d+1)) (h amp : ℝ)
    (W : ℝ → Set (Space (d+1))) (hW : ∀ a ∈ A, MeasurableSet (W a))
    (hfin : ∀ a ∈ A, (surfaceMeasure S) (W a) ≠ ⊤) (x : Space (d+1)) :
    extension S (capTest A W amp) x * ∑ ζ ∈ B, (𝐞 (h * ζ.1 * x j + h ^ 2 * ζ.2 * x k) : ℂ) =
      (amp : ℂ) * ∑ p ∈ A ×ˢ B, ∫ ξ in W p.1,
        planeWave (fun i => x i) (shiftedFrequency j k h p.2 ξ) ∂(surfaceMeasure S) := by
  rw [extension_capTest S A W hW hfin amp x, mul_assoc, Finset.sum_mul_sum, Finset.sum_product]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  refine Finset.sum_congr rfl (fun ζ hζ => ?_)
  simp_rw [planeWave_shifted, integral_mul_const]

/-- Pull the frequency map across the Fourier pairing using its adjoint. -/
theorem planeWave_linear {n : ℕ} (L : Space n →L[ℝ] Space n) (x ξ : Space n) :
    planeWave (fun i => x i) (fun i => L ξ i) =
      planeWave (fun i => L.adjoint x i) (fun i => ξ i) := by
  rw [planeWave_euclidean, planeWave_euclidean, ContinuousLinearMap.adjoint_inner_right]

theorem modulated_cap_extension_linear {d : ℕ} (S : Set (Space (d+1))) (A : Finset ℝ)
    (L : Space (d+1) →L[ℝ] Space (d+1)) (B : Finset (ℝ × ℝ)) (j k : Fin (d+1)) (h amp : ℝ)
    (W : ℝ → Set (Space (d+1))) (hW : ∀ a ∈ A, MeasurableSet (W a))
    (hfin : ∀ a ∈ A, (surfaceMeasure S) (W a) ≠ ⊤) (x : Space (d+1)) :
    extension S (capTest A W amp) (L.adjoint x) * ∑ ζ ∈ B, (𝐞 (h * ζ.1 * x j + h ^ 2 * ζ.2 * x k) : ℂ) =
      (amp : ℂ) * ∑ p ∈ A ×ˢ B, ∫ ξ in W p.1,
        planeWave (fun i => x i) (shiftedFrequency j k h p.2 (L ξ)) ∂(surfaceMeasure S) := by
  rw [extension_capTest S A W hW hfin amp (L.adjoint x), mul_assoc, Finset.sum_mul_sum, Finset.sum_product]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  refine Finset.sum_congr rfl (fun ζ hζ => ?_)
  simp_rw [planeWave_shifted, planeWave_linear, integral_mul_const]

/-- Lemma 3.4 for the actual cap test and physical weight. The remaining
geometric inputs are finite patch areas at least V and the 1/3 phase bound
on the resonant pairs. The means of obtaining them (choice of chart, cube
centres and scales) are independent of this integral inequality. -/
theorem cap_weightedMass_lower_linear {d : ℕ} (S : Set (Space (d+1))) (A : Finset ℝ)
    (L : Space (d+1) →L[ℝ] Space (d+1)) (B : Finset (ℝ × ℝ)) (j k : Fin (d+1)) (h amp Y T V : ℝ)
    (hY : 0 < Y) (hT : 0 < T) (hV : 0 ≤ V)
    (W : ℝ → Set (Space (d+1))) (hW : ∀ a ∈ A, MeasurableSet (W a))
    (hfin : ∀ a ∈ A, (surfaceMeasure S) (W a) ≠ ⊤)
    (harea : ∀ a ∈ A, V ≤ (surfaceMeasure S).real (W a))
    (hphase : ∀ p ∈ A ×ˢ B, ∀ q ∈ A ×ˢ B, parabolicSum p = parabolicSum q →
      ∀ ξ ∈ W p.1, ∀ ξ' ∈ W q.1, ∀ i, |(if i = k then T else Y) *
        (shiftedFrequency j k h p.2 (L ξ) i - shiftedFrequency j k h q.2 (L ξ') i)| ≤ 1/3) :
    ENNReal.ofReal (amp ^ 2 * ((energy A B : ℝ) * ((∏ i : Fin (d+1),
      (if i = k then T else Y) / 4) * V ^ 2))) ≤
        weightedMass (fun x => extension S (capTest A W amp) (L.adjoint x)) (counterWeight B j k h Y T) := by
  classical
  let σ := surfaceMeasure S
  let μ (a : ℝ) := if a ∈ A then σ.restrict (W a) else 0
  have (a : ℝ) : IsFiniteMeasure (μ a) := by
    by_cases ha : a ∈ A
    · exact ⟨by simpa [μ, ha, σ] using lt_top_iff_ne_top.mpr (hfin a ha)⟩
    · simp [μ, ha]; infer_instance
  let scale (i : Fin (d+1)) := if i = k then T else Y
  have hs (i) : 0 < scale i := by dsimp [scale]; split <;> assumption
  let ω (p : ℝ × ℝ × ℝ) := fun z : Space (d+1) => shiftedFrequency j k h p.2 (L z)
  have hm (p) (_ : p ∈ A ×ˢ B) : Measurable (ω p) := by
    apply Measurable.of_eval
    intro i
    dsimp [ω, shiftedFrequency]
    fun_prop
  have hmass := packet_mass_ge_energy A B μ scale hs ω hm V hV
    (fun a ha => by simpa [μ, ha, σ, measureReal_def] using harea a ha)
  have hph (p) (hp : p ∈ A ×ˢ B) (q) (hq : q ∈ A ×ˢ B) (he : parabolicSum p = parabolicSum q) :
      ∀ᵐ zz ∂((μ p.1).prod (μ q.1)), ∀ i, |scale i * (ω p zz.1 i - ω q zz.2 i)| ≤ 1/3 := by
    have hpA := (Finset.mem_product.mp hp).1
    have hqA := (Finset.mem_product.mp hq).1
    have h₁ : ∀ᵐ ξ ∂(μ p.1), ξ ∈ W p.1 := by
      simpa only [μ, ite_eq_left hpA] using ae_restrict_mem (μ := σ) (hW _ hpA)
    have h₂ : ∀ᵐ ξ ∂(μ q.1), ξ ∈ W q.1 := by
      simpa only [μ, ite_eq_left hqA] using ae_restrict_mem (μ := σ) (hW _ hqA)
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h₁, Measure.quasiMeasurePreserving_snd.ae h₂]
      with zz hz hz'
    exact hphase p hp q hq he _ hz _ hz'
  specialize hmass hph
  let P (x : Fin (d+1) → ℝ) :=
    (∏ i, tent (x i / scale i)) *
      ‖∑ p ∈ A ×ˢ B, ∫ z, planeWave x (ω p z) ∂(μ p.1)‖ ^ 2
  let g := fun x : Space (d+1) => extension S (capTest A W amp) (L.adjoint x)
  let w := counterWeight B j k h Y T
  let G (x : Space (d+1)) := ‖g x‖ ^ 2 * w x
  have hpoint (x : Space (d+1)) : G x = amp ^ 2 * P (fun i => x i) := by
    have hext := modulated_cap_extension_linear S A L B j k h amp W hW hfin x
    have hre (p) (hp : p ∈ A ×ˢ B) :
        μ p.1 = σ.restrict (W p.1) := by simp [μ, (Finset.mem_product.mp hp).1]
    have hsum : (∑ p ∈ A ×ˢ B, ∫ z, planeWave (fun i => x i) (ω p z) ∂(μ p.1)) =
        ∑ p ∈ A ×ˢ B, ∫ z in W p.1, planeWave (fun i => x i) (ω p z) ∂σ :=
      Finset.sum_congr rfl (fun p hp => by rw [hre p hp])
    dsimp only [G, w, counterWeight, P]
    rw [hsum]
    have hh := congrArg (fun z : ℂ => ‖z‖ ^ 2) hext
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hh
    dsimp only [g, scale, ω, σ]
    linarith only [congrArg (fun z : ℝ => (∏ i : Fin (d+1), tent (x i / (if i = k then T else Y))) * z) hh]
  have hreal : amp^2 * ((energy A B : ℝ) * ((∏ i, scale i / 4) * V^2)) ≤ ∫ x, G x := by
    have htrans := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (d+1))).integral_comp' P
    simp_rw [hpoint, integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg amp)
    exact hmass.trans_eq htrans.symm
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  by_cases hi : Integrable G
  · rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x =>
      mul_nonneg (sq_nonneg _) (counterWeight_nonneg _ _ _ _ _ _ _))]
    apply le_of_eq
    apply lintegral_congr
    intro x
    exact ENNReal.ofReal_mul (sq_nonneg _)
  · simp [integral_undef hi]

/-- The special case in the original physical coordinates. -/
theorem cap_weightedMass_lower {d : ℕ} (S : Set (Space (d+1))) (A : Finset ℝ)
    (B : Finset (ℝ × ℝ)) (j k : Fin (d+1)) (h amp Y T V : ℝ)
    (hY : 0 < Y) (hT : 0 < T) (hV : 0 ≤ V)
    (W : ℝ → Set (Space (d+1))) (hW : ∀ a ∈ A, MeasurableSet (W a))
    (hfin : ∀ a ∈ A, (surfaceMeasure S) (W a) ≠ ⊤)
    (harea : ∀ a ∈ A, V ≤ (surfaceMeasure S).real (W a))
    (hphase : ∀ p ∈ A ×ˢ B, ∀ q ∈ A ×ˢ B, parabolicSum p = parabolicSum q →
      ∀ ξ ∈ W p.1, ∀ ξ' ∈ W q.1, ∀ i, |(if i = k then T else Y) *
        (shiftedFrequency j k h p.2 ξ i - shiftedFrequency j k h q.2 ξ' i)| ≤ 1/3) :
    ENNReal.ofReal (amp ^ 2 * ((energy A B : ℝ) * ((∏ i : Fin (d+1),
      (if i = k then T else Y) / 4) * V ^ 2))) ≤
        weightedMass (extension S (capTest A W amp)) (counterWeight B j k h Y T) := by
  simpa only [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] using cap_weightedMass_lower_linear S A (ContinuousLinearMap.id ℝ _) B j k
    h amp Y T V hY hT hV W hW hfin harea (by exact hphase)

end MT
