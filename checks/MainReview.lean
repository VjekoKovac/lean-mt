module

import Solution
import MT.Realization

/-! A separately written restatement of the theorem's quantifiers and supremum,
followed by a consequence giving actual integrable data and an admissible weight.
Each section starts with the full theorem in the solution environment. -/

open MT MeasureTheory Set
open scoped ENNReal InnerProductSpace

/-- Independent expansion of the graph hypotheses, normalized surface measure,
extension agreement, weighted numerator and all finiteness conditions. -/
example : ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ α : ℝ, 0 < α ∧
    ∀ (d : ℕ), 0 < d → ∀ S : Set (Space (d+1)),
      (∀ p ∈ S, ∃ g : GraphChart d, g.ValidFor β S ∧ p ∈ g.region) →
      (∃ g : GraphChart d, g.ValidFor β S ∧ ∃ u ∈ g.domain,
        g.point u ∈ g.region ∧ fderiv ℝ (fderiv ℝ g.height) u ≠ 0) →
      ∃ c R₀ : ℝ, 0 < c ∧ 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        let μ := (Measure.euclideanHausdorffMeasure d).restrict S
        let X := fun w : Space (d+1) → ℝ =>
          essSup (fun ν : Space (d+1) =>
            ⨆ (v : Space (d+1)) (_ : ⟪v,ν⟫_ℝ = 0), ∫⁻ t : ℝ, ENNReal.ofReal (w (v+t•ν)))
            ((Measure.euclideanHausdorffMeasure d).restrict (Metric.sphere 0 1))
        ∀ E : (Space (d+1) → ℂ) → Space (d+1) → ℂ,
        (∀ f, Integrable f μ → MemLp f 2 μ →
          ∀ᵐ x ∂volume, E f x = ∫ ξ, f ξ *
            Complex.exp (((2*Real.pi*⟪ξ,x⟫_ℝ : ℝ) : ℂ)*Complex.I) ∂μ) →
        ENNReal.ofReal (c*R^α) ≤ sSup {q | ∃ (f : Space (d+1) → ℂ) (w : Space (d+1) → ℝ),
          MemLp f 2 μ ∧ (∀ x, 0 ≤ w x) ∧ LocallyIntegrable w volume ∧
          tsupport w ⊆ Metric.ball 0 R ∧
          0 < (eLpNorm f 2 μ)^2 * X w ∧ (eLpNorm f 2 μ)^2 * X w < ⊤ ∧
          q = (∫⁻ x, ENNReal.ofReal (‖E f x‖^2) * ENNReal.ofReal (w x)) /
            ((eLpNorm f 2 μ)^2 * X w)} := by
  have hX {n : ℕ} (w : Space n → ℝ) :
      MT.xray w = (fun ν => ⨆ (v : Space n) (_ : ⟪v,ν⟫_ℝ = 0),
        ∫⁻ t : ℝ, ENNReal.ofReal (w (v+t•ν))) := rfl
  simpa only [PowerLoss, IsHypersurface, HasCurvature, hessian, AgreesOnCore, Filter.EventuallyEq, MT.extension,
    fullLocalConstant, ratios, AdmissibleWeight, weightedMass, denominator, xrayNorm, hX, surfaceMeasure,
    true_and, and_assoc] using MT.powerlossMT

/-- Consequence with actual integrable tests, no realization parameter and no
assumption that the supremum is attained. The constant may be halved. -/
example : ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ α : ℝ, 0 < α ∧
    ∀ (d : ℕ), 0 < d → ∀ S : Set (Space (d+1)),
      IsHypersurface β S → HasCurvature β S →
      ∃ b R₀ : ℝ, 0 < b ∧ 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        ∃ (f : Space (d+1) → ℂ) (w : Space (d+1) → ℝ),
          Integrable f (surfaceMeasure S) ∧ MemLp f 2 (surfaceMeasure S) ∧
          AdmissibleWeight R w ∧ 0 < denominator S f w ∧ denominator S f w < ⊤ ∧
          ENNReal.ofReal (b * R^α) < weightedMass (extension S f) w / denominator S f w := by
  intro β hβ hβ₁
  obtain ⟨α, hα, h⟩ := MT.powerlossMT β hβ hβ₁
  refine ⟨α, hα, ?_⟩
  intro d hd S hS hcurv
  obtain ⟨c, R₀, hc, hR₀, hfull⟩ := h d hd S hS hcurv
  refine ⟨c/2, R₀, half_pos hc, hR₀, ?_⟩
  intro R hR
  have hRpos : 0 < R := zero_lt_one.trans_le (hR₀.trans hR)
  have hpow : 0 < R^α := Real.rpow_pos_of_pos hRpos _
  have hlt : ENNReal.ofReal ((c/2)*R^α) < ENNReal.ofReal (c*R^α) :=
    (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc hpow)).mpr
      (mul_lt_mul_of_pos_right (half_lt_self hc) hpow)
  have hbound := (full_lower_bound_iff_integrable S R _).mp (hfull R hR)
  obtain ⟨q, ⟨f,w,hf,hf₂,hw,hden,hfinite,rfl⟩, hval⟩ :=
    lt_sSup_iff.mp (hlt.trans_le hbound)
  exact ⟨f,w,hf,hf₂,hw,hden,hfinite,hval⟩

#check MT.powerlossMT
