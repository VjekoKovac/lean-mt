module

import MT.AnalyticTransfer
import MT.FieldProjection

/-! Independent type and axiom checks for Proposition 3.1 and the projection
in §4.4. This file imports the implementation and never imports Challenge. -/

open MT MeasureTheory
open scoped ENNReal

/-- Spell out the quantifier order and the radius without referring to
the name of the transfer predicate on the expected side of the test. -/
example : ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ (d : ℕ), 0 < d → ∀ S : Set (Space (d+1)),
    IsHypersurface β S → HasCurvature β S →
      ∃ κ b H₀ : ℝ, 0 < κ ∧ 0 < b ∧ 1 ≤ H₀ ∧
        ∀ H : ℝ, H₀ ≤ H → ∀ L : ℝ, 1 ≤ L → ∀ Q : Configuration H L,
          ENNReal.ofReal (b * ((energy Q.A Q.B : ℝ)/(L*Q.A.card*Q.B.card))) ≤
            localConstant S (κ*H^(1+2/β)) := analyticTransfer

#print axioms MT.GraphChart.frequencyCoordinates_point
#print axioms MT.graph_cap_weightedMass_lower
#print axioms MT.inverse_counterWeight_estimates
#print axioms MT.weightedMass_inverse_weight
#print axioms MT.analyticTransfer
#print axioms MT.Arithmetic.configuration_of_bounded_field_sets
