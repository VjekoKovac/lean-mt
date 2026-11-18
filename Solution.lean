module

public import MT.AnalyticTransfer
public import MT.ArithmeticAmplification
public import MT.Configuration
public import MT.Constant
public import MT.Transfer
public import MT.SeedPolynomial

/-! # Theorem 1.3 of arXiv:2611.22465v1
Section 5 combines the two propositions proved in the imported modules.
The independent Challenge is elaborated in a separate environment.
-/

@[expose] public section
noncomputable section

namespace MT

/-- The final implication of Section 5, including the choice of a *single*
exponent for all dimensions and surfaces at each β. -/
theorem powerLoss_of_transfer_and_amplification
    (transfer : AnalyticTransfer) (amplification : ArithmeticAmplification) : PowerLoss := by
  obtain ⟨C, hC, _, _, amplify⟩ := amplification
  have hC₀ : 0 ≤ C := by linarith
  apply powerLoss_of_core
  intro β hβ hβ₁
  refine ⟨paperExponent β C, paperExponent_pos hβ hC, ?_⟩
  intro d hd S hS hcurv
  obtain ⟨κ, b, H₀, hκ, hb, _, transferQ⟩ := transfer β hβ hβ₁ d hd S hS hcurv
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt H₀ hC
  have sample (n : ℕ) (hn : N ≤ n) :
      ENNReal.ofReal (b * (2 : ℝ) ^ (2 ^ n : ℕ)) ≤
        localConstant S (κ * C ^ ((1 + 2 / β) * (2 : ℝ) ^ n)) := by
    let k : ℕ := 2 ^ n
    obtain ⟨L, hL, _, Q, hgain⟩ := amplify n
    have hH : H₀ ≤ C ^ k :=
      hN.le.trans (pow_le_pow_right₀ hC.le (hn.trans n.lt_two_pow_self.le))
    have bound := (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hgain hb.le)).trans
      (transferQ (C ^ k) hH L hL Q)
    have hradius : (C ^ k) ^ (1 + 2 / β) = C ^ ((1 + 2 / β) * (2 : ℝ) ^ n) := by
      rw [← Real.rpow_natCast_mul hC₀, mul_comm]
      simp [k]
    simpa only [hradius] using bound
  obtain ⟨c, hc, R₀, _, hR⟩ := powerLoss_of_dyadic_samples
    (localConstant_mono S) hβ hC hκ hb sample
  exact ⟨c, max 1 R₀, hc, le_max_left _ _, fun R hRR => hR R ((le_max_right _ _).trans hRR)⟩

/-- The unconditional dimension-independent power loss for every eligible
hypersurface, at every sufficiently large real radius. -/
theorem powerlossMT : PowerLoss :=
  powerLoss_of_transfer_and_amplification analyticTransfer arithmeticAmplification

end MT
