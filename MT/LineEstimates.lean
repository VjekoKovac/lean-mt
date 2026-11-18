module

public import MT.OneDimensional
public import MT.XrayNorm
public import MT.SphereArea

/-! # The X-ray bound for the weight of Proposition 3.1 -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped FourierTransform Real ENNReal

namespace MT

/-- An interval cover of the τ-coordinates at slope zero. -/
theorem Configuration.card_le_three_mul {H L : ℝ} (Q : Configuration H L) (hH : 1 ≤ H)
    (hL : 0 ≤ L) : (Q.B.card : ℝ) ≤ 3 * H * L := by
  classical
  have hpos : 0 < H := by linarith
  let s (z : ℝ × ℝ) := ⌊(z.2+1)*H⌋₊
  let N := ⌊2*H⌋₊ + 1
  have hn (z) (hz : z ∈ Q.B) : s z < N := by
    have hτ := (abs_le.mp (Q.inBoxB z hz).2).2
    apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    nlinarith [mul_nonneg (sub_nonneg.mpr hτ) hpos.le]
  have hcount (n : ℕ) : ((Q.B.filter (fun z => s z = n)).card : ℝ) ≤ L := by
    apply le_trans _ (Q.strip 0 ((n:ℝ)/H-1))
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hzB, hzn⟩ := Finset.mem_filter.mp hz
    have hτ := (abs_le.mp (Q.inBoxB z hzB).2).1
    have hlo := Nat.floor_le (show 0 ≤ (z.2+1)*H by exact mul_nonneg (by linarith) hpos.le)
    have hhi := Nat.lt_floor_add_one ((z.2+1)*H)
    change ⌊(z.2+1)*H⌋₊ = n at hzn
    rw [hzn] at hlo hhi
    apply Finset.mem_filter.mpr
    refine ⟨hzB, ?_⟩
    simp only [mul_zero, zero_mul, sub_zero, mem_Icc]
    constructor
    · have := (div_le_iff₀ hpos).2 hlo
      linarith
    · have := (lt_div_iff₀ hpos).2 hhi
      rw [add_div, one_div] at this
      linarith
  have h := kernel_shell_sum Q.B N s (fun _ => 1) (fun _ => 1) L hn
    (fun n _ => hcount n) (by simp) (by simp)
  have hnR : (N : ℝ) ≤ 3*H := by
    have hf := Nat.floor_le (show 0 ≤ 2*H by positivity)
    dsimp [N]
    push_cast
    linarith
  calc
    _ ≤ L*N := by simpa using h
    _ ≤ L*(3*H) := mul_le_mul_of_nonneg_left hnR hL
    _ = _ := by ring

theorem tent_nonneg (x : ℝ) : 0 ≤ tent x := le_max_right _ _

theorem tent_le_one (x : ℝ) : tent x ≤ 1 :=
  max_le (by linarith [abs_nonneg x]) zero_le_one

@[fun_prop] theorem continuous_tent : Continuous tent := by unfold tent; fun_prop

theorem tent_integrable : Integrable tent := by
  apply continuous_tent.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro' (K := Icc (-1 : ℝ) 1) isCompact_Icc isClosed_Icc
  intro x hx
  have h : 1 ≤ |x| := by
    by_contra! hh
    exact hx ⟨(abs_lt.mp hh).1.le, (abs_lt.mp hh).2.le⟩
  exact max_eq_right (sub_nonpos.mpr h)

theorem integral_tent : ∫ x : ℝ, tent x = 1 := by
  have h := fourier_tent 0
  rw [Real.fourier_real_eq] at h
  have hc : (∫ x : ℝ, (tent x : ℂ)) = 1 := by simpa using h
  rw [integral_complex_ofReal] at hc
  exact_mod_cast hc

/-- The spatial frequency coordinate p and the time coordinate q of the chart.
Use q = Fin.last d in the coordinates of the paper. -/
def counterWeight {n : ℕ} (B : Finset (ℝ × ℝ)) (p q : Fin n) (h Y T : ℝ)
    (x : Space n) : ℝ :=
  (∏ i : Fin n, tent (x i / (if i = q then T else Y))) *
    ‖∑ z ∈ B, (𝐞 (h*z.1*x p + h^2*z.2*x q) : ℂ)‖ ^ 2

@[fun_prop] theorem continuous_counterWeight {n : ℕ} (B : Finset (ℝ × ℝ))
    (p q : Fin n) (h Y T : ℝ) : Continuous (counterWeight B p q h Y T) := by
  unfold counterWeight
  fun_prop

theorem counterWeight_nonneg {n : ℕ} (B : Finset (ℝ × ℝ)) (p q : Fin n) (h Y T : ℝ)
    (x : Space n) : 0 ≤ counterWeight B p q h Y T x :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => tent_nonneg _) (sq_nonneg _)

theorem counterWeight_at_zero {n : ℕ} (B : Finset (ℝ × ℝ)) (p q : Fin n) (h Y T : ℝ) :
    counterWeight B p q h Y T 0 = (B.card : ℝ)^2 := by
  simp [counterWeight, tent]

/-- Enlarge the closed support box to an open ball of radius (√(d+1)+1)T. -/
theorem admissible_counterWeight {d : ℕ} (B : Finset (ℝ × ℝ))
    (p q : Fin (d+1)) {h Y T : ℝ} (hY : 0 < Y) (hYT : Y ≤ T) :
    AdmissibleWeight ((Real.sqrt (d+1 : ℝ) + 1)*T) (counterWeight B p q h Y T) := by
  have hT := hY.trans_le hYT
  refine ⟨counterWeight_nonneg B p q h Y T, (continuous_counterWeight B p q h Y T).locallyIntegrable, ?_⟩
  apply Set.Subset.trans _ (Metric.closedBall_subset_ball (show
    Real.sqrt (d+1 : ℝ)*T < (Real.sqrt (d+1 : ℝ)+1)*T by nlinarith))
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  change counterWeight B p q h Y T x ≠ 0 at hx
  have hxcoord (i : Fin (d+1)) : |x i| ≤ T := by
    let D := if i = q then T else Y
    have hD : 0 < D := by dsimp [D]; split <;> assumption
    have hDT : D ≤ T := by dsimp [D]; split <;> first | assumption | rfl
    by_contra! h_large
    have hbad : tent (x i/D) = 0 := by
      apply max_eq_right
      rw [abs_div, abs_of_pos hD]
      have := (le_div_iff₀ hD).2 (by linarith : 1*D ≤ |x i|)
      linarith
    apply hx
    unfold counterWeight
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hbad, zero_mul]
  rw [Metric.mem_closedBall, dist_zero_right, ← Real.sqrt_sq (norm_nonneg x),
    EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ Real.sqrt (∑ _i : Fin (d+1), T^2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum (fun i _ => sq_le_sq.mpr (by simpa [abs_of_pos hT] using hxcoord i))
    _ = _ := by
      simp [Real.sqrt_mul (show 0 ≤ (d+1:ℝ) by positivity), Real.sqrt_sq hT.le]

private theorem retain_tent {n : ℕ} (B : Finset (ℝ × ℝ)) (p q i : Fin n) (h Y T : ℝ)
    (x : Space n) :
    counterWeight B p q h Y T x ≤ tent (x i / (if i = q then T else Y)) *
      ‖∑ z ∈ B, (𝐞 (h*z.1*x p + h^2*z.2*x q) : ℂ)‖ ^ 2 := by
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hh := Finset.prod_le_prod_of_subset_of_le_one₀
    (s := {i}) (t := Finset.univ) (f := fun j => tent (x j / (if j = q then T else Y)))
    (Finset.subset_univ _) (fun _ _ => tent_nonneg _) (fun _ _ _ => tent_le_one _)
  simpa using hh

private theorem char_sum_le (B : Finset (ℝ × ℝ)) (φ : ℝ × ℝ → ℝ) :
    ‖∑ z ∈ B, (𝐞 (φ z) : ℂ)‖ ^ 2 ≤ (B.card : ℝ)^2 := by
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact (norm_sum_le _ _).trans (by simp)

private theorem large_coordinate {n : ℕ} (v : Space n) (h : ‖v‖ = 1) :
    ∃ i : Fin n, (1:ℝ) ≤ n * |v i| := by
  by_contra! hsmall
  have hsq (i : Fin n) : v i ^ 2 ≤ |v i| := by
    have hi := PiLp.norm_apply_le v i
    rw [h, Real.norm_eq_abs] at hi
    calc
      v i ^ 2 = |v i| * |v i| := by rw [← sq, sq_abs]
      _ ≤ _ := mul_le_of_le_one_right (abs_nonneg _) hi
  have hn : n ≠ 0 := by
    intro hz
    subst n
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv] at h
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  have hs : ∑ i : Fin n, (v i)^2 < ∑ _i : Fin n, (1:ℝ)/n :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
      (hsq i).trans_lt ((lt_div_iff₀ hnR).2 (by simpa [mul_comm] using hsmall i))
  rw [← EuclideanSpace.real_norm_sq_eq, h] at hs
  simp [ne_of_gt hnR] at hs

private theorem time_frequency_bound {H L T h : ℝ} (Q : Configuration H L) (hH : 0 < H)
    (hh : 0 < h) (hT : T*h^2 = H) (m t : ℝ) :
    ((Q.B.filter fun z => h*z.1*m + h^2*z.2 ∈ Icc t (t+T⁻¹)).card : ℝ) ≤ L := by
  have hs : h^2 ≠ 0 := by positivity
  have hTpos : 0 < T := by nlinarith [sq_pos_of_pos hh]
  apply le_trans _ (Q.strip (-m/(2*h)) (t/h^2))
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzB, hlo, hhi⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨hzB, ?_⟩
  have hf : (z.2 - 2*(-m/(2*h))*z.1)*h^2 = h*z.1*m + h^2*z.2 := by
    field_simp; ring
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < h^2)).2
    rwa [hf]
  · have he : t/h^2 + H⁻¹ = (t+T⁻¹)/h^2 := by
      rw [← hT]; field_simp
    rw [he]
    exact (le_div_iff₀ (by positivity : 0 < h^2)).2 (hf.trans_le hhi)

private theorem time_integral_bound {H L T h : ℝ} (Q : Configuration H L) (hH : 0 < H)
    (hh : 0 < h) (hT : T*h^2 = H) (hL : 0 ≤ L) (b m : ℝ) :
    (∫ t : ℝ, tent (t/T) *
      ‖∑ z ∈ Q.B, (𝐞 (h*z.1*(b+m*t) + h^2*z.2*t) : ℂ)‖ ^ 2) ≤ 12*T*L*Q.B.card := by
  let c (z : ℝ × ℝ) : ℂ := 𝐞 (h*z.1*b)
  let ω (z : ℝ × ℝ) := h*z.1*m + h^2*z.2
  have hTpos : 0 < T := by nlinarith [sq_pos_of_pos hh]
  have he (t : ℝ) (z : ℝ × ℝ) :
      (𝐞 (h*z.1*(b+m*t) + h^2*z.2*t) : ℂ) = c z * (𝐞 (t*ω z) : ℂ) := by
    dsimp [ω,c]
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [he]
  exact tent_large_sieve Q.B ω c hTpos hL (time_frequency_bound Q hH hh hT m)
    (fun _ _ => Circle.norm_coe _)

private theorem integrable_scaled_tent {D : ℝ} (hD : 0 < D) :
    Integrable (fun t : ℝ => tent (t/D)) := by
  simpa only [div_eq_mul_inv] using tent_integrable.comp_mul_right' (inv_ne_zero hD.ne')

private theorem integrable_time_sum {H L T h : ℝ} (Q : Configuration H L) (hT : 0 < T)
    (b m : ℝ) :
    Integrable (fun t : ℝ => tent (t/T) *
      ‖∑ z ∈ Q.B, (𝐞 (h*z.1*(b+m*t) + h^2*z.2*t) : ℂ)‖ ^ 2) := by
  apply integrable_of_le_of_le (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall (fun t => mul_nonneg (tent_nonneg _) (sq_nonneg _)))
    (Filter.Eventually.of_forall (fun t => mul_le_mul_of_nonneg_left
      (char_sum_le Q.B (fun z => h*z.1*(b+m*t) + h^2*z.2*t)) (tent_nonneg _)))
    (integrable_zero ..) ((integrable_scaled_tent hT).mul_const _)

/-- Lemma 3.5 with explicit surface-coordinate constant. The test weight is the
actual finite product of tents times the squared exponential sum. The index p
selects the curved spatial direction and q the time coordinate. The scale
assumptions hold for T = H/h², Y = H/h and hH ≤ 1. -/
theorem counterWeight_line_bound {d : ℕ} {H L T Y h : ℝ} (Q : Configuration H L)
    (p q : Fin (d+1)) (hH : 1 ≤ H) (hL : 0 ≤ L) (hh : 0 < h) (hY : 0 < Y)
    (hT : 0 < T) (hscaleT : T*h^2 = H) (hscaleY : Y*H ≤ T)
    (v y : Space (d+1)) (hunit : ‖v‖ = 1) :
    Integrable (fun s : ℝ => counterWeight Q.B p q h Y T (y+s•v)) ∧
    (∫ s : ℝ, counterWeight Q.B p q h Y T (y+s•v)) ≤
      12*(d+1 : ℝ)*T*L*Q.B.card := by
  let n : ℝ := d+1
  obtain ⟨i, hi⟩ := large_coordinate v hunit
  push_cast at hi
  have hv0 : v i ≠ 0 := by intro hv; norm_num [hv] at hi
  have hinv : |(v i)⁻¹| ≤ n := by
    rw [abs_inv, ← one_div]
    exact (div_le_iff₀ (abs_pos.mpr hv0)).2 hi
  let line (u : ℝ) := y + ((u-y i)/v i) • v
  let G (u : ℝ) := counterWeight Q.B p q h Y T (line u)
  have hcoord (u : ℝ) : line u i = u := by
    change y i + ((u-y i)/v i)*(v i) = u
    field_simp
    ring
  have hback (s : ℝ) : line (y i+s * v i) = y+s•v := by
    dsimp [line]
    rw [show (y i+s*v i-y i)/v i = s by field_simp; ring]
  let D := if i = q then T else Y
  have hD : 0 < D := by dsimp [D]; split <;> assumption
  have hmajor (u : ℝ) : G u ≤ tent (u/D)*(Q.B.card : ℝ)^2 := by
    calc
      _ ≤ _ := retain_tent Q.B p q i h Y T (line u)
      _ ≤ _ := by
        rw [hcoord]
        exact mul_le_mul_of_nonneg_left (char_sum_le Q.B _) (tent_nonneg _)
  have hzero (u : ℝ) : 0 ≤ G u := counterWeight_nonneg _ _ _ _ _ _ _
  have hGI : Integrable G := by
    apply integrable_of_le_of_le (Continuous.aestronglyMeasurable (by dsimp [G,line]; fun_prop))
      (Filter.Eventually.of_forall hzero) (Filter.Eventually.of_forall hmajor)
      (integrable_zero ..) ((integrable_scaled_tent hD).mul_const _)
  have hGsum : ∫ u, G u ≤ 12*T*L*Q.B.card := by
    by_cases hiq : i = q
    · subst i
      let b := y p - y q * (v p / v q)
      let m := v p / v q
      have hsp (u : ℝ) : line u p = b+m*u := by
        change y p + ((u-y q)/v q) * v p = _
        dsimp [b,m]
        ring
      have htime (u : ℝ) : G u ≤ tent (u/T) *
          ‖∑ z ∈ Q.B, (𝐞 (h*z.1*(b+m*u) + h^2*z.2*u) : ℂ)‖ ^ 2 := by
        have hh := retain_tent Q.B p q q h Y T (line u)
        simpa only [hcoord, ite_true, hsp] using hh
      exact (integral_mono hGI (integrable_time_sum Q hT b m) htime).trans
        (time_integral_bound Q (by linarith) hh hscaleT hL b m)
    · have hcard := Q.card_le_three_mul hH hL
      have hbase : Y*(Q.B.card : ℝ) ≤ 3*T*L := calc
        _ ≤ Y * (3*H*L) := mul_le_mul_of_nonneg_left hcard hY.le
        _ = 3*(Y*H)*L := by ring
        _ ≤ _ := by gcongr
      have hd : D = Y := by simp [D, hiq]
      calc
        _ ≤ ∫ u : ℝ, tent (u/D)*(Q.B.card : ℝ)^2 :=
          integral_mono hGI ((integrable_scaled_tent hD).mul_const _) hmajor
        _ = Y*(Q.B.card : ℝ)^2 := by
          rw [integral_mul_const, Measure.integral_comp_div tent D,
            abs_of_pos hD, smul_eq_mul, integral_tent, hd, mul_one]
        _ = (Y*Q.B.card)*Q.B.card := by ring
        _ ≤ (3*T*L)*Q.B.card := mul_le_mul_of_nonneg_right hbase (by positivity)
        _ ≤ _ := by gcongr; norm_num
  have hfn : (fun s : ℝ => counterWeight Q.B p q h Y T (y+s•v)) =
      fun s : ℝ => G (y i+s*v i) := funext (fun s => by dsimp [G]; rw [hback])
  rw [hfn]
  refine ⟨(hGI.comp_add_left (y i)).comp_mul_right' hv0, ?_⟩
  calc
    _ = |(v i)⁻¹| • ∫ u : ℝ, G (y i+u) :=
      Measure.integral_comp_mul_right (fun u => G (y i+u)) (v i)
    _ = |(v i)⁻¹| * ∫ u : ℝ, G u := by rw [integral_add_left_eq_self]; rfl
    _ ≤ n*(12*T*L*Q.B.card) :=
      mul_le_mul hinv hGsum (integral_nonneg hzero) (by dsimp [n]; positivity)
    _ = _ := by dsimp [n]; ring

/-- The X-ray norm bound in Lemma 3.5 for the actual weight of the source. -/
theorem counterWeight_xrayNorm {d : ℕ} {H L T Y h : ℝ} (Q : Configuration H L)
    (p q : Fin (d+1)) (hH : 1 ≤ H) (hL : 0 ≤ L) (hh : 0 < h) (hY : 0 < Y)
    (hT : 0 < T) (hscaleT : T*h^2 = H) (hscaleY : Y*H ≤ T) :
    xrayNorm (counterWeight Q.B p q h Y T) ≤
      ENNReal.ofReal (12*(d+1 : ℝ)*T*L*Q.B.card) := by
  apply xrayNorm_le_of_line_bound (continuous_counterWeight Q.B p q h Y T) (counterWeight_nonneg Q.B p q h Y T)
  · intro v hv y
    exact (counterWeight_line_bound Q p q hH hL hh hY hT hscaleT hscaleY v y hv).1
  · intro v hv y
    exact (counterWeight_line_bound Q p q hH hL hh hY hT hscaleT hscaleY v y hv).2

/-- Nonempty B gives a strictly positive X-ray denominator. -/
theorem counterWeight_xrayNorm_pos {d : ℕ} (B : Finset (ℝ × ℝ)) (hB : B.Nonempty)
    (p q : Fin (d+1)) (h Y T : ℝ) : 0 < xrayNorm (counterWeight B p q h Y T) := by
  apply xrayNorm_pos (continuous_counterWeight B p q h Y T) _ (sphereArea_pos d)
  rw [counterWeight_at_zero]
  have hc := Finset.card_pos.mpr hB
  positivity

end MT
