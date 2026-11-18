module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Statement of the local MT power loss

Source: Cairo, Gottlieb Fenves, Kovač, Oliveira, Zakharov and Zhang,
arXiv:2611.22465v1, §1, Theorem 1.3. Independent challenge specification. The proof holes below are confined to this file.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace MT

/-- Euclidean space with its Euclidean norm and Lebesgue measure. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A height graph in rigid coordinates. Both the parameter domain and ambient
neighborhood are needed: other parts of the surface can lie outside the chart. -/
structure GraphChart (d : ℕ) where
  rigid : Space (d + 1) ≃ᵢ Space (d + 1)
  domain : Set (Space d)
  region : Set (Space (d + 1))
  height : Space d → ℝ

def GraphChart.point {d : ℕ} (g : GraphChart d) (u : Space d) : Space (d + 1) :=
  g.rigid (WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => u i) (g.height u)))

/-- On an open parameter domain, two total Fréchet derivatives give the Hessian;
the value is independent of how the height has been extended off that domain. -/
def hessian {d : ℕ} (φ : Space d → ℝ) (u : Space d) :=
  fderiv ℝ (fderiv ℝ φ) u

def GraphChart.ValidFor {d : ℕ} (g : GraphChart d) (β : ℝ)
    (S : Set (Space (d + 1))) : Prop :=
  IsOpen g.domain ∧ IsOpen g.region ∧
  S ∩ g.region = (g.point '' g.domain) ∩ g.region ∧
  ContDiffOn ℝ 2 g.height g.domain ∧
  ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ g.domain, ∀ y ∈ g.domain,
    ‖hessian g.height x - hessian g.height y‖ ≤ K * dist x y ^ β

def IsHypersurface {d : ℕ} (β : ℝ) (S : Set (Space (d + 1))) : Prop :=
  ∀ p ∈ S, ∃ g : GraphChart d, g.ValidFor β S ∧ p ∈ g.region

/-- At a point of a height graph, the coefficients of the second fundamental
form in graph coordinates are the Hessian times a nonzero normalizing scalar. -/
def HasCurvature {d : ℕ} (β : ℝ) (S : Set (Space (d + 1))) : Prop :=
  ∃ g : GraphChart d, g.ValidFor β S ∧ ∃ u ∈ g.domain,
    g.point u ∈ g.region ∧ hessian g.height u ≠ 0

/-- Mathlib's Euclidean-normalized d-dimensional Hausdorff area on the surface. -/
def surfaceMeasure {d : ℕ} (S : Set (Space (d + 1))) : Measure (Space (d + 1)) :=
  (Measure.euclideanHausdorffMeasure d).restrict S

/-- The positive-sign Fourier extension integral on absolutely integrable data. -/
def extension {d : ℕ} (S : Set (Space (d + 1))) (f : Space (d + 1) → ℂ)
    (x : Space (d + 1)) : ℂ :=
  ∫ ξ, f ξ * Complex.exp (((2 * Real.pi * ⟪ξ, x⟫_ℝ : ℝ) : ℂ) * Complex.I)
    ∂(surfaceMeasure S)

/-- In a unit direction ν, take the pointwise supremum over perpendicular
offsets. The caller restricts directions to the sphere with its area measure. -/
def xray {n : ℕ} (w : Space n → ℝ) (ν : Space n) : ℝ≥0∞ :=
  ⨆ (v : Space n) (_ : ⟪v, ν⟫_ℝ = 0),
    ∫⁻ t : ℝ, ENNReal.ofReal (w (v + t • ν))

def xrayNorm {d : ℕ} (w : Space (d + 1) → ℝ) : ℝ≥0∞ :=
  essSup (xray w) (surfaceMeasure (Metric.sphere (0 : Space (d + 1)) 1))

/-- Weights are pointwise representatives: restricting to a particular line
can distinguish weights that agree almost everywhere in ambient space. -/
def AdmissibleWeight {n : ℕ} (R : ℝ) (w : Space n → ℝ) : Prop :=
  (∀ x, 0 ≤ w x) ∧ LocallyIntegrable w volume ∧ tsupport w ⊆ Metric.ball 0 R

def weightedMass {n : ℕ} (g : Space n → ℂ) (w : Space n → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) * ENNReal.ofReal (w x)

def denominator {d : ℕ} (S : Set (Space (d + 1)))
    (f : Space (d + 1) → ℂ) (w : Space (d + 1) → ℝ) : ℝ≥0∞ :=
  (eLpNorm f 2 (surfaceMeasure S)) ^ 2 * xrayNorm w

/-- Ratios use finite positive denominators. Values of f off S do not enter its
L² norm or the integral. The additional predicate selects the test domain. -/
def ratios {d : ℕ} (S : Set (Space (d + 1))) (R : ℝ)
    (E : (Space (d + 1) → ℂ) → Space (d + 1) → ℂ)
    (test : (Space (d + 1) → ℂ) → (Space (d + 1) → ℝ) → Prop) : Set ℝ≥0∞ :=
  {q | ∃ f w, test f w ∧ MemLp f 2 (surfaceMeasure S) ∧ AdmissibleWeight R w ∧
    0 < denominator S f w ∧ denominator S f w < ⊤ ∧
    q = weightedMass (E f) w / denominator S f w}

/-- The constant tested on L¹ ∩ L², where the displayed extension integral
converges absolutely, with Borel weights so all line restrictions are measurable.
The continuous weights and integrable functions constructed in §3 belong to this class. -/
def localConstant {d : ℕ} (S : Set (Space (d + 1))) (R : ℝ) : ℝ≥0∞ :=
  sSup (ratios S R (extension S) (fun f w => Integrable f (surfaceMeasure S) ∧ Measurable w))

/-- The source supremum over the entire L² class, for a realization E of the
extension operator. It can take the value ∞. -/
def fullLocalConstant {d : ℕ} (S : Set (Space (d + 1))) (R : ℝ)
    (E : (Space (d + 1) → ℂ) → Space (d + 1) → ℂ) : ℝ≥0∞ :=
  sSup (ratios S R E (fun _ _ => True))

/-- On a noncompact surface arbitrary L² data need not be in L¹. Require the
chosen realization to agree with the integral on L¹ ∩ L². Almost-everywhere
agreement suffices because the numerator is integrated against w dx. -/
def AgreesOnCore {d : ℕ} (S : Set (Space (d + 1)))
    (E : (Space (d + 1) → ℂ) → Space (d + 1) → ℂ) : Prop :=
  ∀ f, Integrable f (surfaceMeasure S) → MemLp f 2 (surfaceMeasure S) →
    E f =ᵐ[volume] extension S f

/-- A lower bound for every sufficiently large real radius, with constants
allowed to depend on the surface. -/
def EventuallyPowerBound (α : ℝ) (C : ℝ → ℝ≥0∞) : Prop :=
  ∃ c R₀ : ℝ, 0 < c ∧ 1 ≤ R₀ ∧
    ∀ R : ℝ, R₀ ≤ R → ENNReal.ofReal (c * R ^ α) ≤ C R

/-- Theorem 1.3. The one exponent for β works in every dimension. The constants
c and R₀ are chosen before the realization E; only its values on integrable
tests will be needed. No global compactness, connectivity, orientation, or
Gaussian curvature assumption occurs here. -/
def PowerLoss : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 →
    ∃ α : ℝ, 0 < α ∧ ∀ (d : ℕ), 0 < d → ∀ S : Set (Space (d + 1)),
      IsHypersurface β S → HasCurvature β S →
      ∃ c R₀ : ℝ, 0 < c ∧ 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        ∀ E, AgreesOnCore S E →
          ENNReal.ofReal (c * R ^ α) ≤ fullLocalConstant S R E

/-- Radius monotonicity is a separately comparable milestone. -/
theorem localConstant_mono {d : ℕ} (S : Set (Space (d + 1))) :
    Monotone (localConstant S) := by sorry

/-- The target of the full comparison, corresponding to paper Theorem 1.3. -/
theorem powerlossMT : PowerLoss := by sorry

/-- One representation of a sum of a point on the parabola and a planar point. -/
def parabolicSum {K : Type*} [Semiring K] (p : K × (K × K)) : K × K :=
  (p.1 + p.2.1, p.1 ^ 2 + p.2.2)

/-- Ordered pairs of representations with the same sum, as in Section 3. -/
def energy {K : Type*} [Semiring K] (A : Finset K) (B : Finset (K × K)) : ℕ := by
  classical
  let T := A ×ˢ B
  exact ((T ×ˢ T).filter fun q => parabolicSum q.1 = parabolicSum q.2).card

/-- The box, separation and vertical strip conditions at scale H in Proposition 3.1.
Using closed intervals gives a uniform bound for all intervals of this length. -/
structure Configuration (H L : ℝ) where
  A : Finset ℝ
  B : Finset (ℝ × ℝ)
  nonemptyA : A.Nonempty
  nonemptyB : B.Nonempty
  inBoxA : ∀ a ∈ A, |a| ≤ 1
  inBoxB : ∀ z ∈ B, |z.1| ≤ 1 ∧ |z.2| ≤ 1
  separated : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → H⁻¹ ≤ |a - a'|
  strip : ∀ s u : ℝ, (((B.filter fun z =>
    z.2 - 2 * s * z.1 ∈ Set.Icc u (u + H⁻¹)).card : ℕ) : ℝ) ≤ L

/-- The exact ratio entering both propositions. -/
def Configuration.gain {H L : ℝ} (Q : Configuration H L) : ℝ :=
  (energy Q.A Q.B : ℝ) / (L * Q.A.card * Q.B.card)

/-- Proposition 4.1, including one absolute scale base and the exponential
upper bound on the strip occupancy. The public statement includes every
dyadic degree, even though Section 5 needs just an eventual tail. -/
def ArithmeticAmplification : Prop :=
  ∃ C : ℝ, 1 < C ∧ ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ,
    let k : ℕ := 2 ^ n
    ∃ L : ℝ, 1 ≤ L ∧ L ≤ Real.exp (b * k) ∧
      ∃ Q : Configuration (C ^ k) L, (2 : ℝ) ^ k ≤ Q.gain

/-- Proposition 3.1 for the integrable test functions the paper constructs.
The scale threshold, radius multiplier and comparison constant are uniform
over H, L and both finite sets for a fixed surface. -/
def AnalyticTransfer : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ (d : ℕ), 0 < d → ∀ S : Set (Space (d + 1)),
    IsHypersurface β S → HasCurvature β S →
    ∃ κ b H₀ : ℝ, 0 < κ ∧ 0 < b ∧ 1 ≤ H₀ ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ L : ℝ, 1 ≤ L → ∀ Q : Configuration H L,
        ENNReal.ofReal (b * Q.gain) ≤ localConstant S (κ * H ^ (1 + 2 / β))

/-- Independent specification of the Section 5 milestone. -/
theorem powerLoss_of_transfer_and_amplification
    (transfer : AnalyticTransfer) (amplification : ArithmeticAmplification) : PowerLoss := by sorry

end MT

namespace MT.Seed

/-- The two integer subset sums indexed by the same subset of the generators. -/
def seedPoint {m : ℕ} {R : Type*} [CommRing R] (a : Fin m → R)
    (s : Finset (Fin m)) : R × R :=
  (∑ i ∈ s, a i, ∑ i ∈ s, (a i)^2)

/-- Twice the signed area of the triangle with these three vertices. -/
def determinant {R : Type*} [CommRing R] (p q r : R × R) : R :=
  (p.1-r.1)*(q.2-r.2) - (q.1-r.1)*(p.2-r.2)

def tripleDet {m : ℕ} {R : Type*} [CommRing R] (a : Fin m → R)
    (s t u : Finset (Fin m)) : R :=
  determinant (seedPoint a s) (seedPoint a t) (seedPoint a u)

/-- Source lemma labelled `lemma:seednoncollinearity`.
The same choice of the integers must work for every triple. -/
theorem exists_bounded_seed (m : ℕ) (hm : 2 ≤ m) :
    ∃ a : Fin m → ℤ, (∀ i, 1 ≤ a i ∧ a i ≤ (2:ℤ)^(3*m)) ∧
      Function.Injective a ∧ Function.Injective (seedPoint a) ∧
      ∀ s t u : Finset (Fin m), s ≠ t → s ≠ u → t ≠ u → tripleDet a s t u ≠ 0 := by
  sorry

end MT.Seed
