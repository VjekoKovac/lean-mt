module

public import MT.NumberFieldDual
public import MT.BoxCutoffLattice

/-! # Translated boxes of algebraic integers in real embeddings

The Euclidean coordinate change is an isometry, so it preserves the covolume
and the geometric dual. We transport the finite box itself along the bijection
from the ring of integers to its lattice, retaining the cardinality exactly.
-/

@[expose] public section
noncomputable section
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open DedekindZeta.PoissonSummation
open scoped NumberField Classical InnerProductSpace
namespace MT.Arithmetic

variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

/-- For a totally real field the standard mixed-coordinate index is just the real places. -/
def realIndex : InfinitePlace K ≃ index K where
  toFun v := Sum.inl ⟨v, IsTotallyReal.isReal v⟩
  invFun := Sum.elim Subtype.val (fun v => False.elim
    ((not_isReal_iff_isComplex.mpr v.1.2) (IsTotallyReal.isReal v.1.1)))
  left_inv _ := rfl
  right_inv := by
    rintro (v | ⟨v,j⟩)
    · rfl
    · exact False.elim ((not_isReal_iff_isComplex.mpr v.2) (IsTotallyReal.isReal v.1))

/-- Real coordinates with the Euclidean metric of lattice Poisson summation. -/
def realCoordinates : euclidean.mixedSpace K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (InfinitePlace K) :=
  ((euclidean.stdOrthonormalBasis K).reindex (realIndex K).symm).repr

theorem realCoordinates_apply (w : euclidean.mixedSpace K) (v : InfinitePlace K) :
    realCoordinates K w v = ((euclidean.toMixed K) w).1 ⟨v, IsTotallyReal.isReal v⟩ := by
  rw [realCoordinates, OrthonormalBasis.repr_reindex, ← OrthonormalBasis.coe_toBasis_repr_apply]
  change _ = (stdBasis K).repr (euclidean.toMixed K w) (Sum.inl ⟨v, _⟩)
  rw [← euclidean.stdOrthonormalBasis_map_eq, Module.Basis.map_repr]
  rfl

/-- The full lattice of algebraic integers in the standard real coordinates. -/
abbrev realIntegerLattice : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K)) :=
  ZLattice.comap ℝ (euclidean.integerLattice K)
    (realCoordinates K).symm.toContinuousLinearEquiv.toLinearMap

/-- The integral elements, bijectively identified with their lattice points. -/
def integerLatticeEquiv : 𝓞 K ≃ realIntegerLattice K := by
  let f (a : 𝓞 K) : realIntegerLattice K :=
    ⟨realCoordinates K (minkowskiVector (a : K)), by
      change (realCoordinates K).symm ((realCoordinates K) _) ∈ euclidean.integerLattice K
      simpa using minkowskiVector_mem a⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    have h₁ := (realCoordinates K).injective (congrArg Subtype.val h)
    have h₂ := (euclidean.toMixed K).symm.injective h₁
    exact Subtype.ext (mixedEmbedding_injective K h₂)
  · intro y
    have h := y.property
    change ∃ a : 𝓞 K, mixedEmbedding K (a : K) =
      euclidean.toMixed K ((realCoordinates K).symm y) at h
    obtain ⟨a, ha⟩ := h
    exact ⟨a, Subtype.ext ((realCoordinates K).eq_symm_apply.mp
      ((euclidean.toMixed K).symm_apply_eq.mpr ha))⟩

theorem integerLatticeEquiv_apply (a : 𝓞 K) (v : InfinitePlace K) :
    ((integerLatticeEquiv K a : realIntegerLattice K) : EuclideanSpace ℝ (InfinitePlace K)) v =
      embedding_of_isReal (IsTotallyReal.isReal v) (a : K) := by
  change realCoordinates K (minkowskiVector (a : K)) v = _
  rw [realCoordinates_apply]
  simp [minkowskiVector]

def latticeToField : realIntegerLattice K ↪ K :=
  (integerLatticeEquiv K).symm.toEmbedding.trans (Function.Embedding.subtype _)

/-- Integral field elements in an axis-parallel box with individually prescribed half-widths. -/
def fieldRect (c M : InfinitePlace K → ℝ) : Finset K :=
  (BoxCutoff.latticeBox (realIntegerLattice K) M c).map (latticeToField K)

@[simp] theorem mem_fieldRect (c M : InfinitePlace K → ℝ) (x : K) :
    x ∈ fieldRect K c M ↔ IsIntegral ℤ x ∧
      ∀ i : InfinitePlace K, |embedding_of_isReal (IsTotallyReal.isReal i) x - c i| ≤ M i := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp h
    let a := (integerLatticeEquiv K).symm p
    have ha : integerLatticeEquiv K a = p := (integerLatticeEquiv K).apply_symm_apply p
    refine ⟨a.property, fun i => ?_⟩
    change |embedding_of_isReal _ (a : K) - c i| ≤ M i
    rw [← integerLatticeEquiv_apply K a i, ha]
    exact (BoxCutoff.mem_latticeBox _ M c p).mp hp i
  · rintro ⟨hx, h⟩
    let a : 𝓞 K := ⟨x, hx⟩
    refine Finset.mem_map.mpr ⟨integerLatticeEquiv K a, ?_, ?_⟩
    · apply (BoxCutoff.mem_latticeBox _ M c _).mpr
      intro i
      rw [integerLatticeEquiv_apply]
      exact h i
    · change (((integerLatticeEquiv K).symm (integerLatticeEquiv K a)) : K) = x
      exact congrArg (fun z : 𝓞 K => (z : K)) ((integerLatticeEquiv K).symm_apply_apply a)

/-- Integral field elements in a translated cube of half-width r. -/
def fieldBox (c : InfinitePlace K → ℝ) (r : ℝ) : Finset K := fieldRect K c (fun _ => r)

@[simp] theorem mem_fieldBox (c : InfinitePlace K → ℝ) (r : ℝ) (x : K) :
    x ∈ fieldBox K c r ↔ IsIntegral ℤ x ∧
      ∀ i : InfinitePlace K, |embedding_of_isReal (IsTotallyReal.isReal i) x - c i| ≤ r :=
  mem_fieldRect K c _ x

theorem card_places_eq_degree : Fintype.card (InfinitePlace K) = Module.finrank ℚ K := by
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, ← card_add_two_mul_card_eq_rank,
    nrComplexPlaces_eq_zero_iff.mpr (inferInstance : IsTotallyReal K)]

private theorem realIntegerLattice_covolume :
    ZLattice.covolume (realIntegerLattice K) = Real.sqrt |(discr K : ℝ)| := by
  rw [realIntegerLattice, ZLattice.covolume_comap _ volume volume (realCoordinates K).symm.measurePreserving,
    minkowski_covolume K]

private theorem realIntegerLattice_gap (x : realIntegerLattice K) (hx : x ≠ 0) :
    1 ≤ ∏ v, |(x : EuclideanSpace ℝ (InfinitePlace K)) v| := by
  let a := (integerLatticeEquiv K).symm x
  have ha : integerLatticeEquiv K a = x := (integerLatticeEquiv K).apply_symm_apply x
  have hna : a ≠ 0 := by
    intro h
    apply hx
    rw [← ha, h]
    apply Subtype.ext
    change realCoordinates K (minkowskiVector ((0 : 𝓞 K) : K)) = 0
    simp [minkowskiVector]
  rw [← ha]
  simp only [integerLatticeEquiv_apply, ← Real.norm_eq_abs, norm_embedding_of_isReal]
  simpa only [← prod_eq_abs_norm, IsTotallyReal.mult_eq, pow_one] using one_le_abs_rational_norm hna

private theorem realIntegerLattice_dual_gap (x : dualLattice (realIntegerLattice K)) (hx : x ≠ 0) :
    1 / ((discr K).natAbs : ℝ) ≤ ∏ v, |(x : EuclideanSpace ℝ (InfinitePlace K)) v| := by
  let e := realCoordinates K
  let w := e.symm (x : EuclideanSpace ℝ (InfinitePlace K))
  have hw : w ∈ dualLattice (euclidean.integerLattice K) := by
    apply mem_dualLattice.mpr
    intro y hy
    have hye : e y ∈ realIntegerLattice K := by
      change e.symm (e y) ∈ euclidean.integerLattice K
      simpa using hy
    have h := mem_dualLattice.mp x.property (e y) hye
    rwa [← e.inner_map_map w y, show e w = x from e.apply_symm_apply _]
  have hn : w ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    calc
      (x : EuclideanSpace ℝ (InfinitePlace K)) = e w := (e.apply_symm_apply _).symm
      _ = 0 := by rw [h, map_zero]
  have h := minkowski_dual_coordinate_gap hw hn
  simpa only [← realCoordinates_apply, ← show e = realCoordinates K from rfl,
    w, LinearIsometryEquiv.apply_symm_apply] using h

/-- Lower bound including the exact covolume. -/
theorem fieldRect_lower (c M : InfinitePlace K → ℝ) {D : ℝ} (hD : 0 < D)
    (hdisc : ((discr K).natAbs : ℝ) ≤ D ^ Module.finrank ℚ K)
    (hM : ∀ v, 48 * BoxCutoff.constant * D ≤ M v) :
    (∏ v, M v) / (2 * Real.sqrt |(discr K : ℝ)|) ≤ (fieldRect K c M).card := by
  have h := BoxCutoff.lattice_box_lower (Classical.arbitrary (InfinitePlace K))
    (realIntegerLattice K) M c D hD hM (fun x hx => ?_)
  · simpa only [fieldRect, Finset.card_map, realIntegerLattice_covolume] using h
  · rw [card_places_eq_degree]
    exact (one_div_le_one_div_of_le (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)) hdisc).trans
      (realIntegerLattice_dual_gap K x hx)

/-- Upper bound uniform in the discriminant, from the field norm. -/
theorem fieldRect_upper (c M : InfinitePlace K → ℝ) (hM : ∀ v, 0 < M v) :
    ((fieldRect K c M).card : ℝ) ≤ 1 + 2 ^ Module.finrank ℚ K * ∏ v, M v := by
  simpa only [fieldRect, Finset.card_map, card_places_eq_degree] using
    BoxCutoff.lattice_box_upper (Classical.arbitrary (InfinitePlace K)) (realIntegerLattice K)
      M c hM (realIntegerLattice_gap K)

/-- Lower bound for a translated cube of integral field elements. -/
theorem fieldBox_lower (c : InfinitePlace K → ℝ) {D r : ℝ} (hD : 0 < D)
    (hdisc : ((discr K).natAbs : ℝ) ≤ D ^ Module.finrank ℚ K)
    (hr : 48 * BoxCutoff.constant * D ≤ r) :
    r ^ Module.finrank ℚ K / (2 * Real.sqrt ((discr K).natAbs : ℝ)) ≤ (fieldBox K c r).card := by
  have habs : ((discr K).natAbs : ℝ) = |(discr K : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  simpa [fieldBox, card_places_eq_degree, habs] using fieldRect_lower K c (fun _ => r) hD hdisc (fun _ => hr)

/-- Upper bound for the same translated cube. -/
theorem fieldBox_upper (c : InfinitePlace K → ℝ) {r : ℝ} (hr : 0 < r) :
    ((fieldBox K c r).card : ℝ) ≤ 1 + 2 ^ Module.finrank ℚ K * r ^ Module.finrank ℚ K := by
  simpa [fieldBox, card_places_eq_degree] using fieldRect_upper K c (fun _ => r) (fun _ => hr)

/-- Uniform exponential-in-degree bounds with coarse explicit constants. -/
theorem fieldBox_uniform (c : InfinitePlace K → ℝ) {D r : ℝ} (hD : 1 ≤ D)
    (hdisc : ((discr K).natAbs : ℝ) ≤ D ^ Module.finrank ℚ K)
    (hr : 48 * BoxCutoff.constant * D ≤ r) :
    (r / (2 * D)) ^ Module.finrank ℚ K ≤ ((fieldBox K c r).card : ℝ) ∧
      ((fieldBox K c r).card : ℝ) ≤ (4 * r) ^ Module.finrank ℚ K := by
  let k := Module.finrank ℚ K
  have hk : k ≠ 0 := Nat.ne_of_gt Module.finrank_pos
  have htwo : (2 : ℝ) ≤ 2 ^ k := le_self_pow₀ (by norm_num) hk
  have hdisc1 : (1 : ℝ) ≤ (discr K).natAbs := by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)
  have hdpos : (0 : ℝ) < (discr K).natAbs := by linarith
  have hK := BoxCutoff.constant_one_le
  have hr1 : 1 ≤ r := by nlinarith [mul_le_mul_of_nonneg_right hK (hD.trans' zero_le_one)]
  have hr0 : 0 < r := by linarith
  have hD0 : 0 < D := by linarith
  constructor
  · refine le_trans ?_ (fieldBox_lower K c hD0 hdisc hr)
    rw [div_pow]
    apply div_le_div_of_nonneg_left (pow_nonneg hr0.le _) (mul_pos (by norm_num) (Real.sqrt_pos.mpr hdpos))
    rw [mul_pow]
    exact mul_le_mul htwo ((Real.sqrt_le_self_iff.mpr (Or.inr hdisc1)).trans hdisc)
      (Real.sqrt_nonneg _) (by positivity)
  · refine (fieldBox_upper K c hr0).trans ?_
    change 1 + 2 ^ k * r ^ k ≤ (4 * r) ^ k
    rw [← mul_pow, show 4*r = 2*(2*r) by ring, mul_pow (2 : ℝ) (2*r)]
    have hb : (1 : ℝ) ≤ (2*r)^k := one_le_pow₀ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right htwo (by positivity : 0 ≤ (2*r)^k)]

end MT.Arithmetic
