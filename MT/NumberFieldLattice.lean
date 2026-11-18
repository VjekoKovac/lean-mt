module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Covolume of the Minkowski lattice
Appendix A of arXiv:2611.22465v1. The lattice is in the Euclidean model
required by the multidimensional lattice Poisson summation theorem.
-/

public section
noncomputable section
open MeasureTheory NumberField NumberField.InfinitePlace
open NumberField.mixedEmbedding

open scoped Classical

namespace MT.Arithmetic

/-- Transporting the mixed embedding to its Euclidean realization preserves
the covolume. The classical mixed-embedding formula specializes to sqrt of
the absolute discriminant for a totally real field. -/
theorem minkowski_covolume (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    ZLattice.covolume (E := euclidean.mixedSpace K) (euclidean.integerLattice K) volume = Real.sqrt |(discr K : ℝ)| := by
  classical
  change ZLattice.covolume (ZLattice.comap ℝ (mixedEmbedding.integerLattice K)
    (euclidean.toMixed K).toLinearMap) = _
  rw [ZLattice.covolume_comap _ volume volume (euclidean.volumePreserving_toMixed K),
    mixedEmbedding.covolume_integerLattice, IsTotallyReal.nrComplexPlaces_eq_zero]
  simp

end MT.Arithmetic
