module

public import MT.Smoothing
public import MT.Upstream.Poisson

/-! # Poisson lower bound for the number of lattice points in a box
This is the step in Lemma 4.3 converting a dual Fourier remainder estimate
into a primal count. The smooth cutoff and its nonzero-frequency bound are
inputs. The periodisation identity and its convergence are proved theorems.
-/

public section
noncomputable section

open MeasureTheory DedekindZeta.PoissonSummation
open scoped FourierTransform

namespace MT

theorem lattice_count_of_fourier_tail {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] (B : Finset L) (f : SchwartzMap V ℂ) (E : ℝ)
    (hsupp : ∀ v : L, v ∉ B → f (v : V) = 0)
    (hbump : ∀ v ∈ B, ‖f (v : V)‖ ≤ 1)
    (htail : tailNorm (fun ξ : dualLattice L => 𝓕 (f : V → ℂ) (ξ : V)) ≤ E) :
    (‖𝓕 (f : V → ℂ) (0 : V)‖ - E) / ZLattice.covolume L ≤ B.card := by
  have hc := ZLattice.covolume_pos L volume
  have hne : (ZLattice.covolume L volume : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hs := summable_periodisation_fourier L f 0
  simp only [inner_zero_left, AddChar.map_zero_eq_one, one_smul] at hs
  have habs : Summable (fun ξ : dualLattice L => ‖𝓕 (f : V → ℂ) (ξ : V)‖) := by
    apply Summable.norm
    exact (hs.mul_left (ZLattice.covolume L volume : ℂ)).congr fun ξ => by
      simp [← mul_assoc, hne]
  exact count_from_zero_frequency B (fun v : L => f (v : V))
    (fun ξ : dualLattice L => 𝓕 (f : V → ℂ) (ξ : V))
    (ZLattice.covolume L) E (ZLattice.covolume_pos L volume) hsupp hbump
    habs (tsum_eq_tsum_fourier L f) htail

end MT
