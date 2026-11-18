module

public import MT.SeedGeometry

/-! # Inner rectangles of returning parabolic shifts
Section 4.3 intersects a seed rectangle and the translate of its successor.
The following closed rectangle inside that intersection has half the original
half-width in each coordinate, so the lattice count can use an explicit size
threshold. The midpoint construction works independently in each coordinate.
-/

@[expose] public section
noncomputable section
namespace MT.Seed

private theorem midpoint_bounds {w t x : ℝ} (ht : |t| ≤ w)
    (hx : |x + t/2| ≤ w/2) : |x| ≤ w ∧ |x+t| ≤ w := by
  rw [abs_le] at ht hx
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- An inner rectangle of the overlap for a generator a and a seed point p.
A point x is near the generator ρa. The two center displacements are u and
v; the small rectangle is centered at the midpoint after undoing the shift. -/
theorem returning_rectangle (p : ℤ × ℤ) (a : ℤ) (H ρ x : ℝ)
    (hu : |x - ρ * a| ≤ H)
    (hv : |x^2 - ρ^2 * (a : ℝ)^2| ≤ ρ^(3/2 : ℝ)) :
    ∃ center : Plane, ∀ q : Plane,
      |q.1-center.1| ≤ H/2 → |q.2-center.2| ≤ ρ^(3/2 : ℝ)/2 →
      q ∈ rectangle H ρ p ∧
      (q.1+x, q.2+x^2) ∈ rectangle H ρ (p + parabola a) := by
  let u := x - ρ * a
  let v := x^2 - ρ^2 * (a : ℝ)^2
  refine ⟨(ρ*p.1-u/2, ρ^2*p.2-v/2), ?_⟩
  intro q hx hy
  have horiz := midpoint_bounds hu (x := q.1-ρ*p.1) (by
    change |q.1 - (ρ * p.1 - u / 2)| ≤ H / 2 at hx
    convert hx using 1; congr 1; dsimp [u]; ring)
  have vert := midpoint_bounds hv (x := q.2-ρ^2*p.2) (by
    change |q.2 - (ρ^2 * p.2 - v / 2)| ≤ ρ^(3/2 : ℝ) / 2 at hy
    convert hy using 1; congr 1; dsimp [v]; ring)
  refine ⟨⟨horiz.1, vert.1⟩, ?_⟩
  change |q.1 + x - ρ * ((p.1 + a : ℤ) : ℝ)| ≤ H ∧
    |q.2 + x^2 - ρ^2 * ((p.2 + a^2 : ℤ) : ℝ)| ≤ ρ^(3/2 : ℝ)
  push_cast
  constructor
  · convert horiz.2 using 1; congr 1; ring
  · convert vert.2 using 1; congr 1; ring

/-- The vertical displacement estimate for choosing ρ in terms of the seed
and horizontal half-width. It is uniform over x in the full seed interval. -/
theorem vertical_shift_le {x c H : ℝ} (hu : |x-c| ≤ H) :
    |x^2-c^2| ≤ H*(2*|c|+H) := by
  have hplus : |x+c| ≤ 2*|c|+H := calc
    _ = |(x-c)+(c+c)| := by rw [show x+c=(x-c)+(c+c) by ring]
    _ ≤ |x-c| + |c+c| := abs_add_le .. 
    _ ≤ H + (|c|+|c|) := add_le_add hu (abs_add_le ..)
    _ = _ := by ring
  rw [show x^2-c^2 = (x-c)*(x+c) by ring, abs_mul]
  exact mul_le_mul hu hplus (abs_nonneg _) ((abs_nonneg _).trans hu)

end MT.Seed
