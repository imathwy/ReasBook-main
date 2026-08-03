module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

open Set

namespace FixedFociEllipse

/-- The Euclidean plane containing the fixed-foci elliptical regions. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Projection to the first coordinate of the Euclidean plane. -/
def firstCoordinate (x : Plane) : ℝ :=
  x 0

/-- Helper for Example 37.3: `firstCoordinate` evaluates the zeroth coordinate. -/
lemma firstCoordinate_apply (x : Plane) : firstCoordinate x = x 0 := by
  -- Unfold the projection at its defining argument.
  rfl

/-- Projection to the second coordinate of the Euclidean plane. -/
def secondCoordinate (x : Plane) : ℝ :=
  x 1

/-- Helper for Example 37.3: `secondCoordinate` evaluates the first coordinate. -/
lemma secondCoordinate_apply (x : Plane) : secondCoordinate x = x 1 := by
  -- Unfold the projection at its defining argument.
  rfl

/-- The first focus `p = (1 / 3, 1 / 3)`. -/
noncomputable def p : Plane :=
  WithLp.toLp 2 ![(1 / 3 : ℝ), (1 / 3 : ℝ)]

/-- Helper for Example 37.3: every coordinate of `p` equals `1 / 3`. -/
lemma p_apply (i : Fin 2) : p i = (1 / 3 : ℝ) := by
  -- Exhaust the two coordinates, then evaluate the `WithLp` vector explicitly.
  fin_cases i
  · norm_num [p, PiLp.toLp_apply]
  · norm_num [p, PiLp.toLp_apply]

/-- The second focus `q = (1 / 2, 2 / 3)`. -/
noncomputable def q : Plane :=
  WithLp.toLp 2 ![(1 / 2 : ℝ), (2 / 3 : ℝ)]

/-- The unit square `[0, 1] × [0, 1]` in the Euclidean plane. -/
def unitSquare : Set Plane :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/-- Helper for Example 37.3: membership in `unitSquare` is coordinatewise membership
in the unit interval. -/
lemma mem_unitSquare (x : Plane) :
    x ∈ unitSquare ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  -- Unfold the set membership predicate exposed by `unitSquare`.
  rfl

/-- The filled ellipse with foci `p`, `q` and focal-distance bound `c`. -/
def region (c : ℝ) : Set Plane :=
  {x | dist x p + dist x q ≤ c}

/-- The family of fixed-foci filled ellipses contained in the unit square. -/
def family : Set (Set Plane) :=
  {D | ∃ c, dist p q < c ∧ region c ⊆ unitSquare ∧ D = region c}

/-- Membership in a fixed-foci region in focal-distance form. -/
theorem mem_region (x : Plane) (c : ℝ) :
    x ∈ region c ↔ dist x p + dist x q ≤ c := by
  -- The region is defined by this inequality.
  rfl

/-- Membership in the fixed-foci family with the ellipse parameter exposed. -/
theorem mem_family (D : Set Plane) :
    D ∈ family ↔ ∃ c,
      dist p q < c ∧ region c ⊆ unitSquare ∧ D = region c := by
  -- The family is defined by the displayed witnesses and conditions.
  rfl

/-- Every fixed-foci region is closed. -/
theorem isClosed_region (c : ℝ) : IsClosed (region c) := by
  -- The focal-distance sum is continuous, so its closed sublevel set is closed.
  exact isClosed_le
    ((continuous_id.dist continuous_const).add (continuous_id.dist continuous_const))
    continuous_const

/-- Every member of the fixed-foci family is closed. -/
theorem isClosed_of_mem_family {D : Set Plane} (hD : D ∈ family) :
    IsClosed D := by
  -- Expose the region representing the family member.
  obtain ⟨c, -, -, rfl⟩ := (mem_family D).mp hD
  exact isClosed_region c

end FixedFociEllipse
