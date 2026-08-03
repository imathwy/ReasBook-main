import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped IntegerVectorNotation

section Exercise612

local notation "R2" => Fin 2 → ℝ

/-- The three vertices of a `Fin 4`-indexed quadrilateral vertex family other than the `i`th one. -/
def quadrilateral_other_vertices
    (v : Fin 4 → R2)
    (i : Fin 4) : Set R2 :=
  Set.range fun j : {j : Fin 4 // j ≠ i} ↦ v j

/-- `has_quadrilateral_vertices Q v` means that the planar set `Q` is the convex hull of the four
listed vertices `v`. -/
def has_quadrilateral_vertices (Q : Set R2) (v : Fin 4 → R2) : Prop :=
  Q = convexHull ℝ (Set.range v)

/-- A planar convex set is a quadrilateral when it is the convex hull of four distinct vertices
and each listed vertex is extreme among the other three. -/
def is_quadrilateral (Q : Set R2) : Prop :=
  ∃ v : Fin 4 → R2,
    Function.Injective v ∧
      has_quadrilateral_vertices Q v ∧
        ∀ i : Fin 4, v i ∉ convexHull ℝ (quadrilateral_other_vertices v i)

/-- The integral points lying on the boundary of a planar set. -/
def boundary_integer_points (Q : Set R2) : Set R2 :=
  frontier Q ∩ ℤ^2

/-- Membership in `boundary_integer_points Q` means simultaneous membership in the frontier of `Q`
and the embedded lattice `ℤ^2`. -/
theorem mem_boundary_integer_points_iff
    {Q : Set R2} {x : R2} :
    x ∈ boundary_integer_points Q ↔ x ∈ frontier Q ∧ x ∈ ℤ^2 :=
  Iff.rfl

/-- The determinant giving twice the signed area of the triangle with vertices `u`, `v`, and `w`
in `ℝ²`. -/
def triangle_determinant2
    (u v w : R2) : ℝ :=
  (v 0 - u 0) * (w 1 - u 1) - (v 1 - u 1) * (w 0 - u 0)

/-- A `Fin 4`-indexed family lists the vertices of a parallelogram of area one when opposite
vertices have the same midpoint and the parallelogram area computed from one adjacent edge pair is
`1`. -/
def unit_area_parallelogram_vertices (v : Fin 4 → R2) : Prop :=
  v 0 + v 2 = v 1 + v 3 ∧
    |triangle_determinant2 (v 0) (v 1) (v 3)| = 1

/-- The boundary lattice points of `Q` are the vertices of a unit-area parallelogram. -/
def boundary_integer_points_form_unit_area_parallelogram (Q : Set R2) : Prop :=
  ∃ v : Fin 4 → R2,
    boundary_integer_points Q = Set.range v ∧
      unit_area_parallelogram_vertices v

/-- `boundary_integer_points_form_unit_area_parallelogram Q` unfolds to a `Fin 4`-indexed
enumeration of the boundary lattice points whose vertices form a unit-area parallelogram. -/
theorem boundary_integer_points_form_unit_area_parallelogram_iff
    {Q : Set R2} :
    boundary_integer_points_form_unit_area_parallelogram Q ↔
      ∃ v : Fin 4 → R2,
        boundary_integer_points Q = Set.range v ∧
          unit_area_parallelogram_vertices v :=
  Iff.rfl

/-- Exercise 6.12 (1). Let `Q` be a maximal lattice-free convex set in `ℝ²` which is a
quadrilateral. Then `Q` contains exactly four integral points on its boundary. -/
theorem exercise_6_12_boundary_integer_points_encard
    {Q : Set R2}
    (hQ : is_maximal_lattice_free Q)
    (hquad : is_quadrilateral Q) :
    (boundary_integer_points Q).encard = 4 := sorry

/-- Exercise 6.12 (2). Let `Q` be a maximal lattice-free convex set in `ℝ²` which is a
quadrilateral. Then the four integral points on the boundary of `Q` are the vertices of a
parallelogram of area one. -/
theorem exercise_6_12_boundary_integer_points_are_unit_area_parallelogram_vertices
    {Q : Set R2}
    (hQ : is_maximal_lattice_free Q)
    (hquad : is_quadrilateral Q) :
    boundary_integer_points_form_unit_area_parallelogram Q := sorry

end Exercise612
