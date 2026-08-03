import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18

-- Declarations for this item will be appended below by the statement pipeline.
-- This exercise reuses the Chapter 6 lattice-free owner `is_maximal_lattice_free` from
-- Theorem 6.18, the Chapter 3 facet owner `IsFacetOf`, and the canonical lattice notation `ℤ^n`.

open scoped IntegerVectorNotation

section Exercise611

local notation "R2" => Fin 2 → ℝ

/-- `has_triangle_vertices T t` means that the planar triangle `t` realizes the set `T` as its
convex hull. -/
def has_triangle_vertices (T : Set R2) (t : Affine.Triangle ℝ R2) : Prop :=
  T = t.closedInterior

/-- A planar set is a triangle when it is the convex hull of three affinely independent vertices.
-/
def is_triangle (T : Set R2) : Prop :=
  ∃ t : Affine.Triangle ℝ R2, has_triangle_vertices T t

/-- The facet opposite the vertex `t.points i` in the triangle `t`. -/
def triangle_opposite_facet
    (t : Affine.Triangle ℝ R2)
    (i : Fin 3) : Set R2 :=
  (t.faceOpposite i).closedInterior

/-- `has_integral_triangle_vertices T` means that `T` is a triangle whose three vertices are
integral lattice points. -/
def has_integral_triangle_vertices (T : Set R2) : Prop :=
  ∃ t : Affine.Triangle ℝ R2, has_triangle_vertices T t ∧ ∀ i : Fin 3, t.points i ∈ ℤ^2

/-- The relative interior of the facet `F` contains exactly one embedded integer point. -/
def facet_has_unique_integer_point_in_intrinsicInterior (F : Set R2) : Prop :=
  ∃! x : R2, x ∈ intrinsicInterior ℝ F ∧ x ∈ ℤ^2

/-- The relative interior of the facet `F` contains at least two distinct embedded integer
points. -/
def facet_has_two_distinct_integer_points_in_intrinsicInterior (F : Set R2) : Prop :=
  ∃ x y : R2, x ≠ y ∧ x ∈ intrinsicInterior ℝ F ∩ ℤ^2 ∧ y ∈ intrinsicInterior ℝ F ∩ ℤ^2

/-- Every facet of `T` contains a unique embedded integer point in its relative interior. -/
def facets_have_unique_integer_point_in_intrinsicInterior (T : Set R2) : Prop :=
  ∀ F : Set R2, IsFacetOf T F → facet_has_unique_integer_point_in_intrinsicInterior F

/-- Case (a): the triangle has integral vertices and each facet contains exactly one embedded
integer point in its relative interior. -/
def exercise_6_11_case_a (T : Set R2) : Prop :=
  has_integral_triangle_vertices T ∧
    facets_have_unique_integer_point_in_intrinsicInterior T

/-- Case (b): some vertex of the triangle is nonintegral and the opposite facet is a facet of `T`
whose relative interior contains at least two distinct embedded integer points. -/
def exercise_6_11_case_b (T : Set R2) : Prop :=
  ∃ t : Affine.Triangle ℝ R2,
    has_triangle_vertices T t ∧
      ∃ i : Fin 3,
        t.points i ∉ ℤ^2 ∧
          IsFacetOf T (triangle_opposite_facet t i) ∧
            facet_has_two_distinct_integer_points_in_intrinsicInterior
              (triangle_opposite_facet t i)

/-- Case (c): the triangle contains exactly three embedded integer points, and each facet contains
exactly one of them in its relative interior. -/
def exercise_6_11_case_c (T : Set R2) : Prop :=
  (T ∩ ℤ^2).encard = 3 ∧
    facets_have_unique_integer_point_in_intrinsicInterior T

/-- Exercise 6.11. Let `T` be a maximal lattice-free convex set in `ℝ²` which is a triangle.
Then `T` satisfies one of the following three alternatives: it has integral vertices and exactly
one embedded integer point in the relative interior of each facet, or some nonintegral vertex has
an opposite facet with at least two embedded integer points in its relative interior, or `T`
contains exactly three embedded integer points with one in the relative interior of each facet. -/
theorem exercise_6_11_triangle_satisfies_one_of_three_integral_point_configurations
    (T : Set R2)
    (hT_maximal : is_maximal_lattice_free T)
    (hT_triangle : is_triangle T) :
    exercise_6_11_case_a T ∨ exercise_6_11_case_b T ∨ exercise_6_11_case_c T := sorry

end Exercise611
