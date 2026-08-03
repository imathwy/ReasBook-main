import Integer.Chapters.Chap06.section_6_5.ch6_sec6_5_exercise_6_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped IntegerVectorNotation Matrix

-- This exercise reuses the triangle-specific owner `has_integral_triangle_vertices` from
-- Exercise 6.11 together with the canonical Chapter 6 lattice-free owner
-- `is_maximal_lattice_free`, the canonical facet owner `IsFacetOf`, and mathlib's canonical
-- affine-map owner `AffineMap`.

section Exercise613

local notation "R2" => Fin 2 → ℝ
local notation "Z2" => Fin 2 → ℤ

/-- The standard maximal lattice-free triangle in `ℝ²` with vertices `(0, 0)`, `(2, 0)`, and
`(0, 2)`. -/
def exercise_6_13_standard_triangle : Affine.Triangle ℝ R2 :=
  ⟨![(![(0 : ℝ), 0] : R2), ![2, 0], ![0, 2]], by sorry⟩

/-- The closed triangular region cut out by `exercise_6_13_standard_triangle`. -/
def exercise_6_13_standard_triangle_region : Set R2 :=
  exercise_6_13_standard_triangle.closedInterior

/-- The standard triangle region is realized by `exercise_6_13_standard_triangle`. -/
theorem has_triangle_vertices_exercise_6_13_standard_triangle_region :
    has_triangle_vertices exercise_6_13_standard_triangle_region
      exercise_6_13_standard_triangle :=
  rfl

/-- The affine map on `ℝ²` given by an integer matrix and an integral translation vector. -/
def integerAffineMap (c : Z2) (M : Matrix (Fin 2) (Fin 2) ℤ) : R2 →ᵃ[ℝ] R2 :=
  ((Matrix.toLin' fun i j ↦ (M i j : ℝ)).toAffineMap) +ᵥ
    AffineMap.const ℝ R2 (fun i ↦ (c i : ℝ))

/-- Exercise 6.13. Let `T` be a maximal lattice-free triangle in `ℝ²` whose vertices are integral
and such that each facet contains exactly one integral point in its relative interior. Then there
exists an integral translation and a unimodular integer matrix sending `T` to the triangle with
vertices `(0, 0)`, `(2, 0)`, and `(0, 2)`. -/
theorem exercise_6_13_exists_unimodular_integer_affine_image_of_maximal_lattice_free_triangle
    (T : Set R2)
    (hT_triangle : has_integral_triangle_vertices T)
    (hT_max : is_maximal_lattice_free T)
    (hT_facets : facets_have_unique_integer_point_in_intrinsicInterior T) :
    ∃ c : Z2, ∃ M : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit M.det ∧
        integerAffineMap c M '' T = exercise_6_13_standard_triangle_region := sorry

end Exercise613
