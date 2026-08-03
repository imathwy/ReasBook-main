import Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the declarations
-- below follow the local Chapter 3/4 `Fin n → ℝ` conventions, with `IsGreatest` on the objective
-- image to express the finite attained maximum.

section Theorem41

variable {n : ℕ}

/-- The subset of `ℝ^n` cut out by a rational inequality system after coercing the data to `ℝ`. -/
abbrev rational_matrix_polyhedron {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) : Set (Fin n → ℝ) :=
  polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))

/-- Membership in `rational_matrix_polyhedron A b` is the corresponding real inequality system. -/
theorem mem_rational_matrix_polyhedron {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (x : Fin n → ℝ) :
    x ∈ rational_matrix_polyhedron A b ↔
      (A.map (Rat.castHom ℝ)) *ᵥ x ≤ fun i ↦ (b i : ℝ) :=
  Iff.rfl

/-- A subset of `ι → ℝ` is integral if it is the convex hull of its integer points. -/
def is_integral {ι : Type*} (P : Set (ι → ℝ)) : Prop :=
  P =
    convexHull ℝ
      (P ∩ Set.range (fun z : ι → ℤ ↦ Int.cast ∘ z))

/-- A subset of `ι → ℝ` is integral exactly when it equals the convex hull of its integer points. -/
theorem is_integral_iff {ι : Type*} {P : Set (ι → ℝ)} :
    is_integral P ↔
      P =
        convexHull ℝ
          (P ∩ Set.range (fun z : ι → ℤ ↦ Int.cast ∘ z)) :=
  Iff.rfl

/-- The embedded lattice points `ℤ^n ⊆ ℝ^n`. -/
def integerVectors (n : ℕ) : Set (Fin n → ℝ) :=
  Set.range (fun z : Fin n → ℤ ↦ Int.cast ∘ z)

namespace IntegerVectorNotation

scoped notation "ℤ^" n:max => integerVectors n

end IntegerVectorNotation

open scoped IntegerVectorNotation

/-- Membership in `ℤ^n` means that the vector is the real coercion of an integer vector. -/
theorem mem_integerVectors_iff {x : Fin n → ℝ} :
    x ∈ ℤ^n ↔ ∃ z : Fin n → ℤ, x = Int.cast ∘ z :=
by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩

/-- A real vector lies in `ℤ^n` exactly when each coordinate is an integer. -/
theorem mem_integerVectors_iff_forall {x : Fin n → ℝ} :
    x ∈ ℤ^n ↔ ∀ j, x j ∈ Set.range (Int.cast : ℤ → ℝ) := by
  constructor
  · rintro ⟨z, rfl⟩ j
    exact ⟨z j, rfl⟩
  · intro hx
    refine ⟨fun j ↦ Classical.choose (hx j), ?_⟩
    funext j
    exact Classical.choose_spec (hx j)

/-- Theorem 4.1 (1). Let `P` be a rational polyhedron. Then `P` is an integral polyhedron if and
only if every minimal face of `P` contains an integral point. -/
theorem rational_polyhedron_is_integral_iff_minimal_faces_contain_integral_point
    (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P) :
    is_integral P ↔
      ∀ F, IsMinimalFaceOf ℝ P F → ∃ x ∈ F, x ∈ ℤ^n := sorry

/-- Theorem 4.1 (2). Let `P` be a rational polyhedron. Then `P` is an integral polyhedron if and
only if every finite maximum of a linear objective over `P` is attained at an integral point of
`P`. -/
theorem rational_polyhedron_is_integral_iff_linear_maxima_attained_by_integral_points
    (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P) :
    is_integral P ↔
      ∀ c z,
        IsGreatest ((c ⬝ᵥ ·) '' P) z →
          ∃ x ∈ P ∩ ℤ^n, c ⬝ᵥ x = z := sorry

/-- Theorem 4.1 (3). Let `P` be a rational polyhedron. Then `P` is an integral polyhedron if and
only if every finite maximum of an integral linear objective over `P` is an integer. -/
theorem rational_polyhedron_is_integral_iff_integral_linear_maxima_are_integer
    (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P) :
    is_integral P ↔
      ∀ c z,
        IsGreatest (((Int.cast ∘ c) ⬝ᵥ ·) '' P) z →
          ∃ k : ℤ, z = k := sorry

end Theorem41
