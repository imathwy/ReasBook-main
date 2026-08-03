import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped BigOperators Matrix

section Exercise52

variable {n p : ℕ}

-- Semantic recall check via `lean_leansearch`: no canonical mathlib owner for a closed facet-count
-- formula for split pairs surfaced, so this file keeps the source-facing Chapter 3/5 split and
-- facet owners.

/-- The mixed-integer coordinates from `(5.1)` are the first `n` coordinates of `ℝ^(n+p)`. -/
def exercise_5_2_integer_indices (n p : ℕ) : Finset (Fin (n + p)) :=
  Finset.univ.image (fun j : Fin n ↦ j.castAdd p)

/-- Helper for Exercise 5.2: `Π₁` and `Π₂` arise from one Chapter 5 split on `P` supported on
the integer coordinates from `(5.1)`. -/
def exercise_5_2_is_split_pair
    (P Pi1 Pi2 : Set (Fin (n + p) → ℝ)) : Prop :=
  ∃ s : Split (exercise_5_2_integer_indices n p),
    Pi1 = split_branch_lower P s s.π0 ∧
      Pi2 = split_branch_upper P s s.π0

/-- Helper for Exercise 5.2: `nFaces k` records the exposed `k`-faces of `Π` in the source
range. -/
def exercise_5_2_has_face_counts
    (Pi : Set (Fin (n + p) → ℝ))
    (nFaces : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ n + p - 2 →
    {F : Set (Fin (n + p) → ℝ) |
        IsExposed ℝ Pi F ∧
          polyhedronDim F = k}.encard =
      (nFaces k : ℕ∞)

/-- Helper for Exercise 5.2: `nFacets` records the number of facets of `Π`. -/
def exercise_5_2_has_facet_count
    (Pi : Set (Fin (n + p) → ℝ))
    (nFacets : ℕ) : Prop :=
  {F : Set (Fin (n + p) → ℝ) | IsFacetOf Pi F}.encard =
    (nFacets : ℕ∞)

/-- Helper for Exercise 5.2: `B` is a combinatorial facet bound if, in the source regime
`3 ≤ n + p`, it bounds the number of facets of `conv(Π₁ ∪ Π₂)` using only the source face-count
functions of the two split branches. -/
def exercise_5_2_is_combinatorial_facet_bound
    (n p : ℕ)
    (B : (ℕ → ℕ) → (ℕ → ℕ) → ℕ) : Prop :=
  ∀ (P Pi1 Pi2 : Set (Fin (n + p) → ℝ))
    (nFaces1 nFaces2 : ℕ → ℕ),
      is_polyhedron P →
      exercise_5_2_is_split_pair P Pi1 Pi2 →
      3 ≤ n + p →
      exercise_5_2_has_face_counts Pi1 nFaces1 →
      exercise_5_2_has_face_counts Pi2 nFaces2 →
      {F : Set (Fin (n + p) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F}.encard ≤
        (B nFaces1 nFaces2 : ℕ∞)

/-- Helper for Exercise 5.2: every member `P m` of the family has an `m`-constraint matrix
presentation. -/
def exercise_5_2_has_m_constraint_presentations
    (d : ℕ → ℕ)
    (P : ∀ m : ℕ, Set (Fin (d m) → ℝ)) : Prop :=
  ∀ m : ℕ, ∃ A : Matrix (Fin m) (Fin (d m)) ℝ, ∃ b : Fin m → ℝ,
    P m = polyhedron_le_set A b

/-- Helper for Exercise 5.2: each pair `Π₁ m`, `Π₂ m` is obtained from the same Chapter 5 split
on `P m` supported on the designated mixed-integer coordinates `I m`. -/
def exercise_5_2_is_split_family
    (d : ℕ → ℕ)
    (I : ∀ m : ℕ, Finset (Fin (d m)))
    (P Pi1 Pi2 : ∀ m : ℕ, Set (Fin (d m) → ℝ)) : Prop :=
  ∀ m : ℕ, ∃ s : Split (I m),
    Pi1 m = split_branch_lower (P m) s s.π0 ∧
      Pi2 m = split_branch_upper (P m) s s.π0

/-- Helper for Exercise 5.2: the split-disjunctive hull family eventually beats every linear
facet bound. -/
def exercise_5_2_has_superlinear_split_disjunctive_facet_growth
    (d : ℕ → ℕ)
    (Pi1 Pi2 : ∀ m : ℕ, Set (Fin (d m) → ℝ)) : Prop :=
  ∀ C : ℕ, ∃ m : ℕ,
    (C * m : ℕ∞) <
      {F : Set (Fin (d m) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 m ∪ Pi2 m)) F}.encard

/-- Exercise 5.2 (1). Let `P`, `Π₁`, and `Π₂` be as in `(5.1)`, so `Π₁` and `Π₂` are the two
split branches of `P`. If, for each `k = 1, …, n + p - 2`, the polyhedra `Π₁` and `Π₂` have
`n_k^1` and `n_k^2` `k`-dimensional faces, respectively, then, in the nondegenerate regime
`3 ≤ n + p`, there exists a combinatorial upper bound on the number of facets of
`conv(Π₁ ∪ Π₂)` depending only on these source face numbers. -/
theorem exercise_5_2_facet_bound_of_split_pair
    (hambient : 3 ≤ n + p) :
    ∃ B : (ℕ → ℕ) → (ℕ → ℕ) → ℕ,
      exercise_5_2_is_combinatorial_facet_bound n p B := sorry

/-- Exercise 5.2 (2). One can construct a family of polyhedra `P` with `m` constraints whose
associated split-disjunctive hulls `conv(Π₁ ∪ Π₂)` have more than linear facet growth in `m`;
the ambient dimension and the designated mixed-integer coordinates are allowed to vary with `m`.
-/
theorem exists_polyhedron_family_with_superlinear_split_disjunctive_facet_growth :
    ∃ d : ℕ → ℕ, ∃ P : ∀ m : ℕ, Set (Fin (d m) → ℝ),
      ∃ I : ∀ m : ℕ, Finset (Fin (d m)),
        ∃ Pi1 Pi2 : ∀ m : ℕ, Set (Fin (d m) → ℝ),
        ∃ hP : exercise_5_2_has_m_constraint_presentations d P,
          ∃ hsplit : exercise_5_2_is_split_family d I P Pi1 Pi2,
            exercise_5_2_has_superlinear_split_disjunctive_facet_growth d Pi1 Pi2 := sorry

end Exercise52
