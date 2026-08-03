import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped IntegerVectorNotation Matrix

-- Semantic recall note: `lean_leansearch` was unavailable in this runner, and `tool_search`
-- exposed no deferred Lean semantic-search tools. The declarations below follow the local
-- Chapter 4 product-space and convex-hull conventions for mixed-integer polyhedra.

section Theorem43

variable {m n p : ℕ}

/-- A point of the ambient space `ℝ^n × ℝ^p`. -/
abbrev MixedRealPoint (n p : ℕ) := (Fin n → ℝ) × (Fin p → ℝ)

/-- The rational mixed polyhedron
`{(x, y) : ℝ^n × ℝ^p | A x + G y ≤ b}` attached to rational data `A`, `G`, and `b`. -/
def rational_mixed_polyhedron
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) :
    Set (MixedRealPoint n p) :=
  {xy |
    (A.map (Rat.castHom ℝ)) *ᵥ xy.1 + (G.map (Rat.castHom ℝ)) *ᵥ xy.2 ≤ fun i ↦ (b i : ℝ)}

/-- Membership in `rational_mixed_polyhedron A G b` is exactly the inequality system
`A x + G y ≤ b` after coercing the rational data to `ℝ`. -/
theorem mem_rational_mixed_polyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ}
    {xy : MixedRealPoint n p} :
    xy ∈ rational_mixed_polyhedron A G b ↔
      (A.map (Rat.castHom ℝ)) *ᵥ xy.1 + (G.map (Rat.castHom ℝ)) *ᵥ xy.2 ≤
        fun i ↦ (b i : ℝ) :=
  Iff.rfl

/-- The mixed-integer lattice `ℤ^n × ℝ^p` embedded in `ℝ^n × ℝ^p`. -/
def mixed_integer_lattice (n p : ℕ) : Set (MixedRealPoint n p) :=
  {xy | xy.1 ∈ ℤ^n}

namespace MixedIntegerNotation

scoped notation "ℤ^" n:max "×ℝ^" p:max => mixed_integer_lattice n p

end MixedIntegerNotation

open scoped MixedIntegerNotation

/-- Membership in `mixed_integer_lattice n p` means that the `x`-block lies in the canonical
integer-vector owner `integerVectors n`. -/
theorem mem_mixed_integer_lattice_iff
    {xy : MixedRealPoint n p} :
    xy ∈ mixed_integer_lattice n p ↔ xy.1 ∈ ℤ^n :=
  Iff.rfl

/-- The mixed-integer points of `P` are the members of `P` whose `x`-block is integral. -/
def mixed_integer_points (P : Set (MixedRealPoint n p)) : Set (MixedRealPoint n p) :=
  P ∩ (ℤ^n×ℝ^p)

/-- Membership in `mixed_integer_points P` means membership in `P` together with integrality of
the `x`-block. -/
theorem mem_mixed_integer_points_iff
    {P : Set (MixedRealPoint n p)}
    {xy : MixedRealPoint n p} :
    xy ∈ mixed_integer_points P ↔ xy ∈ P ∧ xy ∈ (ℤ^n×ℝ^p) :=
  Iff.rfl

/-- Source-facing bridge/view: a subset of `ℝ^n × ℝ^p` is a rational mixed polyhedron when its
canonical flattening in `ℝ^(n + p)` is a rational polyhedron. -/
def is_rational_mixed_polyhedron (P : Set (MixedRealPoint n p)) : Prop :=
  is_rational_polyhedron ((Fin.appendEquiv n p) '' P)

/-- Source-facing expansion of `is_rational_mixed_polyhedron` into a rational mixed-system
presentation. -/
theorem is_rational_mixed_polyhedron_iff
    {P : Set (MixedRealPoint n p)} :
    is_rational_mixed_polyhedron P ↔
      ∃ m : ℕ,
        ∃ A : Matrix (Fin m) (Fin n) ℚ,
          ∃ G : Matrix (Fin m) (Fin p) ℚ,
            ∃ b : Fin m → ℚ,
              P = rational_mixed_polyhedron A G b := sorry

/-- The linear objective `(x, y) ↦ c x + h y` on `ℝ^n × ℝ^p`. -/
def mixed_linear_objective
    (c : Fin n → ℝ) (h : Fin p → ℝ) (xy : MixedRealPoint n p) : ℝ :=
  c ⬝ᵥ xy.1 + h ⬝ᵥ xy.2

/-- Unfolding equation for `mixed_linear_objective`. -/
theorem mixed_linear_objective_def
    (c : Fin n → ℝ) (h : Fin p → ℝ) (xy : MixedRealPoint n p) :
    mixed_linear_objective c h xy = c ⬝ᵥ xy.1 + h ⬝ᵥ xy.2 :=
  rfl

/-- Theorem 4.3 (1). Let `P ⊆ ℝ^n × ℝ^p` be a rational polyhedron, and let
`S := mixed_integer_points P`. Then `P = conv(S)` if and only if every minimal face of `P`
contains a point of `S`. -/
theorem mixed_integer_hull_eq_iff_minimal_faces_contain_mixed_integer_point
    (P : Set (MixedRealPoint n p))
    (hP : is_rational_mixed_polyhedron P) :
    P = convexHull ℝ (mixed_integer_points P) ↔
      ∀ F : Set (MixedRealPoint n p), IsMinimalFaceOf ℝ P F →
        ∃ xy : MixedRealPoint n p, xy ∈ F ∧ xy ∈ mixed_integer_points P := sorry

/-- Theorem 4.3 (2). Let `P ⊆ ℝ^n × ℝ^p` be a rational polyhedron, and let
`S := mixed_integer_points P`. Then `P = conv(S)` if and only if every finite maximum of a linear
objective `(x, y) ↦ c x + h y` over `P` is attained at a point of `S`. -/
theorem mixed_integer_hull_eq_iff_linear_maxima_attained_by_mixed_integer_points
    (P : Set (MixedRealPoint n p))
    (hP : is_rational_mixed_polyhedron P) :
    P = convexHull ℝ (mixed_integer_points P) ↔
      ∀ (c : Fin n → ℝ) (h : Fin p → ℝ) (z : ℝ),
        IsGreatest (mixed_linear_objective c h '' P) z →
          ∃ xy : MixedRealPoint n p,
            xy ∈ mixed_integer_points P ∧ mixed_linear_objective c h xy = z := sorry

end Theorem43
