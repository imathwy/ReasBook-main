import Mathlib
import Nesterov.Chap01.Definition_1_10_2
import Nesterov.Chap03.Definition_3_62
import Nesterov.Chap07.Definition_7_26

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open Matrix
open scoped EllipsoidNotation

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Matₙ" => Matrix (Fin n) (Fin n) ℝ

/- Theorem 7.9 lies in Chapter 7's diagonal ellipsoid / orthant-polyhedron rounding domain.

Sampled owner-style declarations:
- `matrixEllipsoid` with notation `W[r](G)` in `Chap07/Definition_7_26`, the chapter owner for
  radius-parametrized ellipsoids;
- `mem_centeredMatrixEllipsoid_iff_dualNorm_le` in `Chap07/Definition_7_26`, the canonical
  positive-definite membership view for `W[r](G)`;
- `innerLePolyhedron` and `mem_innerLePolyhedron_iff` in `Chap03/Definition_3_62`, the chapter
  owner for finite inner-product half-space presentations;
- `Matrix.IsDiag` and `Matrix.isDiag_diagonal` in mathlib's matrix diagonal API, the canonical
  owner and constructor theorem for diagonality;
- `Matrix.posDef_diagonal_iff` in mathlib's positive-definite diagonal API, the canonical matrix
  positivity criterion for diagonal matrices;
- `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.mem_nonnegativeOrthant_iff` in
  `Chap01/Definition_1_10_2`, the chapter owner for orthant constraints.

Best owner abstraction:
- source-facing: the orthant-constrained polyhedron from Theorem 7.9;
- core/canonical: `W[r](G)`, `innerLePolyhedron`, `nonnegativeOrthant`, `Matrix.IsDiag`, and
  `Matrix.PosDef`;
- bridge/view: the orthant-specialized view `orthantHalfspacePolyhedron`.

Primitive data:
- `a : Fin m → Eₙ` and `b : Fin m → ℝ`;
- boundedness of the source-facing orthant polyhedron `orthantHalfspacePolyhedron a b`.

Derived API:
- the diagonal positive-definite rounding matrix `D : Matₙ`;
- the centered diagonal ellipsoids `W[1](D)` and `W[r](D)`;
- the source-facing orthant polyhedron `orthantHalfspacePolyhedron a b`, built from
  `innerLePolyhedron a b`.

Source/core/bridge triage:
- source-facing: `orthantHalfspacePolyhedron` and the theorem below;
- core/canonical: `W[r](G)`, `innerLePolyhedron`, `nonnegativeOrthant`, `Matrix.IsDiag`, and
  `Matrix.PosDef`;
- bridge/view: no additional public bridge owner is needed.

This refinement keeps the orthant polyhedron source-facing, but moves the existential witness to
the matrix owner level used by Chapter 7 ellipsoids: the theorem now returns a diagonal matrix
together with an orthant-specialized rounding predicate, rather than a four-way conjunction of
matrix properties and containments.
-/

/-- The polyhedron in the nonnegative orthant cut out by the inequalities
`⟪a_i, x⟫ ≤ b_i`. -/
def orthantHalfspacePolyhedron (a : Fin m → Eₙ) (b : Fin m → ℝ) : Set Eₙ :=
  nonnegativeOrthant n ∩ innerLePolyhedron a b

-- Proof sketch: unfold `orthantHalfspacePolyhedron` and use `mem_innerLePolyhedron_iff`.
/-- Membership in `orthantHalfspacePolyhedron a b` means belonging to the nonnegative orthant and
satisfying all inequalities `⟪a_i, x⟫ ≤ b_i`. -/
@[simp] theorem mem_orthantHalfspacePolyhedron_iff
    (a : Fin m → Eₙ) (b : Fin m → ℝ) (x : Eₙ) :
    x ∈ orthantHalfspacePolyhedron a b ↔
      x ∈ nonnegativeOrthant n ∧ ∀ i : Fin m, inner ℝ (a i) x ≤ b i := by
  simp [orthantHalfspacePolyhedron]

/-- An orthant ellipsoidal rounding of `C` with parameter `γ` is a positive-definite matrix `D`
whose unit ellipsoid restricted to the nonnegative orthant lies in `C`, and whose outer ellipsoid
of radius `γ √n`, again restricted to the nonnegative orthant, contains `C`. -/
structure IsOrthantEllipsoidalRounding
    (C : Set Eₙ) (γ : ℝ) (D : Matₙ) : Prop where
  /-- The rounding matrix is positive definite. -/
  posDef : D.PosDef
  /-- The positive-orthant slice of the unit ellipsoid lies in `C`. -/
  unit_ellipsoid_inter_nonnegativeOrthant_subset :
    W[1](D) ∩ nonnegativeOrthant n ⊆ C
  /-- The set `C` lies in the positive-orthant slice of the outer ellipsoid of radius `γ √n`. -/
  subset_outer_ellipsoid_inter_nonnegativeOrthant :
    C ⊆ W[(γ * Real.sqrt (n : ℝ))](D) ∩ nonnegativeOrthant n

-- Proof sketch: apply the diagonal comparison theorem for positive homogeneous convex functions on
-- the nonnegative orthant to the gauge `f(x) = max_i ⟪a_i, x⟫ / b_i`, which is convex and
-- positively homogeneous because each `a_i` lies in `ℝⁿ_+` and each `b_i` is positive. The extra
-- boundedness hypothesis rules out degenerate orthant directions where all these inequalities stay
-- vacuous. The unit sublevel set of `f` is exactly `orthantHalfspacePolyhedron a b`, and the
-- comparison `‖x‖_D ≤ f(x) ≤ √n ‖x‖_D` rewrites as an orthant ellipsoidal rounding of
-- `orthantHalfspacePolyhedron a b`.
/-- Theorem 7.9: if `a_i ∈ ℝⁿ_+`, `b_i > 0` for `i = 1, …, m`, and the orthant polyhedron
`{x ∈ ℝⁿ_+ | ⟪a_i, x⟫ ≤ b_i for all i}` is bounded, then it is sandwiched between
`W₁(D) ∩ ℝⁿ_+` and `W_{√n}(D) ∩ ℝⁿ_+` for some diagonal positive-definite matrix `D`. -/
theorem exists_positive_diagonal_rounding_of_orthant_polyhedron
    (a : Fin m → Eₙ) (b : Fin m → ℝ)
    (ha_nonneg : ∀ i : Fin m, a i ∈ nonnegativeOrthant n)
    (hb_pos : ∀ i : Fin m, 0 < b i)
    (h_bounded : Bornology.IsBounded (orthantHalfspacePolyhedron a b)) :
    ∃ D : Matₙ, D.IsDiag ∧
      IsOrthantEllipsoidalRounding (orthantHalfspacePolyhedron a b) 1 D := sorry

end
