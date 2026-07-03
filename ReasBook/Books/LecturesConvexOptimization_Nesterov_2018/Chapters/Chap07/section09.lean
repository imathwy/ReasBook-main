import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_9 (from Chap07) -/
noncomputable section

universe u

section

/-- Definition 7.9: the a priori radius estimate attached to a function `f`, a base point `x0`,
and a scalar `γ₀` is the quantity `γ₀⁻¹ f(x₀)`. -/
def aPrioriRadiusEstimate {X : Type u} (f : X → ℝ) (γ₀ : ℝ) (x0 : X) : ℝ :=
  f x0 / γ₀

/-- The a priori radius estimate can equivalently be written as the quotient `f x0 / γ₀`. -/
@[simp]
theorem aPrioriRadiusEstimate_eq_div {X : Type u} (f : X → ℝ) (γ₀ : ℝ) (x0 : X) :
    aPrioriRadiusEstimate f γ₀ x0 = f x0 / γ₀ := rfl

end

/-! ### Lemma_7_9 (from Chap07) -/
noncomputable section

open EuclideanSpace (positiveOrthant)
open Matrix
open scoped BigOperators EllipsoidNotation SymmetricBox

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Lemma 7.9 lies in Chapter 7's diagonal ellipsoid / symmetric-box rounding domain.

Sampled owner-style declarations:
- `symmetricBox` with notation `B(g)` in `Chap07/Definition_7_33`, the chapter owner for
  coordinate boxes;
- `mem_symmetricBox_iff_abs_le` in `Chap07/Definition_7_33`, the owner theorem for the textbook
  absolute-value membership view of `B(a)`;
- `matrixEllipsoid` with centered notation `W[r](G)` in `Chap07/Definition_7_26`, the chapter
  owner for ellipsoids;
- `IsEllipsoidalRounding` in `Chap07/Definition_7_29`, the chapter owner for centered
  `γ √n`-ellipsoidal roundings;
- `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` in
  `Chap01/Definition_1_10_2`, the canonical positivity owner for the semiaxis vector.

Best owner abstraction:
- source-facing: the symmetric-box sandwich hypothesis and the resulting diagonal ellipsoidal
  rounding;
- core/canonical: `positiveOrthant`, `B(g)`, `W[r](G)`, and `IsEllipsoidalRounding`;
- bridge/view: the coordinate membership theorems specialized to `B(a)` and
  `W[r](Matrix.diagonal fun i ↦ (a i)^2)`.

Primitive data:
- the semiaxis vector `a : E`;
- a set `C : Set E`;
- a dilation factor `m : ℝ`.

Derived API:
- the inner box `B(a)` and outer box `B(m • a)`, read through
  `mem_symmetricBox_iff_abs_le`;
- the diagonal shape matrix `Matrix.diagonal fun i ↦ (a i)^2`, whose semiaxes are `a i`;
- the centered rounding datum
  `IsEllipsoidalRounding C m (Matrix.diagonal fun i ↦ (a i)^2)`;
- the inner and outer ellipsoid containments recovered canonically from that owner.

Source/core/bridge triage:
- source-facing: the sandwich theorem below;
- core/canonical: `positiveOrthant`, `B(g)`, `mem_symmetricBox_iff_abs_le`, `W[r](G)`, and
  `IsEllipsoidalRounding`;
- bridge/view: the diagonal-square ellipsoid membership theorem specialized to
  `W[r](Matrix.diagonal fun i ↦ (a i)^2)`.

This refinement deletes the local duplicate box-membership theorem and reuses the Chapter 7 box
owner `B(·)` together with `mem_symmetricBox_iff_abs_le` directly. The main theorem is now stated
through the Chapter 7 rounding owner `IsEllipsoidalRounding` instead of exposing its positive
definiteness and ellipsoid containments as a parallel conjunction, while the ambient dimension now
matches the chapter owners at `{n : ℕ}` instead of unnecessarily strengthening to `ℕ+`.
-/

-- Proof sketch: specialize the centered ellipsoid owner `W[r](G)` to the diagonal-square matrix
-- `G = D²` with `D = diag(d)`, then expand the inverse diagonal quadratic form.
/-- Membership in the diagonal ellipsoid with shape matrix `D²`, where `D = diag(d)`, is exactly
the coordinate inequality `sqrt (∑ i, (x i / d i)^2) ≤ r` when the semiaxes `d i` are positive.
-/
theorem mem_diagonalSquareEllipsoid_iff
    (a : E) (ha : a ∈ positiveOrthant n) (r : ℝ) (x : E) :
    x ∈ W[r]((diagonal fun i ↦ (a i) ^ (2 : ℕ))) ↔
      Real.sqrt (∑ i, (x i / a i) ^ (2 : ℕ)) ≤ r := sorry

-- Proof sketch: the inner containment `W[1](D²) ⊆ B(d)` is the coordinatewise estimate
-- `|x i| / d i ≤ 1` obtained by bounding each nonnegative summand in
-- `∑ i, (x i / d i)^2 ≤ 1`. For the outer containment, `x ∈ B(m d)` gives
-- `|x i| / d i ≤ m` for each coordinate, so
-- `∑ i, (x i / d i)^2 ≤ n * m^2`, equivalently
-- `sqrt (∑ i, (x i / d i)^2) ≤ m * sqrt n`.
/-- Lemma 7.9: if a set `C` lies between the boxes `B(d)` and `B(m d)`, where the semiaxes `d i`
are positive, then `C` lies between the corresponding diagonal ellipsoids
`W₁(D²)` and `W_{m √n}(D²)`, where `D = diag(d)`. Equivalently, the diagonal-square matrix
`D²` is an ellipsoidal rounding of `C` with parameter `m`. -/
theorem symmetricBox_sandwich_implies_diagonalEllipsoid_sandwich
    (a : E) (ha : a ∈ positiveOrthant n) {m : ℝ} {C : Set E}
    (h_left : B(a) ⊆ C)
    (h_right : C ⊆ B((m • a))) :
    IsEllipsoidalRounding C m (diagonal fun i ↦ (a i) ^ (2 : ℕ)) := sorry

end

/-! ### Proposition_7_9 (from Chap07) -/
noncomputable section

open Matrix
open scoped BigOperators Matrix

universe u

variable {ι : Type u} [Fintype ι]
variable {m : ℕ}
variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- This file keeps the finite-family weighted Gram-matrix owner used downstream in Chapter 7 and
adds the convex-combination invariant behind the rank-one update rule of Algorithm 7.6.

Relevant owner-style declarations sampled before refinement:
- `Matrix.vecMulVec`, the canonical rank-one outer-product owner in mathlib;
- `Matrix.vecMulVec_apply`, the canonical entrywise bridge for that owner;
- `centralSymmetricRoundingUpdatedMatrix` in `Algorithm_7_5`, the Chapter 7 owner of the
  Algorithm 7.6 rank-one matrix update;
- `TrussTopologyDesignProblem.stiffnessMatrix` in `Definition_7_22`, the chapter's specialized
  weighted-sum-of-rank-one-matrices owner for truss data.

Best owner abstraction:
- source-facing: `weightedGramMatrix` and the convex-combination invariant for repeated rank-one
  updates from a fixed finite family;
- core/canonical: `vecMulVec` for the rank-one summands;
- bridge/view: the entrywise evaluation lemma and the simplex-weight statements below.

Primitive data:
- a finite family `a : ι → ℝⁿ` or `a : Fin m → ℝⁿ`;
- a weight function `w : ι → ℝ`;
- the update coefficients `αₖ ∈ [0, 1]` and the chosen generators `a_{jₖ}`.

Derived API:
- the textbook notation `B[a](w)`;
- the entrywise formula for `B[a](w)`;
- the one-step and iterated preservation of the simplex-weighted Gram-matrix form.

The right public owner here is the general weighted Gram matrix itself. `Definition_7_22`
specializes the same pattern to truss geometry, and `Proposition_7_7` already depends on this
general owner. The current item is therefore expressed as a theorem on repeated
`centralSymmetricRoundingUpdatedMatrix` steps rather than by introducing a second wrapper around
Algorithm 7.6. -/

/-- The weighted Gram matrix `∑ᵢ wᵢ aᵢ aᵢᵀ` associated to a finite family of vectors in `ℝⁿ`. -/
def weightedGramMatrix (a : ι → Eₙ) (w : ι → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, w i • Matrix.vecMulVec (a i) (a i)

namespace WeightedGramMatrix

/- Source-facing Lean notation for the textbook operator `B(w)` attached to the family `a`. -/
scoped notation:max "B[" a:arg "](" w:arg ")" => weightedGramMatrix a w

end WeightedGramMatrix

open scoped WeightedGramMatrix

-- Proof sketch: expand the `(p, q)` entry of each rank-one matrix `aᵢ aᵢᵀ` and distribute the
-- finite sum over the matrix entries.
/-- Evaluating the weighted Gram matrix entrywise gives the coefficient-weighted sum
`∑ᵢ wᵢ aᵢ(p) aᵢ(q)`. -/
theorem weightedGramMatrix_apply (a : ι → Eₙ) (w : ι → ℝ)
    (p q : Fin n) :
    B[a](w) p q = ∑ i, w i * a i p * a i q := sorry

section ConvexCombinationStructure

-- Proof sketch: expand
-- `centralSymmetricRoundingUpdatedMatrix (B[a](λ.weights)) (a j) α` as
-- `(1 - α) ∑ i, λᵢ aᵢ aᵢᵀ + α aⱼ aⱼᵀ`, then absorb the last term into the updated simplex weights
-- whose `j`-th coordinate becomes `(1 - α) λⱼ + α` and whose other coordinates become
-- `(1 - α) λᵢ`.
/-- A single rank-one update with coefficient `α ∈ [0, 1]` preserves the simplex-weighted Gram
matrix form attached to the family `a₁, …, aₘ`. -/
theorem exists_simplex_weights_of_weightedGramMatrix_update
    (a : Fin m → Eₙ) (weights : StdSimplex ℝ (Fin m)) (j : Fin m) {α : ℝ}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1) :
    ∃ weights' : StdSimplex ℝ (Fin m),
      centralSymmetricRoundingUpdatedMatrix (B[a](weights.weights)) (a j) α =
        B[a](weights'.weights) := sorry

-- Proof sketch: start from the initial simplex weights `λ₀`; apply the previous one-step
-- preservation theorem inductively along the update sequence
-- `Gₖ₊₁ = centralSymmetricRoundingUpdatedMatrix Gₖ a_{jₖ} αₖ`.
/-- Proposition 7.9 [Chapter7_1.json:55]: if a matrix sequence starts from a convex combination of
the rank-one matrices `aᵢ aᵢᵀ` and each step applies the Algorithm 7.6 rank-one update with some
coefficient `αₖ ∈ [0, 1]` and some chosen generator `a_{jₖ}`, then every `Gₖ` is again a convex
combination of the same rank-one matrices. -/
theorem exists_simplex_weights_for_rank_one_update_sequence
    (a : Fin m → Eₙ) (G : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (choice : ℕ → Fin m) (α : ℕ → ℝ) (weights0 : StdSimplex ℝ (Fin m))
    (hG0 : G 0 = B[a](weights0.weights))
    (hα : ∀ k : ℕ, 0 ≤ α k ∧ α k ≤ 1)
    (hGsucc :
      ∀ k : ℕ,
        G (k + 1) =
          centralSymmetricRoundingUpdatedMatrix (G k) (a (choice k)) (α k)) :
    ∀ k : ℕ, ∃ weightsk : StdSimplex ℝ (Fin m), G k = B[a](weightsk.weights) := sorry

end ConvexCombinationStructure

/-! ### Theorem_7_9 (from Chap07) -/
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
