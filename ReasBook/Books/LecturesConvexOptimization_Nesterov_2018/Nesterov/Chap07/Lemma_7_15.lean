import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators MatrixOrder RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₙ" => Fin n → ℝ
local notation "SymmMat" => 𝕊^n

/-
Lemma 7.15 lies in Chapter 7's positive-definite / semidefinite-factorization domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n`, `𝕊^n₊`, and `𝕊^n₊₊`, the project owners for symmetric, positive-semidefinite,
  and strict positive-definite matrices;
- `StrictPositiveSemidefiniteCone.inv`, the canonical inverse view of a strict-cone point;
- `mem_positiveSemidefiniteCone_iff`, the bridge from intrinsic cone membership to
  `Matrix.PosSemidef`;
- mathlib `Matrix.toQuadraticMap'`, the canonical quadratic-form owner on `Fin n → ℝ`.

Best owner abstraction:
- source-facing: Lemma 7.15's inverse-diagonal relaxation value and its semidefinite
  representation;
- core/canonical: the Chapter 5 symmetric-matrix cone owners together with
  `Matrix.toQuadraticMap'`;
- bridge/view: the textbook matrix-order and trace formulas recovered by the membership and
  expansion lemmas below.

Primitive data:
- `A : 𝕊^n₊₊`;
- `L : Mₙ`.

Derived API:
- inverse-diagonal feasibility expressed intrinsically by the PSD slack
  `A⁻¹ - diag(u) ∈ 𝕊^n₊`;
- semidefinite feasibility expressed on the symmetric carrier by `X ∈ 𝕊^n₊` and `trace X = 1`;
- the semidefinite objective written through the canonical quadratic-map owner instead of the
  duplicate entrywise formula `dotProduct (X.mulVec v) v`.

This refinement keeps the source-facing real-valued `inf`/`sup` statements, but removes the
parallel subtype `{A // A.PosDef}` and raw `Matrix.PosSemidef` surface from the primitive public
API. The textbook inequalities remain as bridge theorems.
-/

/-- The feasible diagonal vectors `u` for the inverse-diagonal relaxation, expressed intrinsically
by requiring the symmetric slack matrix `A⁻¹ - diag(u)` to be positive semidefinite and each
coordinate of `u` to be positive. -/
def factorizationDiagonalInverseFeasibleSet
    (A : 𝕊^n₊₊) : Set Eₙ :=
  {u |
    (StrictPositiveSemidefiniteCone.inv A -
        ⟨Matrix.diagonal u, by
          rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
          simp
        ⟩ : SymmMat) ∈ 𝕊^n₊ ∧
      ∀ i : Fin n, 0 < u i}

-- Proof sketch: expand membership in `𝕊^n₊` for the slack matrix `A⁻¹ - diag(u)`, then use
-- `Matrix.nonneg_iff_posSemidef` to recover the textbook matrix-order inequality
-- `diag(u) ≤ A⁻¹`.
/-- Membership in the inverse-diagonal feasible set means exactly that `diag(u) ≤ A⁻¹` and every
coordinate of `u` is positive. -/
theorem mem_factorizationDiagonalInverseFeasibleSet_iff
    (A : 𝕊^n₊₊) (u : Eₙ) :
    u ∈ factorizationDiagonalInverseFeasibleSet A ↔
      Matrix.diagonal u ≤ (((A : SymmMat) : Mₙ)⁻¹) ∧ ∀ i : Fin n, 0 < u i := by
  rw [factorizationDiagonalInverseFeasibleSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hfeas, hpos⟩
    rw [mem_positiveSemidefiniteCone_iff] at hfeas
    refine ⟨?_, hpos⟩
    exact sub_nonneg.mp <| by
      simpa using (Matrix.nonneg_iff_posSemidef).mpr hfeas
  · rintro ⟨hdiag, hpos⟩
    refine ⟨?_, hpos⟩
    rw [mem_positiveSemidefiniteCone_iff]
    exact (Matrix.nonneg_iff_posSemidef).mp <| by
      simpa using sub_nonneg.mpr hdiag

/-- The inverse-diagonal relaxation value
`inf {∑ᵢ uᵢ⁻¹ | diag(u) ≤ A⁻¹, uᵢ > 0}` attached to a positive-definite matrix `A`. -/
def factorizationDiagonalInverseRelaxationValue
    (A : 𝕊^n₊₊) : ℝ :=
  sInf ((fun u : Eₙ ↦ ∑ i : Fin n, (u i)⁻¹) '' factorizationDiagonalInverseFeasibleSet A)

/-- Expanding `factorizationDiagonalInverseRelaxationValue A` recovers the defining infimum over
the feasible diagonal vectors `u`. -/
theorem factorizationDiagonalInverseRelaxationValue_eq_sInf
    (A : 𝕊^n₊₊) :
    factorizationDiagonalInverseRelaxationValue A =
      sInf ((fun u : Eₙ ↦ ∑ i : Fin n, (u i)⁻¹) '' factorizationDiagonalInverseFeasibleSet A) :=
  rfl

/-- The feasible matrices `X` in the semidefinite representation: positive semidefinite symmetric
matrices with unit trace. -/
def factorizationSemidefiniteFeasibleSet : Set SymmMat :=
  {X | X ∈ 𝕊^n₊ ∧ Matrix.trace (X : Mₙ) = 1}

/-- Membership in the semidefinite feasible set means being positive semidefinite with unit trace.
-/
theorem mem_factorizationSemidefiniteFeasibleSet_iff
    (X : SymmMat) :
    X ∈ factorizationSemidefiniteFeasibleSet ↔
      (X : Mₙ).PosSemidef ∧ Matrix.trace (X : Mₙ) = 1 := by
  rw [factorizationSemidefiniteFeasibleSet, Set.mem_setOf_eq, mem_positiveSemidefiniteCone_iff]

/-- The semidefinite objective
`X ↦ (∑ᵢ √(qᵢᵀ X qᵢ))²`, where `qᵢ` is the `i`-th column of `L`, written as the `i`-th row of
`Lᵀ`. -/
def factorizationSemidefiniteObjective (L : Mₙ) (X : SymmMat) : ℝ :=
  (∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) ^ (2 : ℕ)

/-- The semidefinite relaxation value attached to the factor matrix `L`. -/
def factorizationSemidefiniteRelaxationValue (L : Mₙ) : ℝ :=
  sSup (factorizationSemidefiniteObjective L '' factorizationSemidefiniteFeasibleSet)

/-- Expanding `factorizationSemidefiniteRelaxationValue L` gives the defining supremum of
`(∑ᵢ √(qᵢᵀ X qᵢ))²` over positive-semidefinite trace-one matrices `X`. -/
theorem factorizationSemidefiniteRelaxationValue_eq_sSup
    (L : Mₙ) :
    factorizationSemidefiniteRelaxationValue L =
      sSup (factorizationSemidefiniteObjective L '' factorizationSemidefiniteFeasibleSet) :=
  rfl

-- Proof sketch: start from the inverse-diagonal formulation of `ψ⋆`, form the Lagrange dual with
-- a positive-semidefinite multiplier, maximize along a fixed ray to obtain the quadratic-root
-- objective, and then apply the change of variables `X = L^{-T} Y L^{-1}` using
-- `A = Lᵀ L`.
/-- Lemma 7.15: if `A = Lᵀ L`, then the value
`ψ⋆ = inf {∑ᵢ uᵢ⁻¹ | diag(u) ≤ A⁻¹, uᵢ > 0}` admits the semidefinite representation
`sup {([∑ᵢ √(qᵢᵀ X qᵢ)]^2) | X ⪰ 0, trace X = 1}`, where `qᵢ` are the columns of `L`. -/
theorem factorizationDiagonalInverseRelaxationValue_eq_semidefiniteRelaxationValue
    (A : 𝕊^n₊₊) (L : Mₙ) (hA : ((A : SymmMat) : Mₙ) = Lᵀ * L) :
    factorizationDiagonalInverseRelaxationValue A =
      factorizationSemidefiniteRelaxationValue L := by
  sorry
