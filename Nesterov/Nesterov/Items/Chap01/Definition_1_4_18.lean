import Mathlib.Analysis.Matrix.Order

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MatrixOrder

/- Definition 1.4.18 is a source-facing recall of positive semidefinite and positive definite real
square matrices, implemented by the generic matrix-positivity owners below and specialized here to
the textbook setting over `ℝ`.

Primary domain:
- matrix positivity and the induced order on real matrices.

Sampled owner-style declarations:
- `Matrix.PosSemidef`
- `Matrix.PosDef`
- `Matrix.nonneg_iff_posSemidef`
- `Matrix.isStrictlyPositive_iff_posDef`

Best owner abstraction:
- the canonical matrix-positivity owners `Matrix.PosSemidef` and `Matrix.PosDef`

Primitive data:
- a square matrix `B`

Derived API:
- the order-notation bridges `Matrix.nonneg_iff_posSemidef`
- the strict-order bridge `Matrix.isStrictlyPositive_iff_posDef`

Source/core/bridge triage:
- source-facing: the textbook notions `B ≥ 0` and `B > 0` for real square matrices
- core/canonical: `Matrix.PosSemidef` and `Matrix.PosDef`
- bridge/view: `Matrix.nonneg_iff_posSemidef` and `Matrix.isStrictlyPositive_iff_posDef`

This file therefore recalls the owner predicates directly, keeping the order-notation lemmas only
as companion bridges for the textbook notation `B ≥ 0` and `B > 0`.
-/

section

variable {n : Type*} (B : Matrix n n ℝ)

/- Definition 1.4.18: the textbook notation `B ≥ 0` for a symmetric real matrix means that `B`
is positive semidefinite; the canonical owner notion is `Matrix.PosSemidef`. -/
#check (B.PosSemidef : Prop)

/- Positive definiteness is the corresponding canonical matrix-positivity notion. -/
#check (B.PosDef : Prop)

/- The matrix-order notation `0 ≤ B` is exactly positive semidefiniteness. -/
#check (Matrix.nonneg_iff_posSemidef : 0 ≤ B ↔ B.PosSemidef)

end

section

variable {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ)

/- In the textbook real-matrix setting, the canonical strict-positivity predicate is exactly
positive definiteness. -/
#check (Matrix.isStrictlyPositive_iff_posDef : IsStrictlyPositive B ↔ B.PosDef)

end
