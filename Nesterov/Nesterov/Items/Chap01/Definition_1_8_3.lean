import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : ℕ}

local notation "E" => Fin n → ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "PosMat" => {A : Mat // Matrix.PosDef A}

/- Definition 1.8.3 is a source-facing recall in the positive-definite matrix geometry of `ℝ^n`,
modeled as `Fin n → ℝ`.

Primary domain:
- inner products and norms induced by positive-(semi)definite matrices.

Sampled owner-style declarations:
- `Matrix.toNormedAddCommGroup`, the canonical norm owner attached to a positive-definite matrix;
- `Matrix.toInnerProductSpace`, the canonical inner-product owner attached to a positive
  semidefinite matrix;
- `Matrix.PosDef.posSemidef`, the bridge from the positive-definite hypothesis needed for the norm
  owner to the positive-semidefinite hypothesis needed for the inner-product owner;
- `Matrix.dotProduct_mulVec`, the coordinate formula used in the textbook expansion.

Best owner abstraction:
- the canonical induced structures `Matrix.toNormedAddCommGroup A hA` and
  `Matrix.toInnerProductSpace A hA.posSemidef`.

Primitive data:
- `A : Mat`
- `hA : A.PosDef`

Derived API:
- the source-facing notation `‖x‖[A]` and `⟪x, y⟫_[A]` for
  `A : PosMat`;
- the textbook coordinate formulas recorded below as thin bridge lemmas.

Source/core/bridge triage:
- source-facing: the induced norm and inner product attached to a positive-definite matrix;
- core/canonical: `Matrix.toNormedAddCommGroup` and `Matrix.toInnerProductSpace`;
- bridge/view: the notation layer `‖x‖[A]`, `⟪x, y⟫_[A]`, and the formula companions
  `inner_eq_dotProduct_mulVec`, `norm_eq_sqrt_dotProduct_mulVec`, implemented through private
  abbreviation-level notation bridges only.

This file therefore keeps Definition 1.8.3 as direct canonical recall/use of the induced owner
structures, rather than introducing a second public wrapper API for the same norm and inner
product.
-/

recall Matrix.toNormedAddCommGroup
    {n : Type*} {𝕜 : Type*} [Fintype n] [RCLike 𝕜] (M : Matrix n n 𝕜) (hM : M.PosDef) :
    NormedAddCommGroup (n → 𝕜)

recall Matrix.toInnerProductSpace
    {n : Type*} {𝕜 : Type*} [Fintype n] [RCLike 𝕜] (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    @InnerProductSpace 𝕜 (n → 𝕜) _ (M.toSeminormedAddCommGroup hM)

namespace Matrix
namespace PosDef

private abbrev weightedInner (A : PosMat) (x y : E) : ℝ :=
  @inner ℝ E (Matrix.toInnerProductSpace A.1 A.2.posSemidef).toInner x y

private abbrev weightedNorm (A : PosMat) (x : E) : ℝ :=
  @norm E (Matrix.toNormedAddCommGroup A.1 A.2).toNorm x

end PosDef
end Matrix

namespace MatrixPosDef

scoped notation:70 "⟪" x ", " y "⟫_[" A:arg "]" => Matrix.PosDef.weightedInner A x y
scoped notation:max "‖" x "‖[" A:arg "]" => Matrix.PosDef.weightedNorm A x

end MatrixPosDef

open scoped MatrixPosDef

namespace Matrix
namespace PosDef

/-- For a positive-definite real matrix owner, the weighted inner product is the textbook pairing
`⟪Ax, y⟫`. -/
theorem inner_eq_dotProduct_mulVec (A : PosMat) (x y : E) :
    ⟪x, y⟫_[A] = dotProduct (A.1 *ᵥ x) y := by
  change dotProduct (A.1 *ᵥ y) x = dotProduct (A.1 *ᵥ x) y
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose]
  have hA' : A.1ᴴ = A.1 := by
    simpa using A.2.1.eq
  rw [← conjTranspose_eq_transpose_of_trivial A.1, hA']

/-- For a positive-definite real matrix owner, the weighted norm is the square root of the weighted
quadratic form `⟪Ax, x⟫`. -/
theorem norm_eq_sqrt_dotProduct_mulVec (A : PosMat) (x : E) :
    ‖x‖[A] = Real.sqrt (dotProduct (A.1 *ᵥ x) x) := by
  rw [show ‖x‖[A] = Real.sqrt (⟪x, x⟫_[A]) by
    exact @norm_eq_sqrt_real_inner E
      (Matrix.toNormedAddCommGroup A.1 A.2).toSeminormedAddCommGroup
      (Matrix.toInnerProductSpace A.1 A.2.posSemidef) x]
  rw [inner_eq_dotProduct_mulVec]

end PosDef
end Matrix

end
