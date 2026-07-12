import Mathlib.Algebra.Lie.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u𝔤

variable {𝔤 : Type u𝔤} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

-- Semantic recall note: no `lean_leansearch`-style MCP tool was available in this runner, so this
-- recall-only item was verified directly against `Mathlib.Algebra.Lie.Basic`.

/-
Definition 8.60-extra-2 is recall-only.

The canonical mathlib notion of a real Lie algebra is a type `𝔤`
equipped with instances `[LieRing 𝔤] [LieAlgebra ℝ 𝔤]`. Bilinearity is expressed by
`add_lie`, `lie_add`, `smul_lie`, and `lie_smul`; antisymmetry is available as `lie_skew`; and
the Jacobi identity is available as `lie_jacobi`.
-/
recall LieRing
recall LieAlgebra
recall add_lie
recall lie_add
recall smul_lie
recall lie_smul
recall lie_skew
recall lie_jacobi
