import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical structure-sheaf vanishing owners
-- `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact` and
-- `exists_of_res_zero_of_qcqs_of_top`; the Chapter 31 owner
-- `LocallyRingedSpace.meromorphicFunctionSheaf` from Definition 31.23.1 is the source-facing
-- meromorphic surface for this item.

variable {X : Scheme.{u}} [CompactSpace X]

local notation "MerX" => X.toLocallyRingedSpace.meromorphicFunctions
local notation "KX" => X.toLocallyRingedSpace.meromorphicFunctionSheaf
local notation "toMerX" => X.toLocallyRingedSpace.toMeromorphicFunctions

/-- Lemma 31.24.1: if a meromorphic function on a quasi-compact scheme restricts to zero on the
basic open `X_h`, then some power of `h` annihilates it in the ring of meromorphic functions. -/
theorem exists_pow_mul_eq_zero_of_meromorphic_restrict_eq_zero
    (h : Γ(X, ⊤)) (f : MerX)
    (hf : f |_ₕ (homOfLE (X.basicOpen_le h)) = 0) :
    ∃ n : ℕ, (toMerX h) ^ n * f = 0 := sorry

end AlgebraicGeometry
