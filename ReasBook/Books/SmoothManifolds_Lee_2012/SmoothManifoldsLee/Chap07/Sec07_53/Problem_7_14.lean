import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Group.Matrix
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_49.Definition_7_49_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_53.Problem_7_13

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped Matrix.Norms.Operator LieGroup Manifold ContDiff MatrixGroups

noncomputable section

-- Semantic recall via `lean_leansearch` confirmed the canonical matrix owner
-- `Matrix.specialUnitaryGroup`; local precedent then fixed the source-facing Chapter 7 surface as
-- the actual special unitary group `SU(n)` together with `Set.IsProperlyEmbedded` for its ambient
-- embeddedness inside `U(n)`.

local notation "U(" n ")" => Matrix.unitaryGroup (Fin n) ℂ
local notation "SU(" n ")" => Matrix.specialUnitaryGroup (Fin n) ℂ

/-- The canonical inclusion `SU(n) →* U(n)`. -/
def specialUnitaryToUnitary (n : ℕ) : SU(n) →* U(n) where
  toFun A := ⟨A.1, Matrix.specialUnitaryGroup_le_unitaryGroup A.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The subgroup of `U(n)` consisting of the special unitary matrices. -/
def specialUnitarySubgroupInUnitary (n : ℕ) : Subgroup (U(n)) :=
  (specialUnitaryToUnitary n).range

section ComplexSpecialUnitaryLieSubgroup

variable {n : ℕ}
local notation "M_U(" n ")" => Fin n → Fin n → ℂ
local notation "I_U(" n ")" => 𝓘(ℝ, M_U(n))
variable [ChartedSpace M_U(n) (U(n))] [LieGroup I_U(n) ∞ (U(n))]
-- These statements use the canonical charted-space and Lie-group instances on `U(n)` inferred
-- from the standard matrix-algebra model.

/-- Problem 7-14 (1): for each `n ≥ 1`, the canonical special unitary subgroup of `U(n)` is the
carrier of a Lie subgroup whose model space has real dimension `n^2 - 1`. -/
theorem specialUnitarySubgroupInUnitary_has_lieSubgroup_structure
    (hn : 0 < n) :
    ∃ (S : LieSubgroup (I_U(n))) (h_finiteDimensional : FiniteDimensional ℝ S.ModelSpace),
      S.carrier = specialUnitarySubgroupInUnitary n ∧
      Module.finrank ℝ S.ModelSpace = n ^ 2 - 1 := sorry

/-- Problem 7-14 (2): for each `n ≥ 1`, the canonical special unitary subgroup of `U(n)` is
properly embedded in the ambient unitary group. -/
theorem specialUnitarySubgroupInUnitary_isProperlyEmbedded
    (hn : 0 < n) :
    (specialUnitarySubgroupInUnitary n : Set (U(n))).IsProperlyEmbedded := sorry

end ComplexSpecialUnitaryLieSubgroup
