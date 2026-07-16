import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.KrullDimension.Basic
import StacksProject_2024.stacks_project.Chap28.Definition_28_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Owner choice: the source-facing content here is the scheme-specific bridge from the local
-- dimension `topologicalKrullDimAt x` to the Krull dimension of the canonical local ring
-- `X.presheaf.stalk x`, together with the resulting global supremum formula over stalk dimensions.
-- The ambient topological owners remain `topologicalKrullDim` and `topologicalKrullDimAt`.

variable (X : Scheme.{u})

/-- Companion bridge for Lemma 28.10.2: for a scheme `X`, the local dimension at `x` equals the
Krull dimension of the local ring `𝒪_{X,x}`, formalized as `X.presheaf.stalk x`. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_stalk (x : X) :
    topologicalKrullDimAt x = ringKrullDim (X.presheaf.stalk x) := sorry

/-- Lemma 28.10.2 (1 = 2): the dimension of a scheme `X` is the supremum of the Krull dimensions
of its local rings `X.presheaf.stalk x`. -/
@[stacks 04MU]
theorem topologicalKrullDim_eq_iSup_ringKrullDim_stalk :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.Scheme
