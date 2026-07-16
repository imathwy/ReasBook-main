import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1
import StacksProject_2024.stacks_project.Chap28.Lemma_28_5_12
import StacksProject_2024.stacks_project.Chap29.Definition_29_50_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (ℱ : X.Modules) [ℱ.IsQuasicoherent]

-- Semantic recall: `lean_leansearch` surfaced the stalk-local associated-prime infrastructure for
-- locally Noetherian schemes, while the local project already packages the source hypothesis as
-- `X.minimalSpecializationPoints (moduleSupport ℱ)` and the generic-point corollary through
-- `genericPointsOfIrreducibleComponents`.

/-- Lemma 31.2.9 (1): for a quasi-coherent `\mathcal O_X`-module `\mathcal F` on a locally
Noetherian scheme `X`, every point of the support of `\mathcal F` which is not a specialization of
another point of the support is an associated point of `\mathcal F`. -/
theorem minimalSpecializationPoints_support_subset_associatedPoints :
    X.minimalSpecializationPoints (moduleSupport ℱ) ⊆ associatedPoints ℱ := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- Lemma 31.2.9 (2): any generic point of an irreducible component of a locally Noetherian scheme
`X` is an associated point of `X`. This is the structure-sheaf specialization of the module-level
support statement above. -/
theorem genericPointsOfIrreducibleComponents_subset_associatedPoints :
    genericPointsOfIrreducibleComponents X ⊆ X.associatedPoints := sorry

end AlgebraicGeometry.Scheme
