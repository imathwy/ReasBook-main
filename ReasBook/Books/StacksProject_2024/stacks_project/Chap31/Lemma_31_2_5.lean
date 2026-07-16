import Mathlib
import StacksProject_2024.stacks_project.Chap30.Lemma_30_9_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

-- Semantic recall: `lean_leansearch` surfaced the quasi-compact affine-open finite-union API
-- `isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen`; local Chapter 31 precedent fixes the
-- sheaf-side owner as `Scheme.Modules.associatedPoints`, with Chapter 30 providing coherence as
-- the source-facing route to quasi-coherence.

/-- Helper for Lemma 31.2.5: in this file, a coherent `\mathcal O_X`-module is used through its
quasi-coherent associated-points interface. -/
local instance instIsQuasicoherentOfIsCoherentForLemma3125 : ℱ.IsQuasicoherent := sorry

/-- Lemma 31.2.5: let `X` be a locally Noetherian scheme and let `ℱ` be a coherent
`\mathcal O_X`-module. Then `Ass(ℱ) ∩ U` is finite for every quasi-compact open
`U ⊆ X`. -/
@[stacks 05AF]
theorem associatedPoints_inter_quasiCompactOpen_finite
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    (associatedPoints ℱ ∩ (U : Set X)).Finite := sorry

end AlgebraicGeometry.Scheme.Modules
