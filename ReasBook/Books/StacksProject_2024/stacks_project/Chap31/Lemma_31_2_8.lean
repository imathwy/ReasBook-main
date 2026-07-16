import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent] [IsLocallyNoetherian X]

-- Semantic recall: `lean_leansearch` only surfaced general locally Noetherian scheme API, while
-- local Chapter 31 precedent fixes the source-facing owner as `Scheme.Modules.associatedPoints`
-- and the global-to-open restriction map as the canonical presheaf map from `⊤` to `U`.

/-- Lemma 31.2.8: let `X` be a locally Noetherian scheme, let `\mathcal F` be a quasi-coherent
`\mathcal O_X`-module, and let `U ⊆ X` be open. If `Ass(\mathcal F) ⊆ U`, then the restriction
map `\Gamma(X, \mathcal F) \to \Gamma(U, \mathcal F)` is injective. -/
@[stacks 0B3L]
theorem injective_restrictionToOpen_of_associatedPoints_subset
    (U : X.Opens) (hU : associatedPoints ℱ ⊆ (U : Set X)) :
    Function.Injective
      (ℱ.val.map (TopologicalSpace.Opens.leTop U).op) := sorry

end AlgebraicGeometry.Scheme.Modules
