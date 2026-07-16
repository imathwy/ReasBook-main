import StacksProject_2024.stacks_project.Chap28.Definition_28_26_1
import StacksProject_2024.stacks_project.Chap28.Lemma_28_26_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable (ℒ : X.Modules)
variable [hℒ : Invertible ℒ] [IsAmple ℒ]

-- Semantic recall: `lean_leansearch` surfaced the canonical `Proj` API
-- `AlgebraicGeometry.Proj.fromOfGlobalSections` and the local dependency `Lemma 28.26.9`
-- records the available construction layer for the canonical morphism from an invertible sheaf.
-- The current project has the Chapter 17 section-ring owner `Γ_*(ℒ)` at the ringed-space module
-- layer and the Chapter 28 ampleness owner `IsAmple ℒ`, but it does not yet package
-- `Proj(Γ_*(X, ℒ))`, the resulting morphism `f : X ⟶ Proj(Γ_*(X, ℒ))`, or the full `ℤ`-graded
-- algebra map `⊕ f^*𝒪_Y(n) ⟶ ⊕ ℒ^{⊗ n}` as concrete data. This situation is therefore a labeled
-- recall block rather than a wrapper declaration.

/- Situation 28.28.1: let `X` be a scheme and let `\mathcal L` be an ample invertible sheaf on
`X`. Set `S = Γ_*(X, \mathcal L)` as a graded ring, set `Y = Proj(S)`, and let
`f : X ⟶ Y` be the canonical morphism of Lemma 28.26.9. This morphism comes equipped with a
`\mathbf Z`-graded `\mathcal O_X`-algebra map
`⊕ f^*\mathcal O_Y(n) ⟶ ⊕ \mathcal L^{\otimes n}`. In the current dependency-closed API, the
graded section ring, the ampleness owner, and the generic `Proj.fromOfGlobalSections` morphism are
available, while this exact source-facing construction and comparison map are not yet packaged as
concrete declarations. -/
#check (IsAmple ℒ : Prop)
#check (hℒ : Invertible ℒ)
#check AlgebraicGeometry.RingedSpace.gradedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedGlobalSectionsDegree
#check AlgebraicGeometry.Proj
#check AlgebraicGeometry.Proj.fromOfGlobalSections
#check AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen

end AlgebraicGeometry.Scheme.Modules
