import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_28_10

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owner
-- `AlgebraicGeometry.LocallyOfFinitePresentation` together with the sheaf owner
-- `SheafOfModules.IsFinitePresentation`; local Chapter 29 precedent in `Lemma_29_32_12` already
-- fixes `Ω[f.toShHom]` as the source-facing sheaf of relative differentials.

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- Lemma 29.32.13: let `f : X ⟶ S` be a morphism of schemes. If `f` is locally of finite
presentation, then `\Omega_{X/S}` is an `\mathcal O_X`-module of finite presentation. -/
@[stacks 01V3]
theorem isFinitePresentation_differentials_of_locallyOfFinitePresentation
    (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    (Ω[f.toShHom]).IsFinitePresentation := sorry

end AlgebraicGeometry
