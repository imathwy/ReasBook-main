import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_28_10

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced the canonical owners
-- `AlgebraicGeometry.LocallyOfFiniteType` and `SheafOfModules.IsFiniteType`; local Chapter 17/29
-- precedent fixes `Ω[f.toShHom]` as the source-facing sheaf of relative differentials for a
-- scheme morphism `f`. This item is therefore a thin bridge on the canonical differential sheaf.

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- Lemma 29.32.12: let `f : X ⟶ S` be a morphism of schemes. If `f` is locally of finite type,
then `\Omega_{X/S}` is a finite type `\mathcal O_X`-module. -/
@[stacks 01V2]
theorem isFiniteType_differentials_of_locallyOfFiniteType
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    (Ω[f.toShHom]).IsFiniteType := sorry

end AlgebraicGeometry
