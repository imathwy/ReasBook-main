import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

section CoherentPullback

variable {X Y : Scheme.{u}}
variable [IsIntegral X] [IsIntegral Y]
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable (f : X ⟶ Y) [Flat f] (𝒢 : Y.Modules) [𝒢.IsCoherent]

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-level flatness owner
-- `AlgebraicGeometry.Flat`, the pullback owner `Scheme.Modules.pullback`, and the algebraic
-- analogue `Module.IsReflexive.baseChange_of_flat`; local Chapter 31 precedent fixes the
-- reflexive-sheaf owner as `Scheme.Modules.IsReflexive`.

/-- Lemma 31.12.6 (1): for a flat morphism `f : X ⟶ Y` of integral locally Noetherian schemes and
a coherent `\mathcal O_Y`-module `\mathcal G`, the pullback `f^*\mathcal G` is a
coherent `\mathcal O_X`-module. -/
theorem pullback_isCoherent_of_flat :
    ((Scheme.Modules.pullback f).obj 𝒢).IsCoherent := sorry

/-- The pullback of a coherent module along a flat morphism is coherent. This companion instance
exposes Lemma 31.12.6 (1) to the typeclass system for use in reflexivity statements. -/
instance instIsCoherent_pullback_of_flat :
    ((Scheme.Modules.pullback f).obj 𝒢).IsCoherent :=
  pullback_isCoherent_of_flat f 𝒢

end CoherentPullback

section ReflexivePullback

variable {X Y : Scheme.{u}}
variable [IsIntegral X] [IsIntegral Y]
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]
variable [MonoidalCategory Y.Modules] [BraidedCategory Y.Modules] [MonoidalClosed Y.Modules]
variable (f : X ⟶ Y) [Flat f]
variable (𝒢 : Y.Modules) [𝒢.IsCoherent] [IsReflexive 𝒢]

/-- Lemma 31.12.6 (2): for a flat morphism `f : X ⟶ Y` of integral locally Noetherian schemes and
a coherent reflexive `\mathcal O_Y`-module `\mathcal G`, the pullback `f^*\mathcal G` is a
reflexive `\mathcal O_X`-module. -/
theorem pullback_isReflexive_of_flat :
    IsReflexive ((Scheme.Modules.pullback f).obj 𝒢) := sorry

/-- The pullback of a coherent reflexive module along a flat morphism is reflexive. This companion
instance exposes Lemma 31.12.6 (2) to the typeclass system for downstream pullback arguments. -/
instance instIsReflexive_pullback_of_flat :
    IsReflexive ((Scheme.Modules.pullback f).obj 𝒢) :=
  pullback_isReflexive_of_flat f 𝒢

end ReflexivePullback

end AlgebraicGeometry.Scheme.Modules
