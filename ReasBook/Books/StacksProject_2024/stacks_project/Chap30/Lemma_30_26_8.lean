import Mathlib
import StacksProject_2024.Chap29.Lemma_29_5_3
import StacksProject_2024.Chap30.Lemma_30_26_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Scheme.IdealSheafData

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` returned `AlgebraicGeometry.IsProper`,
-- `AlgebraicGeometry.IsProper.isStableUnderBaseChange`, and
-- `AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange`; local Chapter 29/30 precedent
-- represents the support of a scheme module by `moduleSupport` and properness over a base by the
-- closed subscheme attached to that support through `vanishingIdeal`.

/-- Pullback of a finite type scheme module is finite type, used locally to form the closed
support of the pulled-back module. -/
local instance instPullbackModuleSupportFiniteType
    {X Y : Scheme.{u}} (f : Y ⟶ X) (ℱ : X.Modules) [ℱ.IsFiniteType] :
    ((Scheme.Modules.pullback f).obj ℱ).IsFiniteType := sorry

/-- Pullback of a quasi-coherent scheme module is quasi-coherent, used locally to form the closed
support of the pulled-back module. -/
local instance instPullbackModuleSupportQuasicoherent
    {X Y : Scheme.{u}} (f : Y ⟶ X) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj ℱ).IsQuasicoherent := sorry

/-- Lemma 30.26.8: in a cartesian diagram of schemes, if `f : X ⟶ S` is locally of
finite type and `ℱ` is a finite type quasi-coherent `\mathcal O_X`-module whose support is proper
over `S`, then the support of the pullback `(g')^*ℱ` is proper over `S'`. -/
@[stacks 0CYT]
theorem moduleSupport_pullback_isProper_over_base
    {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (sq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [IsProper ((vanishingIdeal
      (⟨moduleSupport ℱ, Scheme.Modules.isClosed_moduleSupport ℱ⟩ :
        TopologicalSpace.Closeds X)).subschemeι ≫ f)] :
    IsProper ((vanishingIdeal
      (⟨moduleSupport ((Scheme.Modules.pullback g').obj ℱ),
        Scheme.Modules.isClosed_moduleSupport ((Scheme.Modules.pullback g').obj ℱ)⟩ :
        TopologicalSpace.Closeds X')).subschemeι ≫ f') := sorry

end AlgebraicGeometry
