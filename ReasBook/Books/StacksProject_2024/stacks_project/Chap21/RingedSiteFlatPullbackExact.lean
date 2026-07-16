import StacksProject_2024.stacks_project.Chap18.Definition_18_31_1

open CategoryTheory
open CategoryTheory.Limits
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [Fact (IsFlat f)]

/-- Flat pullback on module sheaves preserves finite limits. -/
instance pullback_preservesFiniteLimits_of_isFlat :
    PreservesFiniteLimits (f^*) := by
  let hexact := IsFlat.pullback_exact f Fact.out
  exact (exactFunctor_iff (f^*)).1 hexact |>.1

/-- Flat pullback on module sheaves preserves finite colimits. -/
instance pullback_preservesFiniteColimits_of_isFlat :
    PreservesFiniteColimits (f^*) := by
  let hexact := IsFlat.pullback_exact f Fact.out
  exact (exactFunctor_iff (f^*)).1 hexact |>.2

end

end RingedSite.Hom
