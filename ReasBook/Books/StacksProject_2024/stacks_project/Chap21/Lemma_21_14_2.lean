import StacksProject_2024.Chap12.Lemma_12_29_1
import StacksProject_2024.Chap18.Definition_18_13_1
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]

/- Domain-style sampling for Lemma 21.14.2:
- primary domain: adjunctions, exact functors, and injective-object preservation for module sheaves
  on ringed sites;
- sampled owner declarations:
  `Functor.PreservesInjectiveObjects`,
  `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`,
  `RingedSite.Hom.IsFlat.pullback_exact`,
  `Functor.injective_obj_of_injective`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `RingedSite.Hom.pushforward`;
- best owner abstraction: `Functor.PreservesInjectiveObjects` for the canonical direct-image
  functor `f _*`;
- primitive data: the morphism of ringed sites `f` together with the exactness owner
  `exactFunctor _ _ (f^*)`, obtained source-faithfully from flatness via `IsFlat.pullback_exact`,
  and the canonical presheaf pushforward right-adjoint owner used to derive the module-sheaf
  right adjoint `f.modulePushforward`;
- derived API: the source-facing injectivity statement for the direct image of an injective module
  sheaf.

Source/core/bridge triage:
- `source-facing`: the textbook claim that flat direct image on module sheaves preserves injective
  objects;
- `core/canonical`: `Functor.PreservesInjectiveObjects`,
  `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`, and
  `SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap`;
- `bridge/view`: this ringed-site specialization using the exactness bridge
  `exactFunctor _ _ (f^*)`, which is source-faithfully supplied by `IsFlat.pullback_exact`. -/

/-- Helper for Lemma 21.14.2: for a flat morphism of ringed sites, the canonical direct-image
functor on module sheaves preserves injective objects. -/
@[stacks 0730]
instance modulePushforward_preservesInjectiveObjects_of_isFlat [Fact (IsFlat f)] :
    f.modulePushforward.PreservesInjectiveObjects := by
  -- Apply the generic adjunction criterion to the pullback-pushforward adjunction for `f`.
  simpa using CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint
    (SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap)
    -- Flatness identifies pullback with an exact left adjoint.
    (IsFlat.pullback_exact f Fact.out)

/-- Lemma 21.14.2: if `f : X ⟶ Y` is flat and `ℐ` is an injective `𝒪_X`-module, then
`(f _*).obj ℐ` is an injective `𝒪_Y`-module. -/
@[stacks 0730]
theorem modulePushforward_injective_of_isFlat
    (hf : IsFlat f) (ℐ : SheafOfModules X.structureSheaf) (hℐ : Injective ℐ) :
    Injective ((f _*).obj ℐ) := by
  -- Package flatness as the typeclass input used by the helper instance above.
  let _ : Fact (IsFlat f) := ⟨hf⟩
  -- Then apply injective-object preservation to the chosen injective module sheaf.
  simpa [RingedSite.Hom.modulePushforward] using
    (f.modulePushforward.injective_obj_of_injective hℐ)

end RingedSite.Hom
