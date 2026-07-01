import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import stacks_project.Chap12.Lemma_12_29_1
import stacks_project.Chap18.Definition_18_31_1
import stacks_project.Chap18.Lemma_18_41_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

/- Domain-style sampling for Lemma 21.14.2:
- primary domain: adjunctions, exact functors, and injective-object preservation for module sheaves
  on ringed sites;
- sampled owner declarations:
  `Functor.PreservesInjectiveObjects`,
  `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`,
  `Functor.injective_obj_of_injective`,
  `RingedSite.Hom.IsFlat.pullback_exact`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `RingedSite.Hom.modulePushforward`;
- best owner abstraction: `Functor.PreservesInjectiveObjects` for the canonical direct-image
  functor `f.modulePushforward`;
- primitive data: the morphism of ringed sites `f` together with the flatness instance `[f.IsFlat]`;
- derived API: the source-facing injectivity statement for the direct image of an injective module
  sheaf.

Source/core/bridge triage:
- `source-facing`: the textbook claim that flat direct image on module sheaves preserves injective
  objects;
- `core/canonical`: `Functor.PreservesInjectiveObjects`,
  `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`, and
  `SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap`;
- `bridge/view`: this ringed-site specialization using the canonical pullback exactness owner
  `IsFlat.pullback_exact`. -/

/-- For a flat morphism of ringed sites, direct image on module sheaves preserves injective
objects. -/
-- Proof sketch: combine the canonical adjunction `f^* ⊣ f_*` with the exactness owner
-- `IsFlat.pullback_exact`, then apply the Chapter 12 adjunction criterion
-- `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`.
instance modulePushforward_preservesInjectiveObjects [f.IsFlat] :
    f.modulePushforward.PreservesInjectiveObjects := by
  let v : SheafOfModules Y.structureSheaf ⥤ SheafOfModules X.structureSheaf := f^*
  let u : SheafOfModules X.structureSheaf ⥤ SheafOfModules Y.structureSheaf := f.modulePushforward
  let _ : Abelian (SheafOfModules X.structureSheaf) := inferInstance
  let _ : Abelian (SheafOfModules Y.structureSheaf) := inferInstance
  let _ : v.Additive := by
    simpa [v] using (inferInstance : (f^*).Additive)
  have adj : v ⊣ u := by
    simpa [v, u] using SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap
  have hExact : exactFunctor _ _ v := by
    simpa [v] using (IsFlat.pullback_exact : exactFunctor _ _ (f^*))
  simpa [u] using CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint adj hExact

-- Proof sketch: apply the preceding injective-preservation instance for
-- `SheafOfModules.pushforward f.structureSheafMap` to the given injective module sheaf `ℐ`.
/-- Lemma 21.14.2: if `f : (\mathit{Sh}(\mathcal C), \mathcal O_\mathcal C) \to
(\mathit{Sh}(\mathcal D), \mathcal O_\mathcal D)` is flat, formalized here by a flat morphism of
ringed sites `f`, then the direct image `f_* \mathcal I` of any injective
`\mathcal O_\mathcal C`-module `\mathcal I` is an injective `\mathcal O_\mathcal D`-module. -/
theorem modulePushforward_injective_of_isFlat
    [f.IsFlat] (ℐ : SheafOfModules X.structureSheaf) (hℐ : Injective ℐ) :
    Injective (f.modulePushforward.obj ℐ) :=
  f.modulePushforward.injective_obj_of_injective hℐ

end RingedSite.Hom
