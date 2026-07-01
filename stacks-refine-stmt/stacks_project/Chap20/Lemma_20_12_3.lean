import Mathlib
import stacks_project.Chap20.Lemma_20_11_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.12.3:
- primary domain: sheaf cohomology of `\mathcal O_X`-modules on a ringed space, computed from
  injective resolutions by taking sections over an open subset;
- sampled owner declarations:
  `(RingedSpace.Modules X)`,
  `moduleUnderlyingSheaf`,
  `SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)`,
  `CategoryTheory.Sheaf.cohomologyOver_eq_homology_sections_of_injectiveResolution`;
- best owner abstraction: the Chapter 20 ringed-space owner `(RingedSpace.Modules X)`, together with the
  canonical underlying-abelian-sheaf bridge `moduleUnderlyingSheaf`; sections over `U` are the
  evaluation functor on `(RingedSpace.ringCatSheaf X)`, followed by the standard forgetful functor to abelian
  groups;
- primitive data: a ringed space `X`, an open subset `U`, a module `ℱ : (RingedSpace.Modules X)`, and an
  injective resolution `I : InjectiveResolution ℱ`;
- derived API: flasqueness of `moduleUnderlyingSheaf ℱ` and vanishing of the positive homology of
  the sections complex `Γ(U, I^•)`.

Source/core/bridge triage:
- `source-facing`: the vanishing statement for the positive homology of the sections complex of a
  chosen injective resolution;
- `core/canonical`: `(RingedSpace.Modules X)`, `moduleUnderlyingSheaf`, and evaluation on `U`;
- `bridge/view`: forgetting the `Γ(U, \mathcal O_X)`-module structure on sections down to
  `AddCommGrpCat`.

This file should therefore reuse the ringed-space owners already introduced in Chapter 20 rather
than spelling the same module category and underlying-sheaf data through raw
`ringedSpaceRingCatSheaf` composites. -/

instance moduleSectionsToAddCommGrp_preservesZeroMorphisms
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)) ⋙
      forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}).PreservesZeroMorphisms := by
  letI : (SheafOfModules.forget (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms := by
    infer_instance
  letI : (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).PreservesZeroMorphisms := by
    infer_instance
  letI : (forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}).PreservesZeroMorphisms :=
    by infer_instance
  change
    (((SheafOfModules.forget (RingedSpace.ringCatSheaf X) ⋙
        PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)) ⋙
        forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}).PreservesZeroMorphisms)
  infer_instance

-- Proof sketch: resolve `ℱ` by an injective resolution `I`, note from Lemma `20.12.2` that the
-- injective terms are flasque, and then apply the flasque-resolution criterion from the proof of
-- Lemma `13.15.6` to the sections functor on `U`. This forces the positive homology of the
-- sections complex `Γ(U, I^\bullet)` to vanish.
/-- Lemma 20.12.3: if an `\mathcal O_X`-module on a ringed space is flasque, then for every open
subset `U` and every injective resolution `I^\bullet` of that module, the positive homology of the
sections complex `Γ(U, I^\bullet)` vanishes; taking `U = X` recovers the global-sections case. -/
theorem flasque_module_higherSectionsHomology_isZero
    {X : RingedSpace.{u}}
    [HasInjectiveResolutions (RingedSpace.Modules X)]
    (U : Opens X.carrier) (ℱ : (RingedSpace.Modules X))
    (hℱ : TopCat.Sheaf.IsFlasque (moduleUnderlyingSheaf ℱ))
    (n : ℕ) (I : InjectiveResolution ℱ) :
    IsZero
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) (n + 1)).obj
        ((((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)) ⋙
            forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat.{u}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)) := sorry

end AlgebraicGeometry.RingedSpace
