import StacksProject_2024.Chap21.Lemma_21_20_3
import StacksProject_2024.Chap21.Lemma_21_20_4
import StacksProject_2024.Chap21.Lemma_21_20_5_core
import StacksProject_2024.Chap21.Lemma_21_20_7_core

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open scoped RingedSiteCohomology
open scoped RingedSiteDerived
open scoped RingedSiteDerivedSections

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

section

variable (X : RingedSite.{u, v})
variable [Limits.HasBinaryProducts X.carrier]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable (U : X)
variable [HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor (X.localization U).siteTopology AddCommGrpCat.{max u v}]

local instance localizedToSheaf_preservesZeroMorphisms :
    (SheafOfModules.toSheaf (X.localization U).structureSheaf).PreservesZeroMorphisms :=
  { map_zero _ _ := by rfl }

local instance localizedSheafGamma_preservesZeroMorphisms :
    (Sheaf.Γ (X.localization U).siteTopology AddCommGrpCat.{max u v}).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext s
    simp

local instance localizedRestriction_comp_moduleGlobalSectionsAdditiveFunctor_preservesZeroMorphisms :
    ((localizedRestriction X U) ⋙
      moduleGlobalSectionsAdditiveFunctor (X.localization U)).PreservesZeroMorphisms := by
  letI : (localizedRestriction X U).PreservesZeroMorphisms :=
    RingedSite.Hom.localizedRestriction_preservesZeroMorphisms X U
  dsimp [moduleGlobalSectionsAdditiveFunctor]
  infer_instance

local instance localized_moduleGlobalSectionsAdditiveFunctor_additive :
    (moduleGlobalSectionsAdditiveFunctor (X.localization U)).Additive :=
  moduleGlobalSectionsAdditiveFunctor_additive (X.localization U)

/- Domain-style sampling for Lemma 21.20.2:
- primary domain: localized restriction of `𝒪_X`-modules on a ringed site and the
  comparison between sections over `U` and global sections on the localized ringed site `X/U`;
- sampled owner declarations:
  `localizedRestriction`,
  `localizedRestrictionDerived`,
  `moduleSectionsAsAbelianFunctor`,
  `moduleGlobalSectionsAdditiveFunctor`,
  `cohomologyOverObject`;
- best owner abstraction:
  the arbitrary ringed-site owner `X : RingedSite`, its localized restriction owner
  `localizedRestriction X U`, the derived localized restriction owner
  `localizedRestrictionDerived X U`, the Chapter 21 sections owner
  `moduleSectionsAsAbelianFunctor X U`, and the Chapter 21 additive global-sections bridge
  `moduleGlobalSectionsAdditiveFunctor (X.localization U)` on the localized ringed site `X/U`;
- primitive data:
  the ringed site `X` and the object `U : X`;
- derived API:
  the canonical sections comparison on the owner functors and its degreewise homology
  specialization for complexes.

Source/core/bridge triage:
- `source-facing`: the comparison `Γ(U, -) ≅ Γ(X/U, -|_{X/U})`;
- `core/canonical`: `localizedRestriction X U`, `localizedRestrictionDerived X U`,
  `moduleSectionsAsAbelianFunctor X U`,
  `moduleGlobalSectionsAdditiveFunctor (X.localization U)`, and the slice terminal object
  `Over.mk (𝟙 U)`;
- `bridge/view`: the terminal-object identification on the localized site used to realize global
  sections via the canonical Chapter 21 owner, together with the induced complex-homology
  companion below. -/

-- Proof sketch: the localized restriction `j_U^*` identifies sections over `U` with evaluation at
-- the terminal object `U ⟶ U` given by `𝟙 U` in the localized site; the canonical
-- `Sheaf.ΓNatIsoSheafSections` then transports those terminal sections to global sections on
-- `X/U`.
/-- The canonical comparison
`Γ(U, -) ≅ Γ(X/U, -|_{X/U})` on `𝒪_X`-modules, expressed on the Chapter 21
owner `moduleSectionsAsAbelianFunctor X U` and the canonical localized global-sections functor. -/
noncomputable def moduleSectionsAsAbelianFunctor_iso_localizedRestriction_globalSections :
    moduleSectionsAsAbelianFunctor X U ≅
      (localizedRestriction X U) ⋙
        moduleGlobalSectionsAdditiveFunctor (X.localization U) := by
  let e :
      moduleSectionsAsAbelianFunctor X U ≅
        localizedRestriction X U ⋙
          SheafOfModules.toSheaf (X.localization U).structureSheaf ⋙
            Sheaf.Γ (X.localization U).siteTopology AddCommGrpCat.{max u v} :=
    NatIso.ofComponents
      (fun ℱ ↦ by
        change
          ((SheafOfModules.pushforward (𝟙 ((X.localization U).structureSheaf))).obj ℱ).val.presheaf.obj
              (op (Over.mk (𝟙 U))) ≅
            ((SheafOfModules.pushforward (𝟙 ((X.localization U).structureSheaf))).obj ℱ).val.presheaf.obj
              (op (Over.mk (𝟙 U)))
        exact Iso.refl _)
      (fun {_ _} f ↦ by
        ext x
        rfl) ≪≫
      Functor.isoWhiskerLeft
      (localizedRestriction X U ⋙
        SheafOfModules.toSheaf (X.localization U).structureSheaf)
      (Sheaf.ΓNatIsoSheafSections (X.localization U).siteTopology AddCommGrpCat
        Over.mkIdTerminal).symm
  simpa [moduleGlobalSectionsAdditiveFunctor] using e

variable [CategoryWithHomology (ModuleCat X)]

-- Proof sketch: rewrite the source-facing localized-site cohomology comparison above through the
-- canonical realization of the global cohomology of `X/U` by the derived global-sections functor
-- `RΓ[X/U]`.
/-- Lemma 21.20.2: for `K : ModuleDerived X` and `p : ℤ`, the cohomology over `U` is canonically
isomorphic to the global cohomology of the restricted derived `𝒪_X`-module on the localized
ringed site `X/U`, computed by the canonical localized-site owner `RΓ[X.localization U]` on
`localizedRestrictionDerived X U`. -/
@[stacks 0D6F]
theorem ringedSiteDerived_localizationModuleRestriction_cohomologyOver_eq
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
    [IsGrothendieckAbelian.{max u v} (ModuleCat (X.localization U))]
    [PreservesFiniteLimits (localizedRestriction X U)]
    [PreservesFiniteColimits (localizedRestriction X U)]
    [Functor.HasRightDerivedFunctor
      (moduleGlobalSectionsToDerived (X.localization U))
      (ModuleQis (X.localization U))]
    (K : ModuleDerived X) (p : ℤ) :
    IsIsomorphic
      (H^p(U, K))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).obj
        ((RΓ[X.localization U]).obj
          ((localizedRestrictionDerived X U).obj K))) := by
  sorry

-- Proof sketch: derive the underived sections comparison above and express both sides through the
-- Chapter 21 objectwise cohomology owners. On the localized site `X/U`, evaluation at the
-- terminal object `Over.mk (𝟙 U)` is the bridge from the source-facing localized-site global
-- cohomology statement to the terminal-object realization.
/-- Lemma 21.20.2, terminal-object companion: for `K : ModuleDerived X` and `p : ℤ`, the
cohomology over `U` is canonically isomorphic to the cohomology of the restricted derived
`𝒪_X`-module `localizedRestrictionDerived X U` on the localized ringed site `X/U`, realized at the
terminal object
`Over.mk (𝟙 U)`. -/
@[stacks 0D6F]
theorem ringedSiteDerived_localizationModuleRestriction_cohomologyAtTerminal_isomorphic
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
    [IsGrothendieckAbelian.{max u v} (ModuleCat (X.localization U))]
    [PreservesFiniteLimits (localizedRestriction X U)]
    [PreservesFiniteColimits (localizedRestriction X U)]
    (K : ModuleDerived X) (p : ℤ) :
    IsIsomorphic
      (H^p(U, K))
      (H^p(Over.mk (𝟙 U), ((localizedRestrictionDerived X U).obj K))) := by
  sorry

/- Proof sketch: apply `HomologicalComplex.homologyFunctor` to the owner-level sections comparison
above after mapping cochain complexes. This is the complex-level companion to the source-facing
derived/cohomology statements, and it remains useful when working with an explicit complex
representative `I•`. -/
/-- Lemma 21.20.2, complex-homology companion: for a complex `I•` of
`𝒪_X`-modules, the degree-`p` homology of the sections complex over `U` is canonically
isomorphic to the degree-`p` homology of the global-sections complex on the localized ringed site
`X/U`. This is the homology specialization of the mapped-complex comparison induced by
`moduleSectionsAsAbelianFunctor_iso_localizedRestriction_globalSections`, not the derived owner
`cohomologyOverObject`. -/
@[stacks 0D6F]
noncomputable def moduleSectionsAsAbelianFunctor_homology_iso_localizedRestriction_globalSections
    (I : CochainComplex (ModuleCat X) ℤ) (p : ℤ) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (up ℤ) p).obj
        (((moduleSectionsAsAbelianFunctor X U).mapHomologicalComplex (up ℤ)).obj I) ≅
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (up ℤ) p).obj
        ((((localizedRestriction X U) ⋙
          moduleGlobalSectionsAdditiveFunctor (X.localization U)).mapHomologicalComplex
          (up ℤ)).obj I) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (up ℤ) p).mapIso
    ((NatIso.mapHomologicalComplex
        (moduleSectionsAsAbelianFunctor_iso_localizedRestriction_globalSections X U)
        (up ℤ)).app I)

end

end RingedSite.Hom
