import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import StacksProject_2024.Chap20.Open_subspace_module_core
import StacksProject_2024.Chap20.Open_subspace_module_extension_derived
import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.Sections_on_open
import StacksProject_2024.Chap20.«20_11_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.7.1:
- primary domain: restriction of sheaves of modules to an open subspace of a ringed space and the
  induced comparison on higher sheaf cohomology;
- sampled owner declarations:
  `moduleRestrictionToOpen`,
  `openSubspaceModuleCategory`,
  `moduleUnderlyingSheaf`,
  `Functor.PreservesInjectiveObjects`;
- best owner abstraction: the Chapter 20 open-subspace restriction owner
  `moduleRestrictionToOpen X U` together with the chapter-level forgetful bridge
  `moduleUnderlyingSheaf`; the public statements should live on the restricted module category
  `openSubspaceModuleCategory X U` and its underlying additive sheaf, rather than on the raw
  `SheafOfModules.over`/`toSheaf` composite;
- primitive data: a ringed space `X`, an open subset `U`, and a module sheaf `ℱ : (RingedSpace.Modules X)`;
- derived API: preservation of injective objects under restriction to `U`, and the degree-`p`
  comparison between the cohomology of the underlying additive sheaf over `U` and the global
  cohomology of the restricted module on the open subspace.

Source/core/bridge triage:
- `source-facing`: the two textbook statements about restricting injective `𝒪_X`-modules
  and comparing cohomology on `U` with cohomology of the restricted module on `X|_U`;
- `core/canonical`: `moduleRestrictionToOpen`, `openSubspaceModuleCategory`,
  `Functor.PreservesInjectiveObjects`, and `moduleUnderlyingSheaf`;
- `bridge/view`: the underlying-additive-sheaf owners `moduleUnderlyingSheaf X` on `X` and
  `moduleUnderlyingSheaf (X.restrict U.isOpenEmbedding)` on the restricted ringed space. -/

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

local notation "ModX" => X.Modules
local notation "XU" => X.restrict U.isOpenEmbedding
local notation "ModU" => openSubspaceModuleCategory X U
local notation "ΓModU" => ModuleCat (sectionsRingOnOpen X U)
local notation "ΓModTopU" =>
  ModuleCat (sectionsRingOnOpen (X.restrict U.isOpenEmbedding) ⊤)

/-- Helper for Lemma 20.7.1: the structure sheaf on the restricted ringed space `X|_U`, viewed in
`RingCat`, agrees with the canonical pullback of the ambient `RingCat` structure sheaf to the open
subspace `U`. -/
private noncomputable def openSubspaceRingSheafIsoRing :
    RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding) ≅
      (TopCat.Sheaf.pullback RingCat U.inclusion').obj (RingedSpace.ringCatSheaf X) := by
  -- Route correction: this is the owner-level `RingCat` bridge from the current re-plan, so the
  -- proof no longer depends on the old `CommRingCat`-then-forget sheafification detour.
  simpa [RingedSpace.ringCatSheaf] using
    ((U.isOpenEmbedding.sheafPullbackIso RingCat).symm.app (RingedSpace.ringCatSheaf X))

/-- Restriction to an open subspace preserves injective `𝒪_X`-modules. -/
instance moduleRestrictionToOpen_preservesInjectiveObjects :
    (moduleRestrictionToOpen X U).PreservesInjectiveObjects := by
  -- TODO: transport Chapter 6's `openSubsetModuleSheafExtensionByZeroAdjunction` across the
  -- direct `RingCat` bridge `openSubspaceRingSheafIsoRing`, then apply the adjunction criterion
  -- for preservation of injectives. The remaining blocker is an owner-level comparison between
  -- `moduleRestrictionToOpen X U` and the Chapter 6 restriction functor on pullback module sheaves.
  sorry

/-- Lemma 20.7.1 (1), objectwise form: the restriction of an injective `𝒪_X`-module to
the open subspace `U` is injective as an `𝒪_U`-module, written through the canonical
owner `moduleRestrictionToOpen X U`. -/
@[stacks 01E1]
theorem moduleRestrictionToOpen_injective
    (ℐ : ModX) (hℐ : Injective ℐ) :
    Injective ((moduleRestrictionToOpen X U).obj ℐ) := by
  -- Proof comment: apply the explicit preservation witness just proved to the injective object
  -- `ℐ`, rather than re-running the same instance search through the adjunction.
  let hPres : (moduleRestrictionToOpen X U).PreservesInjectiveObjects :=
    moduleRestrictionToOpen_preservesInjectiveObjects (X := X) (U := U)
  exact hPres.injective_obj hℐ

/-- Helper for Lemma 20.7.1: the top open of the restricted space `X|_U` is sent back to the
original open subset `U` by the open-embedding functor on opens. -/
private theorem restrictedTopOpen_obj_eq_open :
    ((U.isOpenEmbedding.functor).obj
      (⊤ : Opens ((Opens.toTopCat X.toPresheafedSpace).obj U))) = U := by
  -- Proof comment: an element of the top open of the restricted space is exactly a point of `X`
  -- together with the proof that it lies in `U`, so its image open is literally `U`.
  ext x
  simp

/-- Helper for Lemma 20.7.1: the ring of sections on the top open of the restricted ringed space
`X|_U` is canonically the same as the ring of sections on `U ⊆ X`. -/
private noncomputable def restrictedTopOpenSectionsRingIso :
    sectionsRingOnOpen (X.restrict U.isOpenEmbedding)
      (⊤ : Opens (X.restrict U.isOpenEmbedding).carrier) ≅
      sectionsRingOnOpen X U := by
  let topU : Opens ((Opens.toTopCat X.toPresheafedSpace).obj U) := ⊤
  let hObj :
      ((U.isOpenEmbedding.sheafPullback CommRingCat).obj X.sheaf).obj.obj (op topU) =
        X.sheaf.obj.obj (op U) := by
    -- Route correction: identify the restricted structure sheaf with the open-embedding
    -- pullback, then normalize the top open of the restricted space back to `U`.
    simpa [TopCat.Sheaf.forget, Topology.IsOpenEmbedding.sheafPullback, topU] using
      congrArg (fun V ↦ X.sheaf.obj.obj (op V))
        (restrictedTopOpen_obj_eq_open (X := X) U)
  -- Proof comment: after that normalization, the section ring on the restricted top open is just
  -- the ambient section ring on `U`.
  simpa [sectionsRingOnOpen, topU] using eqToIso hObj

/-- Helper for Lemma 20.7.1: after forgetting coefficients, sections on `U` agree with
top-open sections on the restricted ringed space `X|_U`. -/
private noncomputable def forgetRestrictedTopOpenEvaluationIso
    (ℱ : ModX) :
    ((moduleSectionsAsAbelianFunctor X U).obj ℱ) ≅
      ((moduleSectionsAsAbelianFunctor XU
          (⊤ : Opens (X.restrict U.isOpenEmbedding).carrier)).obj
        ((moduleRestrictionToOpen X U).obj ℱ)) := by
  -- TODO: rewrite the restricted module through the open-embedding pullback, evaluate at `⊤`,
  -- and normalize that open back to `U` using `restrictedTopOpen_obj_eq_open`.
  sorry

/-- Helper for Lemma 20.7.1: after forgetting coefficients, sections on `U` agree functorially
with top-open sections on the restricted ringed space `X|_U`. -/
private noncomputable def moduleSectionsAsAbelianFunctor_restrictedTopOpenIso :
    moduleSectionsAsAbelianFunctor X U ≅
      moduleRestrictionToOpen X U ⋙
        moduleSectionsAsAbelianFunctor XU
          ⊤ := by
  -- TODO: promote the objectwise sections identification to a natural isomorphism and prove
  -- naturality by rewriting both sides through the same restriction map on sections.
  sorry

/-- Lemma 20.7.1 (2), source-facing module-cohomology form: for an `𝒪_X`-module `𝓕`, the
cohomology of `𝓕` on `U` agrees, after forgetting the module structure, with the top-open
cohomology of the restricted module on the open subspace `X|_U`. -/
@[stacks 01E1]
theorem moduleCohomologyOnOpen_isomorphic_restrictedTopOpenModuleCohomology
    (ℱ : ModX) (p : ℕ) :
    IsIsomorphic
      ((forget₂ ΓModU AddCommGrpCat.{u}).obj (moduleCohomologyAtOpen U ℱ p))
      ((forget₂
          (ModuleCat
            (sectionsRingOnOpen XU (⊤ : Opens (X.restrict U.isOpenEmbedding).carrier)))
          AddCommGrpCat.{u}).obj
        (moduleCohomologyAtOpen
          (⊤ : Opens (X.restrict U.isOpenEmbedding).carrier)
          ((moduleRestrictionToOpen X U).obj ℱ) p)) := by
  -- TODO: compare the two right-derived section functors by restricting one chosen injective
  -- resolution and then applying `mapHomologyIso` to the functor-level sections identification.
  sorry

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
  AddCommGrpCat.{u}]
variable [HasExt.{u} ((X.restrict U.isOpenEmbedding).carrier.Sheaf AddCommGrpCat.{u})]

/-- Helper for Lemma 20.7.1: after forgetting the module structure on open cohomology, the chosen
injective resolution computes the ordinary sheaf cohomology of the underlying additive sheaf. -/
private theorem forgetModuleCohomologyAtOpen_isomorphic_underlyingSheafCohomology
    {Y : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    (V : Opens Y.carrier) (𝒢 : Y.Modules) (p : ℕ) :
    IsIsomorphic
      ((forget₂ (ModuleCat (sectionsRingOnOpen Y V)) AddCommGrpCat.{u}).obj
        (moduleCohomologyAtOpen V 𝒢 p))
      (((moduleUnderlyingSheaf Y).obj 𝒢).H' p V) := by
  -- TODO: reintroduce the local dependency-closed bridge from module cohomology to the
  -- underlying additive-sheaf cohomology without importing later Chapter 20 API.
  sorry

/-- Lemma 20.7.1 (2), underlying-sheaf companion: the canonical source-facing module-cohomology
comparison above identifies the cohomology of the underlying additive sheaf on `U` with the
top-open cohomology of the restricted underlying additive sheaf on the restricted ringed space
`X|_U`. -/
@[stacks 01E1]
theorem moduleCohomologyOnOpen_isomorphic_restrictedTopOpenCohomology
    (ℱ : ModX) (p : ℕ) :
    IsIsomorphic
      (((moduleUnderlyingSheaf X).obj ℱ).H' p U)
      (((moduleUnderlyingSheaf XU).obj
        ((moduleRestrictionToOpen X U).obj ℱ)).H' p
        (⊤ : Opens (X.restrict U.isOpenEmbedding).carrier)) := by
  rcases
      forgetModuleCohomologyAtOpen_isomorphic_underlyingSheafCohomology
        (Y := X) U ℱ p with
    ⟨eLeft⟩
  rcases
      moduleCohomologyOnOpen_isomorphic_restrictedTopOpenModuleCohomology
        (X := X) (U := U) ℱ p with
    ⟨eMiddle⟩
  rcases
      forgetModuleCohomologyAtOpen_isomorphic_underlyingSheafCohomology
        (Y := XU) (⊤ : Opens (X.restrict U.isOpenEmbedding).carrier)
        ((moduleRestrictionToOpen X U).obj ℱ) p with
    ⟨eRight⟩
  -- Proof comment: convert both endpoints to the source-facing module-cohomology owners, apply
  -- the comparison just proved, and then forget back to the underlying additive sheaves.
  exact ⟨eLeft.symm ≪≫ eMiddle ≪≫ eRight⟩

/-- Lemma 20.7.1 (2), global-cohomology companion: after the canonical top-open comparison on the
restricted ringed space `X|_U`, the same cohomology group may be written as the global cohomology
of the restricted underlying additive sheaf. -/
@[stacks 01E1]
theorem moduleCohomologyOnOpen_isomorphic_restrictedGlobalCohomology
    (ℱ : ModX) (p : ℕ) :
    IsIsomorphic
      (((moduleUnderlyingSheaf X).obj ℱ).H' p U)
      (AddCommGrpCat.of (((moduleUnderlyingSheaf XU).obj
        ((moduleRestrictionToOpen X U).obj ℱ)).H p)) := by
  -- TODO: compose the top-open comparison with the canonical bridge from
  -- `F.H' p (⊤ : Opens XU.carrier)` to `AddCommGrpCat.of (F.H p)` on the restricted space.
  -- The blocker is the owner-level theorem relating `H'` on `⊤` to the global `H` owner without
  -- importing later Chapter 20 API.
  sorry

end AlgebraicGeometry.RingedSpace
