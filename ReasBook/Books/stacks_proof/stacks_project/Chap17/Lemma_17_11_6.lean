import Mathlib
import stacks_proof.stacks_project.Chap17.Lemma_17_10_7
import stacks_proof.stacks_project.Chap10.Definition_10_5_1
import stacks_proof.stacks_project.Chap10.Lemma_10_11_3
import stacks_proof.stacks_project.Chap17.Lemma_17_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Helper for Lemma 17.11.6: local alias for the associated-module-sheaf functor from
Lemma `17.10.7`, used here to avoid the broken later import chain through `Definition_17.10.6`.
-/
private noncomputable abbrev globalSectionsModuleFunctor
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) :
    ModuleCat R ⥤ SheafOfModules ((RingedSpace.ringCatSheaf X)) :=
  «_private.stacks_project.Chap17.Lemma_17_10_7.0.AlgebraicGeometry.globalSectionsModuleFunctor» α

/-- Helper for Lemma 17.11.6: local alias for the associated `\mathcal O_X`-module attached to
an `R`-module through a global-sections ring map. -/
private abbrev associatedModuleSheaf
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    RingedSpace.Modules X :=
  «_private.stacks_project.Chap17.Lemma_17_10_7.0.AlgebraicGeometry.associatedModuleSheaf» α M

/-- Helper for Lemma 17.11.6: local alias for the presheaf model
`U ↦ \mathcal O_X(U) \otimes_R M` of the associated sheaf. -/
private abbrev associatedModulePresheaf
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    PresheafOfModules (RingedSpace.ringCatSheaf X).obj :=
  «_private.stacks_project.Chap17.Lemma_17_10_7.0.AlgebraicGeometry.associatedModulePresheaf» α M

/-- Helper for Lemma 17.11.6: local alias for the sheafification model of the associated sheaf. -/
private abbrev associatedModuleSheafFromPresheaf
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    RingedSpace.Modules X :=
  «_private.stacks_project.Chap17.Lemma_17_10_7.0.AlgebraicGeometry.associatedModuleSheafFromPresheaf»
    α M

/-- Helper for Lemma 17.11.6: local alias for the canonical identification between the owner
associated sheaf and its presheaf sheafification model. -/
private noncomputable abbrev associatedModuleSheafFromPresheafIso
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    associatedModuleSheaf α M ≅ associatedModuleSheafFromPresheaf α M :=
  «_private.stacks_project.Chap17.Lemma_17_10_7.0.AlgebraicGeometry.associatedModuleSheafFromPresheafIso»
    α M

/-- Helper for Lemma 17.11.6: the map on associated sheaves induced by a free-module presentation
map. -/
private abbrev associatedModulePresentationMap
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤))
    {I J : Type u}
    (f : ModuleCat.of R (J →₀ R) ⟶ ModuleCat.of R (I →₀ R)) :
    associatedModuleSheaf α (ModuleCat.of R (J →₀ R)) ⟶
      associatedModuleSheaf α (ModuleCat.of R (I →₀ R)) :=
  (globalSectionsModuleFunctor α).map f

/-- Helper for Lemma 17.11.6: the cokernel sheaf attached to a chosen free presentation. -/
private noncomputable abbrev associatedModuleSheafFromPresentation
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤))
    {I J : Type u}
    (f : ModuleCat.of R (J →₀ R) ⟶ ModuleCat.of R (I →₀ R)) :
    RingedSpace.Modules X :=
  cokernel (associatedModulePresentationMap α f)

/-- Helper for Lemma 17.11.6: the associated-module-sheaf functor preserves colimits. -/
private theorem globalSectionsModuleFunctor_preservesColimits
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) :
    PreservesColimits (globalSectionsModuleFunctor α) := by
  infer_instance

/-- Helper for Lemma 17.11.6: the cokernel presentation attached to a finite free presentation is
canonically isomorphic to the associated sheaf of the presented module. -/
private noncomputable def associatedModuleSheafFromPresentationIso
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤))
    {I J : Type u} {M : ModuleCat R}
    (f : ModuleCat.of R (J →₀ R) ⟶ ModuleCat.of R (I →₀ R))
    (g : ModuleCat.of R (I →₀ R) ⟶ M)
    (H : f ≫ g = 0)
    (h : IsColimit (CokernelCofork.ofπ g H)) :
    associatedModuleSheafFromPresentation α f ≅ associatedModuleSheaf α M := by
  let F := globalSectionsModuleFunctor α
  letI : PreservesColimits F := globalSectionsModuleFunctor_preservesColimits α
  let e : M ≅ cokernel f := h.coconePointUniqueUpToIso (colimit.isColimit (parallelPair f 0))
  exact (PreservesCokernel.iso F f).symm ≪≫ (F.mapIso e).symm

/- Domain-style sampling for Lemma 17.11.6:
- primary domain: filtered-colimit presentations of `\mathcal O_X`-modules associated to modules
  over the global-sections ring;
- inspected owner declarations:
  `CategoryTheory.ObjectProperty.ind`,
  `SheafOfModules.isFinitePresentation`,
  `associatedModuleSheaf`,
  `globalSectionsModuleFunctor_preservesColimits`;
- best owner abstraction: the filtered-colimit conclusion should be stated directly in the
  canonical owner form `ind (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X))`
  on `X.Modules`, rather than by a parallel local predicate that unpacks the same witness data;
- primitive data: the ringed space `X`, the global-sections module `M`, and the source-facing
  isomorphism witness `ℱ ≅ 𝓕_ M`;
- derived API: the `ind` packaging of the filtered-colimit presentation by finitely presented
  module sheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that a module sheaf associated to a global-sections module
  is a filtered colimit of finitely presented `\mathcal O_X`-modules;
- `core/canonical`: `CategoryTheory.ObjectProperty.ind` and
  `SheafOfModules.isFinitePresentation`;
- `bridge/view`: the associated-module-sheaf owner `𝓕_ M`, together with the ambient isomorphism
  witness identifying `ℱ` with that owner.
-/

/-- Helper for Lemma 17.11.6: the standard finite free module `(Fin n → R)` is canonically the
same free module written in the `→₀` model expected by the associated-sheaf presentation API. -/
private noncomputable theorem functionFiniteFreeIsoFinsuppFiniteFree
    {R : Type u} [CommRing R] (n : ℕ) :
    ModuleCat.of R (Fin n → R) ≅ ModuleCat.of R (ULift.{u} (Fin n) →₀ R) := by
  let eULift :
      (Fin n → R) ≃ₗ[R] (ULift.{u} (Fin n) → R) :=
    LinearEquiv.funCongrLeft R R ((Equiv.ulift : Fin n ≃ ULift.{u} (Fin n)).symm)
  let eFinsupp :
      (ULift.{u} (Fin n) →₀ R) ≃ₗ[R] (ULift.{u} (Fin n) → R) :=
    Finsupp.linearEquivFunOnFinite R R (ULift.{u} (Fin n))
  -- Proof comment: compose the `ULift` reindexing with the finite-support/function equivalence,
  -- then package the resulting linear equivalence as an isomorphism in `ModuleCat`.
  exact (eULift.trans eFinsupp.symm).toModuleIso

/-- Helper for Lemma 17.11.6: a finitely presented module admits a cokernel presentation by
finite free modules in the standard function-model basis. -/
private lemma finitelyPresentedModule_existsFunctionFreeCokernelPresentation
    {R : Type u} [CommRing R] (M : ModuleCat R) [Module.FinitePresentation R M] :
    ∃ n m : ℕ,
      ∃ f : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R),
        ∃ g : ModuleCat.of R (Fin n → R) ⟶ M,
          ∃ hfg : f ≫ g = 0, Nonempty (IsColimit (CokernelCofork.ofπ g hfg)) := by
  obtain ⟨n, m, f, g, hExact, hSurj⟩ :=
    (Module.FinitePresentation.iff_exists_exact_free_sequence (R := R) (M := M)).1 inferInstance
  let fCat : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R) := ModuleCat.ofHom f
  let gCat : ModuleCat.of R (Fin n → R) ⟶ M := ModuleCat.ofHom g
  have hfg : fCat ≫ gCat = 0 := by
    -- Proof comment: exactness on the underlying linear maps immediately forces the composite to
    -- vanish in the categorical free presentation.
    ext x
    change g (f x) = 0
    exact hExact.apply_apply_eq_zero x
  refine ⟨n, m, fCat, gCat, hfg, ?_⟩
  -- Proof comment: exactness and surjectivity identify the quotient by `f` with `M`, so `g`
  -- is the categorical cokernel of `f`.
  exact ⟨by
    simpa [fCat, gCat, hfg] using ModuleCat.isColimitCokernelCofork fCat gCat hExact hSurj⟩

/-- Helper for Lemma 17.11.6: a finite free `\mathcal O_X`-module is finitely presented. -/
private theorem free_isFinitePresentation_of_finite
    {X : RingedSpace.{u}} (I : Type u) [Finite I] :
    (SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I : X.Modules).IsFinitePresentation := by
  let P : (SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I : X.Modules).Presentation :=
    SheafOfModules.presentationOfIsCokernelFree
      (0 : SheafOfModules.free (R := RingedSpace.ringCatSheaf X) Empty ⟶
        SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I)
      (𝟙 _)
      (by simp)
      (CokernelCofork.IsColimit.ofπ' (𝟙 _) (by simp) fun s ↦ ⟨s.π, by simp⟩)
  letI : P.IsFinite := by
    refine ⟨?_, ?_⟩
    · dsimp [P, SheafOfModules.presentationOfIsCokernelFree,
        SheafOfModules.generatorsOfIsCokernelFree]
      exact ⟨inferInstance⟩
    · dsimp [P, SheafOfModules.presentationOfIsCokernelFree,
        SheafOfModules.relationsOfIsCokernelFree]
      infer_instance
  exact isFinitePresentationOfFinitePresentation P

/-- Helper for Chap17 Lemma 17 11 6: on each open, the associated-module presheaf of the free
global-sections module is the free module on the same basis after extending scalars. -/
private theorem associatedModulePresheafFinsuppObjIsoFreeObj
    {X : RingedSpace.{u}} (I : Type u) (U : (Opens X)ᵒᵖ) :
    (associatedModulePresheaf (X := X) (RingHom.id _)
        (ModuleCat.of _ (I →₀ X.presheaf.obj (op ⊤)))).obj U ≅
      ((SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I : X.Modules).val.obj U) := by
  classical
  -- Proof comment: sectionwise, the associated presheaf is the scalar extension
  -- `𝒪_X(U) ⊗_{Γ(X,𝒪_X)} (I →₀ Γ(X,𝒪_X))`, and `finsuppScalarLeft` identifies this with
  -- the free `𝒪_X(U)`-module on `I`.
  simpa [associatedModulePresheaf] using
    (TensorProduct.finsuppScalarLeft
      (X.presheaf.obj U) (X.presheaf.obj (op ⊤)) I).toModuleIso

/-- Helper for Chap17 Lemma 17 11 6: the sectionwise `finsuppScalarLeft` identifications are
natural in the open subset, so they assemble into a presheaf isomorphism. -/
private theorem associatedModulePresheafFinsuppIsoFreePresheaf
    {X : RingedSpace.{u}} (I : Type u) :
    associatedModulePresheaf (X := X) (RingHom.id _)
        (ModuleCat.of _ (I →₀ X.presheaf.obj (op ⊤))) ≅
      (SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I : X.Modules).val := by
  classical
  refine NatIso.ofComponents
    (fun U ↦ associatedModulePresheafFinsuppObjIsoFreeObj (X := X) I U) ?_
  intro U V i
  -- Proof comment: both restriction maps act coefficientwise, so the square commutes after
  -- checking it on the `I`-basis of the finitely supported module.
  apply ModuleCat.hom_ext
  ext j
  simp [associatedModulePresheafFinsuppObjIsoFreeObj, associatedModulePresheaf,
    TensorProduct.finsuppScalarLeft_apply_tmul]

/-- Helper for Chap17 Lemma 17 11 6: sheafifying the presheaf comparison identifies the
associated-module sheaf of the free global-sections module with the free module sheaf. -/
private theorem associatedModuleSheafFromPresheafFinsuppIsoFree
    {X : RingedSpace.{u}} (I : Type u) :
    associatedModuleSheafFromPresheaf (X := X) (RingHom.id _)
        (ModuleCat.of _ (I →₀ X.presheaf.obj (op ⊤))) ≅
      (SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I : X.Modules) := by
  -- Proof comment: sheafify the presheaf comparison, then use that the free module presheaf is
  -- already a sheaf so its sheafification counit is an isomorphism.
  exact
    (PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).mapIso
        (associatedModulePresheafFinsuppIsoFreePresheaf (X := X) I) ≪≫
      asIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (RingedSpace.ringCatSheaf X).obj)).counit.app
          (SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I : X.Modules))

/-- Helper for Lemma 17.11.6: the associated sheaf of a finitely supported free
`Γ(X,\mathcal O_X)`-module should identify with the free `\mathcal O_X`-module on the same basis.
-/
private theorem associatedModuleSheafFinsuppIsoFree
    {X : RingedSpace.{u}} (I : Type u) :
    associatedModuleSheaf (RingHom.id _) (ModuleCat.of _ (I →₀ X.presheaf.obj (op ⊤))) ≅
      (SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I : X.Modules) := by
  -- Proof comment: finally compose the canonical comparison `F₁ ≅ F₃` from Lemma `17.10.5`
  -- with the sheafified free-presheaf identification.
  exact associatedModuleSheafFromPresheafIso (X := X) (RingHom.id _)
      (ModuleCat.of _ (I →₀ X.presheaf.obj (op ⊤))) ≪≫
    associatedModuleSheafFromPresheafFinsuppIsoFree (X := X) I

/-- Helper for Lemma 17.11.6: once the associated free module sheaf is identified with the free
sheaf, finite free modules over `Γ(X,\mathcal O_X)` give finitely presented associated sheaves. -/
private theorem associatedModuleSheafFinsupp_isFinitePresentation_of_finite
    {X : RingedSpace.{u}} (I : Type u) [Finite I] :
    (associatedModuleSheaf (RingHom.id _) (ModuleCat.of _ (I →₀ X.presheaf.obj (op ⊤)))).IsFinitePresentation := by
  let e := associatedModuleSheafFinsuppIsoFree (X := X) I
  let hfree :
      (SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I : X.Modules).IsFinitePresentation :=
    free_isFinitePresentation_of_finite (X := X) I
  -- Proof comment: finite presentation is an owner property, so it transports directly across the
  -- free/associated-free comparison isomorphism.
  exact
    (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X)).prop_of_iso e.symm hfree

/-- Helper for Lemma 17.11.6: the function-model finite free modules used by the finite
presentation API have finitely presented associated sheaves after one transport to the `→₀`
model. -/
private theorem associatedModuleSheafFunctionFinite_isFinitePresentation
    {X : RingedSpace.{u}} (n : ℕ) :
    (associatedModuleSheaf (RingHom.id _)
      (ModuleCat.of _ (Fin n → X.presheaf.obj (op ⊤)))).IsFinitePresentation := by
  let e :=
    functionFiniteFreeIsoFinsuppFiniteFree (R := X.presheaf.obj (op ⊤)) n
  let eSheaf := (globalSectionsModuleFunctor (RingHom.id _)).mapIso e
  let hFinsupp :
      (associatedModuleSheaf (RingHom.id _)
        (ModuleCat.of _ (ULift.{u} (Fin n) →₀ X.presheaf.obj (op ⊤)))).IsFinitePresentation :=
    associatedModuleSheafFinsupp_isFinitePresentation_of_finite (X := X) (ULift.{u} (Fin n))
  -- Proof comment: the function model and the finitely supported model are already isomorphic as
  -- `Γ(X,\mathcal O_X)`-modules, so the associated-sheaf finite-presentation property transports
  -- across the functorial image of that isomorphism.
  exact
    (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X)).prop_of_iso
      eSheaf.symm hFinsupp

/-- Helper for Lemma 17.11.6: the explicit cokernel model
`associatedModuleSheafFromPresentation` already carries a finite global presentation whenever the
chosen relation and generator index types are finite. -/
private theorem associatedModuleSheafFromPresentation_isFinitePresentation
    {X : RingedSpace.{u}} {I J : Type u} [Finite I] [Finite J]
    (f : ModuleCat.of _ (J →₀ X.presheaf.obj (op ⊤)) ⟶
      ModuleCat.of _ (I →₀ X.presheaf.obj (op ⊤))) :
    (associatedModuleSheafFromPresentation (RingHom.id _) f).IsFinitePresentation := by
  letI :
      (associatedModuleSheaf (RingHom.id _)
        (ModuleCat.of _ (J →₀ X.presheaf.obj (op ⊤)))).IsFinitePresentation :=
    associatedModuleSheafFinsupp_isFinitePresentation_of_finite (X := X) J
  letI :
      (associatedModuleSheaf (RingHom.id _)
        (ModuleCat.of _ (I →₀ X.presheaf.obj (op ⊤)))).IsFinitePresentation :=
    associatedModuleSheafFinsupp_isFinitePresentation_of_finite (X := X) I
  exact SheafOfModules.isFinitePresentation_cokernel (associatedModulePresentationMap (RingHom.id _) f)

/-- Helper for Lemma 17.11.6: a finitely presented module over `Γ(X, \mathcal O_X)` should give a
finitely presented associated `\mathcal O_X`-module. -/
lemma associatedModuleSheaf_isFinitePresentation_of_moduleFinitePresentation
    {X : RingedSpace.{u}} {N : ModuleCat.{u} (X.presheaf.obj (op ⊤))}
    [Module.FinitePresentation (X.presheaf.obj (op ⊤)) N] :
    (𝓕_ N).IsFinitePresentation := by
  -- Proof comment: choose a finite free cokernel presentation of `N`, map it through the
  -- associated-module-sheaf functor, and then use the cokernel finite-presentation theorem on the
  -- resulting presentation by associated finite free sheaves.
  obtain ⟨n, m, f, g, hfg, ⟨hcolim⟩⟩ :=
    finitelyPresentedModule_existsFunctionFreeCokernelPresentation (M := N)
  let F : ModuleCat.{u} (X.presheaf.obj (op ⊤)) ⥤ X.Modules :=
    globalSectionsModuleFunctor (RingHom.id _)
  letI : PreservesColimits F := globalSectionsModuleFunctor_preservesColimits (RingHom.id _)
  letI :
      (F.obj (ModuleCat.of _ (Fin m → X.presheaf.obj (op ⊤)))).IsFinitePresentation :=
    associatedModuleSheafFunctionFinite_isFinitePresentation (X := X) m
  letI :
      (F.obj (ModuleCat.of _ (Fin n → X.presheaf.obj (op ⊤)))).IsFinitePresentation :=
    associatedModuleSheafFunctionFinite_isFinitePresentation (X := X) n
  have hCokernel : (cokernel (F.map f)).IsFinitePresentation := by
    exact SheafOfModules.isFinitePresentation_cokernel (F.map f)
  let eModule : N ≅ cokernel f :=
    hcolim.coconePointUniqueUpToIso (colimit.isColimit (parallelPair f 0))
  let eSheaf : cokernel (F.map f) ≅ F.obj N :=
    (PreservesCokernel.iso F f).symm ≪≫ (F.mapIso eModule).symm
  -- Proof comment: the associated sheaf of `N` is the image under `F` of the cokernel of `f`, so
  -- finite presentation transports across the preserved-cokernel comparison.
  exact
    (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X)).prop_of_iso
      eSheaf hCokernel

/-- Helper for Lemma 17.11.6: mapping a filtered colimit presentation of modules through the
associated-module-sheaf functor yields a filtered colimit presentation of associated sheaves. -/
lemma associatedModuleSheaf_ind_of_module_ind
    {X : RingedSpace.{u}} (M : ModuleCat.{u} (X.presheaf.obj (op ⊤)))
    (hM : ind (fun N : ModuleCat.{u} (X.presheaf.obj (op ⊤)) ↦
      Module.FinitePresentation (X.presheaf.obj (op ⊤)) N) M) :
    ind (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X)) (𝓕_ M) := by
  rcases hM with ⟨J, _, _, pres, hpres⟩
  let F : ModuleCat.{u} (X.presheaf.obj (op ⊤)) ⥤ X.Modules :=
    globalSectionsModuleFunctor (RingHom.id _)
  letI : PreservesColimits F := globalSectionsModuleFunctor_preservesColimits (RingHom.id _)
  letI : PreservesColimitsOfShape J F := inferInstance
  refine ⟨J, inferInstance, inferInstance, pres.map F, ?_⟩
  intro j
  -- Proof comment: each stage of the filtered module presentation is finitely presented by
  -- hypothesis, so the stagewise bridge upgrades its associated module sheaf accordingly.
  letI : Module.FinitePresentation (X.presheaf.obj (op ⊤)) (pres.diag.obj j) := hpres j
  simpa [F] using
    associatedModuleSheaf_isFinitePresentation_of_moduleFinitePresentation
      (X := X) (N := pres.diag.obj j)

-- Proof sketch: choose an associated-module-sheaf presentation of `ℱ` from Definition `17.10.6`,
-- then recover a functor realizing that presentation from Lemma `17.10.5`. Apply Lemma
-- `10.11.3` to write `M` as a filtered colimit of finitely presented `R`-modules, then use that
-- the associated-sheaf functor preserves colimits and carries finitely presented modules to
-- finitely presented `\mathcal O_X`-modules.
/-- Lemma 17.11.6: if `ℱ` is an `\mathcal O_X`-module associated to an
`R = \Gamma(X, \mathcal O_X)`-module `M`, then `ℱ` is a directed colimit of finitely presented
`\mathcal O_X`-modules. -/
@[stacks 01BR]
theorem associatedGlobalSectionsModuleSheaf_isFilteredColimitOfFinitePresentation
    {X : RingedSpace.{u}} (M : ModuleCat.{u} (X.presheaf.obj (op ⊤))) (ℱ : X.Modules)
    (hℱ : Nonempty (ℱ ≅ 𝓕_ M)) :
    ind (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X)) ℱ := by
  rcases hℱ with ⟨e⟩
  let hM :
      ind (fun N : ModuleCat.{u} (X.presheaf.obj (op ⊤)) ↦
        Module.FinitePresentation (X.presheaf.obj (op ⊤)) N) M :=
    module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented
      (R := X.presheaf.obj (op ⊤)) (M := M)
  have hAssociated :
      ind (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X)) (𝓕_ M) :=
    associatedModuleSheaf_ind_of_module_ind (X := X) M hM
  -- Proof comment: the target sheaf differs from the canonical associated sheaf only by the given
  -- isomorphism, so the filtered-colimit property transports across `e.symm`.
  exact
    (ind (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X))).prop_of_iso
      e.symm hAssociated

end AlgebraicGeometry
