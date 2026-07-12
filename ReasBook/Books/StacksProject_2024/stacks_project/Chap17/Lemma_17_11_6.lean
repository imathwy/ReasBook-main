import Mathlib
import StacksProject_2024.Chap17.Definition_17_10_6
import StacksProject_2024.Chap17.Lemma_17_11_3
import StacksProject_2024.Chap10.Definition_10_5_1
import StacksProject_2024.Chap10.Lemma_10_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

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
private noncomputable def functionFiniteFreeIsoFinsuppFiniteFree
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
          ∃ hfg : f ≫ g = 0, IsColimit (CokernelCofork.ofπ g hfg) := by
  obtain ⟨n, m, f, g, hExact, hSurj⟩ :=
    (Module.FinitePresentation.iff_exists_exact_free_sequence (R := R) (M := M)).1 inferInstance
  let fCat : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R) := ModuleCat.ofHom f
  let gCat : ModuleCat.of R (Fin n → R) ⟶ M := ModuleCat.ofHom g
  have hfg : fCat ≫ gCat = 0 := by
    -- Proof comment: exactness on the underlying linear maps immediately forces the composite to
    -- vanish in the categorical free presentation.
    ext x
    exact hExact.apply_apply_eq_zero x
  refine ⟨n, m, fCat, gCat, hfg, ?_⟩
  -- Proof comment: exactness and surjectivity identify the quotient by `f` with `M`, so `g`
  -- is the categorical cokernel of `f`.
  simpa [fCat, gCat, hfg] using ModuleCat.isColimitCokernelCofork fCat gCat hExact hSurj

/-- Helper for Lemma 17.11.6: restricting a finite global presentation of an `\mathcal O_X`-module
keeps the same finite generator and relation index types. -/
private theorem presentation_map_isFinite
    {X : RingedSpace.{u}} {ℱ : X.Modules} (P : ℱ.Presentation) [P.IsFinite]
    (U : Opens X) :
    ((P.map (pushforward (𝟙 ((RingedSpace.ringCatSheaf X).over U))) (by rfl))).IsFinite := by
  -- Proof comment: `Presentation.map` only transports the existing presentation data to the slice
  -- over `U`, so the chosen finite generator and relation index types are unchanged.
  refine ⟨?_, ?_⟩
  · dsimp [SheafOfModules.Presentation.map, SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.generatorsOfIsCokernelFree]
    refine ⟨?_⟩
    change Finite P.generators.I
    infer_instance
  · dsimp [SheafOfModules.Presentation.map, SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.relationsOfIsCokernelFree]
    infer_instance

/-- Helper for Lemma 17.11.6: a finite global presentation upgrades a module sheaf to the owner
predicate `IsFinitePresentation`. -/
private theorem isFinitePresentation_of_finitePresentationData
    {X : RingedSpace.{u}} {ℱ : X.Modules} (P : ℱ.Presentation) [P.IsFinite] :
    ℱ.IsFinitePresentation := by
  -- Proof comment: use the trivial-cover quasicoherent data attached to `P`; after restricting to
  -- any open, the previous helper keeps the same finite presentation data.
  refine ⟨P.quasicoherentData, ?_⟩
  constructor
  intro U
  simpa using presentation_map_isFinite (P := P) U

/-- Helper for Lemma 17.11.6: a finite free `\mathcal O_X`-module is finitely presented. -/
private theorem free_isFinitePresentation_of_finite
    {X : RingedSpace.{u}} (I : Type u) [Finite I] :
    (SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I : X.Modules).IsFinitePresentation := by
  classical
  rcases (inferInstance :
      Nonempty
        {P :
          (SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I : X.Modules).Presentation //
            P.IsFinite}) with ⟨P⟩
  let Q :
      (SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I : X.Modules).Presentation := P.1
  letI : Q.IsFinite := P.2
  -- Proof comment: the imported finite free presentation witness already gives a finite global
  -- presentation, so the owner bridge above closes the finite-presentation predicate.
  exact isFinitePresentation_of_finitePresentationData (P := Q)

/-- Helper for Lemma 17.11.6: the associated sheaf of a finitely supported free
`Γ(X,\mathcal O_X)`-module should identify with the free `\mathcal O_X`-module on the same basis.
-/
private noncomputable def associatedModuleSheafFinsuppIsoFree
    {X : RingedSpace.{u}} (I : Type u) :
    associatedModuleSheaf (RingHom.id _) (ModuleCat.of _ (I →₀ X.presheaf.obj (op ⊤))) ≅
      (SheafOfModules.free (R := RingedSpace.ringCatSheaf X) I : X.Modules) := sorry

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

/-- Helper for Lemma 17.11.6: a finitely presented module over `Γ(X, \mathcal O_X)` should give a
finitely presented associated `\mathcal O_X`-module. -/
lemma associatedModuleSheaf_isFinitePresentation_of_moduleFinitePresentation
    {X : RingedSpace.{u}} {N : ModuleCat.{u} (X.presheaf.obj (op ⊤))}
    [Module.FinitePresentation (X.presheaf.obj (op ⊤)) N] :
    (𝓕_ N).IsFinitePresentation := by
  -- Route correction: the old singleton-source pullback plan depends on private helper
  -- declarations from Lemma `17.10.5`. The stabilized route now keeps the whole proof inside the
  -- public API: choose a finite free cokernel presentation of `N`, rewrite the associated finite
  -- free terms to genuine free sheaves, and finish with `isFinitePresentation_cokernel`.
  obtain ⟨n, m, f, g, hfg, hcolim⟩ :=
    finitelyPresentedModule_existsFunctionFreeCokernelPresentation (M := N)
  let en :=
    functionFiniteFreeIsoFinsuppFiniteFree (R := X.presheaf.obj (op ⊤)) n
  let em :=
    functionFiniteFreeIsoFinsuppFiniteFree (R := X.presheaf.obj (op ⊤)) m
  let f' :
      ModuleCat.of _ (ULift.{u} (Fin m) →₀ X.presheaf.obj (op ⊤)) ⟶
        ModuleCat.of _ (ULift.{u} (Fin n) →₀ X.presheaf.obj (op ⊤)) :=
    em.inv ≫ f ≫ en.hom
  let g' :
      ModuleCat.of _ (ULift.{u} (Fin n) →₀ X.presheaf.obj (op ⊤)) ⟶ N :=
    en.inv ≫ g
  have hfg' : f' ≫ g' = 0 := by
    -- Proof comment: conjugating the presentation by the free-module isomorphisms preserves the
    -- vanishing composite.
    simp [f', g', hfg, Category.assoc]
  have hcolim' : IsColimit (CokernelCofork.ofπ g' hfg') := by
    -- Proof comment: any cofork over the transported presentation becomes a cofork over the
    -- original function-model presentation after postcomposing with `en.hom`, so the original
    -- cokernel witness transfers directly.
    refine Cofork.IsColimit.mk (CokernelCofork.ofπ g' hfg') (fun s ↦ ?_) (fun s ↦ ?_) (fun s k hk ↦ ?_)
    · have hs : f ≫ (en.hom ≫ s.π) = 0 := by
        calc
          f ≫ (en.hom ≫ s.π) = em.hom ≫ (f' ≫ s.π) := by
            simp [f', Category.assoc]
          _ = 0 := by simp [s.condition]
      exact hcolim.desc (CokernelCofork.ofπ (en.hom ≫ s.π) hs)
    · have hs : f ≫ (en.hom ≫ s.π) = 0 := by
        calc
          f ≫ (en.hom ≫ s.π) = em.hom ≫ (f' ≫ s.π) := by
            simp [f', Category.assoc]
          _ = 0 := by simp [s.condition]
      have hdesc :
          g ≫ hcolim.desc (CokernelCofork.ofπ (en.hom ≫ s.π) hs) = en.hom ≫ s.π :=
        hcolim.fac (CokernelCofork.ofπ (en.hom ≫ s.π) hs)
      calc
        g' ≫ hcolim.desc (CokernelCofork.ofπ (en.hom ≫ s.π) hs)
            = en.inv ≫ (g ≫ hcolim.desc (CokernelCofork.ofπ (en.hom ≫ s.π) hs)) := by
                simp [g', Category.assoc]
        _ = en.inv ≫ (en.hom ≫ s.π) := by rw [hdesc]
        _ = s.π := by simp [Category.assoc]
    · have hs : f ≫ (en.hom ≫ s.π) = 0 := by
        calc
          f ≫ (en.hom ≫ s.π) = em.hom ≫ (f' ≫ s.π) := by
            simp [f', Category.assoc]
          _ = 0 := by simp [s.condition]
      apply hcolim.uniq (CokernelCofork.ofπ (en.hom ≫ s.π) hs)
      calc
        g ≫ k = en.hom ≫ (g' ≫ k) := by
          simp [g', Category.assoc]
        _ = en.hom ≫ s.π := by rw [hk]
  letI :
      (associatedModuleSheaf (RingHom.id _)
        (ModuleCat.of _ (ULift.{u} (Fin m) →₀ X.presheaf.obj (op ⊤)))).IsFinitePresentation :=
    associatedModuleSheafFinsupp_isFinitePresentation_of_finite (X := X) (ULift.{u} (Fin m))
  letI :
      (associatedModuleSheaf (RingHom.id _)
        (ModuleCat.of _ (ULift.{u} (Fin n) →₀ X.presheaf.obj (op ⊤)))).IsFinitePresentation :=
    associatedModuleSheafFinsupp_isFinitePresentation_of_finite (X := X) (ULift.{u} (Fin n))
  have hPresentation :
      (associatedModuleSheafFromPresentation (RingHom.id _) f').IsFinitePresentation := by
    -- Proof comment: the cokernel of a finite-type map into a finitely presented sheaf is again
    -- finitely presented.
    simpa [associatedModuleSheafFromPresentation, associatedModulePresentationMap] using
      (SheafOfModules.isFinitePresentation_cokernel
        (R := RingedSpace.ringCatSheaf X)
        (φ := associatedModulePresentationMap (RingHom.id _) f'))
  let ePresentation :=
    associatedModuleSheafFromPresentationIso (RingHom.id _) f' g' hfg' hcolim'
  -- Proof comment: the associated sheaf of `N` is the transported cokernel of the finite free
  -- presentation just constructed, so the owner property closes after one final iso transport.
  exact
    (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X)).prop_of_iso
      ePresentation hPresentation

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
