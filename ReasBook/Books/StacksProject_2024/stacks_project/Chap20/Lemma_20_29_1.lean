import StacksProject_2024.Chap12.Lemma_12_24_2
import StacksProject_2024.Chap12.Lemma_12_24_13
import StacksProject_2024.Chap13.Lemma_13_31_6
import StacksProject_2024.Chap19.Lemma_19_13_7
import StacksProject_2024.Chap20.Global_sections_module_owners_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.FilteredComplex
open AlgebraicGeometry
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})

local notation "ModX" => RingedSpace.Modules X
local notation "ModΓX" => ModuleCat (globalSectionsRing X)
local notation "QX" => (DerivedCategory.Q : CochainComplex ModX ℤ ⥤ DerivedCategory ModX)
local notation "RΓ" => moduleDerivedGlobalSections X
local notation "HΓ" n => DerivedCategory.homologyFunctor ModΓX n

/-- Helper for Lemma `20.29.1`: applying a monomorphism-preserving functor to each stage of a
filtered object again produces a filtered object. -/
private def mapFilteredObject
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (T : C ⥤ D) [T.PreservesMonomorphisms] (A : FilteredObject C) :
    FilteredObject D where
  obj := T.obj A.obj
  filtration :=
    { toFun := fun p ↦ Subobject.mk (T.map (A.filtration.obj p).arrow)
      monotone' := by
        intro p q hpq
        refine Subobject.mk_le_mk_of_comm
          (T.map (Subobject.ofLE _ _ (A.filtration.monotone hpq))) ?_
        rw [← T.map_comp, Subobject.ofLE_arrow] }

/-- Helper for Lemma `20.29.1`: a filtered morphism stays filtered after applying a
monomorphism-preserving functor. -/
private theorem mapFilteredObject_preserves
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (T : C ⥤ D) [T.PreservesMonomorphisms]
    {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    ((mapFilteredObject T B).filtration p).Factors
      (((mapFilteredObject T A).filtration p).arrow ≫ T.map f.hom) := by
  let u := (B.filtration p).factorThru ((A.filtration p).arrow ≫ f.hom) (f.preserves p)
  let e := Subobject.underlyingIso (T.map (A.filtration p).arrow)
  -- Proof comment: rewrite the mapped filtration stages as explicit `Subobject.mk` owners and
  -- apply `T` to the original stagewise factorization.
  change (Subobject.mk (T.map (B.filtration p).arrow)).Factors
    ((Subobject.mk (T.map (A.filtration p).arrow)).arrow ≫ T.map f.hom)
  rw [Subobject.mk_factors_iff]
  refine ⟨e.hom ≫ T.map u, ?_⟩
  have hu :
      T.map u ≫ T.map (B.filtration p).arrow =
        T.map (A.filtration p).arrow ≫ T.map f.hom := by
    dsimp [u]
    rw [← T.map_comp, Subobject.factorThru_arrow, T.map_comp]
  calc
    (e.hom ≫ T.map u) ≫ T.map (B.filtration p).arrow
        = e.hom ≫ (T.map u ≫ T.map (B.filtration p).arrow) := by
            simp [Category.assoc]
    _ = e.hom ≫ (T.map (A.filtration p).arrow ≫ T.map f.hom) := by rw [hu]
    _ = (e.hom ≫ T.map (A.filtration p).arrow) ≫ T.map f.hom := by
          simp [Category.assoc]
    _ = (Subobject.mk (T.map (A.filtration p).arrow)).arrow ≫ T.map f.hom := by
          rw [Subobject.underlyingIso_hom_comp_eq_mk]

/-- Helper for Lemma `20.29.1`: applying a monomorphism-preserving functor defines a functor on
filtered objects. -/
private def mapFilteredObjectFunctor
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (T : C ⥤ D) [T.PreservesMonomorphisms] :
    FilteredObject C ⥤ FilteredObject D where
  obj A := mapFilteredObject T A
  map f :=
    { hom := T.map f.hom
      preserves := mapFilteredObject_preserves T f }
  map_id A := by
    apply FilteredObject.Hom.ext
    change T.map (𝟙 A.obj) = 𝟙 (T.obj A.obj)
    exact T.map_id A.obj
  map_comp f g := by
    apply FilteredObject.Hom.ext
    change T.map (f.hom ≫ g.hom) = T.map f.hom ≫ T.map g.hom
    exact T.map_comp f.hom g.hom

/-- Helper for Lemma `20.29.1`: if `T` preserves zero morphisms, then its induced functor on
filtered objects also preserves zero morphisms. -/
private instance mapFilteredObjectFunctor_preservesZeroMorphisms
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (T : C ⥤ D) [T.PreservesMonomorphisms] [T.PreservesZeroMorphisms] :
    (mapFilteredObjectFunctor T).PreservesZeroMorphisms where
  map_zero A B := by
    apply FilteredObject.Hom.ext
    change T.map (0 : A.obj ⟶ B.obj) = 0
    simpa using Functor.map_zero T A.obj B.obj

local instance moduleGlobalSectionsFunctor_preservesMonomorphisms :
    (moduleGlobalSectionsFunctor X).PreservesMonomorphisms := by
  refine ⟨fun {A B} f _ ↦ ?_⟩
  -- Proof comment: global sections is evaluation at the terminal open, and a monomorphism of
  -- sheaves of modules is monic on every section object.
  let _ : Mono ((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map f) :=
    (SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map_mono f
  change Mono
    (((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map f).app
      (op (⊤ : Opens X.carrier)))
  infer_instance

/-- Helper for Lemma `20.29.1`: apply global sections degreewise to a filtered complex of
`𝒪_X`-modules. -/
private noncomputable def filteredGlobalSectionsComplex
    (K : FilteredComplex ModX) : FilteredComplex ModΓX :=
  ((mapFilteredObjectFunctor (moduleGlobalSectionsFunctor X)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- Helper for Lemma `20.29.1`: every graded piece of a filtered complex is the cokernel of the
successor stage map. -/
private theorem filteredComplexGradedPiece_obj_eq_cokernel
    {C : Type*} [Category C] [Abelian C] (K : FilteredComplex C) (n p : ℤ) :
    (K.gradedPiece p).X n = cokernel ((K.stageMapOfLE (lt_add_one p).le).f n) := by
  -- Proof comment: evaluating the graded-piece complex at degree `n` is definitionally the
  -- cokernel of the degree-`n` stage map.
  rfl

/-- Helper for Lemma `20.29.1`: every graded piece of a filtered complex is canonically the
cokernel of the successor stage map. -/
private noncomputable def filteredComplexGradedPieceCokernelIso
    {C : Type*} [Category C] [Abelian C] (K : FilteredComplex C) (p : ℤ) :
    K.gradedPiece p ≅ cokernel (K.stageMapOfLE (lt_add_one p).le) := by
  -- Proof comment: for filtered cochain complexes, `gr^p` is definitionally the cokernel of
  -- `F^{p + 1} K^• ⟶ F^p K^•`.
  -- TODO: prove the owner-level equality `K.gradedPiece p = cokernel (K.stageMapOfLE
  -- (lt_add_one p).le)` and package it with `eqToIso`; `rfl` alone does not close the
  -- comparison on this file's owner spelling.
  sorry

/-- Helper for Lemma `20.29.1`: the graded piece `gr^{p} K` is the successor filtration
subquotient `K.subquotient (lt_add_one p).le`. -/
private noncomputable def filteredComplexGradedPieceSubquotientIso
    (K : FilteredComplex ModX) (p : ℤ) :
    gr^{p} K ≅ K.subquotient (lt_add_one p).le := by
  -- Proof comment: `FilteredComplex.subquotient` is the same cokernel, with the filtration step
  -- pair already packed into the Chapter `19` owner API.
  simpa [FilteredComplex.subquotient] using filteredComplexGradedPieceCokernelIso K p

/-- Helper for Lemma `20.29.1`: the graded piece of the filtered global-sections complex is the
global-sections complex of the corresponding filtration subquotient. -/
private noncomputable def gradedPieceFilteredGlobalSectionsIsoOfSubquotient
    (J : FilteredComplex ModX) (p : ℤ) :
    gr^{p} (filteredGlobalSectionsComplex X J) ≅
      ((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (J.subquotient (lt_add_one p).le) := by
  -- Route correction: compare both sides through the common cokernel owner and use the canonical
  -- preserved-cokernel isomorphism for degreewise global sections.
  -- TODO: build the complex-level cokernel comparison by supplying the pointwise cokernel
  -- isomorphisms from `moduleGlobalSectionsCokernelIsoOfInjectiveSource`, then rewrite the target
  -- cokernel owner to `J.subquotient (lt_add_one p).le`.
  sorry

/-- Helper for Lemma `20.29.1`: the cochain-level derived-unit component for global sections is
an isomorphism on K-injective complexes. -/
private theorem moduleGlobalSectionsHomotopy_hasPointwiseRightDerivedFunctor :
    (((moduleGlobalSectionsFunctor X).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
      (DerivedCategory.Qh : HomotopyCategory ModΓX (ComplexShape.up ℤ) ⥤
        DerivedCategory ModΓX)).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso ModX (ComplexShape.up ℤ)) := by
  let F :
      HomotopyCategory ModX (ComplexShape.up ℤ) ⥤ DerivedCategory ModΓX :=
    ((moduleGlobalSectionsFunctor X).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
      DerivedCategory.Qh
  let Qish :
      MorphismProperty (HomotopyCategory ModX (ComplexShape.up ℤ)) :=
    HomotopyCategory.quasiIso ModX (ComplexShape.up ℤ)
  -- Proof comment: replicate the Chapter 13 K-injective-resolution existence argument on the
  -- homotopy side, so every object is connected to a computing K-injective representative.
  refine F.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt Qish ?_
  intro K
  obtain ⟨Kinj, _, hKinj⟩ := CochainComplex.exists_functorial_kInjective_resolution ModX
  refine
    ⟨(HomotopyCategory.quotient ModX (ComplexShape.up ℤ)).obj (Kinj.toFunctor.obj K.as), ?_, ?_, ?_⟩
  · -- Proof comment: the chosen functorial replacement arrow gives the required comparison in the
    -- homotopy category after rewriting `K` back to its quotient model.
    simpa [HomotopyCategory.quotient_obj_as] using
      (HomotopyCategory.quotient ModX (ComplexShape.up ℤ)).map (Kinj.ι.app K.as)
  · -- Proof comment: the replacement arrow is a quasi-isomorphism by construction.
    exact
      (HomotopyCategory.quotient_map_mem_quasiIso_iff (C := ModX) (c := ComplexShape.up ℤ)
        (Kinj.ι.app K.as)).2
        (Kinj.quasiIso_app K.as)
  · -- Proof comment: a K-injective target computes the right derived functor at that object.
    letI : (Kinj.toFunctor.obj K.as).IsKInjective := hKinj K.as
    simpa [F, Qish] using
      (kInjective_computesRightDerivedFunctorAt (F := F) (Kinj.toFunctor.obj K.as))

/-- Helper for Lemma `20.29.1`: on a K-injective complex, the homotopy-side total right derived
unit for global sections is an isomorphism. -/
private theorem moduleGlobalSectionsHomotopyUnit_app_isIso_of_isKInjective
    (L : CochainComplex ModX ℤ) [L.IsKInjective] :
    let Qish : MorphismProperty (HomotopyCategory ModX (ComplexShape.up ℤ)) :=
      HomotopyCategory.quasiIso ModX (ComplexShape.up ℤ)
    IsIso
      ((Functor.totalRightDerivedUnit
          (((moduleGlobalSectionsFunctor X).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
            DerivedCategory.Qh)
          Qish.Q
          Qish).app
        ((HomotopyCategory.quotient ModX (ComplexShape.up ℤ)).obj L)) := by
  let F :
      HomotopyCategory ModX (ComplexShape.up ℤ) ⥤ DerivedCategory ModΓX :=
    ((moduleGlobalSectionsFunctor X).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
      DerivedCategory.Qh
  let Qish :
      MorphismProperty (HomotopyCategory ModX (ComplexShape.up ℤ)) :=
    HomotopyCategory.quasiIso ModX (ComplexShape.up ℤ)
  letI : F.HasPointwiseRightDerivedFunctor Qish :=
    moduleGlobalSectionsHomotopy_hasPointwiseRightDerivedFunctor (X := X)
  have hCompute :
      F.ComputesRightDerivedAt Qish
        ((HomotopyCategory.quotient ModX (ComplexShape.up ℤ)).obj L) := by
    -- Proof comment: a K-injective complex already computes the homotopy-side right derived
    -- global-sections functor.
    simpa [F, Qish] using
      (kInjective_computesRightDerivedFunctorAt (F := F) L)
  -- Proof comment: the owner bridge `computesRightDerivedAt_iff` turns the K-injective
  -- computation fact into invertibility of the homotopy-side total right-derived unit component.
  simpa [F, Qish] using
    (Functor.computesRightDerivedAt_iff
      (F := F)
      (S := Qish)
      (X := ((HomotopyCategory.quotient ModX (ComplexShape.up ℤ)).obj L))).1
      hCompute

private theorem moduleDerivedGlobalSectionsUnit_app_isIso_of_isKInjective
    (L : CochainComplex ModX ℤ) [L.IsKInjective] :
    IsIso ((additiveFunctorTotalRightDerivedUnit (moduleGlobalSectionsFunctor X)).app L) := by
  -- TODO: the homotopy-side unit is now proved on the canonical localization owner
  -- `Qish.Q` in `moduleGlobalSectionsHomotopyUnit_app_isIso_of_isKInjective`. The remaining
  -- blocker is an owner-level normalization lemma identifying that unit with the explicit
  -- `DerivedCategory.Qh`-based spelling inside `additiveFunctorTotalRightDerivedUnit`.
  sorry

private noncomputable def moduleDerivedGlobalSectionsIsoOfIsKInjective
    (L : CochainComplex ModX ℤ) [L.IsKInjective] :
    DerivedCategory.Q.obj
        (((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≅
      (RΓ).obj ((QX).obj L) := by
  -- TODO: compare `additiveFunctorTotalRightDerived (moduleGlobalSectionsFunctor X)` with the
  -- local owner `moduleDerivedGlobalSections X` by `Functor.rightDerivedUnique`, then compose the
  -- resulting functor-level comparison with
  -- `moduleDerivedGlobalSectionsUnit_app_isIso_of_isKInjective`.
  sorry

/-- Helper for Lemma `20.29.1`: a quasi-isomorphism into a K-injective complex computes
hypercohomology by taking ordinary homology after applying global sections. -/
private noncomputable def mappedGlobalSectionsHomologyIsoOfQuasiIsoToKInjective
    {A L : CochainComplex ModX ℤ} (f : A ⟶ L) (n : ℤ) (hf : QuasiIso f) [L.IsKInjective] :
    (((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homology n ≅
      (HΓ n).obj ((RΓ).obj ((QX).obj A)) := by
  -- TODO: after identifying `moduleDerivedGlobalSections X` with
  -- `additiveFunctorTotalRightDerived (moduleGlobalSectionsFunctor X)`, combine
  -- `DerivedCategory.homologyFunctorFactors`, the K-injective unit comparison, and the derived
  -- image of `f`.
  sorry

/-- Helper for Lemma `20.29.1`: if `i : A ⟶ B` has injective source, then the induced map on
global sections is split monic. -/
private theorem moduleGlobalSectionsMap_isSplitMono_of_injective_source
    {A B : ModX} (i : A ⟶ B) [Mono i] [Injective A] :
    IsSplitMono ((moduleGlobalSectionsFunctor X).map i) := by
  let S : ShortComplex ModX :=
    ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance
  have hs : IsSplitMono i := by
    -- Proof comment: the exact row `0 ⟶ A ⟶ B ⟶ cokernel i ⟶ 0` splits because `A` is injective.
    simpa [S] using (hS.splittingOfInjective).isSplitMono_f
  let _ : IsSplitMono i := hs
  refine IsSplitMono.mk' ⟨(moduleGlobalSectionsFunctor X).map (retraction i), ?_⟩
  -- Proof comment: applying the functor to the chosen retraction preserves the split identity.
  calc
    (moduleGlobalSectionsFunctor X).map i ≫
        (moduleGlobalSectionsFunctor X).map (retraction i)
        = (moduleGlobalSectionsFunctor X).map (i ≫ retraction i) := by
            symm
            exact (moduleGlobalSectionsFunctor X).map_comp i (retraction i)
    _ = (moduleGlobalSectionsFunctor X).map (𝟙 A) := by rw [IsSplitMono.id i]
    _ = 𝟙 ((moduleGlobalSectionsFunctor X).obj A) := by
          simp

/-- Helper for Lemma `20.29.1`: if `i : A ⟶ B` has injective source, then global sections carries
the cokernel of `i` to the cokernel of the induced map on global sections. -/
private noncomputable def moduleGlobalSectionsCokernelIsoOfInjectiveSource
    {A B : ModX} (i : A ⟶ B) [Mono i] [Injective A] :
    cokernel ((moduleGlobalSectionsFunctor X).map i) ≅
      (moduleGlobalSectionsFunctor X).obj (cokernel i) := by
  let S : ShortComplex ModX :=
    ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance
  let spl : S.Splitting := hS.splittingOfInjective
  have hMapped : (S.map (moduleGlobalSectionsFunctor X)).ShortExact := by
    -- Proof comment: the chosen splitting of the original short exact row survives after
    -- applying the additive global-sections functor.
    exact (spl.map (moduleGlobalSectionsFunctor X)).shortExact
  let hCok :
      IsColimit
        (CokernelCofork.ofπ
          (f := (moduleGlobalSectionsFunctor X).map i)
          ((moduleGlobalSectionsFunctor X).map (cokernel.π i))
          (by
            rw [← (moduleGlobalSectionsFunctor X).map_comp]
            simpa using
              (Functor.map_zero (moduleGlobalSectionsFunctor X) A (cokernel i)))) := by
    simpa [S] using (ShortComplex.ShortExact.gIsCokernel hMapped)
  -- Proof comment: both targets represent cokernels of the same mapped morphism, so the universal
  -- comparison gives the desired object-level bridge.
  let e :
      cokernel ((moduleGlobalSectionsFunctor X).map i) ≅
        (moduleGlobalSectionsFunctor X).obj (cokernel i) := by
    simpa using
      (IsColimit.coconePointUniqueUpToIso
        (cokernelIsCokernel ((moduleGlobalSectionsFunctor X).map i))
        hCok)
  exact e

/-- In each total degree, the hypercohomology of the filtration stages vanishes for all
sufficiently large filtration indices. -/
def EventualStageHypercohomologyVanishesAbove
    (K : FilteredComplex ModX) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄, p₀ ≤ p →
    IsZero ((HΓ n).obj ((RΓ).obj ((QX).obj (F^{p} K))))

/-- In each total degree, the canonical maps from stage hypercohomology to the hypercohomology
of the underlying complex are isomorphisms for all sufficiently small filtration indices. -/
def EventualStageHypercohomologyStabilizesBelow
    (K : FilteredComplex ModX) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p₁ →
    IsIso ((HΓ n).map ((RΓ).map ((QX).map (K.stageInclusion p))))

/-- The combined stage-control hypotheses of Lemma `20.29.1`: in every total degree, the
hypercohomology of the filtration stages vanishes for `p ≫ 0` and the canonical stage maps to the
abutment hypercohomology are isomorphisms for `p ≪ 0`. -/
def EventualStageHypercohomologyControl
    (K : FilteredComplex ModX) : Prop :=
  EventualStageHypercohomologyVanishesAbove X K ∧
    EventualStageHypercohomologyStabilizesBelow X K

theorem EventualStageHypercohomologyControl.vanishesAbove
    {K : FilteredComplex ModX}
    (hcontrol : EventualStageHypercohomologyControl X K) :
    EventualStageHypercohomologyVanishesAbove X K :=
  hcontrol.1

theorem EventualStageHypercohomologyControl.stabilizesBelow
    {K : FilteredComplex ModX}
    (hcontrol : EventualStageHypercohomologyControl X K) :
    EventualStageHypercohomologyStabilizesBelow X K :=
  hcontrol.2

/- Domain-style sampling for Lemma `20.29.1`.
- primary domain: filtered complexes and their associated cohomological spectral sequences after
  applying derived global sections and viewing the result over `Γ(X, 𝒪_X)`;
- sampled owner declarations:
  `moduleDerivedGlobalSections`,
  `EventualStageHypercohomologyVanishesAbove`,
  `EventualStageHypercohomologyStabilizesBelow`,
  `EventualStageHypercohomologyControl`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction: the source-facing theorem should quantify directly over the canonical
  Chapter `12` owners `FilteredComplex`, `CohomologicalSpectralSequence`, and
  `IsAssociatedToFilteredComplex`, while the hypercohomology terms should reuse the established
  Chapter `20` owner `moduleDerivedGlobalSections X` rather than a parallel local top-open
  wrapper of the same global-sections functor;
- primitive data: the filtered complex in `ModΓX`, its associated spectral sequence, the
  source-facing `E₁`-page and abutment comparison isomorphisms obtained by taking homology of the
  canonical derived global-sections owner, and the eventual stagewise control owners
  displayed on the theorem surface;
- derived API: the returned page-one and abutment comparison isomorphisms, the bundled
  source-facing control owner `EventualStageHypercohomologyControl`, and the canonical
  boundedness/convergence consequence via `FilteredComplex.convergesToCohomology`;
- source/core/bridge triage:
  `source-facing`: `EventualStageHypercohomologyVanishesAbove`,
    `EventualStageHypercohomologyStabilizesBelow`,
    `EventualStageHypercohomologyControl`, and the existence theorem;
  `core/canonical`: `FilteredComplex`, `CohomologicalSpectralSequence`, and
    `IsAssociatedToFilteredComplex`;
  `bridge/view`: the page-one and target comparison isomorphisms specialized to
    `moduleDerivedGlobalSections X`. -/

-- Proof sketch: choose a filtered K-injective replacement `K^• ⟶ J^•` as in Lemma `19.13.7`,
-- apply the global-sections functor degreewise to obtain a filtered complex of
-- `Γ(X, 𝒪_X)`-modules, and take its associated spectral sequence from Chapter `12.24`.
-- Evaluating cohomology on the graded pieces gives the stated `E₁`-page, and Lemma `12.24.13`
-- supplies boundedness and convergence from the eventual vanishing and stabilization hypotheses on
-- the stage hypercohomology.
/-- Lemma 20.29.1: for a ringed space `X` and a filtered complex `𝒜^•` of `𝒪_X`-modules, there
exist a filtered complex of `Γ(X, 𝒪_X)`-modules and an associated cohomological spectral
sequence realizing the filtered hypercohomology of `𝒜^•`. The theorem returns the canonical
Chapter `12` owners `filteredComplex`, `spectralSequence`, and
`IsAssociatedToFilteredComplex filteredComplex spectralSequence`, together with the source-facing
`E₁`-page isomorphisms
`(spectralSequence.page 1).X (p, q) ≅ H^(p + q)(RΓ(X, gr^p 𝒜^•))` and the abutment isomorphisms
`filteredComplex.underlying.homology n ≅ H^n(RΓ(X, 𝒜^•.underlying))`. Under the bundled
stage-control owner `EventualStageHypercohomologyControl X K`, the same chosen spectral sequence
is bounded and converges to the hypercohomology of `𝒜^•`. -/
@[stacks 0BKK]
theorem exists_filteredHypercohomologySpectralSequence
    (K : FilteredComplex ModX) :
    ∃ (filteredComplex : FilteredComplex ModΓX)
      (spectralSequence : CohomologicalSpectralSequence ModΓX 0)
      (associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageOne : ∀ p q : ℤ,
        (spectralSequence.page 1).X (p, q) ≅
          (HΓ (p + q)).obj ((RΓ).obj ((QX).obj (gr^{p} K))))
      (abutment : ∀ n : ℤ,
        filteredComplex.underlying.homology n ≅
          (HΓ n).obj ((RΓ).obj ((QX).obj K.underlying))),
      EventualStageHypercohomologyControl X K →
        CohomologicalSpectralSequence.IsBounded spectralSequence ∧
          filteredComplex.convergesToCohomology spectralSequence := by
  let filteredComplexFunctor :
      FilteredComplex ModX ⥤ FilteredComplex ModΓX :=
    (mapFilteredObjectFunctor (moduleGlobalSectionsFunctor X)).mapHomologicalComplex
      (ComplexShape.up ℤ)
  obtain ⟨J, j, hJunderlyingInjective, hJstageInjective, hJquotientInjective,
      hJsubquotientInjective, hJunderlyingKInjective, hJstageKInjective, hJquotientKInjective,
      hJsubquotientKInjective, hjUnderlyingQuasiIso, hjStageQuasiIso, hjQuotientQuasiIso,
      hjSubquotientQuasiIso⟩ := exists_filteredComplex_kInjectiveReplacement K
  let filteredComplex := filteredComplexFunctor.obj J
  obtain ⟨spectralSequence, associated⟩ :=
    exists_filteredComplexAssociatedSpectralSequence filteredComplex
  letI : IsAssociatedToFilteredComplex filteredComplex spectralSequence := associated
  refine ⟨filteredComplex, spectralSequence, associated, ?_, ?_, ?_⟩
  · intro p q
    -- Proof comment: start from the Chapter `12` page-one isomorphism for the filtered
    -- global-sections complex, then identify its graded piece with global sections of the
    -- resolved filtration subquotient and finally transport across the derived-unit comparison
    -- and the subquotient quasi-isomorphism induced by `j`.
    -- TODO: first build the comparison
    -- `gr^{p}(filteredGlobalSectionsComplex X J) ≅
    --   ((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    --     (J.subquotient (lt_add_one p).le)`
    -- using the termwise injectivity of `J.subquotient (lt_add_one p).le`, then compose
    -- `FilteredComplex.pageOneIso filteredComplex spectralSequence p q` with the derived-unit
    -- isomorphism on that K-injective subquotient and the quasi-isomorphism coming from
    -- `FilteredComplex.subquotientMap j (lt_add_one p).le`.
    sorry
  · intro n
    -- Proof comment: compare the underlying complex of `filteredComplex` with the underived
    -- global-sections complex of `J.underlying`, apply the K-injective derived-unit
    -- comparison, and transport along the quasi-isomorphism on underlying complexes induced by
    -- `j`.
    -- TODO: normalize `filteredComplex.underlying` to the underived global-sections complex of
    -- `J.underlying`, then apply the K-injective/quasi-isomorphism homology transport helper.
    sorry
  · intro hcontrol
    -- Proof comment: transport the source-facing eventual stage hypercohomology conditions from
    -- `K` to the filtered global-sections replacement `filteredComplex`, then invoke the Chapter
    -- `12.24.13` boundedness and convergence owners.
    -- TODO: show that `hcontrol` implies the Chapter `12` hypotheses
    -- `FilteredComplex.EventualStageCohomologyVanishesAbove filteredComplex` and
    -- `FilteredComplex.EventualStageCohomologyStabilizesBelow filteredComplex`
    -- by comparing stage cohomology through `hjStageQuasiIso`, the K-injective derived-unit
    -- isomorphisms for `J.stage p`, and the naturality of `stageInclusion`.
    sorry

end AlgebraicGeometry.RingedSpace
