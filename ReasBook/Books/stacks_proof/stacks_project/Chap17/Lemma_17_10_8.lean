import Mathlib
import stacks_proof.stacks_project.Chap17.Lemma_17_4_2
import stacks_proof.stacks_project.Chap17.Lemma_17_3_5
import stacks_proof.stacks_project.Chap17.Definition_17_10_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped Topology

noncomputable section

universe u

namespace AlgebraicGeometry

/-
Domain-style sampling for Lemma 17.10.8:
- primary domain: quasi-coherent `\mathcal O_X`-modules and associated module sheaves on open
  subspaces;
- inspected owner declarations:
  `associatedModuleSheaf`,
  `RingedSpace.restrict`,
  `RingedSpace.Hom.pullback`,
  `SheafedSpace.Γ`;
- best owner abstraction: the source-facing existence statement should be expressed directly on the
  restricted ringed space `X.restrict U.isOpenEmbedding`, with owner `associatedModuleSheaf` in its
  identity-map form `𝓕_ M`, rather than through a separate ring-map bridge from `Γ(U, \mathcal O_X)`;
- primitive data: `U`, `x ∈ U`, the open-inclusion morphism `X.ofRestrict U.isOpenEmbedding`, the
  restricted ringed space `X.restrict U.isOpenEmbedding`, and a module `M` over its top-sections
  ring `(X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)`;
- derived API: the neighborhood existence conclusion together with the direct isomorphism witness
  `((X.ofRestrict U.isOpenEmbedding)^*).obj ℱ ≅ 𝓕_ M`.

Source/core/bridge triage:
- `source-facing`: existence of an open neighbourhood on which `ℱ` is associated to a module over
  the ring of sections of that neighbourhood;
- `core/canonical`: `associatedModuleSheaf` on the restricted ringed space and the pullback owner
  `j^*` for `j := X.ofRestrict U.isOpenEmbedding`;
- `bridge/view`: the upstream identification between sections on `U` and global sections of the
  restricted ringed space stays internal and does not belong in the public theorem surface.
-/

section PresentationHelpers

variable {X : RingedSpace.{u}}

/-- Helper for Lemma 17.10.8: the explicit relation morphism of a local presentation, obtained by
composing the chosen relation map with the kernel inclusion of the generator surjection. -/
private noncomputable def presentationRelationMap
    {U : Opens X} {ℱ : RingedSpace.Modules X} (P : (ℱ.over U).Presentation) :
    (SheafOfModules.free.{u} P.relations.I : SheafOfModules (X.ringCatSheaf.over U)) ⟶
      (SheafOfModules.free.{u} P.generators.I : SheafOfModules (X.ringCatSheaf.over U)) :=
  P.relations.π ≫ kernel.ι P.generators.π

/-- Helper for Lemma 17.10.8: the explicit relation morphism indeed composes trivially with the
generator surjection of the chosen presentation. -/
private theorem presentationRelationMap_comp_generators
    {U : Opens X} {ℱ : RingedSpace.Modules X} (P : (ℱ.over U).Presentation) :
    presentationRelationMap P ≫ P.generators.π = 0 := by
  -- Proof comment: the presentation relations land in the kernel of the generator surjection by
  -- construction, so the composite vanishes immediately.
  simp [presentationRelationMap]

/-- Helper for Lemma 17.10.8: the generator surjection of a presentation is a cokernel of the
explicit relation morphism above. -/
private noncomputable def presentationGenerators_isColimit
    {U : Opens X} {ℱ : RingedSpace.Modules X} (P : (ℱ.over U).Presentation) :
    IsColimit (CokernelCofork.ofπ P.generators.π (presentationRelationMap_comp_generators P)) := by
  -- Proof comment: this is exactly the owner-level cokernel structure already packaged by
  -- `P.isColimit`, after rewriting the hidden relation map to the explicit spelling used here.
  simpa [presentationRelationMap] using P.isColimit

/-- Helper for Lemma 17.10.8: the `i`th basis vector in the relation free module of a chosen
presentation. -/
private noncomputable def presentationBasisInclusion
    {U : Opens X} {ℱ : RingedSpace.Modules X} (P : (ℱ.over U).Presentation)
    (i : P.relations.I) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      (SheafOfModules.free.{u} P.relations.I :
        SheafOfModules (X.ringCatSheaf.over U)) :=
  show SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      (SheafOfModules.free.{u} P.relations.I :
        SheafOfModules (X.ringCatSheaf.over U)) from
    @SheafOfModules.ιFree _ _ _ (X.ringCatSheaf.over U) _ _ _ P.relations.I i

/-- Helper for Lemma 17.10.8: the `i`th basis relation of a chosen presentation, viewed as a
unit-to-generator morphism. -/
private noncomputable def presentationBasisRelation
    {U : Opens X} {ℱ : RingedSpace.Modules X} (P : (ℱ.over U).Presentation)
    (i : P.relations.I) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      (SheafOfModules.free.{u} P.generators.I :
        SheafOfModules (X.ringCatSheaf.over U)) :=
  -- Proof comment: isolate one relation basis vector first, then apply the full relation map.
  presentationBasisInclusion P i ≫ presentationRelationMap P

/-- Helper for Lemma 17.10.8: each basis relation separately composes trivially with the generator
surjection. -/
private theorem presentationBasisRelation_comp_generators
    {U : Opens X} {ℱ : RingedSpace.Modules X} (P : (ℱ.over U).Presentation)
    (i : P.relations.I) :
    presentationBasisRelation P i ≫ P.generators.π = 0 := by
  -- Proof comment: precompose the vanishing of the full relation map with the chosen basis
  -- inclusion of the relation free module.
  simpa [presentationBasisRelation, presentationBasisInclusion, Category.assoc] using
    congrArg (fun f ↦ presentationBasisInclusion P i ≫ f)
      (presentationRelationMap_comp_generators P)

/-- Helper for Lemma 17.10.8: a morphism out of the generator free sheaf kills the full relation
map exactly when it kills every basis relation separately. -/
private theorem presentationRelationMap_comp_eq_zero_iff_basisRelations
    {U : Opens X} {ℱ : RingedSpace.Modules X} (P : (ℱ.over U).Presentation)
    {J : Type u}
    (A :
      (SheafOfModules.free.{u} P.generators.I :
        SheafOfModules (X.ringCatSheaf.over U)) ⟶
        (SheafOfModules.free.{u} J :
          SheafOfModules (X.ringCatSheaf.over U))) :
    presentationRelationMap P ≫ A = 0 ↔
      ∀ i : P.relations.I, presentationBasisRelation P i ≫ A = 0 := by
  constructor
  · intro h i
    -- Proof comment: precomposing the full relation vanishing with the `i`th basis inclusion
    -- isolates the corresponding basis relation.
    simpa [presentationBasisRelation, Category.assoc] using
      congrArg (fun f ↦ presentationBasisInclusion P i ≫ f) h
  · intro hbasis
    -- Proof comment: morphisms from the relation free sheaf are determined by their values on the
    -- free basis, so basiswise vanishing reconstructs vanishing of the full relation map.
    apply ((SheafOfModules.free.{u} J :
      SheafOfModules (X.ringCatSheaf.over U)).freeHomEquiv).injective
    ext i
    have hi :=
      congrArg
        (SheafOfModules.unitHomEquiv
          (SheafOfModules.free.{u} J :
            SheafOfModules (X.ringCatSheaf.over U)))
        (hbasis i)
    simpa [presentationBasisRelation, presentationBasisInclusion, Category.assoc,
      SheafOfModules.freeHomEquiv_apply] using hi

/-- Helper for Lemma 17.10.8: a presentation on `ℱ.over U` restricts to any smaller open
`V : Over U` after transporting along the canonical equivalence between the iterated slice and the
ordinary slice over `V.left`. -/
private noncomputable def presentationRestrict
    {U : Opens X} {ℱ : RingedSpace.Modules X}
    (P : (ℱ.over U).Presentation) (V : Over U) :
    (ℱ.over V.left).Presentation := by
  let F :=
    ringedSiteLocalizedRestriction
      (J := (Opens.grothendieckTopology X).over U) (𝒪 := X.sheaf.over U) V
  letI : PreservesColimitsOfSize.{u, u}
      F := (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf.over U) V)
      .leftAdjoint_preservesColimits
  -- Proof comment: map the presentation along the localized restriction functor; on the ambient
  -- opens site this functor is exactly restriction from `U` to the smaller open `V.left`.
  simpa [F, SheafOfModules.over, ringedSiteLocalizedRestriction] using P.map F (by rfl)

end PresentationHelpers

section RestrictedNeighborhoodHelpers

variable {X : RingedSpace.{u}}

/-- Helper for Lemma 17.10.8: the opens functor induced by restricting to `U` is final, which is
the instance required by `SheafOfModules.pullbackObjFreeIso` on the restricted ringed space. -/
private instance opensMapOfRestrictFinal (U : Opens X) :
    Functor.Final (Opens.map (X.ofRestrict U.isOpenEmbedding).hom.base) := by
  -- Proof comment: the inclusion of an open subset is an open map, and finality follows from the
  -- standard adjunction between direct and inverse image on opens.
  let hU : IsOpenMap U.inclusion' := U.isOpenEmbedding.isOpenMap
  simpa using
    (CategoryTheory.Functor.final_of_adjunction hU.adjunction :
      Functor.Final (Opens.map U.inclusion'))

/-- Helper for Lemma 17.10.8: the restricted ringed space on the chosen open neighborhood. -/
private abbrev restrictedRingedSpace (U : Opens X) : RingedSpace.{u} :=
  X.restrict U.isOpenEmbedding

/-- Helper for Lemma 17.10.8: the structure sheaf of the restricted ringed space on `U`. -/
private abbrev restrictedRingCatSheaf (U : Opens X) :=
  RingedSpace.ringCatSheaf (restrictedRingedSpace U)

/-- Helper for Lemma 17.10.8: the global-sections ring on the restricted ringed space `X|_U`. -/
private abbrev restrictedGlobalSectionsRing (U : Opens X) :=
  (restrictedRingedSpace U).presheaf.obj (op ⊤)

/-- Helper for Lemma 17.10.8: the free `Γ(U, \mathcal O_U)`-module on the basis `I`. -/
private abbrev restrictedGlobalSectionsFreeModule (U : Opens X) (I : Type u) :
    ModuleCat (restrictedGlobalSectionsRing U) :=
  ModuleCat.of (restrictedGlobalSectionsRing U) (I →₀ restrictedGlobalSectionsRing U)

/-- Helper for Lemma 17.10.8: the unique morphism from the top open of `X|_U` to a chosen open
of `X|_U`. -/
private abbrev topToRestrictedOpen (U : Opens X)
    (V : (Opens (restrictedRingedSpace U))ᵒᵖ) :
    op (⊤ : Opens (restrictedRingedSpace U)) ⟶ V :=
  (homOfLE (show unop V ≤ (⊤ : Opens (restrictedRingedSpace U)) from by
    intro x hx
    trivial)).op

/-- Helper for Lemma 17.10.8: a global section of `\mathcal O_U` determines the corresponding
global section of the unit module on `X|_U`. -/
private noncomputable def unitSectionOfGlobalSectionsOnNeighborhood
    (U : Opens X) (r : restrictedGlobalSectionsRing U) :
    (SheafOfModules.unit (restrictedRingCatSheaf U)).sections :=
  PresheafOfModules.sectionsMk
    (fun V ↦ ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U V)).hom r)
    (by
      intro V W f
      change (CommRingCat.Hom.hom ((restrictedRingedSpace U).presheaf.map f))
          ((CommRingCat.Hom.hom
              ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U V))) r) =
        (CommRingCat.Hom.hom
            ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U W))) r
      have htop : topToRestrictedOpen U W = topToRestrictedOpen U V ≫ f := Subsingleton.elim _ _
      have hcomp :
          (CommRingCat.Hom.hom
              ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U W))) r =
            (CommRingCat.Hom.hom ((restrictedRingedSpace U).presheaf.map f))
              ((CommRingCat.Hom.hom
                  ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U V))) r) := by
        have hmapComp :=
          (restrictedRingedSpace U).presheaf.map_comp (topToRestrictedOpen U V) f
        have hmap := congrArg (fun g ↦ g r) (congrArg CommRingCat.Hom.hom hmapComp)
        simpa [htop] using hmap
      exact hcomp.symm)

/-- Helper for Lemma 17.10.8: a finitely supported family of coefficients in `Γ(U, \mathcal O_U)`
determines the corresponding global section of the free sheaf on `X|_U`. -/
private noncomputable def freeSectionOfGlobalSectionsFinsuppOnNeighborhood
    (U : Opens X) {J : Type u} (a : J →₀ restrictedGlobalSectionsRing U) :
    (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules).sections :=
  (SheafOfModules.unitHomEquiv
      (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules))
    (a.sum fun j r ↦
      (SheafOfModules.unitHomEquiv
          (SheafOfModules.unit (restrictedRingCatSheaf U))).symm
        (unitSectionOfGlobalSectionsOnNeighborhood U r) ≫
          (show SheafOfModules.unit (restrictedRingCatSheaf U) ⟶
              (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules)
            from @SheafOfModules.ιFree _ _ _ (restrictedRingCatSheaf U) _ _ _ J j))

/-- Helper for Lemma 17.10.8: a morphism of free `Γ(U, \mathcal O_U)`-modules induces the
corresponding morphism of free sheaves on the restricted ringed space `X|_U`. -/
private noncomputable def freeSheafMapOnNeighborhood
    (U : Opens X) {I J : Type u}
    (ψ : restrictedGlobalSectionsFreeModule U I ⟶ restrictedGlobalSectionsFreeModule U J) :
    (SheafOfModules.free.{u} I : (restrictedRingedSpace U).Modules) ⟶
      (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules) :=
  (SheafOfModules.freeHomEquiv
      (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules)).symm
    (fun i ↦
      freeSectionOfGlobalSectionsFinsuppOnNeighborhood U ((ψ.hom) (Finsupp.single i 1)))

/-- Helper for Lemma 17.10.8: the free-sheaf morphism induced from a
`Γ(U, \mathcal O_U)`-linear map sends the `i`th free basis section to the corresponding column
section. -/
private theorem freeSheafMapOnNeighborhood_freeSection
    (U : Opens X) {I J : Type u}
    (ψ : restrictedGlobalSectionsFreeModule U I ⟶ restrictedGlobalSectionsFreeModule U J)
    (i : I) :
    SheafOfModules.sectionsMap (freeSheafMapOnNeighborhood U ψ)
        (SheafOfModules.freeSection (R := restrictedRingCatSheaf U) i) =
      freeSectionOfGlobalSectionsFinsuppOnNeighborhood U ((ψ.hom) (Finsupp.single i 1)) := by
  -- Proof comment: this is the defining basis-vector computation built into
  -- `sectionsMap_freeHomEquiv_symm_freeSection`.
  simpa [freeSheafMapOnNeighborhood] using
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (R := restrictedRingCatSheaf U)
      (f := fun j ↦
        freeSectionOfGlobalSectionsFinsuppOnNeighborhood U ((ψ.hom) (Finsupp.single j 1)))
      i)

/-- Helper for Lemma 17.10.8: two morphisms out of a free sheaf on `X|_U` agree once they agree
on every free basis section. -/
private theorem restrictedModuleHom_eq_of_freeSection_eq
    (U : Opens X) {I : Type u} {M : (restrictedRingedSpace U).Modules}
    {f g : (SheafOfModules.free.{u} I : (restrictedRingedSpace U).Modules) ⟶ M}
    (hfg : ∀ i : I,
      SheafOfModules.sectionsMap f
          (SheafOfModules.freeSection (R := restrictedRingCatSheaf U) i) =
        SheafOfModules.sectionsMap g
          (SheafOfModules.freeSection (R := restrictedRingCatSheaf U) i)) :
    f = g := by
  -- Proof comment: the free-Hom equivalence identifies a morphism out of the free sheaf with its
  -- values on the free basis.
  apply (SheafOfModules.freeHomEquiv M).injective
  funext i
  rw [SheafOfModules.freeHomEquiv_apply, SheafOfModules.freeHomEquiv_apply]
  exact hfg i

/-- Helper for Lemma 17.10.8: transport the free-sheaf morphism induced by a
`Γ(U, \mathcal O_U)`-linear map back to the restriction `j^*` from `X` to `X|_U`. -/
private noncomputable def restrictedFreeSheafMapOnNeighborhood
    (U : Opens X) {I J : Type u}
    (ψ : restrictedGlobalSectionsFreeModule U I ⟶ restrictedGlobalSectionsFreeModule U J) :
    ((RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding)).obj
        (SheafOfModules.free.{u} I : X.Modules)) ⟶
      ((RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding)).obj
        (SheafOfModules.free.{u} J : X.Modules)) :=
  let eI :
      ((RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding)).obj
          (SheafOfModules.free.{u} I : X.Modules)) ≅
        (SheafOfModules.free.{u} I : (restrictedRingedSpace U).Modules) :=
    SheafOfModules.pullbackObjFreeIso
      (RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding)) I
  let eJ :
      ((RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding)).obj
          (SheafOfModules.free.{u} J : X.Modules)) ≅
        (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules) :=
    SheafOfModules.pullbackObjFreeIso
      (RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding)) J
  let m :
      (SheafOfModules.free.{u} I : (restrictedRingedSpace U).Modules) ⟶
        (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules) :=
    freeSheafMapOnNeighborhood U ψ
  eI.hom ≫ m ≫ eJ.inv

/-- Helper for Lemma 17.10.8: the stalk of each basis relation of the restricted presentation is
already a finite linear combination of free basis germs on the restricted ringed space. -/
private theorem presentationBasisRelation_stalkFactorsThroughFiniteFamily
    {U : Opens X} {ℱ : RingedSpace.Modules X} (P : (ℱ.over U).Presentation)
    (i : P.relations.I) (y : restrictedRingedSpace U) :
    ∃ (J : Type u) (_ : Finite J) (ι : J → P.generators.I)
      (a : J →₀ (restrictedRingedSpace U).presheaf.stalk y),
        TopCat.Presheaf.germ
            (SheafOfModules.free.{u} P.generators.I :
              (restrictedRingedSpace U).Modules).val.presheaf
            (⊤ : Opens (restrictedRingedSpace U)) y (by trivial)
            ((SheafOfModules.unitHomEquiv
                (SheafOfModules.free.{u} P.generators.I :
                  (restrictedRingedSpace U).Modules))
              (show SheafOfModules.unit (restrictedRingCatSheaf U) ⟶
                  (SheafOfModules.free.{u} P.generators.I :
                    (restrictedRingedSpace U).Modules) from
                presentationBasisRelation P i)) =
          a.sum fun j r ↦
            r • Γgerm
              (SheafOfModules.free.{u} P.generators.I :
                (restrictedRingedSpace U).Modules).val.presheaf y
              ((SheafOfModules.freeSection (R := restrictedRingCatSheaf U) (ι j)).1 (op ⊤)) := by
  classical
  let ρi :
      (SheafOfModules.free.{u} P.generators.I :
        (restrictedRingedSpace U).Modules).sections :=
    (SheafOfModules.unitHomEquiv
      (SheafOfModules.free.{u} P.generators.I :
        (restrictedRingedSpace U).Modules))
      (show SheafOfModules.unit (restrictedRingCatSheaf U) ⟶
          (SheafOfModules.free.{u} P.generators.I :
            (restrictedRingedSpace U).Modules) from
        presentationBasisRelation P i)
  have hspan :
      TopCat.Presheaf.germ
          (SheafOfModules.free.{u} P.generators.I :
            (restrictedRingedSpace U).Modules).val.presheaf
          (⊤ : Opens (restrictedRingedSpace U)) y (by trivial) ρi ∈
        Submodule.span ((restrictedRingedSpace U).presheaf.stalk y)
          (Set.range fun j ↦
            Γgerm
              (SheafOfModules.free.{u} P.generators.I :
                (restrictedRingedSpace U).Modules).val.presheaf y
              ((SheafOfModules.freeSection (R := restrictedRingCatSheaf U) j).1 (op ⊤))) := by
    -- Proof comment: after moving to the restricted ringed space, the earlier free-stalk span
    -- lemma applies directly to the global section determined by the chosen basis relation.
    simpa [ρi] using
      free_germ_mem_span_freeSection_germs
        (X := restrictedRingedSpace U) (I := P.generators.I) y
        (⊤ : Opens (restrictedRingedSpace U)) (by trivial) ρi
  obtain ⟨T, hTsub, hTmem⟩ := Submodule.mem_span_finite_of_mem_span hspan
  have hTmem' :
      TopCat.Presheaf.germ
          (SheafOfModules.free.{u} P.generators.I :
            (restrictedRingedSpace U).Modules).val.presheaf
          (⊤ : Opens (restrictedRingedSpace U)) y (by trivial) ρi ∈
        Submodule.span ((restrictedRingedSpace U).presheaf.stalk y)
          (Set.range fun t : T ↦
            (t :
              RingedSpace.stalkModuleCat
                (SheafOfModules.free.{u} P.generators.I :
                  (restrictedRingedSpace U).Modules) y)) := by
    -- Proof comment: shrink the ambient spanning family to the finite subfamily extracted above.
    simpa using hTmem
  obtain ⟨a, ha⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hTmem'
  let ι : T → P.generators.I := fun t ↦ Classical.choose (hTsub t.2)
  have hι :
      ∀ t : T,
        (t :
          RingedSpace.stalkModuleCat
            (SheafOfModules.free.{u} P.generators.I :
              (restrictedRingedSpace U).Modules) y) =
          Γgerm
            (SheafOfModules.free.{u} P.generators.I :
              (restrictedRingedSpace U).Modules).val.presheaf y
            ((SheafOfModules.freeSection (R := restrictedRingCatSheaf U) (ι t)).1 (op ⊤)) := by
    intro t
    exact Classical.choose_spec (hTsub t.2)
  refine ⟨T, inferInstance, ι, a, ?_⟩
  -- Proof comment: reindex the finite stalk combination by the chosen generating indices.
  simpa [ρi, hι] using ha

end RestrictedNeighborhoodHelpers

section CompactRestrictedPresentationHelper

variable {X : RingedSpace.{u}}

/-- Helper for Lemma 17.10.8: once the quasi-coherent presentation has been restricted to an open
`U` contained in a compact neighborhood `K`, the remaining compact-support argument should produce
an associated-module-sheaf description on `X|_U`. -/
-- TODO: the remaining proof must implement the compact gluing step from Agent C's plan. For each
-- basis relation of `P_U`, first build a global finite-free section on `restrictedRingedSpace U`
-- by gluing the local finite-subfree lifts obtained from
-- `presentationBasisRelation_stalkFactorsThroughFiniteFamily`; only afterwards convert that global
-- finite-free section into a finitely supported `Γ(U)`-column and finish by cokernel comparison.
private theorem exists_associatedModuleSheaf_of_compactRestrictedPresentation
    {ℱ : RingedSpace.Modules X}
    (U : Opens X) (K : Set X) (hUK : (U : Set X) ⊆ K) (hKcompact : IsCompact K)
    (P_U : (ℱ.over U).Presentation) :
    ∃ (M : ModuleCat (restrictedGlobalSectionsRing U)),
      Nonempty
        (((RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ) ≅
          𝓕_ M) := sorry

end CompactRestrictedPresentationHelper

-- Proof sketch: choose a quasi-compact neighbourhood basis element around `x`, shrink to an open
-- neighbourhood on which the local cokernel presentation of the quasi-coherent sheaf `ℱ` is given
-- by a genuine matrix of sections over that open, and then invoke the associated-module-sheaf
-- construction on the restricted ringed space.
/-- Lemma 17.10.8: if `x` has a neighbourhood basis consisting of quasi-compact neighbourhoods,
then every quasi-coherent `\mathcal O_X`-module becomes on some open neighbourhood of `x`
via an isomorphism to a module sheaf associated to a module over the ring of sections on that
neighbourhood. -/
@[stacks 01BK]
theorem exists_open_neighborhood_associatedGlobalSectionsModuleSheaf_of_isQuasicoherent
    {X : RingedSpace.{u}} (x : X)
    (hx : (𝓝 x).HasBasis (fun K : Set X ↦ K ∈ 𝓝 x ∧ IsCompact K) id)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ∃ (U : Opens X) (_ : x ∈ U)
      (M : ModuleCat ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))),
        Nonempty
          (((RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ) ≅
            𝓕_ M) := by
  let q : ℱ.QuasicoherentData := (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
    (M := ℱ)).some
  -- Proof comment: the owner-level quasi-coherent data already gives a cover by opens equipped
  -- with local presentations, so the first step is to choose one cover member containing `x`.
  obtain ⟨V, _iV, hmem, hxV⟩ := q.coversTop ⊤ x (by trivial)
  obtain ⟨j, ⟨f⟩⟩ := hmem
  let U₀ : Opens X := q.X j
  let P : (ℱ.over U₀).Presentation := q.presentation j
  have hP :
      IsColimit (CokernelCofork.ofπ P.generators.π (presentationRelationMap_comp_generators P)) :=
    presentationGenerators_isColimit P
  have hxU₀ : x ∈ U₀ := f.le hxV
  obtain ⟨K, hKbasis, hKU₀⟩ := hx.mem_iff.mp (U₀.isOpen.mem_nhds hxU₀)
  rcases hKbasis with ⟨hKnhds, hKcompact⟩
  obtain ⟨W, hWK, hWOpen, hxW⟩ := mem_nhds_iff.mp hKnhds
  let U : Opens X := ⟨W, hWOpen⟩
  have hxU : x ∈ U := hxW
  have hUK : (U : Set X) ⊆ K := hWK
  have hUU₀ : U ≤ U₀ := by
    intro y hy
    exact hKU₀ (hUK hy)
  -- Route correction: the previous attempt tried to compare the presentation on `U₀` directly to
  -- a `Γ(U₀)`-module presentation, but the source proof needs the compact-neighborhood shrink from
  -- `hx` before the relation columns become finitely supported.
  -- Proof comment: the quasi-coherent presentation is now reduced to a smaller open
  -- `U ⊆ K ⊆ U₀` around `x`; the remaining work is to turn each basis relation
  -- of the restricted presentation into finitely supported coefficients over `Γ(U, 𝒪_U)`.
  let VU : Over U₀ := Over.mk (homOfLE hUU₀)
  let P_U : (ℱ.over U).Presentation := presentationRestrict P VU
  have hP_U :
      IsColimit
        (CokernelCofork.ofπ P_U.generators.π (presentationRelationMap_comp_generators P_U)) :=
    presentationGenerators_isColimit P_U
  let _ := hKcompact
  let _ := hP
  let _ := hP_U
  let _ := hUU₀
  let _ := hxU
  let _ := f
  -- Proof comment: the neighborhood-selection prefix is complete. The only remaining work is the
  -- compact gluing step for the restricted presentation `P_U`, which is now isolated in the
  -- dedicated helper above.
  exact
    exists_associatedModuleSheaf_of_compactRestrictedPresentation
      U K hUK hKcompact P_U

end AlgebraicGeometry
