import Mathlib
import StacksProject_2024.stacks_project.Chap18.Definition_18_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u₁ u₂ v₁ v₂ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : C ⥤ D} [Functor.IsContinuous F J K]
variable {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify K AddCommGrpCat.{u}]
variable [HasSheafify K AddCommGrpCat.{u}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
variable [(pushforward φ).IsRightAdjoint]
variable [IsIso (pullbackObjUnitToUnit φ)]

local notation "fStar" => pullback φ

/-- Helper for Lemma 18.17.2: pullback carries the free sheaf on `I` to the free sheaf on the
same index type by preserving the coproduct cocone and transporting the pulled-back unit sheaf
along `pullbackObjUnitToUnit`. -/
private noncomputable def pullbackFreeIsoOfUnitIso (I : Type u) :
    ((pullback φ).obj (free I : SheafOfModules S)) ≅ (free I : SheafOfModules R) := by
  -- Proof comment: compare the mapped free cocone with the standard free cocone after replacing
  -- each pulled-back unit summand by the target unit sheaf.
  let η : (pullback φ).obj (unit S) ≅ unit R := asIso (pullbackObjUnitToUnit φ)
  let α : (Discrete.functor fun _ : I ↦ unit R) ≅
      ((Discrete.functor fun _ : I ↦ unit S) ⋙ pullback φ) :=
    NatIso.ofComponents (fun _ ↦ η.symm) (by
      intro j j' f
      simp [Discrete.functor])
  have hmap : IsColimit (Functor.mapCocone (pullback φ) (freeCofan (R := S) I)) := by
    -- Pullback is a left adjoint, so it preserves the coproduct colimit defining the free sheaf.
    let _ : PreservesColimitsOfShape (Discrete I) (pullback φ) := inferInstance
    exact isColimitOfPreserves (pullback φ) (isColimitFreeCofan (R := S) I)
  let c : Cofan (fun _ : I ↦ unit R) :=
    (Cocone.precompose α.hom).obj (Functor.mapCocone (pullback φ) (freeCofan (R := S) I))
  have hc : IsColimit c := by
    -- Transport the colimit statement across the constant-diagram isomorphism `α`.
    exact (IsColimit.precomposeHomEquiv α
      (Functor.mapCocone (pullback φ) (freeCofan (R := S) I))).symm hmap
  exact IsColimit.coconePointUniqueUpToIso hc (isColimitFreeCofan (R := R) I)

/-- Helper for Lemma 18.17.2: a chosen generating family on `ℱ` induces an epimorphism from the
free sheaf on the same index type to the pullback of `ℱ`. -/
private noncomputable def pullbackGeneratorsMap {ℱ : SheafOfModules S}
    (σ : ℱ.GeneratingSections) :
    (free σ.I : SheafOfModules R) ⟶ (pullback φ).obj ℱ :=
  (pullbackFreeIsoOfUnitIso (φ := φ) σ.I).inv ≫ (pullback φ).map σ.π

/-- Helper for Lemma 18.17.2: the transported free-source map remains epimorphic after pullback. -/
private theorem pullbackGeneratorsMap_epi {ℱ : SheafOfModules S}
    (σ : ℱ.GeneratingSections) :
    Epi (pullbackGeneratorsMap (φ := φ) σ) := by
  -- Proof comment: both the free-source normalization isomorphism and the mapped generating map
  -- are epimorphisms, so their composite is epi.
  let _ : Epi ((pullback φ).map σ.π) := by
    infer_instance
  let _ : Epi (pullbackFreeIsoOfUnitIso (φ := φ) σ.I).inv := by
    infer_instance
  dsimp [pullbackGeneratorsMap]
  infer_instance

/-- Helper for Lemma 18.17.2: the pulled-back epimorphism defines generating global sections on
the pullback module. -/
private noncomputable def pullbackGeneratorsSections {ℱ : SheafOfModules S}
    (σ : ℱ.GeneratingSections) :
    ((pullback φ).obj ℱ).GeneratingSections :=
  { I := σ.I
    s := ((pullback φ).obj ℱ).freeHomEquiv (pullbackGeneratorsMap (φ := φ) σ)
    epi := by
      -- Proof comment: by construction the associated free map is exactly the transported epi.
      simpa using pullbackGeneratorsMap_epi (φ := φ) σ }

-- Proof sketch: choose an isomorphism from `ℱ` to a free sheaf `free I`; apply the pullback
-- functor, use that it preserves coproducts because it is a left adjoint, and identify the
-- pullback of `unit S` with `unit R` via `pullbackObjUnitToUnit φ`.
/-- Lemma 18.17.2 (1): if an `\mathcal O_\mathcal D`-module is free, then its pullback along a
morphism of ringed topoi is free. -/
instance pullback_isFree (ℱ : SheafOfModules S) [IsFree ℱ] :
    IsFree ((fStar).obj ℱ) := by
  -- Proof comment: transport a chosen free model of `ℱ` through pullback and then normalize the
  -- pulled-back free sheaf back to the standard free sheaf on the same basis.
  obtain ⟨I, ⟨e⟩⟩ := IsFree.exists_iso_free (ℱ := ℱ)
  exact ⟨I, ⟨(pullback φ).mapIso e ≪≫ pullbackFreeIsoOfUnitIso (φ := φ) I⟩⟩

-- Proof sketch: write `ℱ` as a free sheaf on a finite index type, pull back that free
-- presentation, and use the same argument as in the free case together with finiteness of the
-- indexing type.
/-- Lemma 18.17.2 (2): if an `\mathcal O_\mathcal D`-module is finite free, then its pullback
along a morphism of ringed topoi is finite free. -/
instance pullback_isFiniteFree (ℱ : SheafOfModules S) [IsFiniteFree ℱ] :
    IsFiniteFree ((fStar).obj ℱ) := by
  -- Proof comment: keep the same finite basis after applying the free-sheaf pullback comparison.
  obtain ⟨I, hI, ⟨e⟩⟩ := IsFiniteFree.exists_iso_free (ℱ := ℱ)
  exact ⟨I, hI, ⟨(pullback φ).mapIso e ≪≫ pullbackFreeIsoOfUnitIso (φ := φ) I⟩⟩

-- Proof sketch: a generating family of global sections gives an epimorphism from a free sheaf;
-- pull back that epimorphism, use preservation of colimits/right exactness, and transport the
-- free source along the canonical identification of pullback of a free sheaf with a free sheaf.
/-- Lemma 18.17.2 (3): if an `\mathcal O_\mathcal D`-module is generated by global sections, then
its pullback along a morphism of ringed topoi is generated by global sections. -/
instance pullback_isGloballyGenerated (ℱ : SheafOfModules S)
    [Nonempty ℱ.GeneratingSections] :
    Nonempty (((fStar).obj ℱ).GeneratingSections) := by
  classical
  -- Proof comment: a chosen generating epimorphism out of a free sheaf stays epi after pullback,
  -- so it supplies generators on the pullback target.
  rcases (inferInstance : Nonempty ℱ.GeneratingSections) with ⟨σ⟩
  exact ⟨pullbackGeneratorsSections (φ := φ) σ⟩

/-
Proof sketch: start from an epimorphism `\mathcal O_\mathcal D^{\oplus r} \to \mathcal F`, pull
it back, and identify the pullback of `\mathcal O_\mathcal D^{\oplus r}` with
`\mathcal O_\mathcal C^{\oplus r}`.
-/
/-- Lemma 18.17.2 (4): if an `\mathcal O_\mathcal D`-module is generated by `r` global sections,
then its pullback along a morphism of ringed topoi is generated by `r` global sections. -/
instance pullback_isGeneratedBy (ℱ : SheafOfModules S) (r : ℕ)
    [IsGeneratedBy ℱ r] :
    IsGeneratedBy ((fStar).obj ℱ) r := by
  -- Proof comment: transport the chosen epimorphism `\mathcal O^{\oplus r} → ℱ` through pullback
  -- and normalize the pulled-back source back to `\mathcal O^{\oplus r}`.
  rcases IsGeneratedBy.exists_epi (ℱ := ℱ) (r := r) with ⟨π, hπ⟩
  let π' : (free (ULift.{u} (Fin r)) : SheafOfModules R) ⟶ (pullback φ).obj ℱ :=
    (pullbackFreeIsoOfUnitIso (φ := φ) (ULift.{u} (Fin r))).inv ≫ (pullback φ).map π
  have hπ' : Epi π' := by
    let _ : Epi ((pullback φ).map π) := by
      infer_instance
    let _ : Epi (pullbackFreeIsoOfUnitIso (φ := φ) (ULift.{u} (Fin r))).inv := by
      infer_instance
    dsimp [π']
    infer_instance
  exact ⟨π', hπ'⟩

-- Proof sketch: choose `r` with `ℱ` generated by `r` global sections, then apply the previous
-- rank-`r` pullback result.
/-- Lemma 18.17.2 (5): if an `\mathcal O_\mathcal D`-module is generated by finitely many global
sections, then its pullback along a morphism of ringed topoi is again finitely globally
generated. -/
instance pullback_isFiniteGloballyGenerated (ℱ : SheafOfModules S)
    [IsFiniteGloballyGenerated ℱ] :
    IsFiniteGloballyGenerated ((fStar).obj ℱ) := by
  -- Proof comment: reuse the same finite number of generators produced by the source witness and
  -- apply the fixed-rank pullback statement.
  obtain ⟨r, hr⟩ := IsFiniteGloballyGenerated.exists_num (ℱ := ℱ)
  let _ : IsGeneratedBy ℱ r := hr
  let h' : IsGeneratedBy ((pullback φ).obj ℱ) r := by
    exact pullback_isGeneratedBy (φ := φ) ℱ r
  exact ⟨⟨r, h'⟩⟩

/-- Helper for Lemma 18.17.2: a presentation gives an explicit relation map between the two free
sheaves indexed by the chosen relations and generators. -/
private noncomputable def presentationRelationMap {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    (free P.relations.I : SheafOfModules S) ⟶ (free P.generators.I : SheafOfModules S) :=
  P.relations.π ≫ kernel.ι P.generators.π

/-- Helper for Lemma 18.17.2: the explicit relation map lands in the kernel of the generator
epimorphism. -/
private theorem presentationRelationMap_comp_generators {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    presentationRelationMap P ≫ P.generators.π = 0 := by
  -- Proof comment: the relation morphism factors through `kernel.ι P.generators.π` by definition.
  simp [presentationRelationMap]

/-- Helper for Lemma 18.17.2: the pulled-back relation morphism is the transport of the source
relation map between the normalized pulled-back free sheaves. -/
private noncomputable def pullbackPresentationRelations {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    (free P.relations.I : SheafOfModules R) ⟶ (free P.generators.I : SheafOfModules R) :=
  (pullbackFreeIsoOfUnitIso (φ := φ) P.relations.I).inv ≫
    (pullback φ).map (presentationRelationMap P) ≫
      (pullbackFreeIsoOfUnitIso (φ := φ) P.generators.I).hom

/-- Helper for Lemma 18.17.2: the pulled-back generator morphism is the transport of the source
generator epimorphism to the normalized pulled-back free sheaf. -/
private noncomputable def pullbackPresentationGenerators {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    (free P.generators.I : SheafOfModules R) ⟶ (pullback φ).obj ℱ :=
  (pullbackFreeIsoOfUnitIso (φ := φ) P.generators.I).inv ≫
    (pullback φ).map P.generators.π

/-- Helper for Lemma 18.17.2: the normalized pulled-back relation map still kills the normalized
pulled-back generator map. -/
private theorem pullbackPresentationRelations_mapGenerators {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    pullbackPresentationRelations (φ := φ) P ≫
      pullbackPresentationGenerators (φ := φ) P = 0 := by
  -- Proof comment: cancel the generator-side free-sheaf isomorphism and reduce to the mapped
  -- source relation complex.
  simpa [pullbackPresentationRelations, pullbackPresentationGenerators, presentationRelationMap,
    Category.assoc, ← Functor.map_comp] using
    congrArg ((pullback φ).map) (presentationRelationMap_comp_generators (P := P))

/-- Helper for Lemma 18.17.2: the normalized pulled-back generator morphism is epimorphic. -/
private theorem pullbackPresentationGenerators_epi {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    Epi (pullbackPresentationGenerators (φ := φ) P) := by
  -- Proof comment: the source presentation generator is epi, and pullback preserves epis because
  -- it is a left adjoint between these sheaf categories.
  let _ : Epi ((pullback φ).map P.generators.π) := by
    infer_instance
  let _ : Epi (pullbackFreeIsoOfUnitIso (φ := φ) P.generators.I).inv := by
    infer_instance
  dsimp [pullbackPresentationGenerators]
  infer_instance

/-- Helper for Lemma 18.17.2: the generating family used in the pulled-back presentation is the
transport of the source generators along pullback. -/
private noncomputable def pullbackPresentationGeneratorSections {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    ((pullback φ).obj ℱ).GeneratingSections :=
  pullbackGeneratorsSections (φ := φ) P.generators

/-- Helper for Lemma 18.17.2: the mapped relation map still kills the mapped generator map. -/
private theorem mappedPresentationRelationMap_comp_generators {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    (pullback φ).map (presentationRelationMap P) ≫
      (pullback φ).map P.generators.π = 0 := by
  -- Proof comment: this is the mapped source relation complex.
  simpa [Category.assoc, ← Functor.map_comp] using
    congrArg ((pullback φ).map) (presentationRelationMap_comp_generators (P := P))

/-- Helper for Lemma 18.17.2: the chosen generators of a presentation already exhibit the target
as the cokernel of the explicit relation map. -/
private noncomputable def presentationGeneratorsCofork {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    CokernelCofork (presentationRelationMap P) :=
  CokernelCofork.ofπ P.generators.π
    (presentationRelationMap_comp_generators (P := P))

/-- Helper for Lemma 18.17.2: the chosen generators of a presentation already exhibit the target
as the cokernel of the explicit relation map. -/
private noncomputable def presentationGenerators_isCokernel {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    IsColimit
      (CokernelCofork.ofπ P.generators.π
        (presentationRelationMap_comp_generators (P := P))) := by
  classical
  exact sorry

/-- Helper for Lemma 18.17.2: mapping a parallel-pair diagram through pullback gives the
parallel-pair diagram of the mapped morphism. -/
private noncomputable def mappedParallelPairZeroIso {A B : SheafOfModules S}
    (f : A ⟶ B) :
    parallelPair f 0 ⋙ pullback φ ≅ parallelPair ((pullback φ).map f) 0 := by
  -- Proof comment: both mapped diagrams have the same objects, and their two arrows are the
  -- mapped morphism and the preserved zero morphism.
  refine NatIso.ofComponents (fun j ↦ by cases j <;> exact Iso.refl _) (by
    rintro _ _ (_ | _ | _)
    · rfl
    · simpa using (Functor.map_zero (pullback φ) : (pullback φ).map (0 : A ⟶ B) = 0)
    · simp)

/-- Helper for Lemma 18.17.2: placeholder for the diagram-spelling comparison between the mapped
source cokernel and the explicit mapped cokernel. -/
private theorem mappedPresentationCoforkIso {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) : True := by
  trivial

/-- Helper for Lemma 18.17.2: pullback preserves the explicit cokernel presentation attached to a
chosen source presentation. -/
private noncomputable def mappedPresentationGenerators_isCokernel {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    IsColimit
      (CokernelCofork.ofπ ((pullback φ).map P.generators.π)
        (mappedPresentationRelationMap_comp_generators (φ := φ) P)) := by
  classical
  exact sorry

/-- Helper for Lemma 18.17.2: transporting the mapped cokernel along the free-sheaf comparison
isomorphisms gives a normalized cokernel presentation over the target structure sheaf. -/
private noncomputable def pullbackPresentationGenerators_isCokernel {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    IsColimit
      (CokernelCofork.ofπ (pullbackPresentationGenerators (φ := φ) P)
        (pullbackPresentationRelations_mapGenerators (φ := φ) P)) := by
  classical
  exact sorry

/-- Helper for Lemma 18.17.2: pulling back the explicit free presentation and normalizing both free
terms gives a presentation of the pullback module. -/
private noncomputable def pullbackPresentationOfPresentation {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) :
    ((pullback φ).obj ℱ).Presentation :=
  SheafOfModules.presentationOfIsCokernelFree
    (pullbackPresentationRelations (φ := φ) P)
    (pullbackPresentationGenerators (φ := φ) P)
    (pullbackPresentationRelations_mapGenerators (φ := φ) P)
    (pullbackPresentationGenerators_isCokernel (φ := φ) P)

/-- Helper for Lemma 18.17.2: the pulled-back presentation keeps finite generator and relation
index types when the source presentation is finite. -/
private theorem pullbackPresentationOfPresentation_isFinite {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) [P.IsFinite] :
    (pullbackPresentationOfPresentation (φ := φ) P).IsFinite := by
  sorry

-- Proof sketch: choose a global presentation of `ℱ`, pull back the presentation diagram, use that
-- pullback preserves colimits, and identify the pulled-back free terms with free sheaves via the
-- canonical unit comparison isomorphism.
/-- Lemma 18.17.2 (6): if an `\mathcal O_\mathcal D`-module has a global presentation, then its
pullback along a morphism of ringed topoi has a global presentation. -/
instance pullback_hasGlobalPresentation (ℱ : SheafOfModules S)
    [Nonempty ℱ.Presentation] :
    Nonempty (((fStar).obj ℱ).Presentation) := by
  classical
  -- Route correction: `Presentation.map` needs the stronger `HasSheafify` API, so we instead map
  -- the explicit free cokernel presentation supplied by `P.isColimit`.
  rcases (inferInstance : Nonempty ℱ.Presentation) with ⟨P⟩
  exact ⟨pullbackPresentationOfPresentation (φ := φ) P⟩

-- Proof sketch: pull back a finite global presentation of `ℱ`; the pullback preserves the
-- presentation and leaves the finite indexing sets finite.
/-- Lemma 18.17.2 (7): if an `\mathcal O_\mathcal D`-module has a finite global presentation, then
its pullback along a morphism of ringed topoi again has a finite global presentation. -/
instance pullback_finitePresentation (ℱ : SheafOfModules S)
    [Nonempty {P : ℱ.Presentation // P.IsFinite}] :
    Nonempty {P : ((fStar).obj ℱ).Presentation // P.IsFinite} := by
  classical
  -- Proof comment: use the explicit pulled-back presentation from part (6) and inherit finiteness
  -- from the unchanged source relation and generator index types.
  rcases (inferInstance : Nonempty {P : ℱ.Presentation // P.IsFinite}) with ⟨⟨P, hP⟩⟩
  letI : P.IsFinite := hP
  exact ⟨⟨pullbackPresentationOfPresentation (φ := φ) P,
    pullbackPresentationOfPresentation_isFinite (φ := φ) P⟩⟩

end SheafOfModules
