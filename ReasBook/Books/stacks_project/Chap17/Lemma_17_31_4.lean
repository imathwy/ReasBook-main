import Mathlib
import stacks_project.Chap07.Example_7_33_5
import stacks_project.Chap10.Definition_10_134_1
import stacks_project.Chap17.Definition_17_28_3
import stacks_project.Chap17.Definition_17_31_1
import stacks_project.Chap18.Lemma_18_36_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace ComplexShape
open PresheafOfModules.DifferentialsConstruction
open TopCat.Presheaf
open scoped NaiveCotangent TensorProduct ZeroObject

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})]

private instance topCatSheaf_hasBinaryCoproducts :
    HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} X) := by
  simpa [TopCat.Sheaf] using
    (inferInstance :
      HasBinaryCoproducts
        (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}))

private abbrev asCommModulePresheaf
    (O : X.Sheaf CommRingCat.{u}) (ℱ : SheafOfModules (ringSheaf O)) :
    PresheafOfModules (O.obj ⋙ forget₂ CommRingCat RingCat) :=
  ℱ.val

/- Domain-style sampling for Lemma 17.31.4:
- primary domain: naive cotangent complexes of morphisms of sheaves of commutative rings, together
  with their stalkwise realization on local rings;
- sampled owner declarations:
  `TopCat.Sheaf.naiveCotangent`,
  `CommRingCat.Hom.naiveCotangent`,
  `CategoryTheory.point_stalk_ring`,
  `CategoryTheory.point_sheaf_module_stalk_functor`,
  `CategoryTheory.pointGrothendieckTopology_presheafFiber_obj_iso_stalk`,
  `CategoryTheory.Functor.mapHomologicalComplex`,
  `Algebra.naiveCotangent`,
  `Algebra.Extension.naiveCotangentChainComplex`,
  `SheafOfModules.RingedSite.conormalSource`,
  `SheafOfModules.RingedSite.conormalTensorTerm`,
  `SheafOfModules.RingedSite.conormalMap`;
- best owner abstraction: the source-facing owner statement should compare the site-point stalk of
  `TopCat.Sheaf.naiveCotangent` with the commutative-ring morphism owner
  `CommRingCat.Hom.naiveCotangent` for the induced stalk map, i.e. the map-level view of the
  Chapter 10 owner `Algebra.naiveCotangent`; the actual stalked sheaf complex is therefore
  bridge/view data obtained from the canonical site-point module-stalk functor, retargeted to the
  actual topological-space stalk ring, and then `Functor.mapHomologicalComplex`;
- primitive data: a morphism `φ : O₁ ⟶ O₂` of sheaves of commutative rings and a point `x : X`;
- derived API: the bridge/view complex `stalkedNaiveCotangent O₁ O₂ φ x`, the comparison
  theorem `stalkedNaiveCotangent_isIsomorphic O₁ O₂ φ x` from the explicit stalk complex model to
  the canonical Chapter 10 owner `Algebra.naiveCotangent (stalkRing O₁ x) (stalkRing O₂ x)` of
  the induced stalk morphism,
  the explicit degree `-1/0` identifications and `-1 → 0` differential of the bridge/view
  complex, and the companion
  `relativeDifferentials_stalkIso` for the older degree-`0` differentials statement.

Source/core/bridge triage:
- `source-facing`: the comparison
  `NL_{\mathcal O_2/\mathcal O_1, x}` as the naive cotangent complex of the induced stalk map in
  the canonical Chapter 10 owner category, together with its explicit two-term stalk model;
- `core/canonical`: `TopCat.Sheaf.naiveCotangent`,
  `point_stalk_ring (Opens.pointGrothendieckTopology x) (ringSheaf O₂)`,
  `point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x) (ringSheaf O₂)`,
  `pointGrothendieckTopology_presheafFiber_obj_iso_stalk`,
  `Functor.mapHomologicalComplex`, `CommRingCat.Hom.naiveCotangent`, `Algebra.naiveCotangent`,
  `Algebra.Extension.naiveCotangentChainComplex`,
  `presentationBase`, `presentationMap`, `conormalSource`, `conormalTensorTerm`, `conormalMap`,
  and `TopCat.Sheaf.relativeDifferentials`;
- `bridge/view`: this file specializes the canonical site-point stalk owner to the opens site of
  `X`, retargets it to the commutative stalk ring, and records the explicit `-1`, `0`, and
  `d(-1,0)` pieces of the resulting bridge complex `stalkedNaiveCotangent`; the induced-stalk
  owner itself is the canonical Chapter 10 object
  `Algebra.naiveCotangent (stalkRing O₁ x) (stalkRing O₂ x)`.

This file should therefore expose the main stalk statement by an actual comparison with the
Chapter 10 stalk-map owner, and treat the direct site-point stalk complex only as the bridge/view
realizing that comparison. -/

private abbrev pointCommPresheafStalk
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    CommRingCat.{u} :=
  (Opens.pointGrothendieckTopology x).presheafFiber.obj O.obj

private abbrev pointStalkRingEquivPointCommPresheafStalk
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    ↑(point_stalk_ring (Opens.pointGrothendieckTopology x) (ringSheaf O)) ≃+*
      ↑(pointCommPresheafStalk O x) :=
  ((Opens.pointGrothendieckTopology x).presheafFiberCompIso
    (forget₂ CommRingCat RingCat)).app O.obj |>.ringCatIsoToRingEquiv

private abbrev pointStalkRingEquivStalkRing
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    ↑(point_stalk_ring (Opens.pointGrothendieckTopology x) (ringSheaf O)) ≃+*
      ↑((stalkFunctor CommRingCat x).obj O.obj) :=
  (pointStalkRingEquivPointCommPresheafStalk O x).trans
    (CategoryTheory.Iso.commRingCatIsoToRingEquiv
      (CategoryTheory.pointGrothendieckTopology_presheafFiber_obj_iso_stalk x O.obj))

noncomputable abbrev stalkModuleFunctor
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    SheafOfModules (ringSheaf O) ⥤
      ModuleCat ((stalkFunctor CommRingCat x).obj O.obj) :=
  point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x) (ringSheaf O) ⋙
    ModuleCat.restrictScalars (pointStalkRingEquivStalkRing O x).symm.toRingHom

private abbrev stalkRing (O : X.Sheaf CommRingCat.{u}) (x : X) : CommRingCat :=
  (stalkFunctor CommRingCat x).obj O.obj

private abbrev stalkRingHom
    {O O' : X.Sheaf CommRingCat.{u}} (φ : O ⟶ O') (x : X) :
    stalkRing O x ⟶ stalkRing O' x :=
  (stalkFunctor CommRingCat x).map φ.hom

private abbrev stalkKaehlerDifferential
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
  ModuleCat (stalkRing O₂ x) :=
  CommRingCat.KaehlerDifferential (stalkRingHom φ x)

private noncomputable def relativeDifferentialsGermHom
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    ((relativeDifferentials' φ.hom).presheaf.obj (Opposite.op U)) ⟶
      AddCommGrpCat.of ↑(stalkKaehlerDifferential O₁ O₂ φ x) := by
  let comparison :=
    CommRingCat.KaehlerDifferential.map
      (by
        simpa using stalkFunctor_map_germ U x hx φ.hom)
  exact AddCommGrpCat.ofHom
    { toFun := fun m ↦ comparison m
      map_zero' := by
        exact comparison.hom.map_zero
      map_add' := by
        intro m n
        exact comparison.hom.map_add m n }

private noncomputable def relativeDifferentialsNhdsGermHom
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X)
    (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙ (relativeDifferentials' φ.hom).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkKaehlerDifferential O₁ O₂ φ x) := by
  exact show (((OpenNhds.inclusion x).op ⋙ (relativeDifferentials' φ.hom).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkKaehlerDifferential O₁ O₂ φ x) from
    relativeDifferentialsGermHom O₁ O₂ φ x (Opposite.unop U).1 (Opposite.unop U).2

private theorem relativeDifferentialsNhdsGermHom_naturality
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X)
    {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙ (relativeDifferentials' φ.hom).presheaf).map i) ≫
        relativeDifferentialsNhdsGermHom O₁ O₂ φ x V =
      relativeDifferentialsNhdsGermHom O₁ O₂ φ x U := sorry

private def presheafRelativeDifferentialsStalkComparison
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    stalk (relativeDifferentials' φ.hom).presheaf x ⟶
      AddCommGrpCat.of ↑(stalkKaehlerDifferential O₁ O₂ φ x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (relativeDifferentials' φ.hom).presheaf) <|
    Cocone.mk _ <|
      { app := fun U ↦ relativeDifferentialsNhdsGermHom O₁ O₂ φ x U
        naturality := by
          intro U V i
          exact relativeDifferentialsNhdsGermHom_naturality O₁ O₂ φ x i }

private instance instStalkModule
    (O : X.Sheaf CommRingCat.{u}) (ℱ : SheafOfModules (ringSheaf O)) (x : X) :
    Module ((stalkFunctor CommRingCat x).obj O.obj)
      ↑(stalk ℱ.val.presheaf x) := by
  simpa [asCommModulePresheaf] using
    (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (asCommModulePresheaf O ℱ) x)

private noncomputable def relativeDifferentialsStalkComparison_hom
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    ModuleCat.of (stalkRing O₂ x)
      ↑(stalk Ω(φ).val.presheaf x) ⟶
      stalkKaehlerDifferential O₁ O₂ φ x := by
  letI : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
  letI :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  let η :
      stalk (relativeDifferentials' φ.hom).presheaf x ⟶
      stalk Ω(φ).val.presheaf x :=
    (stalkFunctor AddCommGrpCat x).map
      (toSheafify (Opens.grothendieckTopology X) (relativeDifferentials' φ.hom).presheaf)
  haveI : IsIso η := by
    simpa [relativeDifferentials] using
      (stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (relativeDifferentials' φ.hom).presheaf)
  let comparison :
      stalk Ω(φ).val.presheaf x ⟶
        AddCommGrpCat.of ↑(stalkKaehlerDifferential O₁ O₂ φ x) :=
    inv η ≫ presheafRelativeDifferentialsStalkComparison O₁ O₂ φ x
  exact ModuleCat.ofHom
    { toFun := comparison
      map_add' := by
        intro m n
        simpa [comparison] using comparison.hom.map_add m n
      map_smul' := by
        intro r m
        sorry }

private theorem relativeDifferentialsStalkComparison_hom_isIso
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    IsIso (relativeDifferentialsStalkComparison_hom O₁ O₂ φ x) := sorry

/-- The canonical stalk comparison for relative differentials
`(Ω_{O₂/O₁})_x ≅ Ω_{(O₂)_x/(O₁)_x}`. This is the companion degree-`0` differentials bridge used
in Lemma `17.28.7`, not the whole naive cotangent complex comparison of Lemma `17.31.4`. -/
noncomputable def relativeDifferentials_stalkIso
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    ModuleCat.of
      ((stalkFunctor CommRingCat x).obj O₂.obj)
      ↑(stalk Ω(φ).val.presheaf x) ≅
      CommRingCat.KaehlerDifferential ((stalkFunctor CommRingCat x).map φ.hom) := by
  letI := relativeDifferentialsStalkComparison_hom_isIso O₁ O₂ φ x
  exact asIso (relativeDifferentialsStalkComparison_hom O₁ O₂ φ x)

/-- The stalked naive cotangent complex `NL_{\mathcal O_2/\mathcal O_1, x}`, obtained by taking
the stalk of the opens-site owner `NL_{\mathcal O_2/\mathcal O_1}` via the canonical site-point
module-stalk functor, retargeted to the actual topological-space stalk ring
`(\mathcal O_2)_x`, and then `Functor.mapHomologicalComplex`. This is a thin bridge/view
abbreviation, not a second owner. -/
noncomputable abbrev stalkedNaiveCotangent
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    CochainComplex
      (ModuleCat ((stalkFunctor CommRingCat x).obj O₂.obj)) ℤ :=
  (((stalkModuleFunctor O₂ x).mapHomologicalComplex (up ℤ)).obj
    (naiveCotangent O₁ (Under.mk φ)))

/-- Lemma 17.31.4: the stalk of the opens-site naive cotangent complex is canonically
isomorphic, after passing from the explicit stalk cochain model to the derived owner category, to
the Chapter 10 naive cotangent complex of the induced stalk morphism
`(\mathcal O_1)_x \to (\mathcal O_2)_x`, written on the explicit ring-morphism surface as
`CommRingCat.Hom.naiveCotangentObject (stalkRingHom φ x)`. This is the source-facing owner
statement; the direct site-point stalk
complex `stalkedNaiveCotangent` is only its bridge/view realization, while the target remains the
canonical owner `NL_{(stalkRing O₂ x)⁄(stalkRing O₁ x)}` for the stalk algebra structure induced
by `stalkRingHom φ x`. The statement is kept theorem-level so no chosen isomorphism witness
enters the public API. -/
theorem stalkedNaiveCotangent_isIsomorphic
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    IsIsomorphic
      (DerivedCategory.Q.obj (stalkedNaiveCotangent O₁ O₂ φ x))
      (CommRingCat.Hom.naiveCotangentObject (stalkRingHom φ x)) := by
  sorry

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `-1` term of the stalked naive cotangent complex is the stalk of the conormal
source sheaf of the canonical presentation
`\mathcal O_1[\mathcal O_2] \to \mathcal O_2`. -/
theorem stalkedNaiveCotangent_X_negOne
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    (stalkedNaiveCotangent O₁ O₂ φ x).X (-1) =
      (stalkModuleFunctor O₂ x).obj
        (SheafOfModules.RingedSite.conormalSource
          (SheafOfModules.RingedSite.presentationMap O₁ (Under.mk φ))) := by
  exact
    congrArg
      ((stalkModuleFunctor O₂ x).obj)
      (naiveCotangent_X_negOne O₁ (Under.mk φ))

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `0` term of the stalked naive cotangent complex is the stalk of the tensor term
`conormalTensorTerm (presentationBase O₁ (Under.mk φ)) (presentationMap O₁ (Under.mk φ))`. -/
theorem stalkedNaiveCotangent_X_zero
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    (stalkedNaiveCotangent O₁ O₂ φ x).X 0 =
      (stalkModuleFunctor O₂ x).obj
        (SheafOfModules.RingedSite.conormalTensorTerm
          (SheafOfModules.RingedSite.presentationBase O₁ (Under.mk φ))
          (SheafOfModules.RingedSite.presentationMap O₁ (Under.mk φ))) := by
  exact
    congrArg
      ((stalkModuleFunctor O₂ x).obj)
      (naiveCotangent_X_zero O₁ (Under.mk φ))

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The differential in degrees `-1 → 0` of the stalked naive cotangent complex is the map on
stalks induced by the canonical conormal map of the presentation
`\mathcal O_1[\mathcal O_2] \to \mathcal O_2`. -/
theorem stalkedNaiveCotangent_d_negOne_zero
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    (stalkedNaiveCotangent O₁ O₂ φ x).d (-1) 0 =
      (stalkModuleFunctor O₂ x).map
        (SheafOfModules.RingedSite.conormalMap
          (SheafOfModules.RingedSite.presentationBase O₁ (Under.mk φ))
          (SheafOfModules.RingedSite.presentationMap O₁ (Under.mk φ))) := by
  change
    (stalkModuleFunctor O₂ x).map
      ((naiveCotangent O₁ (Under.mk φ)).d (-1) 0) =
      (stalkModuleFunctor O₂ x).map
        (SheafOfModules.RingedSite.conormalMap
          (SheafOfModules.RingedSite.presentationBase O₁ (Under.mk φ))
          (SheafOfModules.RingedSite.presentationMap O₁ (Under.mk φ)))
  rfl

end TopCat.Sheaf
