import Mathlib
import StacksProject_2024.stacks_project.Chap07.Example_7_33_5
import StacksProject_2024.stacks_project.Chap10.Definition_10_134_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_28_3
import StacksProject_2024.stacks_project.Chap18.Definition_18_35_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_36_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace ComplexShape
open AlgebraicGeometry
open PresheafOfModules.DifferentialsConstruction
open SheafOfModules.RingedSite
open TopCat.Presheaf
open scoped NaiveCotangent TensorProduct ZeroObject

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable {O₁ O₂ : X.Sheaf CommRingCat.{u}}
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

/- Domain-style sampling for Lemma 17.31.4:
- primary domain: naive cotangent complexes of morphisms of sheaves of commutative rings, together
  with their stalkwise realization on local rings;
- sampled owner declarations:
  `SheafOfModules.RingedSite.naiveCotangent`,
  `CommRingCat.Hom.naiveCotangent`,
  `GrothendieckTopology.Point.stalkRing`,
  `GrothendieckTopology.Point.sheafModuleStalkFunctor`,
  `CategoryTheory.pointGrothendieckTopology_presheafFiber_obj_iso_stalk`,
  `CategoryTheory.Functor.mapHomologicalComplex`,
  `Algebra.naiveCotangent`,
  `Algebra.Extension.naiveCotangentChainComplex`,
  `SheafOfModules.RingedSite.conormalSource`,
  `SheafOfModules.RingedSite.conormalTensorTerm`,
  `SheafOfModules.RingedSite.conormalMap`;
- best owner abstraction: the source-facing owner statement should compare the site-point stalk of
  `SheafOfModules.RingedSite.naiveCotangent`, specialized to the opens site of `X`, with the
  commutative-ring morphism owner
  `CommRingCat.Hom.naiveCotangent` for the induced stalk map, i.e. the map-level view of the
  Chapter 10 owner `Algebra.naiveCotangent`; the recurring source-facing bridge object is therefore
  the stalkwise mapped complex `stalkedNaiveCotangent φ x`, obtained from the site-point
  module-stalk functor, retargeted to the actual topological-space stalk ring, and then
  `Functor.mapHomologicalComplex`;
- primitive data: a morphism `φ : O₁ ⟶ O₂` of sheaves of commutative rings and a point `x : X`;
- derived API: the bridge functor `stalkModuleFunctor O₂ x`, the stalkwise bridge owner
  `stalkedNaiveCotangent φ x`, the comparison isomorphism
  `stalkedNaiveCotangentIso φ x` from that source-facing bridge object to the canonical cochain
  transport
  `((CommRingCat.Hom.naiveCotangent ((stalkFunctor CommRingCat x).map φ.hom)).extend
  embeddingDownNat)` of the induced stalk morphism, together with the theorem-level companions
  `stalkedNaiveCotangent_isIsomorphic φ x` and
  `stalkedNaiveCotangent_derived_isIsomorphic φ x`,
  the explicit degree `-1/0` identifications and `-1 → 0` differential of that mapped complex,
  and the companion
  `relativeDifferentials_stalkIso` for the older degree-`0` differentials statement.

Source/core/bridge triage:
- `source-facing`: the comparison
  `NL_{\mathcal O_2/\mathcal O_1, x}` as the naive cotangent complex of the induced stalk map in
  the canonical Chapter 10 owner category, together with its explicit two-term stalk model;
- `core/canonical`: `SheafOfModules.RingedSite.naiveCotangent`,
  `(Opens.pointGrothendieckTopology x).stalkRing (ringSheaf O₂)`,
  `(Opens.pointGrothendieckTopology x).sheafModuleStalkFunctor (ringSheaf O₂)`,
  `pointGrothendieckTopology_presheafFiber_obj_iso_stalk`,
  `Functor.mapHomologicalComplex`, `CommRingCat.Hom.naiveCotangent`, `Algebra.naiveCotangent`,
  `Algebra.Extension.naiveCotangentChainComplex`,
  `presentationBase`, `presentationMap`, `conormalSource`, `conormalTensorTerm`, `conormalMap`,
  and `TopCat.Sheaf.relativeDifferentials`;
- `bridge/view`: this file specializes the canonical site-point stalk owner to the opens site of
  `X`, retargets it to the commutative stalk ring via `stalkModuleFunctor O₂ x`, packages the
  resulting direct mapped complex expression as the bridge owner `stalkedNaiveCotangent φ x`, and
  records its explicit `-1`, `0`, and `d(-1,0)` pieces; its main public comparison is
  the named complex isomorphism to the canonical cochain transport
  `((CommRingCat.Hom.naiveCotangent ((stalkFunctor CommRingCat x).map φ.hom)).extend
  embeddingDownNat)`, while the induced-stalk owner itself is the canonical Chapter 10 chain
  complex
  `Algebra.naiveCotangent ((stalkFunctor CommRingCat x).obj O₁.obj)
    ((stalkFunctor CommRingCat x).obj O₂.obj)`.

This file should therefore expose the main stalk statement by an actual comparison with the
Chapter 10 stalk-map owner, and treat the direct site-point stalk complex only as the bridge/view
realizing that comparison. -/

abbrev pointStalkRingEquivStalkRing
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    ↑((Opens.pointGrothendieckTopology x).stalkRing (ringSheaf O)) ≃+*
      ↑((stalkFunctor CommRingCat x).obj O.obj) :=
  (((Opens.pointGrothendieckTopology x).presheafFiberCompIso
      (forget₂ CommRingCat RingCat)).app O.obj).ringCatIsoToRingEquiv.trans
    (Iso.commRingCatIsoToRingEquiv
      (pointGrothendieckTopology_presheafFiber_obj_iso_stalk x O.obj))

/-- The site-point stalk functor for `ringSheaf O`, retargeted along the canonical equivalence
between the point-topology stalk ring and the usual topological-space stalk ring. -/
abbrev stalkModuleFunctor
    (O : X.Sheaf CommRingCat.{u}) (x : X) :=
  (Opens.pointGrothendieckTopology x).sheafModuleStalkFunctor (ringSheaf O) ⋙
    ModuleCat.restrictScalars (pointStalkRingEquivStalkRing O x).symm.toRingHom

/-- The stalkwise realization of the opens-site naive cotangent complex, viewed over the usual
stalk ring at `x`. This is the source-facing bridge object for Lemma `17.31.4`. -/
abbrev stalkedNaiveCotangent
    (φ : O₁ ⟶ O₂) (x : X) :=
  (((stalkModuleFunctor O₂ x).mapHomologicalComplex (up ℤ)).obj
    (naiveCotangent O₁ (Under.mk φ)))

/-- Helper for Lemma 17.31.4: degree `-1` of the stalked naive cotangent complex is the stalked
conormal source term of the canonical presentation. -/
private theorem stalkedNaiveCotangent_X_negOne_aux
    (φ : O₁ ⟶ O₂) (x : X) :
    (stalkedNaiveCotangent φ x).X (-1) =
      (stalkModuleFunctor O₂ x).obj
        (conormalSource (presentationMap O₁ (Under.mk φ))) := by
  -- Proof comment: mapping the opens-site naive cotangent complex through the stalk functor
  -- preserves its explicit degree `-1` description.
  simpa [pointStalkRingEquivStalkRing, stalkModuleFunctor, stalkedNaiveCotangent] using
    congrArg ((stalkModuleFunctor O₂ x).obj)
      (naiveCotangent_X_negOne O₁ (Under.mk φ))

/-- Helper for Lemma 17.31.4: degree `0` of the stalked naive cotangent complex is the stalked
tensor term of the canonical presentation. -/
private theorem stalkedNaiveCotangent_X_zero_aux
    (φ : O₁ ⟶ O₂) (x : X) :
    (stalkedNaiveCotangent φ x).X 0 =
      (stalkModuleFunctor O₂ x).obj
        (conormalTensorTerm (presentationBase O₁ (Under.mk φ))
          (presentationMap O₁ (Under.mk φ))) := by
  -- Proof comment: the degree `0` description is also stable under applying the stalk functor.
  simpa [pointStalkRingEquivStalkRing, stalkModuleFunctor, stalkedNaiveCotangent] using
    congrArg ((stalkModuleFunctor O₂ x).obj)
      (naiveCotangent_X_zero O₁ (Under.mk φ))

/-- Helper for Lemma 17.31.4: the source differential in degrees `-1 → 0` is the stalked
canonical conormal map. -/
private theorem stalkedNaiveCotangent_d_negOne_zero_aux
    (φ : O₁ ⟶ O₂) (x : X) :
    (stalkedNaiveCotangent φ x).d (-1) 0 =
      (stalkModuleFunctor O₂ x).map
        (conormalMap (presentationBase O₁ (Under.mk φ))
          (presentationMap O₁ (Under.mk φ))) := by
  -- Proof comment: in the mapped two-term presentation model, the visible differential is still
  -- literally the conormal map.
  rfl

/-- Helper for Lemma 17.31.4: the stalked conormal source term identifies with chain degree `1`
of the induced stalk-ring naive cotangent complex. -/
private theorem stalkConormalSourceIsoChainDegreeOne
    (φ : O₁ ⟶ O₂) (x : X) :
    (stalkModuleFunctor O₂ x).obj
        (conormalSource (presentationMap O₁ (Under.mk φ))) ≅
      (NL((stalkFunctor CommRingCat x).map φ.hom)).X 1 := by
  -- Proof comment: once the canonical stalk ring is used as the scalar ring, degree `1` is the
  -- self-presentation conormal source by definition.
  simpa [CommRingCat.Hom.naiveCotangent, Algebra.naiveCotangent, stalkModuleFunctor,
    pointStalkRingEquivStalkRing] using
    (Iso.refl ((NL((stalkFunctor CommRingCat x).map φ.hom)).X 1))

/-- Helper for Lemma 17.31.4: the stalked tensor term identifies with chain degree `0` of the
induced stalk-ring naive cotangent complex. -/
private theorem stalkConormalTensorTermIsoChainDegreeZero
    (φ : O₁ ⟶ O₂) (x : X) :
    (stalkModuleFunctor O₂ x).obj
        (conormalTensorTerm (presentationBase O₁ (Under.mk φ))
          (presentationMap O₁ (Under.mk φ))) ≅
      (NL((stalkFunctor CommRingCat x).map φ.hom)).X 0 := by
  -- Proof comment: after the same scalar restriction, the tensor term is exactly the chain
  -- degree `0` module of the self-presentation model.
  simpa [CommRingCat.Hom.naiveCotangent, Algebra.naiveCotangent, stalkModuleFunctor,
    pointStalkRingEquivStalkRing] using
    (Iso.refl ((NL((stalkFunctor CommRingCat x).map φ.hom)).X 0))

/-- Helper for Lemma 17.31.4: the stalked conormal differential matches the chain differential
`1 → 0` of the induced stalk-ring naive cotangent complex. -/
private theorem stalkConormalMap_eq_chain_d_1_0
    (φ : O₁ ⟶ O₂) (x : X) :
    (stalkModuleFunctor O₂ x).map
        (conormalMap (presentationBase O₁ (Under.mk φ))
          (presentationMap O₁ (Under.mk φ))) =
      (stalkConormalSourceIsoChainDegreeOne φ x).hom ≫
        (NL((stalkFunctor CommRingCat x).map φ.hom)).d 1 0 ≫
        (stalkConormalTensorTermIsoChainDegreeZero φ x).inv := by
  -- Proof comment: both sides are the owner differential of the self-presentation chain complex,
  -- written once through the stalked presentation model and once through Chapter 10's `NL`.
  let _ :
      Algebra ((stalkFunctor CommRingCat x).obj O₁.obj)
        ((stalkFunctor CommRingCat x).obj O₂.obj) :=
    ((stalkFunctor CommRingCat x).map φ.hom).hom.toAlgebra
  simpa [stalkConormalSourceIsoChainDegreeOne, stalkConormalTensorTermIsoChainDegreeZero,
    CommRingCat.Hom.naiveCotangent, Algebra.naiveCotangent,
    Algebra.Extension.naiveCotangentChainComplex, stalkModuleFunctor,
    pointStalkRingEquivStalkRing] using
    (Algebra.Extension.naiveCotangentChainComplex_d_1_0
      ((Generators.self
          ((stalkFunctor CommRingCat x).obj O₁.obj)
          ((stalkFunctor CommRingCat x).obj O₂.obj)).toExtension))

/-- Helper for Lemma 17.31.4: every target degree away from `-1` and `0` is zero after extending
the induced stalk-ring naive cotangent complex along `embeddingDownNat`. -/
private theorem stalkNaiveCotangentTarget_isZero_X
    (φ : O₁ ⟶ O₂) (x : X) (i : ℤ) (hiNegOne : i ≠ -1) (hiZero : i ≠ 0) :
    IsZero (((NL((stalkFunctor CommRingCat x).map φ.hom)).extend embeddingDownNat).X i) := by
  -- Proof comment: positive cochain degrees are outside the image of `embeddingDownNat`, and the
  -- remaining negative degrees come from higher chain terms, which are zero modules.
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          exact (False.elim (hiZero rfl))
      | succ n =>
          have hX :
              (((NL((stalkFunctor CommRingCat x).map φ.hom)).extend embeddingDownNat).X
                (Int.ofNat (n + 1))) = 0 := by
            simp [CommRingCat.Hom.naiveCotangent, Algebra.naiveCotangent,
              Algebra.Extension.naiveCotangentChainComplex]
          rw [hX]
          infer_instance
  | negSucc n =>
      cases n with
      | zero =>
          exact (False.elim (hiNegOne rfl))
      | succ n =>
          have hX :
              (((NL((stalkFunctor CommRingCat x).map φ.hom)).extend embeddingDownNat).X
                (Int.negSucc (n + 1))) = 0 := by
            simp [CommRingCat.Hom.naiveCotangent, Algebra.naiveCotangent,
              Algebra.Extension.naiveCotangentChainComplex]
          rw [hX]
          infer_instance

/-- Helper for Lemma 17.31.4: the stalked naive cotangent complex is concentrated in degrees
`-1` and `0`, so every other term is zero. -/
private theorem stalkedNaiveCotangent_isZero_X
    (φ : O₁ ⟶ O₂) (x : X) (i : ℤ) (hiNegOne : i ≠ -1) (hiZero : i ≠ 0) :
    IsZero ((stalkedNaiveCotangent φ x).X i) := by
  -- Proof comment: the opens-site naive cotangent complex already has only the conormal source
  -- in degree `-1` and the tensor term in degree `0`, and mapping a zero term through the stalk
  -- functor stays zero.
  have hX : (stalkedNaiveCotangent φ x).X i = 0 := by
    simp [stalkedNaiveCotangent, SheafOfModules.RingedSite.naiveCotangent,
      hiNegOne, hiZero]
  rw [hX]
  infer_instance

/-- Helper for Lemma 17.31.4: `embeddingDownNat` sends chain degree `0` to cochain degree `0`. -/
private theorem embeddingDownNat_zero :
    embeddingDownNat.f 0 = (0 : ℤ) := by
  simp

/-- Helper for Lemma 17.31.4: `embeddingDownNat` sends chain degree `1` to cochain degree `-1`. -/
private theorem embeddingDownNat_one :
    embeddingDownNat.f 1 = (-1 : ℤ) := by
  simp

/-- Helper for Lemma 17.31.4: the target cochain degree `-1` is the chain degree `1` term of the
induced stalk-ring naive cotangent complex. -/
private abbrev stalkNaiveCotangentTargetXNegOneIso
    (φ : O₁ ⟶ O₂) (x : X) :
    (((NL((stalkFunctor CommRingCat x).map φ.hom)).extend embeddingDownNat).X (-1)) ≅
      (NL((stalkFunctor CommRingCat x).map φ.hom)).X 1 :=
  (NL((stalkFunctor CommRingCat x).map φ.hom)).extendXIso embeddingDownNat embeddingDownNat_one

/-- Helper for Lemma 17.31.4: the target cochain degree `0` is the chain degree `0` term of the
induced stalk-ring naive cotangent complex. -/
private abbrev stalkNaiveCotangentTargetXZeroIso
    (φ : O₁ ⟶ O₂) (x : X) :
    (((NL((stalkFunctor CommRingCat x).map φ.hom)).extend embeddingDownNat).X 0) ≅
      (NL((stalkFunctor CommRingCat x).map φ.hom)).X 0 :=
  (NL((stalkFunctor CommRingCat x).map φ.hom)).extendXIso embeddingDownNat embeddingDownNat_zero

/-- Helper for Lemma 17.31.4: the target differential `(-1) → 0` is the transported chain
differential `1 → 0` of the induced stalk-ring naive cotangent complex. -/
private theorem stalkNaiveCotangentTarget_d_negOne_zero
    (φ : O₁ ⟶ O₂) (x : X) :
    (((NL((stalkFunctor CommRingCat x).map φ.hom)).extend embeddingDownNat).d (-1) 0) =
      (stalkNaiveCotangentTargetXNegOneIso φ x).hom ≫
        (NL((stalkFunctor CommRingCat x).map φ.hom)).d 1 0 ≫
        (stalkNaiveCotangentTargetXZeroIso φ x).inv := by
  -- Proof comment: `extend_d_eq` is the canonical owner-level statement identifying the
  -- differential of an extended complex with the original differential conjugated by
  -- `extendXIso` at the source and target degrees.
  simpa [stalkNaiveCotangentTargetXNegOneIso, stalkNaiveCotangentTargetXZeroIso] using
    (HomologicalComplex.extend_d_eq
      (K := NL((stalkFunctor CommRingCat x).map φ.hom))
      (e := embeddingDownNat)
      (i := 1) (j := 0)
      (i' := (-1 : ℤ)) (j' := (0 : ℤ))
      embeddingDownNat_one embeddingDownNat_zero)

/-- Helper for Lemma 17.31.4: in the cochain shape `ComplexShape.up ℤ`, any visible differential
out of degree `-1` lands in degree `0`. -/
private theorem upRel_negOne_target_eq_zero
    {j : ℤ} (h : (ComplexShape.up ℤ).Rel (-1) j) :
    j = 0 := by
  -- Proof comment: the shape relation for `ComplexShape.up` fixes the codomain once the source
  -- degree is `-1`.
  simpa [ComplexShape.up, ComplexShape.up'] using h

/-- The direct stalked naive cotangent complex expression is canonically identified with the
canonical cochain transport of the induced stalk-map naive cotangent complex. This is the main
source-facing comparison, and the `IsIsomorphic` statements are companion bridges. -/
noncomputable def stalkedNaiveCotangentIso
    (φ : O₁ ⟶ O₂) (x : X) :
    stalkedNaiveCotangent φ x ≅
      ((NL((stalkFunctor CommRingCat x).map φ.hom)).extend embeddingDownNat) := by
  -- Route correction: the target-side `extend embeddingDownNat` transport is now isolated in the
  -- helper lemmas above; the proof packages the two visible degrees and uses zero-object
  -- comparisons away from `-1` and `0`.
  -- Proof comment: the `isoOfComponents` skeleton is stable. Outside degrees `-1` and `0`,
  -- both complexes are zero; the only substantive square is `(-1) → 0`.
  let e :
      ∀ i : ℤ,
        (stalkedNaiveCotangent φ x).X i ≅
          (((NL((stalkFunctor CommRingCat x).map φ.hom)).extend embeddingDownNat).X i) :=
    fun i ↦ by
      by_cases hiNegOne : i = -1
      · subst hiNegOne
        exact
          eqToIso (stalkedNaiveCotangent_X_negOne_aux φ x) ≪≫
            stalkConormalSourceIsoChainDegreeOne φ x ≪≫
            (stalkNaiveCotangentTargetXNegOneIso φ x).symm
      · by_cases hiZero : i = 0
        · subst hiZero
          exact
            eqToIso (stalkedNaiveCotangent_X_zero_aux φ x) ≪≫
              stalkConormalTensorTermIsoChainDegreeZero φ x ≪≫
              (stalkNaiveCotangentTargetXZeroIso φ x).symm
        · exact
            (stalkedNaiveCotangent_isZero_X φ x i hiNegOne hiZero).iso
              (stalkNaiveCotangentTarget_isZero_X φ x i hiNegOne hiZero)
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j hij
  by_cases hiNegOne : i = -1
  · subst hiNegOne
    have hjZero : j = 0 := upRel_negOne_target_eq_zero hij
    subst hjZero
    -- Proof comment: after rewriting the source and target degree identifications, the only
    -- nonzero square is exactly the transported differential comparison `1 → 0`.
    have hzeroNeNegOne : (0 : ℤ) ≠ -1 := by
      norm_num
    simp only [e]
    rw [dif_pos rfl, dif_neg hzeroNeNegOne, dif_pos rfl]
    rw [stalkedNaiveCotangent_d_negOne_zero_aux, stalkNaiveCotangentTarget_d_negOne_zero,
      stalkConormalMap_eq_chain_d_1_0]
    simp
  · -- Proof comment: every other differential is zero on both sides after simplifying the models.
    simp [e, stalkedNaiveCotangent, SheafOfModules.RingedSite.naiveCotangent,
      CommRingCat.Hom.naiveCotangent, Algebra.naiveCotangent,
      Algebra.Extension.naiveCotangentChainComplex, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
      hiNegOne]

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The direct stalked naive cotangent complex expression is canonically identified with the
canonical cochain transport of the induced stalk-map naive cotangent complex. This is the
theorem-level `IsIsomorphic` companion to `stalkedNaiveCotangentIso`. -/
theorem stalkedNaiveCotangent_isIsomorphic
    (φ : O₁ ⟶ O₂) (x : X) :
    IsIsomorphic
      (stalkedNaiveCotangent φ x)
      (((NL((stalkFunctor CommRingCat x).map φ.hom)).extend embeddingDownNat)) :=
  ⟨stalkedNaiveCotangentIso φ x⟩

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The derived-category image of the direct stalked naive cotangent complex expression is
isomorphic to the canonical Chapter 10 derived naive cotangent object of the induced stalk
morphism. This is the companion derived-category bridge of `stalkedNaiveCotangentIso`. -/
theorem stalkedNaiveCotangent_derived_isIsomorphic
    (φ : O₁ ⟶ O₂) (x : X) :
    IsIsomorphic
      (DerivedCategory.Q.obj (stalkedNaiveCotangent φ x))
      (CommRingCat.Hom.naiveCotangentObject ((stalkFunctor CommRingCat x).map φ.hom)) := by
  simpa [CommRingCat.Hom.naiveCotangentObject] using
    (show
      IsIsomorphic
        (DerivedCategory.Q.obj (stalkedNaiveCotangent φ x))
        (DerivedCategory.Q.obj
          ((NL((stalkFunctor CommRingCat x).map φ.hom)).extend embeddingDownNat)) from
      ⟨Functor.mapIso DerivedCategory.Q (stalkedNaiveCotangentIso φ x)⟩)

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `-1` term of the stalked naive cotangent complex is the stalk of the conormal
source sheaf of the canonical presentation
`\mathcal O_1[\mathcal O_2] \to \mathcal O_2`. -/
theorem stalkedNaiveCotangent_X_negOne
    (φ : O₁ ⟶ O₂) (x : X) :
    (stalkedNaiveCotangent φ x).X (-1) =
      (stalkModuleFunctor O₂ x).obj
        (conormalSource (presentationMap O₁ (Under.mk φ))) := by
  -- Proof comment: the public degree `-1` statement is exactly the already-normalized helper.
  exact stalkedNaiveCotangent_X_negOne_aux φ x

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `0` term of the stalked naive cotangent complex is the stalk of the tensor term
`conormalTensorTerm (presentationBase O₁ (Under.mk φ)) (presentationMap O₁ (Under.mk φ))`. -/
theorem stalkedNaiveCotangent_X_zero
    (φ : O₁ ⟶ O₂) (x : X) :
    (stalkedNaiveCotangent φ x).X 0 =
      (stalkModuleFunctor O₂ x).obj
        (conormalTensorTerm (presentationBase O₁ (Under.mk φ))
          (presentationMap O₁ (Under.mk φ))) := by
  -- Proof comment: the public degree `0` statement reuses the corresponding helper unchanged.
  exact stalkedNaiveCotangent_X_zero_aux φ x

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The differential in degrees `-1 → 0` of the stalked naive cotangent complex is the map on
stalks induced by the canonical conormal map of the presentation
`\mathcal O_1[\mathcal O_2] \to \mathcal O_2`. -/
theorem stalkedNaiveCotangent_d_negOne_zero
    (φ : O₁ ⟶ O₂) (x : X) :
    (stalkedNaiveCotangent φ x).d (-1) 0 =
      (stalkModuleFunctor O₂ x).map
        (conormalMap (presentationBase O₁ (Under.mk φ))
          (presentationMap O₁ (Under.mk φ))) := by
  -- Proof comment: the public differential formula is the same visible `-1 → 0` helper.
  exact stalkedNaiveCotangent_d_negOne_zero_aux φ x

end TopCat.Sheaf
