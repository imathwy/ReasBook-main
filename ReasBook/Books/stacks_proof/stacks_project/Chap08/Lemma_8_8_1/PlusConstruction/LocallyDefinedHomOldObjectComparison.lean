import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomSourceProjection

universe u v uX vX w wA

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor

private theorem ulift_heq_of_down_heq
    {A B : Type wA} {x : ULift.{w, wA} A} {y : ULift.{w, wA} B}
    (h : HEq x.down y.down) : HEq x y := by
  cases x
  cases y
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The vertical factor of the ordinary identity representative is the literal source identity
factor after the explicit target transport induced by `X.p.map_id x`.

This is the owner-sensitive bridge between the ordinary-arrow representative of `𝟙 x`, whose
base is `X.p.map (𝟙 x)`, and the source-facing identity representative, whose base is literally
`𝟙 (X.p.obj x)`. -/
theorem ordinaryIdentityPullbackFactor_eq_sourceIdentityFactor_afterTransport
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S) :
    let Fp := canonicalFiberPseudofunctor X.p
    let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
    let hbase : X.p.map (𝟙 x) = 𝟙 (X.p.obj x) := X.p.map_id x
    let targetTransport :
        ((Fp.map (X.p.map (𝟙 x)).op.toLoc).toFunctor.obj xF) ⟶
          ((Fp.map (𝟙 (X.p.obj x)).op.toLoc).toFunctor.obj xF) :=
      (eqToHom (congrArg (fun k => (canonicalPullbackChoice X.p).pullbackFunctor k) hbase)).app xF
    ordinaryHomToPullbackFiberHom X (𝟙 x) ≫ targetTransport =
      (Fp.mapId (LocallyDiscrete.mk (op (X.p.obj x)))).inv.toNatTrans.app xF := by
  intro Fp xF hbase targetTransport
  apply Functor.Fiber.hom_ext
  let hc := canonicalPullbackChoice X.p
  let U := X.p.obj x
  let lhs := ordinaryHomToPullbackFiberHom X (𝟙 x) ≫ targetTransport
  let rhs := (Fp.mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app xF
  change lhs.1 = rhs.1
  refine @Functor.IsStronglyCartesian.ext C X.S _ _ X.p _ _ _ _
    (𝟙 U) (hc.map (𝟙 U) xF) (hc.isStronglyCartesian (𝟙 U) xF)
    _ _ (𝟙 U) lhs.1 rhs.1 ?_ ?_ ?_
  · exact lhs.2
  · exact rhs.2
  · have htransport :
        targetTransport.1 ≫ hc.map (𝟙 U) xF =
          hc.map (X.p.map (𝟙 x)) xF := by
      dsimp [targetTransport, hbase, hc, U, Fp, xF]
      have haux {g : U ⟶ U} (e : X.p.map (𝟙 x) = g) :
          (Functor.Fiber.fiberInclusion.map
              ((eqToHom (congrArg (fun k => (canonicalPullbackChoice X.p).pullbackFunctor k)
                e)).app xF)) ≫
            (canonicalPullbackChoice X.p).map g xF =
          (canonicalPullbackChoice X.p).map (X.p.map (𝟙 x)) xF := by
        cases e
        simp
      exact haux (X.p.map_id x)
    have hleft :
        lhs.1 ≫ hc.map (𝟙 U) xF = 𝟙 x := by
      dsimp [lhs]
      change (Functor.Fiber.fiberInclusion.map
          (ordinaryHomToPullbackFiberHom X (𝟙 x) ≫ targetTransport)) ≫
          hc.map (𝟙 U) xF = 𝟙 x
      rw [Functor.map_comp]
      have htransport' :
          Functor.Fiber.fiberInclusion.map targetTransport ≫ hc.map (𝟙 U) xF =
            hc.map (X.p.map (𝟙 x)) xF := htransport
      rw [Category.assoc, htransport']
      exact ordinaryHomToPullbackFiberHom_id_fac X x
    have hright :
        rhs.1 ≫ hc.map (𝟙 U) xF = 𝟙 x := by
      have hpair :=
        congrArg (fun k => k.1)
          (Cat.Hom.inv_hom_id_toNatTrans_app
            (Fp.mapId (LocallyDiscrete.mk (op U))) xF)
      have hhom :=
        canonicalFiberPseudofunctor_mapId_hom_app_eq_identityCart_core
          (p := X.p) U xF
      dsimp [rhs, hc, U, Fp] at hpair hhom ⊢
      rw [hhom] at hpair
      simpa using hpair
    exact hleft.trans hright.symm

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary identity locally-defined morphism equals the literal source identity
locally-defined morphism.

The proof passes through the common-refinement presentation of the plus construction.  On each
member of the trivial cover, the ordinary local representative is compared with the source
identity representative using the explicit `X.p.map_id x` target transport; the final transport
tail is cancelled by the canonical fiber-pseudofunctor coherence lemma. -/
theorem ordinaryHomToLocallyDefinedHom_id_eq_sourceIdentity
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S) :
    ordinaryHomToLocallyDefinedHom (J := J) X (𝟙 x) =
      sourceIdentityHomToLocallyDefinedHom (J := J) X x := by
  rw [ordinaryHomToLocallyDefinedHom, sourceIdentityHomToLocallyDefinedHom]
  apply (LocallyDefinedHomRepresentative.equivalent_iff_exists_base_eq (J := J)
    (ordinaryHomToRepresentative (J := J) X (𝟙 x))
    (sourceIdentityHomToRepresentative (J := J) X x)).2
  refine ⟨X.p.map_id x, ?_⟩
  dsimp [ordinaryHomToRepresentative, sourceIdentityHomToRepresentative]
  apply (LocallyDefinedHomRepresentativeOver.toPlusSection_eq_iff_equivalent (J := J)
    (LocallyDefinedHomRepresentativeOver.castBase (J := J) (X.p.map_id x)
      (ordinaryHomToRepresentativeOver (J := J) X (𝟙 x)))
    (sourceIdentityHomToRepresentativeOver (J := J) X x)).1
  rw [LocallyDefinedHomRepresentativeOver.castBase_toPlusSection_eq_mk_castBaseFamily]
  change GrothendieckTopology.Plus.mk
      (LocallyDefinedHomRepresentativeOver.castBaseFamily (J := J) (X.p.map_id x)
        (ordinaryHomToRepresentativeOver (J := J) X (𝟙 x))) =
    GrothendieckTopology.Plus.mk (sourceIdentityHomToRepresentativeOver (J := J) X x).family
  rw [GrothendieckTopology.Plus.eq_mk_iff_exists]
  refine ⟨⊤, 𝟙 ⊤, 𝟙 ⊤, ?_⟩
  apply Meq.ext
  intro I
  change
    (LocallyDefinedHomRepresentativeOver.castBaseFamily (J := J) (X.p.map_id x)
      (ordinaryHomToRepresentativeOver (J := J) X (𝟙 x))) I =
    (sourceIdentityHomToRepresentativeOver (J := J) X x).family I
  apply eq_of_heq
  have hcast := LocallyDefinedHomRepresentativeOver.castBaseFamily_apply_heq (J := J)
    (X.p.map_id x) (ordinaryHomToRepresentativeOver (J := J) X (𝟙 x)) I
  refine HEq.trans hcast ?_
  apply ulift_heq_of_down_heq
  let Fp := canonicalFiberPseudofunctor X.p
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  let hbase : X.p.map (𝟙 x) = 𝟙 (X.p.obj x) := X.p.map_id x
  let targetTransport :
      ((Fp.map (X.p.map (𝟙 x)).op.toLoc).toFunctor.obj xF) ⟶
        ((Fp.map (𝟙 (X.p.obj x)).op.toLoc).toFunctor.obj xF) :=
    (eqToHom (congrArg (fun k => (canonicalPullbackChoice X.p).pullbackFunctor k) hbase)).app xF
  let e :=
    (Fp.map I.Y.hom.op.toLoc).toFunctor.map (ordinaryHomToPullbackFiberHom X (𝟙 x))
  have hord :
      ((ordinaryHomToRepresentativeOver (J := J) X (𝟙 x)).family I).down =
        e := by
    have hf : I.f = (Over.homMk I.Y.hom : I.Y ⟶ Over.mk (𝟙 (X.p.obj x))) := by
      ext
      simpa using I.f.w
    rw [ordinaryHomToRepresentativeOver_family_apply (J := J) X (𝟙 x) I]
    change
      ((locallyDefinedHomSaturatedPresheaf X (X.p.map (𝟙 x))).map I.f.op
        (ULift.up
          (((canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv)
            (ordinaryHomToPullbackFiberHom X (𝟙 x))))).down =
        e
    rw [hf]
    simpa [locallyDefinedHomSaturatedPresheaf, locallyDefinedHomPresheaf, Fp, xF, e] using
      (presheafHom_map_identitySlice_hom_overMk (p := X.p) I.Y.hom
        xF ((Fp.map (X.p.map (𝟙 x)).op.toLoc).toFunctor.obj xF)
        (ordinaryHomToPullbackFiberHom X (𝟙 x)))
  have htail :
      HEq
        (e ≫ (Fp.map I.Y.hom.op.toLoc).toFunctor.map targetTransport)
        e := by
    simpa [Fp, xF, hbase, targetTransport, e] using
      canonicalFiberPseudofunctor_map_eqToHom_transport_tail_heq
        (p := X.p) hbase I.Y.hom xF (e := e)
  have hfactor := ordinaryIdentityPullbackFactor_eq_sourceIdentityFactor_afterTransport
    (C := C) X x
  have hfactor' :
      ordinaryHomToPullbackFiberHom X (𝟙 x) ≫ targetTransport =
        (Fp.mapId (LocallyDiscrete.mk (op (X.p.obj x)))).inv.toNatTrans.app xF := by
    simpa [Fp, xF, hbase, targetTransport] using hfactor
  have hmapFactor :
      (Fp.map I.Y.hom.op.toLoc).toFunctor.map
          (ordinaryHomToPullbackFiberHom X (𝟙 x) ≫ targetTransport) =
        (Fp.map I.Y.hom.op.toLoc).toFunctor.map
          ((Fp.mapId (LocallyDiscrete.mk (op (X.p.obj x)))).inv.toNatTrans.app xF) :=
    congrArg (fun φ => (Fp.map I.Y.hom.op.toLoc).toFunctor.map φ) hfactor'
  have hmapComp :
      (Fp.map I.Y.hom.op.toLoc).toFunctor.map
          (ordinaryHomToPullbackFiberHom X (𝟙 x) ≫ targetTransport) =
        e ≫ (Fp.map I.Y.hom.op.toLoc).toFunctor.map targetTransport := by
    rw [Functor.map_comp]
  have hsource := sourceIdentityHomToRepresentativeOver_family_apply_down (J := J) X x I
  exact HEq.trans (heq_of_eq hord)
    (HEq.trans htail.symm
      (HEq.trans (heq_of_eq (hmapComp.symm.trans hmapFactor))
        (heq_of_eq hsource.symm)))

namespace LocallyDefinedHomTotal

/-- Identity component of the old-object comparison frontier, separated out so later functor
construction can use the literal source identity owner surface. -/
theorem oldObjectComparison_identityBridge
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    ∀ x : X.S,
      ordinaryHomToLocallyDefinedHom (J := J) X (𝟙 x) =
        sourceIdentityHomToLocallyDefinedHom (J := J) X x :=
  ordinaryHomToLocallyDefinedHom_id_eq_sourceIdentity (J := J) X

/-- Package the old-object comparison frontier once the ordinary-composition bridge has been
proved.  The identity component is now discharged by
`ordinaryHomToLocallyDefinedHom_id_eq_sourceIdentity`. -/
noncomputable def oldObjectComparisonFrontierOfCompositionBridge
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (hcomp :
      ∀ ⦃x y z : X.S⦄ (f : x ⟶ y) (g : y ⟶ z),
        ordinaryHomToLocallyDefinedHom (J := J) X (f ≫ g) =
          LocallyDefinedHom.comp (J := J)
            (ordinaryHomToLocallyDefinedHom (J := J) X f)
            (ordinaryHomToLocallyDefinedHom (J := J) X g)) :
    OldObjectComparisonFrontier (J := J) X where
  identityBridge := oldObjectComparison_identityBridge (J := J) X
  compositionBridge := hcomp

/-- The old total category maps to the source stage 2 category by the Stacks construction's
unchanged object map and trivial-cover representative on arrows. -/
noncomputable def oldObjectToSourceFunctorOfFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (H : OldObjectComparisonFrontier (J := J) X) :
    letI := sourceCategory (J := J) X
    X.S ⥤ LocallyDefinedHomTotal (J := J) X := by
  letI := sourceCategory (J := J) X
  exact
    { obj := fun x => ofObj (J := J) X x
      map := fun {x y} f => ordinaryHomToLocallyDefinedHom (J := J) X f
      map_id := by
        intro x
        exact H.identityBridge x
      map_comp := by
        intro x y z f g
        exact H.compositionBridge f g }

@[simp]
theorem oldObjectToSourceFunctor_obj
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (H : OldObjectComparisonFrontier (J := J) X) (x : X.S) :
    letI := sourceCategory (J := J) X
    (oldObjectToSourceFunctorOfFrontier (J := J) X H).obj x = ofObj (J := J) X x := by
  letI := sourceCategory (J := J) X
  rfl

@[simp]
theorem oldObjectToSourceFunctor_map
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (H : OldObjectComparisonFrontier (J := J) X) {x y : X.S} (f : x ⟶ y) :
    letI := sourceCategory (J := J) X
    (oldObjectToSourceFunctorOfFrontier (J := J) X H).map f =
      ordinaryHomToLocallyDefinedHom (J := J) X f := by
  letI := sourceCategory (J := J) X
  rfl

/-- Based-functor form of the old-object comparison.  This is still conditional on the
ordinary-composition bridge and does not claim any cartesian preservation. -/
noncomputable def oldObjectToSourceBasedFunctorOfFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (H : OldObjectComparisonFrontier (J := J) X) :
    X.toBasedCategory ⥤ᵇ sourceBasedCategory (J := J) X := by
  letI := sourceCategory (J := J) X
  exact
    { toFunctor := oldObjectToSourceFunctorOfFrontier (J := J) X H
      w := by
        rfl }

end LocallyDefinedHomTotal

end FibredCategoryMor

end CategoryTheory
