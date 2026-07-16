import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationLocalInverseNaturalityProof

universe u v uX vX

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
namespace DescentCompletionObject

/-- Source stage 3.13 local inverse calculation, canonical-owner form:
`rho_(b,j),(a,i) ; rho_(a,i),(b,j) = id` on the total-cover side. -/
theorem projectionDescentOuterFiberHomFromTotalCoverToDatumInner_comp_inverse_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    projectionDescentOuterFiberHomFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K k h ≫
      projectionDescentOuterFiberHomFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a h.symm =
    𝟙 (((canonicalFiberPseudofunctor P).map
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a).op.toLoc).toFunctor.obj
        (D.obj (projectionDescentTotalCoverOuter (J := J) hSheaf D A))) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fK := k ≫ K.f
  let hAK : fA ≫ IA.f = fK ≫ I.f := by
    calc
      fA ≫ IA.f = a ≫ A.f := by
        have hA :
            a ≫ ((projectionDescentTotalCoverInner (J := J) hSheaf D A).f ≫
                (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f) =
              a ≫ A.f :=
          congrArg (fun q => a ≫ q)
            (projectionDescentTotalCover_fac (J := J) hSheaf D A)
        simpa [fA, IA, projectionDescentTotalCoverOuterMap, Category.assoc] using hA
      _ = fK ≫ I.f := by simpa [fK, Category.assoc] using h
  have hbase :
      D.hom (fK ≫ I.f) fK fA rfl hAK =
        D.hom (fA ≫ IA.f) fK fA hAK.symm rfl := by
    exact
      projectionDescentDatumHom_congr_base (J := J) hSheaf D hAK.symm
        fK fA rfl hAK hAK.symm rfl
  have hself :
      D.hom (fA ≫ IA.f) fA fA rfl rfl =
        𝟙 (((canonicalFiberPseudofunctor P).map fA.op.toLoc).toFunctor.obj (D.obj IA)) := by
    simpa [P, IA, fA] using D.hom_self (fA ≫ IA.f) fA rfl
  dsimp [projectionDescentOuterFiberHomFromTotalCoverToDatumInner,
    projectionDescentOuterFiberHomFromDatumInnerToTotalCover, projectionDescentOuterFiberHom]
  change D.hom (fA ≫ IA.f) fA fK rfl hAK.symm ≫
      D.hom (fK ≫ I.f) fK fA rfl hAK =
    𝟙 (((canonicalFiberPseudofunctor P).map fA.op.toLoc).toFunctor.obj (D.obj IA))
  rw [hbase]
  calc
    D.hom (fA ≫ IA.f) fA fK rfl hAK.symm ≫
        D.hom (fA ≫ IA.f) fK fA hAK.symm rfl =
      D.hom (fA ≫ IA.f) fA fA rfl rfl := by
        exact D.hom_comp (fA ≫ IA.f) fA fK fA rfl hAK.symm rfl
    _ = 𝟙 (((canonicalFiberPseudofunctor P).map fA.op.toLoc).toFunctor.obj (D.obj IA)) :=
      hself

/-- Source stage 3.13 local inverse calculation, canonical-owner form:
`rho_(a,i),(b,j) ; rho_(b,j),(a,i) = id` on the datum-inner side. -/
theorem projectionDescentOuterFiberHomFromDatumInnerToTotalCover_comp_realization_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    projectionDescentOuterFiberHomFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a h ≫
      projectionDescentOuterFiberHomFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K k h.symm =
    𝟙 (((canonicalFiberPseudofunctor P).map
        (k ≫ K.f).op.toLoc).toFunctor.obj (D.obj I)) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fK := k ≫ K.f
  let hKA : fK ≫ I.f = fA ≫ IA.f := by
    calc
      fK ≫ I.f = a ≫ A.f := by simpa [fK, Category.assoc] using h
      _ = fA ≫ IA.f := by
        have hA :
            a ≫ ((projectionDescentTotalCoverInner (J := J) hSheaf D A).f ≫
                (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f) =
              a ≫ A.f :=
          congrArg (fun q => a ≫ q)
            (projectionDescentTotalCover_fac (J := J) hSheaf D A)
        simpa [fA, IA, projectionDescentTotalCoverOuterMap, Category.assoc] using hA.symm
  have hbase :
      D.hom (fA ≫ IA.f) fA fK rfl hKA =
        D.hom (fK ≫ I.f) fA fK hKA.symm rfl := by
    exact
      projectionDescentDatumHom_congr_base (J := J) hSheaf D hKA.symm
        fA fK rfl hKA hKA.symm rfl
  have hself :
      D.hom (fK ≫ I.f) fK fK rfl rfl =
        𝟙 (((canonicalFiberPseudofunctor P).map fK.op.toLoc).toFunctor.obj (D.obj I)) := by
    simpa [P, fK] using D.hom_self (fK ≫ I.f) fK rfl
  dsimp [projectionDescentOuterFiberHomFromDatumInnerToTotalCover,
    projectionDescentOuterFiberHomFromTotalCoverToDatumInner, projectionDescentOuterFiberHom]
  change D.hom (fK ≫ I.f) fK fA rfl hKA.symm ≫
      D.hom (fA ≫ IA.f) fA fK rfl hKA =
    𝟙 (((canonicalFiberPseudofunctor P).map fK.op.toLoc).toFunctor.obj (D.obj I))
  rw [hbase]
  calc
    D.hom (fK ≫ I.f) fK fA rfl hKA.symm ≫
        D.hom (fK ≫ I.f) fA fK hKA.symm rfl =
      D.hom (fK ≫ I.f) fK fK rfl rfl := by
        exact D.hom_comp (fK ≫ I.f) fK fA fK rfl hKA.symm rfl
    _ = 𝟙 (((canonicalFiberPseudofunctor P).map fK.op.toLoc).toFunctor.obj (D.obj I)) :=
      hself

/-- Explicit-owner form of
`projectionDescentOuterFiberHomFromTotalCoverToDatumInner_comp_inverse_self`. -/
theorem projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_comp_inverse_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K k h ≫
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a h.symm =
    𝟙 (explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fK := k ≫ K.f
  let eA :=
    projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D IA fA
  let eK :=
    projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I fK
  let outerAK :=
    projectionDescentOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h
  let outerKA :=
    projectionDescentOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h.symm
  have houter : outerAK ≫ outerKA =
      𝟙 (((canonicalFiberPseudofunctor P).map fA.op.toLoc).toFunctor.obj (D.obj IA)) := by
    simpa [P, IA, fA, outerAK, outerKA] using
      projectionDescentOuterFiberHomFromTotalCoverToDatumInner_comp_inverse_self
        (J := J) hSheaf D A I a K k h
  have houterF :
      Functor.Fiber.fiberInclusion.map outerAK ≫
          Functor.Fiber.fiberInclusion.map outerKA =
        𝟙 _ := by
    have hcongr := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) houter
    simpa only [Functor.map_comp, Functor.map_id] using hcongr
  have hcancelK :
      Functor.Fiber.fiberInclusion.map eK.inv ≫
          Functor.Fiber.fiberInclusion.map eK.hom =
        𝟙 _ := by
    have hcongr := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) eK.inv_hom_id
    simpa only [Functor.map_comp, Functor.map_id] using hcongr
  have hcancelA :
      Functor.Fiber.fiberInclusion.map eA.hom ≫
          Functor.Fiber.fiberInclusion.map eA.inv =
        𝟙 _ := by
    have hcongr := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) eA.hom_inv_id
    simpa only [Functor.map_comp, Functor.map_id] using hcongr
  apply Functor.Fiber.hom_ext
  rw [Functor.map_comp]
  dsimp [projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner,
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover]
  change (Functor.Fiber.fiberInclusion.map eA.hom ≫
      Functor.Fiber.fiberInclusion.map outerAK ≫
      Functor.Fiber.fiberInclusion.map eK.inv) ≫
      Functor.Fiber.fiberInclusion.map eK.hom ≫
      Functor.Fiber.fiberInclusion.map outerKA ≫
      Functor.Fiber.fiberInclusion.map eA.inv =
    𝟙 _
  let inc : P.Fiber W ⥤ DescentCompletionObject (J := J) X :=
    Functor.Fiber.fiberInclusion
  calc
    (inc.map eA.hom ≫ inc.map outerAK ≫ inc.map eK.inv) ≫
        inc.map eK.hom ≫ inc.map outerKA ≫ inc.map eA.inv =
      inc.map eA.hom ≫ inc.map outerAK ≫
        (inc.map eK.inv ≫ inc.map eK.hom) ≫ inc.map outerKA ≫ inc.map eA.inv := by
        simp [inc, Category.assoc]
    _ = inc.map eA.hom ≫ inc.map outerAK ≫
        𝟙 _ ≫ inc.map outerKA ≫ inc.map eA.inv := by
        exact congrArg
          (fun q => inc.map eA.hom ≫ inc.map outerAK ≫ q ≫ inc.map outerKA ≫
            inc.map eA.inv)
          hcancelK
    _ = inc.map eA.hom ≫ (inc.map outerAK ≫ inc.map outerKA) ≫ inc.map eA.inv := by
        simp [Category.assoc]
    _ = inc.map eA.hom ≫ 𝟙 _ ≫ inc.map eA.inv := by
        exact congrArg (fun q => inc.map eA.hom ≫ q ≫ inc.map eA.inv) houterF
    _ = 𝟙 _ := by
        simpa [inc, Category.assoc] using hcancelA

/-- Explicit-owner form of
`projectionDescentOuterFiberHomFromDatumInnerToTotalCover_comp_realization_self`. -/
theorem projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_comp_realization_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a h ≫
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K k h.symm =
    𝟙 (explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D I)
        (k ≫ K.f)) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fK := k ≫ K.f
  let eA :=
    projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D IA fA
  let eK :=
    projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I fK
  let outerKA :=
    projectionDescentOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h
  let outerAK :=
    projectionDescentOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h.symm
  have houter : outerKA ≫ outerAK =
      𝟙 (((canonicalFiberPseudofunctor P).map fK.op.toLoc).toFunctor.obj (D.obj I)) := by
    simpa [P, fK, outerKA, outerAK] using
      projectionDescentOuterFiberHomFromDatumInnerToTotalCover_comp_realization_self
        (J := J) hSheaf D I K k A a h
  have houterF :
      Functor.Fiber.fiberInclusion.map outerKA ≫
          Functor.Fiber.fiberInclusion.map outerAK =
        𝟙 _ := by
    have hcongr := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) houter
    simpa only [Functor.map_comp, Functor.map_id] using hcongr
  have hcancelA :
      Functor.Fiber.fiberInclusion.map eA.inv ≫
          Functor.Fiber.fiberInclusion.map eA.hom =
        𝟙 _ := by
    have hcongr := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) eA.inv_hom_id
    simpa only [Functor.map_comp, Functor.map_id] using hcongr
  have hcancelK :
      Functor.Fiber.fiberInclusion.map eK.hom ≫
          Functor.Fiber.fiberInclusion.map eK.inv =
        𝟙 _ := by
    have hcongr := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) eK.hom_inv_id
    simpa only [Functor.map_comp, Functor.map_id] using hcongr
  apply Functor.Fiber.hom_ext
  rw [Functor.map_comp]
  dsimp [projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover,
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner]
  change (Functor.Fiber.fiberInclusion.map eK.hom ≫
      Functor.Fiber.fiberInclusion.map outerKA ≫
      Functor.Fiber.fiberInclusion.map eA.inv) ≫
      Functor.Fiber.fiberInclusion.map eA.hom ≫
      Functor.Fiber.fiberInclusion.map outerAK ≫
      Functor.Fiber.fiberInclusion.map eK.inv =
    𝟙 _
  let inc : P.Fiber W ⥤ DescentCompletionObject (J := J) X :=
    Functor.Fiber.fiberInclusion
  calc
    (inc.map eK.hom ≫ inc.map outerKA ≫ inc.map eA.inv) ≫
        inc.map eA.hom ≫ inc.map outerAK ≫ inc.map eK.inv =
      inc.map eK.hom ≫ inc.map outerKA ≫
        (inc.map eA.inv ≫ inc.map eA.hom) ≫ inc.map outerAK ≫ inc.map eK.inv := by
        simp [inc, Category.assoc]
    _ = inc.map eK.hom ≫ inc.map outerKA ≫
        𝟙 _ ≫ inc.map outerAK ≫ inc.map eK.inv := by
        exact congrArg
          (fun q => inc.map eK.hom ≫ inc.map outerKA ≫ q ≫ inc.map outerAK ≫
            inc.map eK.inv)
          hcancelA
    _ = inc.map eK.hom ≫ (inc.map outerKA ≫ inc.map outerAK) ≫ inc.map eK.inv := by
        simp [Category.assoc]
    _ = inc.map eK.hom ≫ 𝟙 _ ≫ inc.map eK.inv := by
        exact congrArg (fun q => inc.map eK.hom ≫ q ≫ inc.map eK.inv) houterF
    _ = 𝟙 _ := by
        simpa [inc, Category.assoc] using hcancelK

/-- Component form of the total-cover-side self inverse identity. -/
theorem projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner_comp_inverse_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f) :
    projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K k h ≫
      projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a h.symm =
    𝟙 ((DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).restrictedLocalObject
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a) (𝟙 W)) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let EA :=
    explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  let EK :=
    explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D I) (k ≫ K.f)
  let IA := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
  let IK := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k
  let α :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h
  let β :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h.symm
  have hαbase : α.1.base = 𝟙 W :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
      (J := J) hSheaf D A I a K k h
  have hβbase : β.1.base = 𝟙 W :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
      (J := J) hSheaf D I K k A a h.symm
  let hAK : 𝟙 W ≫ IA.f ≫ α.1.base = 𝟙 W ≫ IK.f := by
    rw [hαbase]
    dsimp [IA, IK, projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentDatumExplicitPullbackArrow]
    simp
  let hKA : 𝟙 W ≫ IK.f ≫ β.1.base = 𝟙 W ≫ IA.f := by
    rw [hβbase]
    dsimp [IA, IK, projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentDatumExplicitPullbackArrow]
    simp
  let hAA : 𝟙 W ≫ IA.f ≫ (α.1.base ≫ β.1.base) = 𝟙 W ≫ IA.f := by
    calc
      𝟙 W ≫ IA.f ≫ (α.1.base ≫ β.1.base) =
          𝟙 W ≫ IK.f ≫ β.1.base := by
            simpa [Category.assoc] using congrArg (fun q => q ≫ β.1.base) hAK
      _ = 𝟙 W ≫ IA.f := hKA
  have hcompComponent :
      α.1.components.toHomOver.family IA IK (𝟙 W) (𝟙 W) hAK ≫
          β.1.components.toHomOver.family IK IA (𝟙 W) (𝟙 W) hKA =
        (Hom.compose (J := J) hSheaf α.1 β.1).components.toHomOver.family
          IA IA (𝟙 W) (𝟙 W) hAA := by
    exact Hom.compose_component_eq_of_middle (J := J) hSheaf α.1 β.1
      IA IK IA (𝟙 W) (𝟙 W) (𝟙 W) hAK hKA
  have hhom : α ≫ β = 𝟙 EA := by
    simpa [α, β, EA] using
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_comp_inverse_self
        (J := J) hSheaf D A I a K k h
  let componentOf (δ : EA ⟶ EA) :
      EA.1.object.restrictedLocalObject IA (𝟙 W) ⟶
        EA.1.object.restrictedLocalObject IA (𝟙 W) := by
    letI : P.IsHomLift (𝟙 W) δ.1 := δ.2
    have hbase : δ.1.base = 𝟙 W := by
      have hfac := IsHomLift.fac' P (𝟙 W) δ.1
      simpa [P, projectionFunctor] using hfac
    exact δ.1.components.toHomOver.family IA IA (𝟙 W) (𝟙 W) (by
      rw [hbase]
      dsimp [IA, projectionDescentTotalCoverExplicitPullbackArrow]
      change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
      simp)
  have hcomponent := congrArg componentOf hhom
  dsimp [componentOf] at hcomponent
  let hId : 𝟙 W ≫ IA.f ≫ (DescentCompletionObject.identity (J := J) EA.1).base =
      𝟙 W ≫ IA.f := by
    dsimp [DescentCompletionObject.identity]
    change 𝟙 W ≫ IA.f ≫ 𝟙 W = 𝟙 W ≫ IA.f
    rw [Category.comp_id]
  have hcomponent' :
      (Hom.compose (J := J) hSheaf α.1 β.1).components.toHomOver.family
          IA IA (𝟙 W) (𝟙 W) hAA =
        (DescentCompletionObject.identity (J := J) EA.1).components.toHomOver.family
          IA IA (𝟙 W) (𝟙 W) hId := by
    simpa [P, α, β, EA, IA, hAA, hId] using hcomponent
  dsimp [projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner,
    projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover]
  change α.1.components.toHomOver.family IA IK (𝟙 W) (𝟙 W) _ ≫
      β.1.components.toHomOver.family IK IA (𝟙 W) (𝟙 W) _ =
    𝟙 (EA.1.object.restrictedLocalObject IA (𝟙 W))
  rw [hcompComponent]
  rw [hcomponent']
  dsimp [DescentCompletionObject.identity, DescentCompletionObjectOver.NaturalHomOver.id,
    DescentCompletionObjectOver.idHomOver]
  simpa [P, α, β, EA, IA,
    DescentCompletionObjectOver.NaturalHomOver.id, DescentCompletionObjectOver.idHomOver,
    explicitPullbackFiberObject, projectionDescentDatumObject,
    DescentCompletionObjectOver.pullback, DescentCompletionObjectOver.restrictedLocalObject,
    projectionDescentTotalCoverExplicitPullbackArrow,
    DescentCompletionObjectOver.pullbackCoverBaseArrow,
    DescentCompletionObjectOver.overlapIso_self_hom]

/-- Component form of the datum-inner-side self inverse identity. -/
theorem projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover_comp_realization_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f) :
    projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a h ≫
      projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K k h.symm =
    𝟙 ((DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)
        (k ≫ K.f)).restrictedLocalObject
        (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k) (𝟙 W)) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let EK :=
    explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D I) (k ≫ K.f)
  let EA :=
    explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  let IK := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k
  let IA := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
  let α :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h
  let β :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h.symm
  have hαbase : α.1.base = 𝟙 W :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
      (J := J) hSheaf D I K k A a h
  have hβbase : β.1.base = 𝟙 W :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
      (J := J) hSheaf D A I a K k h.symm
  let hKA : 𝟙 W ≫ IK.f ≫ α.1.base = 𝟙 W ≫ IA.f := by
    rw [hαbase]
    dsimp [IA, IK, projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentDatumExplicitPullbackArrow]
    simp
  let hAK : 𝟙 W ≫ IA.f ≫ β.1.base = 𝟙 W ≫ IK.f := by
    rw [hβbase]
    dsimp [IA, IK, projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentDatumExplicitPullbackArrow]
    simp
  let hKK : 𝟙 W ≫ IK.f ≫ (α.1.base ≫ β.1.base) = 𝟙 W ≫ IK.f := by
    calc
      𝟙 W ≫ IK.f ≫ (α.1.base ≫ β.1.base) =
          𝟙 W ≫ IA.f ≫ β.1.base := by
            simpa [Category.assoc] using congrArg (fun q => q ≫ β.1.base) hKA
      _ = 𝟙 W ≫ IK.f := hAK
  have hcompComponent :
      α.1.components.toHomOver.family IK IA (𝟙 W) (𝟙 W) hKA ≫
          β.1.components.toHomOver.family IA IK (𝟙 W) (𝟙 W) hAK =
        (Hom.compose (J := J) hSheaf α.1 β.1).components.toHomOver.family
          IK IK (𝟙 W) (𝟙 W) hKK := by
    exact Hom.compose_component_eq_of_middle (J := J) hSheaf α.1 β.1
      IK IA IK (𝟙 W) (𝟙 W) (𝟙 W) hKA hAK
  have hhom : α ≫ β = 𝟙 EK := by
    simpa [α, β, EK] using
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_comp_realization_self
        (J := J) hSheaf D I K k A a h
  let componentOf (δ : EK ⟶ EK) :
      EK.1.object.restrictedLocalObject IK (𝟙 W) ⟶
        EK.1.object.restrictedLocalObject IK (𝟙 W) := by
    letI : P.IsHomLift (𝟙 W) δ.1 := δ.2
    have hbase : δ.1.base = 𝟙 W := by
      have hfac := IsHomLift.fac' P (𝟙 W) δ.1
      simpa [P, projectionFunctor] using hfac
    exact δ.1.components.toHomOver.family IK IK (𝟙 W) (𝟙 W) (by
      rw [hbase]
      dsimp [IK, projectionDescentDatumExplicitPullbackArrow]
      change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
      simp)
  have hcomponent := congrArg componentOf hhom
  dsimp [componentOf] at hcomponent
  let hId : 𝟙 W ≫ IK.f ≫ (DescentCompletionObject.identity (J := J) EK.1).base =
      𝟙 W ≫ IK.f := by
    dsimp [DescentCompletionObject.identity]
    change 𝟙 W ≫ IK.f ≫ 𝟙 W = 𝟙 W ≫ IK.f
    rw [Category.comp_id]
  have hcomponent' :
      (Hom.compose (J := J) hSheaf α.1 β.1).components.toHomOver.family
          IK IK (𝟙 W) (𝟙 W) hKK =
        (DescentCompletionObject.identity (J := J) EK.1).components.toHomOver.family
          IK IK (𝟙 W) (𝟙 W) hId := by
    simpa [P, α, β, EK, IK, hKK, hId] using hcomponent
  dsimp [projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover,
    projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner]
  change α.1.components.toHomOver.family IK IA (𝟙 W) (𝟙 W) _ ≫
      β.1.components.toHomOver.family IA IK (𝟙 W) (𝟙 W) _ =
    𝟙 (EK.1.object.restrictedLocalObject IK (𝟙 W))
  rw [hcompComponent]
  rw [hcomponent']
  dsimp [DescentCompletionObject.identity, DescentCompletionObjectOver.NaturalHomOver.id,
    DescentCompletionObjectOver.idHomOver]
  simpa [P, α, β, EK, IK,
    DescentCompletionObjectOver.NaturalHomOver.id, DescentCompletionObjectOver.idHomOver,
    explicitPullbackFiberObject, projectionDescentDatumObject,
    DescentCompletionObjectOver.pullback, DescentCompletionObjectOver.restrictedLocalObject,
    projectionDescentDatumExplicitPullbackArrow,
    DescentCompletionObjectOver.pullbackCoverBaseArrow,
    DescentCompletionObjectOver.overlapIso_self_hom]

/-- Actual realization-component form of
`rho_(b,j),(a,i) ; rho_(a,i),(b,j) = id` on the total-cover side. -/
theorem projectionDescentRealizationComponentFromTotalCoverToDatumInner_comp_inverse_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f) :
    projectionDescentRealizationComponentFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K k h ≫
      projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a h.symm =
    𝟙 ((projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).restrictedLocalObject
        (projectionDescentTotalCoverInner (J := J) hSheaf D A) a) := by
  let tA := projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a
  let eA := projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
    (J := J) hSheaf D A a
  let cAK := projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner
    (J := J) hSheaf D A I a K k h
  let eK := projectionDescentDatumExplicitPullbackArrowRestrictionIso
    (J := J) hSheaf D I K k
  let lK := projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k
  let cKA := projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
    (J := J) hSheaf D I K k A a h.symm
  have hmid : cAK ≫ cKA = 𝟙 _ := by
    simpa [cAK, cKA] using
      projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner_comp_inverse_self
        (J := J) hSheaf D A I a K k h
  dsimp [projectionDescentRealizationComponentFromTotalCoverToDatumInner,
    projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover]
  change (tA.hom ≫ eA.inv ≫ cAK ≫ eK.hom ≫ lK.inv) ≫
      lK.hom ≫ eK.inv ≫ cKA ≫ eA.hom ≫ tA.inv = 𝟙 _
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [Iso.hom_inv_id_assoc]
  calc
    tA.hom ≫ eA.inv ≫ cAK ≫ cKA ≫ eA.hom ≫ tA.inv =
        tA.hom ≫ eA.inv ≫ (cAK ≫ cKA) ≫ eA.hom ≫ tA.inv := by
        simp [Category.assoc]
    _ = tA.hom ≫ eA.inv ≫ 𝟙 _ ≫ eA.hom ≫ tA.inv := by
        rw [hmid]
    _ = tA.hom ≫ eA.inv ≫ eA.hom ≫ tA.inv := by
        simp
    _ = tA.hom ≫ (eA.inv ≫ eA.hom) ≫ tA.inv := by
        simp
    _ = tA.hom ≫ 𝟙 _ ≫ tA.inv := by
        rw [eA.inv_hom_id]
    _ = tA.hom ≫ tA.inv := by
        simp
    _ = 𝟙 _ := tA.hom_inv_id

/-- Actual realization-component form of
`rho_(a,i),(b,j) ; rho_(b,j),(a,i) = id` on the datum-inner side. -/
theorem projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_comp_realization_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f) :
    projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a h ≫
      projectionDescentRealizationComponentFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K k h.symm =
    𝟙 ((projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject K k) := by
  let lK := projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k
  let eK := projectionDescentDatumExplicitPullbackArrowRestrictionIso
    (J := J) hSheaf D I K k
  let cKA := projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
    (J := J) hSheaf D I K k A a h
  let eA := projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
    (J := J) hSheaf D A a
  let tA := projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a
  let cAK := projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner
    (J := J) hSheaf D A I a K k h.symm
  have hmid : cKA ≫ cAK = 𝟙 _ := by
    simpa [cKA, cAK] using
      projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover_comp_realization_self
        (J := J) hSheaf D I K k A a h
  dsimp [projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover,
    projectionDescentRealizationComponentFromTotalCoverToDatumInner]
  change (lK.hom ≫ eK.inv ≫ cKA ≫ eA.hom ≫ tA.inv) ≫
      tA.hom ≫ eA.inv ≫ cAK ≫ eK.hom ≫ lK.inv = 𝟙 _
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [Iso.hom_inv_id_assoc]
  calc
    lK.hom ≫ eK.inv ≫ cKA ≫ cAK ≫ eK.hom ≫ lK.inv =
        lK.hom ≫ eK.inv ≫ (cKA ≫ cAK) ≫ eK.hom ≫ lK.inv := by
        simp [Category.assoc]
    _ = lK.hom ≫ eK.inv ≫ 𝟙 _ ≫ eK.hom ≫ lK.inv := by
        rw [hmid]
    _ = lK.hom ≫ eK.inv ≫ eK.hom ≫ lK.inv := by
        simp
    _ = lK.hom ≫ (eK.inv ≫ eK.hom) ≫ lK.inv := by
        simp
    _ = lK.hom ≫ 𝟙 _ ≫ lK.inv := by
        rw [eK.inv_hom_id]
    _ = lK.hom ≫ lK.inv := by
        simp
    _ = 𝟙 _ := lK.hom_inv_id

/-- Pulled-back realization-component form of
`Lambda_I ; Lambda_I^{-1} = id`, on one visible source and middle component. -/
theorem projectionDescentRealizationComponent_comp_inverse_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (A : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    {W : C} (a : W ⟶ A.Y) (k : W ⟶ K.Y)
    (h : a ≫ A.f ≫ 𝟙 I.Y = k ≫ K.f) :
    projectionDescentRealizationComponent (J := J)
        hSheaf D hPull hComp I A K a k h ≫
      projectionDescentRealizationInverseComponent (J := J)
        hSheaf D hPull hComp I K A k a (by simpa [Category.assoc] using h.symm) =
    𝟙 ((DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).restrictedLocalObject A a) := by
  let G :=
    (projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D hPull hComp).object
  let Atot := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A
  let htotal : a ≫ Atot.f = k ≫ K.f ≫ I.f := by
    dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      a ≫ A.f ≫ I.f = (a ≫ A.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (k ≫ K.f) ≫ I.f := by rw [h]
      _ = k ≫ K.f ≫ I.f := by simp [Category.assoc]
  let hinv : k ≫ K.f ≫ 𝟙 I.Y = a ≫ A.f := by
    simpa [Category.assoc] using h.symm
  have hcomp :=
    projectionDescentRealizationComponent_eq_fromTotalCoverToDatumInner
      (J := J) hSheaf D hPull hComp I A K a k h
  have hinvcomp :=
    projectionDescentRealizationInverseComponent_eq_fromDatumInnerToTotalCover
      (J := J) hSheaf D hPull hComp I K A k a hinv
  rw [hcomp, hinvcomp]
  simpa [G, Atot, htotal, hinv] using
    projectionDescentRealizationComponentFromTotalCoverToDatumInner_comp_inverse_self
      (J := J) hSheaf D Atot I a K k htotal

/-- Pulled-backed realization-component form of
`Lambda_I^{-1} ; Lambda_I = id`, on one visible middle and source component. -/
theorem projectionDescentRealizationInverseComponent_comp_realization_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (A : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    {W : C} (k : W ⟶ K.Y) (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ 𝟙 I.Y = a ≫ A.f) :
    projectionDescentRealizationInverseComponent (J := J)
        hSheaf D hPull hComp I K A k a h ≫
      projectionDescentRealizationComponent (J := J)
        hSheaf D hPull hComp I A K a k (by simpa [Category.assoc] using h.symm) =
    𝟙 ((projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject K k) := by
  let G :=
    (projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D hPull hComp).object
  let Atot := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A
  let htotal : k ≫ K.f ≫ I.f = a ≫ Atot.f := by
    dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      k ≫ K.f ≫ I.f = (k ≫ K.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (a ≫ A.f) ≫ I.f := by rw [h]
      _ = a ≫ A.f ≫ I.f := by simp [Category.assoc]
  let hreal : a ≫ A.f ≫ 𝟙 I.Y = k ≫ K.f := by
    simpa [Category.assoc] using h.symm
  have hinvcomp :=
    projectionDescentRealizationInverseComponent_eq_fromDatumInnerToTotalCover
      (J := J) hSheaf D hPull hComp I K A k a h
  have hcomp :=
    projectionDescentRealizationComponent_eq_fromTotalCoverToDatumInner
      (J := J) hSheaf D hPull hComp I A K a k hreal
  rw [hinvcomp, hcomp]
  simpa [G, Atot, htotal, hreal] using
    projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_comp_realization_self
      (J := J) hSheaf D I K k Atot a htotal

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
