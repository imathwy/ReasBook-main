import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.SharedCore
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.LocalRefinement

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

/-- Iterating the explicit base-change object and then comparing with Lean's canonical pullback is
canonically isomorphic to rebuilding the explicit base-change object for the composite base map.
This is the owner-level bridge behind the source proof's silent identification
`(X_a|_W)|_{W'} = X_a|_{W'}`. -/
noncomputable def explicitPullbackFiberObjectCompIso
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (O : DescentCompletionObject (J := J) X)
    {W W' : C} (i : W ⟶ O.base) (g : W' ⟶ W) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    explicitPullbackFiberObject (J := J) hSheaf O (g ≫ i) ≅
      g ^*[canonicalPullbackChoice P]
        (explicitPullbackFiberObject (J := J) hSheaf O i) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let oldObj : P.Fiber W := explicitPullbackFiberObject (J := J) hSheaf O i
  let directObj : P.Fiber W' := explicitPullbackFiberObject (J := J) hSheaf O (g ≫ i)
  let canonObj : P.Fiber W' := g ^*[canonicalPullbackChoice P] oldObj
  let φold : oldObj.1 ⟶ O := pullbackMap (J := J) O i
  let φdirect : directObj.1 ⟶ O := pullbackMap (J := J) O (g ≫ i)
  let k : canonObj.1 ⟶ oldObj.1 := (canonicalPullbackChoice P).map g oldObj
  have hk : P.IsStronglyCartesian g k := by
    simpa [P, k, canonObj, oldObj] using
      (canonicalPullbackChoice P).isStronglyCartesian g oldObj
  have hφold : P.IsStronglyCartesian i φold := by
    simpa [P, φold, oldObj] using
      pullbackMap_isStronglyCartesian (J := J) hSheaf O i
  have hφdirect : P.IsStronglyCartesian (g ≫ i) φdirect := by
    simpa [P, φdirect, directObj] using
      pullbackMap_isStronglyCartesian (J := J) hSheaf O (g ≫ i)
  letI : P.IsStronglyCartesian g k := hk
  letI : P.IsStronglyCartesian i φold := hφold
  have hcomp : P.IsStronglyCartesian (g ≫ i) (k ≫ φold) := by infer_instance
  letI : P.IsStronglyCartesian (g ≫ i) (k ≫ φold) := hcomp
  letI : P.IsStronglyCartesian (g ≫ i) φdirect := hφdirect
  let e : directObj.1 ≅ canonObj.1 :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ P
      _ _ _ _ _ _ (g ≫ i) (g ≫ i) (Iso.refl W')
      (show g ≫ i = (Iso.refl W').hom ≫ (g ≫ i) by simp)
      (k ≫ φold) φdirect hcomp hφdirect
  have hhom : P.IsHomLift (𝟙 W') e.hom := by
    change P.IsHomLift (Iso.refl W').hom e.hom
    exact
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ P
        _ _ _ _ _ _ (g ≫ i) (g ≫ i) (Iso.refl W')
        (show g ≫ i = (Iso.refl W').hom ≫ (g ≫ i) by simp)
        (k ≫ φold) φdirect hcomp hφdirect)
  have hinv : P.IsHomLift (𝟙 W') e.inv := by
    change P.IsHomLift (Iso.refl W').hom e.inv
    exact
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _ P
        _ _ _ _ _ _ (g ≫ i) (g ≫ i) (Iso.refl W')
        (show g ≫ i = (Iso.refl W').hom ≫ (g ≫ i) by simp)
        (k ≫ φold) φdirect hcomp hφdirect)
  exact
    { hom := Functor.Fiber.homMk P W' e.hom
      inv := Functor.Fiber.homMk P W' e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }

set_option backward.isDefEq.respectTransparency false in
/-- The iterated-explicit-pullback bridge is characterized by the strongly-cartesian triangle:
after the canonical pullback projection and the old explicit projection, it is the direct explicit
projection for the composite base map. -/
theorem explicitPullbackFiberObjectCompIso_hom_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (O : DescentCompletionObject (J := J) X)
    {W W' : C} (i : W ⟶ O.base) (g : W' ⟶ W) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    (explicitPullbackFiberObjectCompIso (J := J) hSheaf O i g).hom.1 ≫
        (canonicalPullbackChoice P).map g
          (explicitPullbackFiberObject (J := J) hSheaf O i) ≫
        pullbackMap (J := J) O i =
      pullbackMap (J := J) O (g ≫ i) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let oldObj : P.Fiber W := explicitPullbackFiberObject (J := J) hSheaf O i
  let directObj : P.Fiber W' := explicitPullbackFiberObject (J := J) hSheaf O (g ≫ i)
  let canonObj : P.Fiber W' := g ^*[canonicalPullbackChoice P] oldObj
  let φold : oldObj.1 ⟶ O := pullbackMap (J := J) O i
  let φdirect : directObj.1 ⟶ O := pullbackMap (J := J) O (g ≫ i)
  let k : canonObj.1 ⟶ oldObj.1 := (canonicalPullbackChoice P).map g oldObj
  have hk : P.IsStronglyCartesian g k := by
    simpa [P, k, canonObj, oldObj] using
      (canonicalPullbackChoice P).isStronglyCartesian g oldObj
  have hφold : P.IsStronglyCartesian i φold := by
    simpa [P, φold, oldObj] using
      pullbackMap_isStronglyCartesian (J := J) hSheaf O i
  have hφdirect : P.IsStronglyCartesian (g ≫ i) φdirect := by
    simpa [P, φdirect, directObj] using
      pullbackMap_isStronglyCartesian (J := J) hSheaf O (g ≫ i)
  letI : P.IsStronglyCartesian g k := hk
  letI : P.IsStronglyCartesian i φold := hφold
  have hcomp : P.IsStronglyCartesian (g ≫ i) (k ≫ φold) := by infer_instance
  letI : P.IsStronglyCartesian (g ≫ i) (k ≫ φold) := hcomp
  letI : P.IsStronglyCartesian (g ≫ i) φdirect := hφdirect
  let e : directObj.1 ≅ canonObj.1 :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ P
      _ _ _ _ _ _ (g ≫ i) (g ≫ i) (Iso.refl W')
      (show g ≫ i = (Iso.refl W').hom ≫ (g ≫ i) by simp)
      (k ≫ φold) φdirect hcomp hφdirect
  have hfac : e.hom ≫ (k ≫ φold) = φdirect := by
    change
      (Functor.IsStronglyCartesian.domainIsoOfBaseIso
        (p := P) (show g ≫ i = (Iso.refl W').hom ≫ (g ≫ i) by simp)
        (k ≫ φold) φdirect).hom ≫ (k ≫ φold) = φdirect
    rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
    exact Functor.IsStronglyCartesian.fac P (g ≫ i) (k ≫ φold)
      (show g ≫ i = (Iso.refl W').hom ≫ (g ≫ i) by simp) φdirect
  dsimp [explicitPullbackFiberObjectCompIso]
  change e.hom ≫ k ≫ φold = φdirect
  simpa [Category.assoc] using hfac

/-- Equality-transported version of `explicitPullbackFiberObjectCompIso`.  This is the practical
owner bridge when the composite base map is definitionally written in a different but equal form,
for example `(g ≫ a) ≫ i = g ≫ (a ≫ i)`. -/
noncomputable def explicitPullbackFiberObjectCompIsoOfEq
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (O : DescentCompletionObject (J := J) X)
    {W W' : C} (i : W ⟶ O.base) (g : W' ⟶ W)
    (i' : W' ⟶ O.base) (hi : g ≫ i = i') :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    explicitPullbackFiberObject (J := J) hSheaf O i' ≅
      g ^*[canonicalPullbackChoice P]
        (explicitPullbackFiberObject (J := J) hSheaf O i) :=
  (eqToIso (by rw [hi]) : explicitPullbackFiberObject (J := J) hSheaf O (g ≫ i) ≅
    explicitPullbackFiberObject (J := J) hSheaf O i').symm ≪≫
      explicitPullbackFiberObjectCompIso (J := J) hSheaf O i g

set_option backward.isDefEq.respectTransparency false in
/-- The equality-transported iterated-pullback bridge satisfies the same cartesian triangle as
`explicitPullbackFiberObjectCompIso`. -/
theorem explicitPullbackFiberObjectCompIsoOfEq_hom_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (O : DescentCompletionObject (J := J) X)
    {W W' : C} (i : W ⟶ O.base) (g : W' ⟶ W)
    (i' : W' ⟶ O.base) (hi : g ≫ i = i') :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    (explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf O i g i' hi).hom.1 ≫
        (canonicalPullbackChoice P).map g
          (explicitPullbackFiberObject (J := J) hSheaf O i) ≫
        pullbackMap (J := J) O i =
      pullbackMap (J := J) O i' := by
  subst i'
  simpa [explicitPullbackFiberObjectCompIsoOfEq] using
    explicitPullbackFiberObjectCompIso_hom_fac (J := J) hSheaf O i g

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the equality-transported iterated-pullback bridge is characterized by the
opposite cartesian triangle. -/
theorem explicitPullbackFiberObjectCompIsoOfEq_inv_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (O : DescentCompletionObject (J := J) X)
    {W W' : C} (i : W ⟶ O.base) (g : W' ⟶ W)
    (i' : W' ⟶ O.base) (hi : g ≫ i = i') :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    (explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf O i g i' hi).inv.1 ≫
        pullbackMap (J := J) O i' =
      (canonicalPullbackChoice P).map g
          (explicitPullbackFiberObject (J := J) hSheaf O i) ≫
        pullbackMap (J := J) O i := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let e := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf O i g i' hi
  have hfac := explicitPullbackFiberObjectCompIsoOfEq_hom_fac
    (J := J) hSheaf O i g i' hi
  have hcancel : e.inv.1 ≫ e.hom.1 = 𝟙 _ := by
    exact congrArg Subtype.val e.inv_hom_id
  calc
    e.inv.1 ≫ pullbackMap (J := J) O i' =
        e.inv.1 ≫ (e.hom.1 ≫
          (canonicalPullbackChoice P).map g
            (explicitPullbackFiberObject (J := J) hSheaf O i) ≫
          pullbackMap (J := J) O i) := by
          rw [hfac]
    _ = (e.inv.1 ≫ e.hom.1) ≫
          (canonicalPullbackChoice P).map g
            (explicitPullbackFiberObject (J := J) hSheaf O i) ≫
          pullbackMap (J := J) O i := by simp [Category.assoc]
    _ = (canonicalPullbackChoice P).map g
          (explicitPullbackFiberObject (J := J) hSheaf O i) ≫
        pullbackMap (J := J) O i := by simp [hcancel]

/-- Source stage 3.13 owner bridge: after replacing the repackaged outer object `X_a` by the
original fibre object from the outer descent datum, the explicit pullback object is still
isomorphic to Lean's canonical pullback choice. -/
theorem projectionDescentDatumPullbackIsoCanonicalOriginal_nonempty
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) (I : S.Arrow)
    (i : W ⟶ I.Y) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    Nonempty
      (explicitPullbackFiberObject (J := J) hSheaf
          (projectionDescentDatumObject (J := J) hSheaf D I) i ≅
        i ^*[canonicalPullbackChoice P] (D.obj I)) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  obtain ⟨e⟩ :=
    projectionDescentDatumPullbackIsoCanonical_nonempty
      (J := J) hSheaf D I i
  refine ⟨e ≪≫ ?_⟩
  exact eqToIso (by
    rw [projectionDescentDatumObject_fiber_eq (J := J) hSheaf D I])

/-- Source stage 3.13 canonical owner bridge: the explicit pullback object is compared with
Lean's canonical pullback choice by the uniqueness of strongly cartesian arrows, using the
explicit cartesian map `pullbackMap`.  Unlike the `Nonempty` wrapper above, this concrete iso has
the coherence data needed for later restriction arguments. -/
noncomputable def projectionDescentDatumPullbackIsoCanonicalOriginal
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) (I : S.Arrow)
    (i : W ⟶ I.Y) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D I) i ≅
      i ^*[canonicalPullbackChoice P] (D.obj I) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let O := projectionDescentDatumObject (J := J) hSheaf D I
  let φ := pullbackMap (J := J) O i
  have hφ : P.IsStronglyCartesian i φ :=
    pullbackMap_isStronglyCartesian (J := J) hSheaf O i
  let yFiber : P.Fiber I.Y :=
    projectionFiberObject (J := J) hSheaf O
  let canonicalY : P.Fiber W :=
    i ^*[canonicalPullbackChoice P] yFiber
  let pulledY : P.Fiber W :=
    explicitPullbackFiberObject (J := J) hSheaf O i
  let k : canonicalY.1 ⟶ O := (canonicalPullbackChoice P).map i yFiber
  have hk : P.IsStronglyCartesian i k := by
    simpa [P, k, yFiber, canonicalY] using
      (canonicalPullbackChoice P).isStronglyCartesian i yFiber
  letI : P.IsStronglyCartesian i k := hk
  letI : P.IsStronglyCartesian i φ := hφ
  let e : pulledY.1 ≅ canonicalY.1 :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ P
      _ _ _ _ _ _ i i (Iso.refl W)
      (show i = (Iso.refl W).hom ≫ i by simp)
      k φ hk hφ
  have hhom : P.IsHomLift (𝟙 W) e.hom := by
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ P
        _ _ _ _ _ _ i i (Iso.refl W)
        (show i = (Iso.refl W).hom ≫ i by simp)
        k φ hk hφ)
  have hinv : P.IsHomLift (𝟙 W) e.inv := by
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _ P
        _ _ _ _ _ _ i i (Iso.refl W)
        (show i = (Iso.refl W).hom ≫ i by simp)
        k φ hk hφ)
  let eFiber : pulledY ≅ canonicalY :=
    { hom := Functor.Fiber.homMk P W e.hom
      inv := Functor.Fiber.homMk P W e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }
  exact eFiber ≪≫ eqToIso (by
    simp [canonicalY, yFiber, O,
      projectionDescentDatumObject_fiber_eq (J := J) hSheaf D I])

set_option backward.isDefEq.respectTransparency false in
/-- The concrete canonical-owner bridge used for outer descent components is characterized by
the strongly-cartesian triangle: after composing with the canonical pullback map, it is the
explicit pullback projection, transported from the repackaged outer object back to the original
outer descent object owner. -/
theorem projectionDescentDatumPullbackIsoCanonicalOriginal_hom_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) (I : S.Arrow)
    (i : W ⟶ I.Y) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    ((projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I i).hom.1 ≫
        (canonicalPullbackChoice P).map i (D.obj I)) =
      pullbackMap (J := J)
        (projectionDescentDatumObject (J := J) hSheaf D I) i ≫
        eqToHom (congrArg Subtype.val
          (projectionDescentDatumObject_fiber_eq (J := J) hSheaf D I)) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let O := projectionDescentDatumObject (J := J) hSheaf D I
  let φ := pullbackMap (J := J) O i
  have hφ : P.IsStronglyCartesian i φ :=
    pullbackMap_isStronglyCartesian (J := J) hSheaf O i
  let yFiber : P.Fiber I.Y :=
    projectionFiberObject (J := J) hSheaf O
  let canonicalY : P.Fiber W :=
    i ^*[canonicalPullbackChoice P] yFiber
  let pulledY : P.Fiber W :=
    explicitPullbackFiberObject (J := J) hSheaf O i
  let k : canonicalY.1 ⟶ O := (canonicalPullbackChoice P).map i yFiber
  have hk : P.IsStronglyCartesian i k := by
    simpa [P, k, yFiber, canonicalY] using
      (canonicalPullbackChoice P).isStronglyCartesian i yFiber
  letI : P.IsStronglyCartesian i k := hk
  letI : P.IsStronglyCartesian i φ := hφ
  let e : pulledY.1 ≅ canonicalY.1 :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ P
      _ _ _ _ _ _ i i (Iso.refl W)
      (show i = (Iso.refl W).hom ≫ i by simp)
      k φ hk hφ
  have hfac : e.hom ≫ k = φ := by
    change
      (Functor.IsStronglyCartesian.domainIsoOfBaseIso
        (p := P) (show i = (Iso.refl W).hom ≫ i by simp) k φ).hom ≫ k = φ
    rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
    exact Functor.IsStronglyCartesian.fac P i k
      (show i = (Iso.refl W).hom ≫ i by simp) φ
  have hhom : P.IsHomLift (𝟙 W) e.hom := by
    change P.IsHomLift (Iso.refl W).hom e.hom
    exact
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ P
        _ _ _ _ _ _ i i (Iso.refl W)
        (show i = (Iso.refl W).hom ≫ i by simp)
        k φ hk hφ)
  letI : P.IsHomLift (𝟙 W) e.hom := hhom
  let hFiber : yFiber = D.obj I :=
    projectionDescentDatumObject_fiber_eq (J := J) hSheaf D I
  let hCanonical : canonicalY = i ^*[canonicalPullbackChoice P] (D.obj I) := by
    simpa [canonicalY] using
      congrArg (fun z : P.Fiber I.Y => i ^*[canonicalPullbackChoice P] z) hFiber
  have htransport :
      (eqToHom hCanonical : canonicalY ⟶ i ^*[canonicalPullbackChoice P] (D.obj I)).1 ≫
        (canonicalPullbackChoice P).map i (D.obj I) =
      k ≫ eqToHom (congrArg Subtype.val hFiber) := by
    simpa [hCanonical, k, canonicalY] using
      canonicalPullbackChoice_map_eqToHom (C := C) P i hFiber
  dsimp [projectionDescentDatumPullbackIsoCanonicalOriginal]
  change (e.hom ≫
      (eqToHom hCanonical : canonicalY ⟶ i ^*[canonicalPullbackChoice P] (D.obj I)).1) ≫
        (canonicalPullbackChoice P).map i (D.obj I) =
    φ ≫ eqToHom (congrArg Subtype.val hFiber)
  rw [Category.assoc, htransport, ← Category.assoc, hfac]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the concrete canonical-owner bridge is characterized by the opposite
cartesian triangle. -/
theorem projectionDescentDatumPullbackIsoCanonicalOriginal_inv_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) (I : S.Arrow)
    (i : W ⟶ I.Y) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    let O := projectionDescentDatumObject (J := J) hSheaf D I
    let hFiber : projectionFiberObject (J := J) hSheaf O = D.obj I :=
      projectionDescentDatumObject_fiber_eq (J := J) hSheaf D I
    (projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I i).inv.1 ≫
        pullbackMap (J := J) O i ≫
        eqToHom (congrArg Subtype.val hFiber) =
      (canonicalPullbackChoice P).map i (D.obj I) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let O := projectionDescentDatumObject (J := J) hSheaf D I
  let hFiber : projectionFiberObject (J := J) hSheaf O = D.obj I :=
    projectionDescentDatumObject_fiber_eq (J := J) hSheaf D I
  let e := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I i
  have hfac := projectionDescentDatumPullbackIsoCanonicalOriginal_hom_fac
    (J := J) hSheaf D I i
  have hcancel : e.inv.1 ≫ e.hom.1 = 𝟙 _ := by
    exact congrArg Subtype.val e.inv_hom_id
  calc
    e.inv.1 ≫ pullbackMap (J := J) O i ≫ eqToHom (congrArg Subtype.val hFiber) =
        e.inv.1 ≫ (e.hom.1 ≫ (canonicalPullbackChoice P).map i (D.obj I)) := by
          rw [← hfac]
    _ = (e.inv.1 ≫ e.hom.1) ≫ (canonicalPullbackChoice P).map i (D.obj I) := by
          rw [Category.assoc]
    _ = (canonicalPullbackChoice P).map i (D.obj I) := by simp [hcancel]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.13 owner naturality: restricting the explicit-to-canonical bridge for an
outer descent object agrees with the bridge rebuilt on the smaller base, followed by the canonical
pseudofunctor composition comparison.  This is the precise Lean form of the source proof's
identification `((x_a)|_W)|_{W'} = (x_a)|_{W'}` for one outer component. -/
theorem projectionDescentDatumPullbackIsoCanonicalOriginal_hom_naturality
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W W' : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) (I : S.Arrow)
    (i : W ⟶ I.Y) (g : W' ⟶ W) (i' : W' ⟶ I.Y) (hi : g ≫ i = i') :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    let O := projectionDescentDatumObject (J := J) hSheaf D I
    let eOld := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I i
    let eNew := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I i'
    let eComp := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf O i g i' hi
    let κ := ((canonicalFiberPseudofunctor P).mapComp' i.op.toLoc g.op.toLoc i'.op.toLoc
      (comp_toLoc_eq i g i' hi)).hom.toNatTrans.app (D.obj I)
    eComp.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOld.hom =
      eNew.hom ≫ κ := by
  subst i'
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let O := projectionDescentDatumObject (J := J) hSheaf D I
  let oldObj : P.Fiber W := explicitPullbackFiberObject (J := J) hSheaf O i
  let directObj : P.Fiber W' := explicitPullbackFiberObject (J := J) hSheaf O (g ≫ i)
  let canonOld : P.Fiber W := i ^*[canonicalPullbackChoice P] (D.obj I)
  let targetObj : P.Fiber W' := g ^*[canonicalPullbackChoice P] canonOld
  let eOld := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I i
  let eNew := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I (g ≫ i)
  let eComp := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf O i g (g ≫ i) rfl
  let κ := ((canonicalFiberPseudofunctor P).mapComp' i.op.toLoc g.op.toLoc (g ≫ i).op.toLoc
      (comp_toLoc_eq i g (g ≫ i) rfl)).hom.toNatTrans.app (D.obj I)
  let mapOld := ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOld.hom
  let targetMap : targetObj.1 ⟶ (D.obj I).1 :=
    (canonicalPullbackChoice P).map g canonOld ≫
      (canonicalPullbackChoice P).map i (D.obj I)
  have htarget : P.IsStronglyCartesian (g ≫ i) targetMap := by
    let kg : targetObj.1 ⟶ canonOld.1 := (canonicalPullbackChoice P).map g canonOld
    let ki : canonOld.1 ⟶ (D.obj I).1 := (canonicalPullbackChoice P).map i (D.obj I)
    have hg : P.IsStronglyCartesian g kg := by
      simpa [P, kg, targetObj, canonOld] using
        (canonicalPullbackChoice P).isStronglyCartesian g canonOld
    have hiCart : P.IsStronglyCartesian i ki := by
      simpa [P, ki, canonOld] using
        (canonicalPullbackChoice P).isStronglyCartesian i (D.obj I)
    letI : P.IsStronglyCartesian g kg := hg
    letI : P.IsStronglyCartesian i ki := hiCart
    change P.IsStronglyCartesian (g ≫ i) (kg ≫ ki)
    exact inferInstance
  let lhs : directObj ⟶ targetObj := eComp.hom ≫ mapOld
  let rhs : directObj ⟶ targetObj := eNew.hom ≫ κ
  change lhs = rhs
  apply Functor.Fiber.hom_ext
  change lhs.1 = rhs.1
  have hLiftL : P.IsHomLift (𝟙 W') lhs.1 := lhs.2
  have hLiftR : P.IsHomLift (𝟙 W') rhs.1 := rhs.2
  exact Functor.IsStronglyCartesian.ext P (g ≫ i) targetMap (𝟙 W')
    (ψ := lhs.1) (ψ' := rhs.1) (by
  change (eComp.hom.1 ≫ mapOld.1) ≫ targetMap = (eNew.hom.1 ≫ κ.1) ≫ targetMap
  calc
    (eComp.hom.1 ≫ mapOld.1) ≫ targetMap =
        eComp.hom.1 ≫ (mapOld.1 ≫ (canonicalPullbackChoice P).map g canonOld) ≫
          (canonicalPullbackChoice P).map i (D.obj I) := by
          simp [targetMap, Category.assoc]
    _ = eComp.hom.1 ≫
          ((canonicalPullbackChoice P).map g oldObj ≫ eOld.hom.1) ≫
          (canonicalPullbackChoice P).map i (D.obj I) := by
          rw [canonical_pullbackFunctor_map_fac (p := P) (f := g) (φ := eOld.hom)]
    _ = eComp.hom.1 ≫
          (canonicalPullbackChoice P).map g oldObj ≫
          (eOld.hom.1 ≫ (canonicalPullbackChoice P).map i (D.obj I)) := by
          simp [Category.assoc]
    _ = eComp.hom.1 ≫
          (canonicalPullbackChoice P).map g oldObj ≫
          (pullbackMap (J := J) O i ≫
            eqToHom (congrArg Subtype.val
              (projectionDescentDatumObject_fiber_eq (J := J) hSheaf D I))) := by
          rw [projectionDescentDatumPullbackIsoCanonicalOriginal_hom_fac (J := J) hSheaf D I i]
    _ = (eComp.hom.1 ≫
          (canonicalPullbackChoice P).map g oldObj ≫
          pullbackMap (J := J) O i) ≫
          eqToHom (congrArg Subtype.val
            (projectionDescentDatumObject_fiber_eq (J := J) hSheaf D I)) := by
          simp [Category.assoc]
    _ = pullbackMap (J := J) O (g ≫ i) ≫
          eqToHom (congrArg Subtype.val
            (projectionDescentDatumObject_fiber_eq (J := J) hSheaf D I)) := by
          rw [explicitPullbackFiberObjectCompIsoOfEq_hom_fac (J := J) hSheaf O i g (g ≫ i) rfl]
    _ = eNew.hom.1 ≫ (canonicalPullbackChoice P).map (g ≫ i) (D.obj I) := by
          rw [projectionDescentDatumPullbackIsoCanonicalOriginal_hom_fac (J := J) hSheaf D I (g ≫ i)]
    _ = eNew.hom.1 ≫
          (κ.1 ≫ (canonicalPullbackChoice P).map g canonOld ≫
            (canonicalPullbackChoice P).map i (D.obj I)) := by
          rw [canonicalFiberPseudofunctor_mapComp'_hom_app_fac (p := P)
            (f := i) (g := g) (gf := g ≫ i) (hgf := rfl) (x := D.obj I)]
    _ = (eNew.hom.1 ≫ κ.1) ≫ targetMap := by
          simp [targetMap, Category.assoc])

set_option maxHeartbeats 800000 in
set_option linter.unnecessarySimpa false in
set_option backward.isDefEq.respectTransparency false in
/-- Inverse form of `projectionDescentDatumPullbackIsoCanonicalOriginal_hom_naturality`.  It is
proved directly by the same cartesian uniqueness argument, postcomposing with the direct explicit
pullback projection and the owner transport back to the original outer fibre object. -/
theorem projectionDescentDatumPullbackIsoCanonicalOriginal_inv_naturality
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W W' : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) (I : S.Arrow)
    (i : W ⟶ I.Y) (g : W' ⟶ W) (i' : W' ⟶ I.Y) (hi : g ≫ i = i') :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    let O := projectionDescentDatumObject (J := J) hSheaf D I
    let eOld := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I i
    let eNew := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I i'
    let eComp := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf O i g i' hi
    let κ := ((canonicalFiberPseudofunctor P).mapComp' i.op.toLoc g.op.toLoc i'.op.toLoc
      (comp_toLoc_eq i g i' hi)).inv.toNatTrans.app (D.obj I)
    ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOld.inv ≫ eComp.inv =
      κ ≫ eNew.inv := by
  subst i'
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let O := projectionDescentDatumObject (J := J) hSheaf D I
  let hFiber : projectionFiberObject (J := J) hSheaf O = D.obj I :=
    projectionDescentDatumObject_fiber_eq (J := J) hSheaf D I
  let oldObj : P.Fiber W := explicitPullbackFiberObject (J := J) hSheaf O i
  let canonOld : P.Fiber W := i ^*[canonicalPullbackChoice P] (D.obj I)
  let targetObj : P.Fiber W' := g ^*[canonicalPullbackChoice P] canonOld
  let directObj : P.Fiber W' := explicitPullbackFiberObject (J := J) hSheaf O (g ≫ i)
  let eOld := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I i
  let eNew := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I (g ≫ i)
  let eComp := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf O i g (g ≫ i) rfl
  let κ := ((canonicalFiberPseudofunctor P).mapComp' i.op.toLoc g.op.toLoc (g ≫ i).op.toLoc
      (comp_toLoc_eq i g (g ≫ i) rfl)).inv.toNatTrans.app (D.obj I)
  let mapOldInv := ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOld.inv
  let targetMap : directObj.1 ⟶ (D.obj I).1 :=
    pullbackMap (J := J) O (g ≫ i) ≫ eqToHom (congrArg Subtype.val hFiber)
  have htarget : P.IsStronglyCartesian (g ≫ i) targetMap := by
    let φ : directObj.1 ⟶ O := pullbackMap (J := J) O (g ≫ i)
    let eps : O ⟶ (D.obj I).1 := eqToHom (congrArg Subtype.val hFiber)
    have hφ : P.IsStronglyCartesian (g ≫ i) φ := by
      simpa [P, φ, directObj] using
        pullbackMap_isStronglyCartesian (J := J) hSheaf O (g ≫ i)
    have hO : P.obj O = I.Y := by
      simpa [P, O, projectionFunctor] using
        projectionDescentDatumObject_base (J := J) hSheaf D I
    have hepslift : P.IsHomLift (𝟙 I.Y) eps := by
      dsimp [eps]
      exact IsHomLift.eqToHom_domain_lift_id (p := P)
        (congrArg Subtype.val hFiber) hO
    have heps : P.IsStronglyCartesian (𝟙 I.Y) eps := by
      letI : P.IsHomLift (𝟙 I.Y) eps := hepslift
      exact Functor.IsStronglyCartesian.of_isIso P (𝟙 I.Y) eps
    letI : P.IsStronglyCartesian (g ≫ i) φ := hφ
    letI : P.IsStronglyCartesian (𝟙 I.Y) eps := heps
    have hcomp : P.IsStronglyCartesian ((g ≫ i) ≫ 𝟙 I.Y) (φ ≫ eps) := inferInstance
    simpa [targetMap, φ, eps] using hcomp
  let lhs : targetObj ⟶ directObj := mapOldInv ≫ eComp.inv
  let rhs : targetObj ⟶ directObj := κ ≫ eNew.inv
  change lhs = rhs
  apply Functor.Fiber.hom_ext
  change lhs.1 = rhs.1
  have hLiftL : P.IsHomLift (𝟙 W') lhs.1 := lhs.2
  have hLiftR : P.IsHomLift (𝟙 W') rhs.1 := rhs.2
  exact Functor.IsStronglyCartesian.ext P (g ≫ i) targetMap (𝟙 W')
    (ψ := lhs.1) (ψ' := rhs.1) (by
  change (mapOldInv.1 ≫ eComp.inv.1) ≫ targetMap = (κ.1 ≫ eNew.inv.1) ≫ targetMap
  calc
    (mapOldInv.1 ≫ eComp.inv.1) ≫ targetMap =
        mapOldInv.1 ≫ (eComp.inv.1 ≫ pullbackMap (J := J) O (g ≫ i)) ≫
          eqToHom (congrArg Subtype.val hFiber) := by
          simp [targetMap, Category.assoc]
    _ = mapOldInv.1 ≫
          ((canonicalPullbackChoice P).map g oldObj ≫ pullbackMap (J := J) O i) ≫
          eqToHom (congrArg Subtype.val hFiber) := by
          rw [explicitPullbackFiberObjectCompIsoOfEq_inv_fac (J := J) hSheaf O i g (g ≫ i) rfl]
    _ = (mapOldInv.1 ≫ (canonicalPullbackChoice P).map g oldObj) ≫
          pullbackMap (J := J) O i ≫ eqToHom (congrArg Subtype.val hFiber) := by
          simp [Category.assoc]
    _ = ((canonicalPullbackChoice P).map g canonOld ≫ eOld.inv.1) ≫
          pullbackMap (J := J) O i ≫ eqToHom (congrArg Subtype.val hFiber) := by
          rw [canonical_pullbackFunctor_map_fac (p := P) (f := g) (φ := eOld.inv)]
    _ = (canonicalPullbackChoice P).map g canonOld ≫
          (eOld.inv.1 ≫ pullbackMap (J := J) O i ≫ eqToHom (congrArg Subtype.val hFiber)) := by
          simp [Category.assoc]
    _ = (canonicalPullbackChoice P).map g canonOld ≫
          (canonicalPullbackChoice P).map i (D.obj I) := by
          rw [projectionDescentDatumPullbackIsoCanonicalOriginal_inv_fac (J := J) hSheaf D I i]
    _ = κ.1 ≫ (canonicalPullbackChoice P).map (g ≫ i) (D.obj I) := by
          rw [canonicalFiberPseudofunctor_mapComp'_inv_app_fac (p := P)
            (f := i) (g := g) (gf := g ≫ i) (hgf := rfl) (x := D.obj I)]
    _ = κ.1 ≫ (eNew.inv.1 ≫ pullbackMap (J := J) O (g ≫ i) ≫
          eqToHom (congrArg Subtype.val hFiber)) := by
          rw [projectionDescentDatumPullbackIsoCanonicalOriginal_inv_fac (J := J) hSheaf D I (g ≫ i)]
    _ = (κ.1 ≫ eNew.inv.1) ≫ targetMap := by
          simp [targetMap, Category.assoc])

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
