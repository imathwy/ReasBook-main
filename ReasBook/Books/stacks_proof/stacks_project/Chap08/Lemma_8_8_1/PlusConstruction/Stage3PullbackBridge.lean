import StacksProject_2024.Chap08.Lemma_8_8_1.BaseChange
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3LocalEssentialSurjectivity

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

/-- A completed descent object, viewed as an object of the fibre of the projection functor over
its base. -/
noncomputable abbrev projectionFiberObject
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X) :
    letI := category (J := J) hSheaf
    (projectionFunctor (J := J) hSheaf).Fiber D.base := by
  letI := category (J := J) hSheaf
  exact
    Functor.Fiber.mk (p := projectionFunctor (J := J) hSheaf)
      (show (projectionFunctor (J := J) hSheaf).obj D = D.base from rfl)

/-- The explicit base change `h^*D` from the source construction, viewed in the projection
fibre over the domain of `h`. -/
noncomputable abbrev explicitPullbackFiberObject
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X) {T : C} (h : T ⟶ D.base) :
    letI := category (J := J) hSheaf
    (projectionFunctor (J := J) hSheaf).Fiber T := by
  letI := category (J := J) hSheaf
  exact
    Functor.Fiber.mk (p := projectionFunctor (J := J) hSheaf)
      (show (projectionFunctor (J := J) hSheaf).obj (pullback (J := J) D h) = T from rfl)

/-- Source stage 3.13 bridge: the explicit pullback object used by the construction is
isomorphic, in the appropriate fibre, to Lean's canonical pullback choice.  This isolates the
owner-level comparison needed before extracting the components of an outer descent isomorphism
`Theta_ab`. -/
theorem explicitPullbackFiberObject_iso_canonicalPullback_nonempty
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X) {T : C} (h : T ⟶ D.base) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    Nonempty
      (explicitPullbackFiberObject (J := J) hSheaf D h ≅
        h ^*[canonicalPullbackChoice P] projectionFiberObject (J := J) hSheaf D) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  have hcart : P.IsStronglyCartesian h (pullbackMap (J := J) D h) :=
    pullbackMap_isStronglyCartesian (J := J) hSheaf D h
  letI : P.IsStronglyCartesian (P.map (pullbackMap (J := J) D h))
      (pullbackMap (J := J) D h) := by
    simpa [P] using hcart
  simpa [P, projectionFiberObject, explicitPullbackFiberObject] using
    Stage3LocalEssentialSurjectivity.stronglyCartesianDomain_iso_canonicalPullback_nonempty
      (p := P) (pullbackMap (J := J) D h)

noncomputable def explicitPullbackFiberObjectIsoCanonical
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X) {T : C} (h : T ⟶ D.base) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    explicitPullbackFiberObject (J := J) hSheaf D h ≅
      h ^*[canonicalPullbackChoice P] projectionFiberObject (J := J) hSheaf D := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let pulledY : P.Fiber T := explicitPullbackFiberObject (J := J) hSheaf D h
  let yFiber : P.Fiber D.base := projectionFiberObject (J := J) hSheaf D
  let canonicalY : P.Fiber T := h ^*[canonicalPullbackChoice P] yFiber
  let φ : pulledY.1 ⟶ D := pullbackMap (J := J) D h
  have hφ : P.IsStronglyCartesian h φ := by
    simpa [P, φ, pulledY] using
      pullbackMap_isStronglyCartesian (J := J) hSheaf D h
  let k : canonicalY.1 ⟶ D := (canonicalPullbackChoice P).map h yFiber
  have hk : P.IsStronglyCartesian h k := by
    simpa [P, k, canonicalY, yFiber, projectionFiberObject] using
      (canonicalPullbackChoice P).isStronglyCartesian h yFiber
  letI : P.IsStronglyCartesian h k := hk
  letI : P.IsStronglyCartesian h φ := hφ
  let e : pulledY.1 ≅ canonicalY.1 :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ P
      _ _ _ _ _ _ h h (Iso.refl T)
      (show h = (Iso.refl T).hom ≫ h by simp)
      k φ hk hφ
  have hhom : P.IsHomLift (𝟙 T) e.hom := by
    change P.IsHomLift (Iso.refl T).hom e.hom
    exact
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ P
        _ _ _ _ _ _ h h (Iso.refl T)
        (show h = (Iso.refl T).hom ≫ h by simp)
        k φ hk hφ)
  have hinv : P.IsHomLift (𝟙 T) e.inv := by
    change P.IsHomLift (Iso.refl T).hom e.inv
    exact
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _ P
        _ _ _ _ _ _ h h (Iso.refl T)
        (show h = (Iso.refl T).hom ≫ h by simp)
        k φ hk hφ)
  exact
    { hom := Functor.Fiber.homMk P T e.hom
      inv := Functor.Fiber.homMk P T e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }

set_option backward.isDefEq.respectTransparency false in
/-- The concrete explicit-to-canonical pullback bridge is characterized by the cartesian
triangle: after composing with the canonical pullback projection, it is the explicit pullback
projection. -/
theorem explicitPullbackFiberObjectIsoCanonical_hom_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X) {T : C} (h : T ⟶ D.base) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    (explicitPullbackFiberObjectIsoCanonical (J := J) hSheaf D h).hom.1 ≫
        (canonicalPullbackChoice P).map h (projectionFiberObject (J := J) hSheaf D) =
      pullbackMap (J := J) D h := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let pulledY : P.Fiber T := explicitPullbackFiberObject (J := J) hSheaf D h
  let yFiber : P.Fiber D.base := projectionFiberObject (J := J) hSheaf D
  let canonicalY : P.Fiber T := h ^*[canonicalPullbackChoice P] yFiber
  let φ : pulledY.1 ⟶ D := pullbackMap (J := J) D h
  have hφ : P.IsStronglyCartesian h φ := by
    simpa [P, φ, pulledY] using
      pullbackMap_isStronglyCartesian (J := J) hSheaf D h
  let k : canonicalY.1 ⟶ D := (canonicalPullbackChoice P).map h yFiber
  have hk : P.IsStronglyCartesian h k := by
    simpa [P, k, canonicalY, yFiber, projectionFiberObject] using
      (canonicalPullbackChoice P).isStronglyCartesian h yFiber
  letI : P.IsStronglyCartesian h k := hk
  letI : P.IsStronglyCartesian h φ := hφ
  let e : pulledY.1 ≅ canonicalY.1 :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ P
      _ _ _ _ _ _ h h (Iso.refl T)
      (show h = (Iso.refl T).hom ≫ h by simp)
      k φ hk hφ
  have hfac : e.hom ≫ k = φ := by
    change
      (Functor.IsStronglyCartesian.domainIsoOfBaseIso
        (p := P) (show h = (Iso.refl T).hom ≫ h by simp) k φ).hom ≫ k = φ
    rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
    exact Functor.IsStronglyCartesian.fac P h k
      (show h = (Iso.refl T).hom ≫ h by simp) φ
  dsimp [explicitPullbackFiberObjectIsoCanonical]
  exact hfac

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the concrete explicit-to-canonical pullback bridge is characterized by the
opposite cartesian triangle. -/
theorem explicitPullbackFiberObjectIsoCanonical_inv_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X) {T : C} (h : T ⟶ D.base) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    (explicitPullbackFiberObjectIsoCanonical (J := J) hSheaf D h).inv.1 ≫
        pullbackMap (J := J) D h =
      (canonicalPullbackChoice P).map h (projectionFiberObject (J := J) hSheaf D) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let e := explicitPullbackFiberObjectIsoCanonical (J := J) hSheaf D h
  have hfac := explicitPullbackFiberObjectIsoCanonical_hom_fac (J := J) hSheaf D h
  have hcancel : e.inv.1 ≫ e.hom.1 = 𝟙 _ := by
    exact congrArg Subtype.val e.inv_hom_id
  calc
    e.inv.1 ≫ pullbackMap (J := J) D h =
        e.inv.1 ≫ (e.hom.1 ≫
          (canonicalPullbackChoice P).map h (projectionFiberObject (J := J) hSheaf D)) := by
          rw [hfac]
    _ = (e.inv.1 ≫ e.hom.1) ≫
        (canonicalPullbackChoice P).map h (projectionFiberObject (J := J) hSheaf D) := by
          rw [Category.assoc]
    _ = (canonicalPullbackChoice P).map h (projectionFiberObject (J := J) hSheaf D) := by
          simp [hcancel]

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
