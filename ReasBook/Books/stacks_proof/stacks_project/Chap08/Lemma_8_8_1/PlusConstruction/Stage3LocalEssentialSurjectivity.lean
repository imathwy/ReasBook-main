import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.CartesianComposition
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3LocalModelInverse

universe u v uX vX uY vY

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

namespace Stage3LocalEssentialSurjectivity

/-- Heterogeneous-owner version of local essential surjectivity for a based functor over `C`.
This is the right frontier for the descent-completion old-object functor: the target projection
lives in a mixed owner, so forcing a same-owner `FibredCategoryMor` would hide the universe issue
rather than solve it. -/
def BasedFunctorLocallyEssentiallySurjectiveOnObjects
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    (F : X ⥤ᵇ Y) (hY : Y.p.IsFibered) : Prop :=
  letI : Y.p.IsFibered := hY
  ∀ (U : C) (y : Y.p.Fiber U),
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      ∃ x : X.p.Fiber I.Y,
        Nonempty (((F.fiberFunctor I.Y).obj x) ≅ I.f ^*[canonicalPullbackChoice Y.p] y)

/-- The two ways to regard a fiber object as an old descent-completion object agree after
unfolding the fiber object's base proof. -/
theorem oldObject_eq_ofFiberObject
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C} (x : X.p.Fiber U) :
    oldObject (J := J) X x.1 = ofFiberObject (J := J) X x := by
  cases x with
  | mk a ha =>
    cases ha
    rfl

/-- A strongly cartesian arrow identifies its domain, as an object of the source fibre, with the
canonical pullback of its codomain.  This is the reusable owner-level bridge needed because
`LocallyEssentiallySurjectiveOnObjects` is stated using `canonicalPullbackChoice`, while the
descent-completion construction has its own explicit pullbacks. -/
theorem stronglyCartesianDomain_iso_canonicalPullback_nonempty
    {B : Type u} {E : Type uX} [Category.{v} B] [Category.{vX} E]
    (p : E ⥤ B) [p.IsFibered]
    {x y : E} (φ : x ⟶ y)
    [hφ : p.IsStronglyCartesian (p.map φ) φ] :
    Nonempty
      ((Functor.Fiber.mk (p := p) (show p.obj x = p.obj x from rfl)) ≅
        ((canonicalPullbackChoice p).pullbackFunctor (p.map φ)).obj
          (Functor.Fiber.mk (p := p) (show p.obj y = p.obj y from rfl))) := by
  let yFiber : p.Fiber (p.obj y) :=
    Functor.Fiber.mk (p := p) (show p.obj y = p.obj y from rfl)
  let canonicalY : p.Fiber (p.obj x) :=
    (p.map φ ^*[canonicalPullbackChoice p] yFiber)
  let pulledY : p.Fiber (p.obj x) :=
    Functor.Fiber.mk (p := p) (show p.obj x = p.obj x from rfl)
  let k : canonicalY.1 ⟶ y := (canonicalPullbackChoice p).map (p.map φ) yFiber
  have hk : p.IsStronglyCartesian (p.map φ) k := by
    simpa [k] using (canonicalPullbackChoice p).isStronglyCartesian (p.map φ) yFiber
  letI : p.IsStronglyCartesian (p.map φ) k := hk
  letI : p.IsStronglyCartesian (p.map φ) φ := hφ
  let e : pulledY.1 ≅ canonicalY.1 :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ p
      _ _ _ _ _ _ (p.map φ) (p.map φ) (Iso.refl (p.obj x))
      (show p.map φ = (Iso.refl (p.obj x)).hom ≫ p.map φ by simp)
      k φ hk hφ
  have hhom : p.IsHomLift (𝟙 (p.obj x)) e.hom := by
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ p
        _ _ _ _ _ _ (p.map φ) (p.map φ) (Iso.refl (p.obj x))
        (show p.map φ = (Iso.refl (p.obj x)).hom ≫ p.map φ by simp)
        k φ hk hφ)
  have hinv : p.IsHomLift (𝟙 (p.obj x)) e.inv := by
    simpa [e] using
      (@Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _ p
        _ _ _ _ _ _ (p.map φ) (p.map φ) (Iso.refl (p.obj x))
        (show p.map φ = (Iso.refl (p.obj x)).hom ≫ p.map φ by simp)
        k φ hk hφ)
  refine ⟨?_⟩
  exact
    { hom := Functor.Fiber.homMk p (p.obj x) e.hom
      inv := Functor.Fiber.homMk p (p.obj x) e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }

/-- Source stage 3.9, at the heterogeneous-owner frontier: every object of the
descent-completion projection is locally isomorphic to an old object.  The covering is the cover
carried by the completed object, and the local isomorphism is the one built in
`Stage3LocalModelInverse`, followed by the comparison with Lean's canonical pullback choice. -/
theorem oldObjectBasedFunctor_locallyEssentiallySurjectiveOnObjects
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    letI := category (J := J) hSheaf
    BasedFunctorLocallyEssentiallySurjectiveOnObjects (J := J)
      (oldObjectBasedFunctor (J := J) X hSheaf)
      (projectionFunctor_isFibered (J := J) hSheaf) := by
  letI := category (J := J) hSheaf
  let p' := projectionFunctor (J := J) hSheaf
  let hFib : p'.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  dsimp [BasedFunctorLocallyEssentiallySurjectiveOnObjects]
  letI : p'.IsFibered := hFib
  intro U y
  cases y with
  | mk D hD =>
    cases hD
    refine ⟨D.object.cover, ?_⟩
    intro I
    let x : X.p.Fiber I.Y := D.object.localObject I
    refine ⟨x, ?_⟩
    let oldFiber : p'.Fiber I.Y :=
      Functor.Fiber.mk (p := p')
        (show p'.obj (stage3LocalOldObject (J := J) D I) = I.Y from rfl)
    let pullFiber : p'.Fiber I.Y :=
      Functor.Fiber.mk (p := p')
        (show p'.obj (stage3LocalPullbackObject (J := J) D I) = I.Y from rfl)
    have hval :
        (((oldObjectBasedFunctor (J := J) X hSheaf).fiberFunctor I.Y).obj x).1 =
          stage3LocalOldObject (J := J) D I := by
      calc
        (((oldObjectBasedFunctor (J := J) X hSheaf).fiberFunctor I.Y).obj x).1 =
            oldObject (J := J) X x.1 := by
          change (oldObjectFunctor (J := J) X hSheaf).obj x.1 =
            oldObject (J := J) X x.1
          rfl
        _ = ofFiberObject (J := J) X x :=
          oldObject_eq_ofFiberObject (J := J) x
    have hleft :
        ((oldObjectBasedFunctor (J := J) X hSheaf).fiberFunctor I.Y).obj x =
          oldFiber := by
      apply Subtype.ext
      exact hval
    have hto : p'.IsHomLift (𝟙 I.Y) (Stage3LocalModel.toPullbackHom (J := J) D I) := by
      change p'.IsHomLift
        (p'.map (Stage3LocalModel.toPullbackHom (J := J) D I))
        (Stage3LocalModel.toPullbackHom (J := J) D I)
      exact Functor.IsHomLift.map (p := p') (Stage3LocalModel.toPullbackHom (J := J) D I)
    have hfrom :
        p'.IsHomLift (𝟙 I.Y) (Stage3LocalModel.fromPullbackHom (J := J) D I) := by
      change p'.IsHomLift
        (p'.map (Stage3LocalModel.fromPullbackHom (J := J) D I))
        (Stage3LocalModel.fromPullbackHom (J := J) D I)
      exact Functor.IsHomLift.map (p := p') (Stage3LocalModel.fromPullbackHom (J := J) D I)
    letI : p'.IsHomLift (𝟙 I.Y) (Stage3LocalModel.toPullbackHom (J := J) D I) := hto
    letI : p'.IsHomLift (𝟙 I.Y) (Stage3LocalModel.fromPullbackHom (J := J) D I) := hfrom
    let eOldPull : oldFiber ≅ pullFiber :=
      { hom := Functor.Fiber.homMk p' I.Y (Stage3LocalModel.toPullbackHom (J := J) D I)
        inv := Functor.Fiber.homMk p' I.Y (Stage3LocalModel.fromPullbackHom (J := J) D I)
        hom_inv_id := by
          apply Functor.Fiber.hom_ext
          exact Stage3LocalModel.toPullback_comp_fromPullback (J := J) hSheaf D I
        inv_hom_id := by
          apply Functor.Fiber.hom_ext
          exact Stage3LocalModel.fromPullback_comp_toPullback (J := J) hSheaf D I }
    have hpullCart : p'.IsStronglyCartesian (I.f) (pullbackMap (J := J) D I.f) :=
      pullbackMap_isStronglyCartesian (J := J) hSheaf D I.f
    letI :
        p'.IsStronglyCartesian
          (p'.map (pullbackMap (J := J) D I.f)) (pullbackMap (J := J) D I.f) := by
      simpa using hpullCart
    obtain ⟨ePullCanonical⟩ :=
      stronglyCartesianDomain_iso_canonicalPullback_nonempty
        (p := p') (pullbackMap (J := J) D I.f)
    exact ⟨eqToIso hleft ≪≫ eOldPull ≪≫ ePullCanonical⟩

end Stage3LocalEssentialSurjectivity

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
