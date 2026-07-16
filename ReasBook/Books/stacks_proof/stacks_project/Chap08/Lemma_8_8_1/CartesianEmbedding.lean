import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.OldEmbedding

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
namespace DescentCompletionObjectOver
namespace HomOver

/-- Source stage 3.10 helper: when the target old object is changed along an original morphism
`φ : a ⟶ b`, a cover arrow of the old object `a` gives the corresponding cover arrow of the old
object `b` by composing its base map with `p(φ)`. -/
noncomputable def oldMapTargetCoverArrow
    {X : FibredCategoryOver.{u, v, uX, vX} C} {a b : X.S} (φ : a ⟶ b)
    (K : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow) :
    (DescentCompletionObject.oldObject (J := J) X b).object.cover.Arrow :=
  { Y := K.Y
    f := K.f ≫ X.p.map φ
    hf := by
      change (⊤ : Sieve (X.p.obj b)).arrows (K.f ≫ X.p.map φ)
      simp }

/-- Base compatibility for the source component of the local cartesian lift in stage 3.10. -/
theorem cartesianLiftToOld_hα
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T W : C}
    {D : DescentCompletionObjectOver (J := J) X T}
    {a b : X.S} (φ : a ⟶ b) {g : T ⟶ X.p.obj a}
    (I : D.cover.Arrow)
    (K : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ g = k ≫ K.f) :
    i ≫ I.f ≫ (g ≫ X.p.map φ) =
      k ≫ (oldMapTargetCoverArrow (J := J) φ K).f := by
  simpa [oldMapTargetCoverArrow, ← Category.assoc] using
    congrArg (fun q => q ≫ X.p.map φ) h

/-- Base compatibility for the old-map component used after constructing the local lift. -/
theorem cartesianLiftToOld_hOld
    {X : FibredCategoryOver.{u, v, uX, vX} C} {W : C}
    {a b : X.S} (φ : a ⟶ b)
    (K : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow)
    (k : W ⟶ K.Y) :
    k ≫ K.f ≫ X.p.map φ =
      k ≫ (oldMapTargetCoverArrow (J := J) φ K).f := by
  dsimp [oldMapTargetCoverArrow]
  rfl

@[reassoc]
theorem oldObjectRestrictedMap_overlap
    {X : FibredCategoryOver.{u, v, uX, vX} C} {W : C}
    (a : X.S)
    {K₁ K₂ : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow}
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f) :
    ((DescentCompletionObject.oldObject (J := J) X a).object.overlapIso k₁ k₂ hK).hom.1 ≫
      DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X
        (Functor.Fiber.mk (p := X.p) (a := a) rfl) K₂ k₂ =
        DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X
          (Functor.Fiber.mk (p := X.p) (a := a) rfl) K₁ k₁ := by
  simpa [DescentCompletionObject.oldObject] using
    DescentCompletionObjectOver.ofFiberObjectRestrictedMap_overlap
      (J := J) X (Functor.Fiber.mk (p := X.p) (a := a) rfl) k₁ k₂ hK

set_option maxHeartbeats 800000 in
/-- Source stage 3.10, component-level construction: given
`α : D ⟶ G(b)` over `g ≫ p(φ)` and `φ : a ⟶ b` strongly cartesian in the original fibred
category, construct the local component of the desired lift `D ⟶ G(a)` over `g`. -/
noncomputable def cartesianLiftToOldFamily
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.HomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ))
    {W : C} (I : D.cover.Arrow)
    (K : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ g = k ≫ K.f) :
    D.restrictedLocalObject I i ⟶
      (DescentCompletionObject.oldObject (J := J) X a).object.restrictedLocalObject K k := by
  let xF : X.p.Fiber (X.p.obj a) := Functor.Fiber.mk (p := X.p) (a := a) rfl
  let yF : X.p.Fiber (X.p.obj b) := Functor.Fiber.mk (p := X.p) (a := b) rfl
  let L := oldMapTargetCoverArrow (J := J) φ K
  let hα := cartesianLiftToOld_hα (J := J) φ I K i k h
  let αcomp := α.family I L i k hα
  let yMap :=
    DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X yF L k
  have hαtotalLift : X.p.IsHomLift ((k ≫ K.f) ≫ X.p.map φ) (αcomp.1 ≫ yMap) := by
    have hαcompLift : X.p.IsHomLift (𝟙 W) αcomp.1 := αcomp.2
    have hyMapLift : X.p.IsHomLift (k ≫ L.f) yMap :=
      (DescentCompletionObjectOver.ofFiberObjectRestrictedMap_isStronglyCartesian
        (J := J) X yF L k).toIsHomLift
    letI : X.p.IsHomLift (𝟙 W) αcomp.1 := hαcompLift
    letI : X.p.IsHomLift (k ≫ L.f) yMap := hyMapLift
    have hcomp : X.p.IsHomLift (𝟙 W ≫ (k ≫ L.f)) (αcomp.1 ≫ yMap) :=
      @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 W) (k ≫ L.f)
        αcomp.1 yMap hαcompLift hyMapLift
    simpa [L, oldMapTargetCoverArrow, Category.assoc] using hcomp
  letI : X.p.IsStronglyCartesian (X.p.map φ) φ := hφ
  let δ : (D.restrictedLocalObject I i).1 ⟶ a :=
    @IsStronglyCartesian.map _ _ _ _ X.p
      (X.p.obj a) (X.p.obj b) a b
      (X.p.map φ) φ hφ
      W (D.restrictedLocalObject I i).1
      (k ≫ K.f) ((k ≫ K.f) ≫ X.p.map φ)
      (by rfl) (αcomp.1 ≫ yMap) hαtotalLift
  have hδLift : X.p.IsHomLift (k ≫ K.f) δ := by
    simpa [δ] using
      @IsStronglyCartesian.map_isHomLift _ _ _ _ X.p
        (X.p.obj a) (X.p.obj b) a b
        (X.p.map φ) φ hφ
        W (D.restrictedLocalObject I i).1
        (k ≫ K.f) ((k ≫ K.f) ≫ X.p.map φ)
        (by rfl) (αcomp.1 ≫ yMap) hαtotalLift
  let xMap :=
    DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X xF K k
  have hxMapCart : X.p.IsStronglyCartesian (k ≫ K.f) xMap :=
    DescentCompletionObjectOver.ofFiberObjectRestrictedMap_isStronglyCartesian
      (J := J) X xF K k
  exact
    ⟨@IsStronglyCartesian.map _ _ _ _ X.p
        W (X.p.obj a)
        ((DescentCompletionObject.oldObject (J := J) X a).object.restrictedLocalObject K k).1
        a
        (k ≫ K.f) xMap hxMapCart
        W (D.restrictedLocalObject I i).1
        (𝟙 W) (k ≫ K.f) (by simp) δ hδLift,
      @IsStronglyCartesian.map_isHomLift _ _ _ _ X.p
        W (X.p.obj a)
        ((DescentCompletionObject.oldObject (J := J) X a).object.restrictedLocalObject K k).1
        a
        (k ≫ K.f) xMap hxMapCart
        W (D.restrictedLocalObject I i).1
        (𝟙 W) (k ≫ K.f) (by simp) δ hδLift⟩

set_option maxHeartbeats 1000000 in
/-- Source stage 3.10, component-level factorization: the component constructed by
`cartesianLiftToOldFamily` becomes the original `α`-component after composing with the corresponding
component of `G(φ)`. -/
theorem cartesianLiftToOldFamily_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.HomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ))
    {W : C} (I : D.cover.Arrow)
    (K : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ g = k ≫ K.f) :
    let L := oldMapTargetCoverArrow (J := J) φ K
    let hα := cartesianLiftToOld_hα (J := J) φ I K i k h
    let hOld := cartesianLiftToOld_hOld (J := J) φ K k
    cartesianLiftToOldFamily (J := J) D φ hφ α I K i k h ≫
        (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family K L k k hOld =
      α.family I L i k hα := by
  intro L hα hOld
  let xF : X.p.Fiber (X.p.obj a) := Functor.Fiber.mk (p := X.p) (a := a) rfl
  let yF : X.p.Fiber (X.p.obj b) := Functor.Fiber.mk (p := X.p) (a := b) rfl
  let αcomp := α.family I L i k hα
  let yMap :=
    DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X yF L k
  have hyMapCart : X.p.IsStronglyCartesian (k ≫ L.f) yMap :=
    DescentCompletionObjectOver.ofFiberObjectRestrictedMap_isStronglyCartesian
      (J := J) X yF L k
  let xMap :=
    DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X xF K k
  have hαtotalLift : X.p.IsHomLift ((k ≫ K.f) ≫ X.p.map φ) (αcomp.1 ≫ yMap) := by
    have hαcompLift : X.p.IsHomLift (𝟙 W) αcomp.1 := αcomp.2
    have hyMapLift : X.p.IsHomLift (k ≫ L.f) yMap := hyMapCart.toIsHomLift
    have hcomp : X.p.IsHomLift (𝟙 W ≫ (k ≫ L.f)) (αcomp.1 ≫ yMap) :=
      @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 W) (k ≫ L.f)
        αcomp.1 yMap hαcompLift hyMapLift
    simpa [L, oldMapTargetCoverArrow, Category.assoc] using hcomp
  let δ : (D.restrictedLocalObject I i).1 ⟶ a :=
    @IsStronglyCartesian.map _ _ _ _ X.p
      (X.p.obj a) (X.p.obj b) a b
      (X.p.map φ) φ hφ
      W (D.restrictedLocalObject I i).1
      (k ≫ K.f) ((k ≫ K.f) ≫ X.p.map φ)
      (by rfl) (αcomp.1 ≫ yMap) hαtotalLift
  have hδLift : X.p.IsHomLift (k ≫ K.f) δ := by
    simpa [δ] using
      @IsStronglyCartesian.map_isHomLift _ _ _ _ X.p
        (X.p.obj a) (X.p.obj b) a b
        (X.p.map φ) φ hφ
        W (D.restrictedLocalObject I i).1
        (k ≫ K.f) ((k ≫ K.f) ≫ X.p.map φ)
        (by rfl) (αcomp.1 ≫ yMap) hαtotalLift
  have hδFac : δ ≫ φ = αcomp.1 ≫ yMap := by
    change
      (@IsStronglyCartesian.map _ _ _ _ X.p
        (X.p.obj a) (X.p.obj b) a b
        (X.p.map φ) φ hφ
        W (D.restrictedLocalObject I i).1
        (k ≫ K.f) ((k ≫ K.f) ≫ X.p.map φ)
        (by rfl) (αcomp.1 ≫ yMap) hαtotalLift) ≫ φ =
          αcomp.1 ≫ yMap
    exact
      @IsStronglyCartesian.fac _ _ _ _ X.p
        (X.p.obj a) (X.p.obj b) a b
        (X.p.map φ) φ hφ
        W (D.restrictedLocalObject I i).1
        (k ≫ K.f) ((k ≫ K.f) ≫ X.p.map φ)
        (by rfl) (αcomp.1 ≫ yMap) hαtotalLift
  have hxMapCart : X.p.IsStronglyCartesian (k ≫ K.f) xMap :=
    DescentCompletionObjectOver.ofFiberObjectRestrictedMap_isStronglyCartesian
      (J := J) X xF K k
  have hβFac :
      (cartesianLiftToOldFamily (J := J) D φ hφ α I K i k h).1 ≫ xMap = δ := by
    unfold cartesianLiftToOldFamily
    dsimp only []
    change
      (@IsStronglyCartesian.map _ _ _ _ X.p
        W (X.p.obj a)
        ((DescentCompletionObject.oldObject (J := J) X a).object.restrictedLocalObject K k).1
        a
        (k ≫ K.f) xMap hxMapCart
        W (D.restrictedLocalObject I i).1
        (𝟙 W) (k ≫ K.f) (by simp) δ hδLift) ≫ xMap = δ
    exact
      @IsStronglyCartesian.fac _ _ _ _ X.p
        W (X.p.obj a)
        ((DescentCompletionObject.oldObject (J := J) X a).object.restrictedLocalObject K k).1
        a
        (k ≫ K.f) xMap hxMapCart
        W (D.restrictedLocalObject I i).1
        (𝟙 W) (k ≫ K.f) (by simp) δ hδLift
  have hOldFac :
      ((DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family
          K L k k hOld).1 ≫ yMap =
        xMap ≫ φ := by
    have hφLift : X.p.IsHomLift (X.p.map φ) φ := hφ.toIsHomLift
    simpa [DescentCompletionObject.oldMap, DescentCompletionObject.oldObject,
      xF, yF, xMap, yMap] using
      @DescentCompletionObjectOver.ofFiberHomComponent_fac _ _ J X
        (X.p.obj a) (X.p.obj b) W
        xF yF (X.p.map φ) φ hφLift K L k k hOld
  have hβFacφ :
      (cartesianLiftToOldFamily (J := J) D φ hφ α I K i k h).1 ≫ (xMap ≫ φ) =
        δ ≫ φ := by
    rw [← Category.assoc]
    exact congrArg (fun q => q ≫ φ) hβFac
  apply Functor.Fiber.hom_ext
  change (cartesianLiftToOldFamily (J := J) D φ hφ α I K i k h ≫
        (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family K L k k hOld).1 =
      αcomp.1
  have hleftLift : X.p.IsHomLift (𝟙 W)
      (cartesianLiftToOldFamily (J := J) D φ hφ α I K i k h ≫
        (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family K L k k hOld).1 :=
    (cartesianLiftToOldFamily (J := J) D φ hφ α I K i k h ≫
        (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family K L k k hOld).2
  have hrightLift : X.p.IsHomLift (𝟙 W) αcomp.1 := αcomp.2
  apply @Functor.IsStronglyCartesian.ext _ _ _ _ X.p
    W (X.p.obj b)
    ((DescentCompletionObject.oldObject (J := J) X b).object.restrictedLocalObject L k).1
    b
    (k ≫ L.f) yMap hyMapCart
    W (D.restrictedLocalObject I i).1
    (𝟙 W)
    (cartesianLiftToOldFamily (J := J) D φ hφ α I K i k h ≫
      (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family K L k k hOld).1
    αcomp.1
    hleftLift hrightLift
  change
    ((cartesianLiftToOldFamily (J := J) D φ hφ α I K i k h).1 ≫
        ((DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family
          K L k k hOld).1) ≫ yMap =
      αcomp.1 ≫ yMap
  rw [Category.assoc]
  rw [hOldFac]
  exact hβFacφ.trans hδFac

set_option maxHeartbeats 500000 in
/-- Source stage 3.10, component-level factorization after projecting the old target component
back to the original object.  This is the form used in the descent-compatibility square: after
postcomposing with the old-object restriction map and then with `φ`, the lifted component agrees
with the original `α` component projected to `b`. -/
theorem cartesianLiftToOldFamily_restrictedMap_comp
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.HomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ))
    {W : C} (I : D.cover.Arrow)
    (K : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ g = k ≫ K.f) :
    let xF : X.p.Fiber (X.p.obj a) := Functor.Fiber.mk (p := X.p) (a := a) rfl
    let yF : X.p.Fiber (X.p.obj b) := Functor.Fiber.mk (p := X.p) (a := b) rfl
    let L := oldMapTargetCoverArrow (J := J) φ K
    let hα := cartesianLiftToOld_hα (J := J) φ I K i k h
    (cartesianLiftToOldFamily (J := J) D φ hφ α I K i k h).1 ≫
        DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X xF K k ≫ φ =
      (α.family I L i k hα).1 ≫
        DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X yF L k := by
  intro xF yF L hα
  let hOld := cartesianLiftToOld_hOld (J := J) φ K k
  let β := cartesianLiftToOldFamily (J := J) D φ hφ α I K i k h
  let oldComp :=
    (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family K L k k hOld
  let xMap := DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X xF K k
  let yMap := DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X yF L k
  let αcomp := α.family I L i k hα
  have hFac : β ≫ oldComp = αcomp := by
    simpa [β, oldComp, αcomp, L, hα, hOld] using
      cartesianLiftToOldFamily_fac (J := J) D φ hφ α I K i k h
  have hFacVal : (β ≫ oldComp).1 = αcomp.1 := congrArg Subtype.val hFac
  have hφLift : X.p.IsHomLift (X.p.map φ) φ := hφ.toIsHomLift
  have hOldFac : oldComp.1 ≫ yMap = xMap ≫ φ := by
    simpa [DescentCompletionObject.oldMap, DescentCompletionObject.oldObject,
      xF, yF, xMap, yMap, oldComp] using
      @DescentCompletionObjectOver.ofFiberHomComponent_fac _ _ J X
        (X.p.obj a) (X.p.obj b) W
        xF yF (X.p.map φ) φ hφLift K L k k hOld
  calc
    β.1 ≫ xMap ≫ φ = β.1 ≫ oldComp.1 ≫ yMap := by
      simpa [Category.assoc] using congrArg (fun q => β.1 ≫ q) hOldFac.symm
    _ = (β ≫ oldComp).1 ≫ yMap := by
      change β.1 ≫ (oldComp.1 ≫ yMap) = (β.1 ≫ oldComp.1) ≫ yMap
      rw [← Category.assoc]
    _ = αcomp.1 ≫ yMap := by
      rw [hFacVal]

@[reassoc]
theorem cartesianLiftToOldFamily_oldRestrictedMap_comp
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.HomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ))
    {W : C} (I : D.cover.Arrow)
    (K : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ g = k ≫ K.f) :
    let L := oldMapTargetCoverArrow (J := J) φ K
    (cartesianLiftToOldFamily (J := J) D φ hφ α I K i k h).1 ≫
        DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X
          (Functor.Fiber.mk (p := X.p) (a := a) rfl) K k ≫ φ =
      (α.family I L i k (cartesianLiftToOld_hα (J := J) φ I K i k h)).1 ≫
        DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X
          (Functor.Fiber.mk (p := X.p) (a := b) rfl) L k := by
  intro L
  simpa using
    cartesianLiftToOldFamily_restrictedMap_comp (J := J) D φ hφ α I K i k h

set_option maxHeartbeats 1000000 in
/-- Source stage 3.10, component compatibility for the local cartesian lift.  This is the
descent-transition square needed to bundle `cartesianLiftToOldFamily` as a `HomOver`. -/
theorem cartesianLiftToOldFamily_compatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.HomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ)) :
    ∀ {W : C}
      (I₁ I₂ : D.cover.Arrow)
      (K₁ K₂ : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow)
      (i₁ : W ⟶ I₁.Y) (i₂ : W ⟶ I₂.Y)
      (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
      (hD : i₁ ≫ I₁.f = i₂ ≫ I₂.f)
      (hE : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
      (h₁ : i₁ ≫ I₁.f ≫ g = k₁ ≫ K₁.f)
      (h₂ : i₂ ≫ I₂.f ≫ g = k₂ ≫ K₂.f),
        (D.overlapIso i₁ i₂ hD).hom ≫
            cartesianLiftToOldFamily (J := J) D φ hφ α I₂ K₂ i₂ k₂ h₂ =
          cartesianLiftToOldFamily (J := J) D φ hφ α I₁ K₁ i₁ k₁ h₁ ≫
            ((DescentCompletionObject.oldObject (J := J) X a).object.overlapIso
              k₁ k₂ hE).hom := by
  intro W I₁ I₂ K₁ K₂ i₁ i₂ k₁ k₂ hD hE h₁ h₂
  let xF : X.p.Fiber (X.p.obj a) := Functor.Fiber.mk (p := X.p) (a := a) rfl
  let yF : X.p.Fiber (X.p.obj b) := Functor.Fiber.mk (p := X.p) (a := b) rfl
  let L₁ := oldMapTargetCoverArrow (J := J) φ K₁
  let L₂ := oldMapTargetCoverArrow (J := J) φ K₂
  let hα₁ := cartesianLiftToOld_hα (J := J) φ I₁ K₁ i₁ k₁ h₁
  let hα₂ := cartesianLiftToOld_hα (J := J) φ I₂ K₂ i₂ k₂ h₂
  let β₁ := cartesianLiftToOldFamily (J := J) D φ hφ α I₁ K₁ i₁ k₁ h₁
  let β₂ := cartesianLiftToOldFamily (J := J) D φ hφ α I₂ K₂ i₂ k₂ h₂
  let xMap₁ := DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X xF K₁ k₁
  let xMap₂ := DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X xF K₂ k₂
  let yMap₁ := DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X yF L₁ k₁
  let yMap₂ := DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X yF L₂ k₂
  let α₁ := α.family I₁ L₁ i₁ k₁ hα₁
  let α₂ := α.family I₂ L₂ i₂ k₂ hα₂
  let sD := (D.overlapIso i₁ i₂ hD).hom
  let sA :=
    ((DescentCompletionObject.oldObject (J := J) X a).object.overlapIso
      (I₁ := K₁) (I₂ := K₂) k₁ k₂ hE).hom
  have hEφ : k₁ ≫ L₁.f = k₂ ≫ L₂.f := by
    simpa [L₁, L₂, oldMapTargetCoverArrow, ← Category.assoc] using
      congrArg (fun q => q ≫ X.p.map φ) hE
  let sB :=
    ((DescentCompletionObject.oldObject (J := J) X b).object.overlapIso
      (I₁ := L₁) (I₂ := L₂) k₁ k₂ hEφ).hom
  apply Functor.Fiber.hom_ext
  change (sD ≫ β₂).1 = (β₁ ≫ sA).1
  let τ := xMap₂
  have hτ : X.p.IsStronglyCartesian (k₂ ≫ K₂.f) τ :=
    DescentCompletionObjectOver.ofFiberObjectRestrictedMap_isStronglyCartesian
      (J := J) X xF K₂ k₂
  have hleftLift : X.p.IsHomLift (𝟙 W) (sD ≫ β₂).1 := (sD ≫ β₂).2
  have hrightLift : X.p.IsHomLift (𝟙 W) (β₁ ≫ sA).1 := (β₁ ≫ sA).2
  apply @Functor.IsStronglyCartesian.ext _ _ _ _ X.p
    W (X.p.obj a)
    ((DescentCompletionObject.oldObject (J := J) X a).object.restrictedLocalObject K₂ k₂).1
    a
    (k₂ ≫ K₂.f) τ hτ
    W (D.restrictedLocalObject I₁ i₁).1
    (𝟙 W) (sD ≫ β₂).1 (β₁ ≫ sA).1 hleftLift hrightLift
  let leftX : (D.restrictedLocalObject I₁ i₁).1 ⟶ a := (sD ≫ β₂).1 ≫ τ
  let rightX : (D.restrictedLocalObject I₁ i₁).1 ⟶ a := (β₁ ≫ sA).1 ≫ τ
  have hτLift : X.p.IsHomLift (k₂ ≫ K₂.f) τ := hτ.toIsHomLift
  have hleftXLift : X.p.IsHomLift (k₂ ≫ K₂.f) leftX := by
    have hcomp : X.p.IsHomLift (𝟙 W ≫ (k₂ ≫ K₂.f)) ((sD ≫ β₂).1 ≫ τ) :=
      @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 W) (k₂ ≫ K₂.f)
        (sD ≫ β₂).1 τ hleftLift hτLift
    simpa [leftX] using hcomp
  have hrightXLift : X.p.IsHomLift (k₂ ≫ K₂.f) rightX := by
    have hcomp : X.p.IsHomLift (𝟙 W ≫ (k₂ ≫ K₂.f)) ((β₁ ≫ sA).1 ≫ τ) :=
      @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 W) (k₂ ≫ K₂.f)
        (β₁ ≫ sA).1 τ hrightLift hτLift
    simpa [rightX] using hcomp
  apply @Functor.IsStronglyCartesian.ext _ _ _ _ X.p
    (X.p.obj a) (X.p.obj b) a b
    (X.p.map φ) φ hφ
    W (D.restrictedLocalObject I₁ i₁).1
    (k₂ ≫ K₂.f) leftX rightX hleftXLift hrightXLift
  have hβ₂proj : β₂.1 ≫ xMap₂ ≫ φ = α₂.1 ≫ yMap₂ := by
    simpa [β₂, xMap₂, yMap₂, α₂, L₂, hα₂, xF, yF] using
      cartesianLiftToOldFamily_oldRestrictedMap_comp (J := J) D φ hφ α I₂ K₂ i₂ k₂ h₂
  have hβ₁proj : β₁.1 ≫ xMap₁ ≫ φ = α₁.1 ≫ yMap₁ := by
    simpa [β₁, xMap₁, yMap₁, α₁, L₁, hα₁, xF, yF] using
      cartesianLiftToOldFamily_oldRestrictedMap_comp (J := J) D φ hφ α I₁ K₁ i₁ k₁ h₁
  have hAover : sA.1 ≫ xMap₂ = xMap₁ := by
    simpa [sA, xMap₁, xMap₂, xF] using
      oldObjectRestrictedMap_overlap (J := J) (X := X) a k₁ k₂ hE
  have hBover : sB.1 ≫ yMap₂ = yMap₁ := by
    simpa [sB, yMap₁, yMap₂, yF] using
      oldObjectRestrictedMap_overlap (J := J) (X := X) b
        (K₁ := L₁) (K₂ := L₂) k₁ k₂ hEφ
  have hαcompatVal : sD.1 ≫ α₂.1 = α₁.1 ≫ sB.1 := by
    have hcompat := α.compatible I₁ I₂ L₁ L₂ i₁ i₂ k₁ k₂ hD hEφ hα₁ hα₂
    exact congrArg Subtype.val (by simpa [sD, sB, α₁, α₂] using hcompat)
  have hleftPost : leftX ≫ φ = α₁.1 ≫ yMap₁ := by
    calc
      leftX ≫ φ = ((sD.1 ≫ β₂.1) ≫ xMap₂) ≫ φ := by
        dsimp [leftX, τ]
        have hsDβ : (sD ≫ β₂).1 = sD.1 ≫ β₂.1 := rfl
        rw [hsDβ]
        rfl
      _ = sD.1 ≫ (β₂.1 ≫ xMap₂ ≫ φ) := by
        simp [Category.assoc]
      _ = sD.1 ≫ (α₂.1 ≫ yMap₂) := by
        simpa [Category.assoc] using congrArg (fun q => sD.1 ≫ q) hβ₂proj
      _ = (sD.1 ≫ α₂.1) ≫ yMap₂ := by
        rw [Category.assoc]
      _ = (α₁.1 ≫ sB.1) ≫ yMap₂ := by
        rw [hαcompatVal]
      _ = α₁.1 ≫ (sB.1 ≫ yMap₂) := by
        rw [Category.assoc]
      _ = α₁.1 ≫ yMap₁ := by
        rw [hBover]
  have hrightPost : rightX ≫ φ = α₁.1 ≫ yMap₁ := by
    calc
      rightX ≫ φ = ((β₁.1 ≫ sA.1) ≫ xMap₂) ≫ φ := by
        dsimp [rightX, τ]
        have hβsA : (β₁ ≫ sA).1 = β₁.1 ≫ sA.1 := rfl
        rw [hβsA]
        rfl
      _ = β₁.1 ≫ (sA.1 ≫ xMap₂) ≫ φ := by
        simp [Category.assoc]
      _ = β₁.1 ≫ xMap₁ ≫ φ := by
        rw [hAover]
      _ = α₁.1 ≫ yMap₁ := hβ₁proj
  exact hleftPost.trans hrightPost.symm

/-- Source stage 3.10, bundled owner-level lift into an old object.  Given
`α : D ⟶ G(b)` over `g ≫ p(φ)` and a strongly cartesian original arrow `φ : a ⟶ b`, this is
the compatible double-indexed family defining the local lift `D ⟶ G(a)` over `g`. -/
noncomputable def cartesianLiftToOldHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.HomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ)) :
    DescentCompletionObjectOver.HomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X a).object g where
  family I K i k h := cartesianLiftToOldFamily (J := J) D φ hφ α I K i k h
  compatible := cartesianLiftToOldFamily_compatible (J := J) D φ hφ α

/-- Source stage 3.10, bundled component factorization: the `HomOver` lift followed by the
old-object component of `G(φ)` gives back the original component of `α`. -/
theorem cartesianLiftToOldHomOver_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.HomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ))
    {W : C} (I : D.cover.Arrow)
    (K : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ g = k ≫ K.f) :
    let L := oldMapTargetCoverArrow (J := J) φ K
    let hα := cartesianLiftToOld_hα (J := J) φ I K i k h
    let hOld := cartesianLiftToOld_hOld (J := J) φ K k
    (cartesianLiftToOldHomOver (J := J) D φ hφ α).family I K i k h ≫
        (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family
          K L k k hOld =
      α.family I L i k hα := by
  intro L hα hOld
  simpa [cartesianLiftToOldHomOver] using
    cartesianLiftToOldFamily_fac (J := J) D φ hφ α I K i k h

/-- Source stage 3.10, local factorization against an arbitrary target cover of `G(b)`.
The basic factorization is first proved for the cover arrow `K.f ≫ p(φ)`; this lemma transports
it across the target descent transition using compatibility of both `α` and `oldMap φ`. -/
theorem cartesianLiftToOldHomOver_oldMap_comp
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.HomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ))
    {W : C} (I : D.cover.Arrow)
    (K : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow)
    (L : (DescentCompletionObject.oldObject (J := J) X b).object.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y) (l : W ⟶ L.Y)
    (hβ : i ≫ I.f ≫ g = k ≫ K.f)
    (hOld : k ≫ K.f ≫ X.p.map φ = l ≫ L.f) :
    let hαL : i ≫ I.f ≫ (g ≫ X.p.map φ) = l ≫ L.f := by
      calc
        i ≫ I.f ≫ (g ≫ X.p.map φ) =
            (i ≫ I.f ≫ g) ≫ X.p.map φ := by
          simp [Category.assoc]
        _ = (k ≫ K.f) ≫ X.p.map φ :=
          congrArg (fun q => q ≫ X.p.map φ) hβ
        _ = k ≫ K.f ≫ X.p.map φ := by
          simp [Category.assoc]
        _ = l ≫ L.f := hOld
    (cartesianLiftToOldHomOver (J := J) D φ hφ α).family I K i k hβ ≫
        (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family
          K L k l hOld =
      α.family I L i l hαL := by
  intro hαL
  let M := oldMapTargetCoverArrow (J := J) φ K
  let hαM := cartesianLiftToOld_hα (J := J) φ I K i k hβ
  let hOldM := cartesianLiftToOld_hOld (J := J) φ K k
  let β := (cartesianLiftToOldHomOver (J := J) D φ hφ α).family I K i k hβ
  let oldM :=
    (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family
      K M k k hOldM
  let oldL :=
    (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family
      K L k l hOld
  let αM := α.family I M i k hαM
  let αL := α.family I L i l hαL
  have hML : k ≫ M.f = l ≫ L.f := by
    simpa [M, oldMapTargetCoverArrow, Category.assoc] using hOld
  let sB :=
    ((DescentCompletionObject.oldObject (J := J) X b).object.overlapIso
      (I₁ := M) (I₂ := L) k l hML).hom
  have hβM : β ≫ oldM = αM := by
    simpa [β, oldM, αM, M, hαM, hOldM] using
      cartesianLiftToOldHomOver_fac (J := J) D φ hφ α I K i k hβ
  have hOldL : oldL = oldM ≫ sB := by
    have hcompat :=
      (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.compatible
        K K M L k k k l rfl hML hOldM hOld
    rw [DescentCompletionObjectOver.overlapIso_self_hom
      (J := J) (DescentCompletionObject.oldObject (J := J) X a).object K k] at hcompat
    simpa [oldM, oldL, sB] using hcompat
  have hαL' : αM ≫ sB = αL := by
    have hcompat := α.compatible I I M L i i k l rfl hML hαM hαL
    rw [DescentCompletionObjectOver.overlapIso_self_hom (J := J) D I i] at hcompat
    simpa [αM, αL, sB] using hcompat.symm
  calc
    β ≫ oldL = β ≫ (oldM ≫ sB) := by
      rw [hOldL]
    _ = (β ≫ oldM) ≫ sB := by
      rw [Category.assoc]
    _ = αM ≫ sB := by
      rw [hβM]
    _ = αL := hαL'

set_option maxHeartbeats 1200000 in
/-- Source stage 3.10, restriction/naturality for the bundled cartesian lift.  The proof pulls
back the factorization square through `G(φ)`, uses functoriality of `pullHom`, and then applies
cartesian uniqueness first for the old-object restriction map and then for `φ`. -/
theorem cartesianLiftToOldHomOver_familyNaturality'
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.HomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ))
    (hαnat : DescentCompletionObjectOver.HomOver.familyNaturality' (J := J) α) :
    DescentCompletionObjectOver.HomOver.familyNaturality' (J := J)
      (cartesianLiftToOldHomOver (J := J) D φ hφ α) := by
  intro W W' I K i k h m mi mk hmi hmk
  let hsmall : mi ≫ I.f ≫ g = mk ≫ K.f := by
    calc
      mi ≫ I.f ≫ g = m ≫ i ≫ I.f ≫ g := by
        rw [← hmi]
        simp [Category.assoc]
      _ = m ≫ k ≫ K.f := by
        simpa [Category.assoc] using congrArg (fun q => m ≫ q) h
      _ = mk ≫ K.f := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk
  let xF : X.p.Fiber (X.p.obj a) := Functor.Fiber.mk (p := X.p) (a := a) rfl
  let yF : X.p.Fiber (X.p.obj b) := Functor.Fiber.mk (p := X.p) (a := b) rfl
  let L := oldMapTargetCoverArrow (J := J) φ K
  let hα := cartesianLiftToOld_hα (J := J) φ I K i k h
  let hαsmall := cartesianLiftToOld_hα (J := J) φ I K mi mk hsmall
  let hOld := cartesianLiftToOld_hOld (J := J) φ K k
  let hOldsmall := cartesianLiftToOld_hOld (J := J) φ K mk
  let β := (cartesianLiftToOldHomOver (J := J) D φ hφ α).family I K i k h
  let βsmall := (cartesianLiftToOldHomOver (J := J) D φ hφ α).family I K mi mk hsmall
  let βpull :=
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := canonicalFiberPseudofunctor X.p) β m mi mk hmi hmk
  let oldComp :=
    (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family
      K L k k hOld
  let oldCompSmall :=
    (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family
      K L mk mk hOldsmall
  let αcomp := α.family I L i k hα
  let αsmall := α.family I L mi mk hαsmall
  have hfac : β ≫ oldComp = αcomp := by
    simpa [β, oldComp, αcomp, L, hα, hOld] using
      cartesianLiftToOldHomOver_fac (J := J) D φ hφ α I K i k h
  have hOldNat :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p) oldComp m mk mk hmk hmk =
        oldCompSmall := by
    have hnat :=
      (DescentCompletionObject.oldMap (J := J) X φ).components.naturality
        K L k k hOld m mk mk hmk hmk
    simpa [oldComp, oldCompSmall, hOldsmall] using hnat
  have hαNat :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p) αcomp m mi mk hmi hmk =
        αsmall := by
    have hnat := hαnat I L i k hα m mi mk hmi hmk
    simpa [αcomp, αsmall, hαsmall] using hnat
  have hβpullFac : βpull ≫ oldCompSmall = αsmall := by
    have hpullFac :=
      congrArg
        (fun q =>
          Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p) q m mi mk hmi hmk)
        hfac
    have hpullComp :
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p) (β ≫ oldComp) m mi mk hmi hmk =
          βpull ≫
            Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (F := canonicalFiberPseudofunctor X.p) oldComp m mk mk hmk hmk := by
      simpa [βpull] using
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
          (F := canonicalFiberPseudofunctor X.p)
          β oldComp m mi mk mk hmi hmk hmk
    have hpullFac' :
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p) (β ≫ oldComp) m mi mk hmi hmk =
          Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p) αcomp m mi mk hmi hmk := by
      simpa using hpullFac
    rw [hpullComp, hOldNat, hαNat] at hpullFac'
    exact hpullFac'
  apply Functor.Fiber.hom_ext
  change βpull.1 = βsmall.1
  let xMap := DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X xF K mk
  have hxMapCart : X.p.IsStronglyCartesian (mk ≫ K.f) xMap :=
    DescentCompletionObjectOver.ofFiberObjectRestrictedMap_isStronglyCartesian
      (J := J) X xF K mk
  have hleftLift : X.p.IsHomLift (𝟙 W') βpull.1 := βpull.2
  have hrightLift : X.p.IsHomLift (𝟙 W') βsmall.1 := βsmall.2
  apply @Functor.IsStronglyCartesian.ext _ _ _ _ X.p
    W' (X.p.obj a)
    ((DescentCompletionObject.oldObject (J := J) X a).object.restrictedLocalObject K mk).1
    a
    (mk ≫ K.f) xMap hxMapCart
    W' (D.restrictedLocalObject I mi).1
    (𝟙 W') βpull.1 βsmall.1 hleftLift hrightLift
  let leftX : (D.restrictedLocalObject I mi).1 ⟶ a := βpull.1 ≫ xMap
  let rightX : (D.restrictedLocalObject I mi).1 ⟶ a := βsmall.1 ≫ xMap
  have hxMapLift : X.p.IsHomLift (mk ≫ K.f) xMap := hxMapCart.toIsHomLift
  have hleftXLift : X.p.IsHomLift (mk ≫ K.f) leftX := by
    have hcomp : X.p.IsHomLift (𝟙 W' ≫ (mk ≫ K.f)) (βpull.1 ≫ xMap) :=
      @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 W') (mk ≫ K.f)
        βpull.1 xMap hleftLift hxMapLift
    simpa [leftX] using hcomp
  have hrightXLift : X.p.IsHomLift (mk ≫ K.f) rightX := by
    have hcomp : X.p.IsHomLift (𝟙 W' ≫ (mk ≫ K.f)) (βsmall.1 ≫ xMap) :=
      @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 W') (mk ≫ K.f)
        βsmall.1 xMap hrightLift hxMapLift
    simpa [rightX] using hcomp
  apply @Functor.IsStronglyCartesian.ext _ _ _ _ X.p
    (X.p.obj a) (X.p.obj b) a b
    (X.p.map φ) φ hφ
    W' (D.restrictedLocalObject I mi).1
    (mk ≫ K.f) leftX rightX hleftXLift hrightXLift
  let yMap := DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X yF L mk
  have hφLift : X.p.IsHomLift (X.p.map φ) φ := hφ.toIsHomLift
  have hOldFac : oldCompSmall.1 ≫ yMap = xMap ≫ φ := by
    simpa [DescentCompletionObject.oldMap, DescentCompletionObject.oldObject,
      xF, yF, xMap, yMap, oldCompSmall] using
      @DescentCompletionObjectOver.ofFiberHomComponent_fac _ _ J X
        (X.p.obj a) (X.p.obj b) W'
        xF yF (X.p.map φ) φ hφLift K L mk mk hOldsmall
  have hβpullProj : leftX ≫ φ = αsmall.1 ≫ yMap := by
    have hfacVal : (βpull ≫ oldCompSmall).1 = αsmall.1 :=
      congrArg Subtype.val hβpullFac
    calc
      leftX ≫ φ = (βpull.1 ≫ xMap) ≫ φ := by
        rfl
      _ = βpull.1 ≫ (xMap ≫ φ) := by
        rw [Category.assoc]
      _ = βpull.1 ≫ (oldCompSmall.1 ≫ yMap) := by
        exact congrArg (fun q => βpull.1 ≫ q) hOldFac.symm
      _ = (βpull.1 ≫ oldCompSmall.1) ≫ yMap := by
        rw [← Category.assoc]
      _ = (βpull ≫ oldCompSmall).1 ≫ yMap := by
        change (βpull.1 ≫ oldCompSmall.1) ≫ yMap =
          (βpull.1 ≫ oldCompSmall.1) ≫ yMap
        rfl
      _ = αsmall.1 ≫ yMap := by
        rw [hfacVal]
  have hβsmallProj : rightX ≫ φ = αsmall.1 ≫ yMap := by
    have hproj :
        βsmall.1 ≫ xMap ≫ φ = αsmall.1 ≫ yMap := by
      simpa [βsmall, xMap, yMap, αsmall, L, hαsmall, xF, yF] using
        cartesianLiftToOldFamily_oldRestrictedMap_comp
          (J := J) D φ hφ α I K mi mk hsmall
    simpa [rightX, Category.assoc] using hproj
  exact hβpullProj.trans hβsmallProj.symm

end HomOver

namespace NaturalHomOver

/-- Source stage 3.10, the cartesian lift bundled with the restriction/naturality law. -/
noncomputable def cartesianLiftToOld
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.NaturalHomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ)) :
    DescentCompletionObjectOver.NaturalHomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X a).object g where
  toHomOver :=
    HomOver.cartesianLiftToOldHomOver (J := J) D φ hφ α.toHomOver
  naturality :=
    HomOver.cartesianLiftToOldHomOver_familyNaturality'
      (J := J) D φ hφ α.toHomOver α.naturality

@[simp]
theorem cartesianLiftToOld_toHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.NaturalHomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ)) :
    (cartesianLiftToOld (J := J) D φ hφ α).toHomOver =
      HomOver.cartesianLiftToOldHomOver (J := J) D φ hφ α.toHomOver :=
  rfl

/-- Source stage 3.10, component factorization for the bundled natural lift. -/
theorem cartesianLiftToOld_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.NaturalHomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ))
    {W : C} (I : D.cover.Arrow)
    (K : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ g = k ≫ K.f) :
    let L := HomOver.oldMapTargetCoverArrow (J := J) φ K
    let hα := HomOver.cartesianLiftToOld_hα (J := J) φ I K i k h
    let hOld := HomOver.cartesianLiftToOld_hOld (J := J) φ K k
    (cartesianLiftToOld (J := J) D φ hφ α).toHomOver.family I K i k h ≫
        (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family
          K L k k hOld =
      α.toHomOver.family I L i k hα := by
  intro L hα hOld
  simpa [cartesianLiftToOld] using
    HomOver.cartesianLiftToOldHomOver_fac
      (J := J) D φ hφ α.toHomOver I K i k h

end NaturalHomOver

end DescentCompletionObjectOver

namespace DescentCompletionObject
namespace Hom

/-- Source stage 3.10, total morphism lift when the incoming component family is already typed
over the strict composite base `g ≫ p(φ)`. -/
noncomputable def cartesianLiftToOldOfComponents
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : D.base ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.NaturalHomOver (J := J) D.object
      (oldObject (J := J) X b).object (g ≫ X.p.map φ)) :
    Hom (J := J) D (oldObject (J := J) X a) where
  base := g
  components :=
    DescentCompletionObjectOver.NaturalHomOver.cartesianLiftToOld
      (J := J) D.object φ hφ α

@[simp]
theorem cartesianLiftToOldOfComponents_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : D.base ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.NaturalHomOver (J := J) D.object
      (oldObject (J := J) X b).object (g ≫ X.p.map φ)) :
    (cartesianLiftToOldOfComponents (J := J) D φ hφ α).base = g :=
  rfl

@[simp]
theorem cartesianLiftToOldOfComponents_components
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : D.base ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.NaturalHomOver (J := J) D.object
      (oldObject (J := J) X b).object (g ≫ X.p.map φ)) :
    (cartesianLiftToOldOfComponents (J := J) D φ hφ α).components =
      DescentCompletionObjectOver.NaturalHomOver.cartesianLiftToOld
        (J := J) D.object φ hφ α :=
  rfl

/-- Source stage 3.10, component factorization for the strict total lift. -/
theorem cartesianLiftToOldOfComponents_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : D.base ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.NaturalHomOver (J := J) D.object
      (oldObject (J := J) X b).object (g ≫ X.p.map φ))
    {W : C} (I : D.object.cover.Arrow)
    (K : (oldObject (J := J) X a).object.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ g = k ≫ K.f) :
    let L := DescentCompletionObjectOver.HomOver.oldMapTargetCoverArrow (J := J) φ K
    let hα := DescentCompletionObjectOver.HomOver.cartesianLiftToOld_hα
      (J := J) φ I K i k h
    let hOld := DescentCompletionObjectOver.HomOver.cartesianLiftToOld_hOld
      (J := J) φ K k
    (cartesianLiftToOldOfComponents (J := J) D φ hφ α).components.toHomOver.family
          I K i k h ≫
        (oldMap (J := J) X φ).components.toHomOver.family K L k k hOld =
      α.toHomOver.family I L i k hα := by
  intro L hα hOld
  simpa [cartesianLiftToOldOfComponents] using
    DescentCompletionObjectOver.NaturalHomOver.cartesianLiftToOld_fac
      (J := J) D.object φ hφ α I K i k h

/-- Source stage 3.10, total descent-completion morphism produced by cartesian lifting through an
old-object arrow.  The base-equality parameter records the source-text condition that
`α : D ⟶ G(b)` lies over `g ≫ p(φ)`. -/
noncomputable def cartesianLiftToOld
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : D.base ⟶ X.p.obj a}
    (α : Hom (J := J) D (oldObject (J := J) X b))
    (hαbase : g ≫ X.p.map φ = α.base) :
    Hom (J := J) D (oldObject (J := J) X a) := by
  let αcomponents :
      DescentCompletionObjectOver.NaturalHomOver (J := J) D.object
        (oldObject (J := J) X b).object (g ≫ X.p.map φ) := by
    exact hαbase.symm ▸ α.components
  exact
    cartesianLiftToOldOfComponents (J := J) D φ hφ αcomponents

@[simp]
theorem cartesianLiftToOld_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : D.base ⟶ X.p.obj a}
    (α : Hom (J := J) D (oldObject (J := J) X b))
    (hαbase : g ≫ X.p.map φ = α.base) :
    (cartesianLiftToOld (J := J) D φ hφ α hαbase).base = g := by
  rfl

end Hom
end DescentCompletionObject

end FibredCategoryMor

end CategoryTheory
