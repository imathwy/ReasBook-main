import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.DescentCompletionCore

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

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.7, component-level functoriality on old objects: the sheaf-glued composite
of two singleton-cover morphisms is the singleton-cover morphism induced by the composite total
morphism. -/
theorem ofFiberHom_comp_family
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z W : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) (z : X.p.Fiber Z)
    {b : U ⟶ V} {c : V ⟶ Z}
    (f : x.1 ⟶ y.1) (g : y.1 ⟶ z.1)
    [X.p.IsHomLift b f] [X.p.IsHomLift c g]
    [X.p.IsHomLift (b ≫ c) (f ≫ g)]
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (I : (ofFiberObject (J := J) X x).cover.Arrow)
    (L : (ofFiberObject (J := J) X z).cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ (b ≫ c) = l ≫ L.f) :
    compositionFamily (J := J) hSheaf
        (ofFiberHom (J := J) x y (b := b) f)
        (ofFiberHom (J := J) y z (b := c) g)
        (ofFiberHom_familyNaturality' (J := J) x y (b := b) f)
        (ofFiberHom_familyNaturality' (J := J) y z (b := c) g)
        I L i l h =
      (ofFiberHom (J := J) x z (b := b ≫ c) (f ≫ g)).family I L i l h := by
  let hbase : i ≫ I.f ≫ b ≫ c = l ≫ L.f := by
    simpa [Category.assoc] using h
  let S := compositionMiddleCover (J := J)
    (D := ofFiberObject (J := J) X x)
    (E := ofFiberObject (J := J) X y)
    (H := ofFiberObject (J := J) X z)
    (f := b) (g := c) I L i l hbase
  apply fiberHom_ext_of_cover (J := J) X.p S
    ((ofFiberObject (J := J) X x).restrictedLocalObject I i)
    ((ofFiberObject (J := J) X z).restrictedLocalObject L l)
    (hSheaf W ((ofFiberObject (J := J) X x).restrictedLocalObject I i)
      ((ofFiberObject (J := J) X z).restrictedLocalObject L l))
  intro Kp
  let hsmall : (Kp.f ≫ i) ≫ I.f ≫ (b ≫ c) = (Kp.f ≫ l) ≫ L.f := by
    simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) h
  let hαK : (Kp.f ≫ i) ≫ I.f ≫ b = 𝟙 Kp.Y ≫ Kp.base.f := by
    simp [S, compositionMiddleCover, Category.assoc]
  let hβK : 𝟙 Kp.Y ≫ Kp.base.f ≫ c = (Kp.f ≫ l) ≫ L.f := by
    simpa [S, compositionMiddleCover, Category.assoc] using
      congrArg (fun q => Kp.f ≫ q) hbase
  let α := ofFiberHom (J := J) x y (b := b) f
  let β := ofFiberHom (J := J) y z (b := c) g
  let hαnat : familyNaturality' (J := J) α :=
    ofFiberHom_familyNaturality' (J := J) x y (b := b) f
  let hβnat : familyNaturality' (J := J) β :=
    ofFiberHom_familyNaturality' (J := J) y z (b := c) g
  let localComp := localComposite (J := J) α β I Kp.base L
    (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l) hαK hβK
  have hleftPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf α β hαnat hβnat I L i l h)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        localComp := by
    have hglue := compositionGluedComponent_pullHom_of_fac (J := J)
      α β hαnat hβnat I L i l hbase
      (hSheaf W ((ofFiberObject (J := J) X x).restrictedLocalObject I i)
        ((ofFiberObject (J := J) X z).restrictedLocalObject L l)) Kp
      (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl hαK hβK
    simpa [compositionFamily, localComp, α, β, hαnat, hβnat, Category.assoc] using hglue
  have hlocal :
      localComp =
        (ofFiberHom (J := J) x z (b := b ≫ c) (f ≫ g)).family
          I L (Kp.f ≫ i) (Kp.f ≫ l) hsmall := by
    let aComp := ofFiberHomComponent (J := J) x y f I Kp.base
      (Kp.f ≫ i) (𝟙 Kp.Y) hαK
    let bComp := ofFiberHomComponent (J := J) y z g Kp.base L
      (𝟙 Kp.Y) (Kp.f ≫ l) hβK
    let cComp := ofFiberHomComponent (J := J) x z (f ≫ g) I L
      (Kp.f ≫ i) (Kp.f ≫ l) hsmall
    change aComp ≫ bComp = cComp
    apply Functor.Fiber.hom_ext
    change (aComp ≫ bComp).1 = cComp.1
    let τ := ofFiberObjectRestrictedMap (J := J) X z L (Kp.f ≫ l)
    have hτ : X.p.IsStronglyCartesian ((Kp.f ≫ l) ≫ L.f) τ :=
      ofFiberObjectRestrictedMap_isStronglyCartesian (J := J) X z L (Kp.f ≫ l)
    letI : X.p.IsStronglyCartesian ((Kp.f ≫ l) ≫ L.f) τ := hτ
    haveI : X.p.IsHomLift (𝟙 Kp.Y) (aComp ≫ bComp).1 := (aComp ≫ bComp).2
    haveI : X.p.IsHomLift (𝟙 Kp.Y) cComp.1 := cComp.2
    apply Functor.IsStronglyCartesian.ext X.p ((Kp.f ≫ l) ≫ L.f) τ (𝟙 Kp.Y)
    let xMap := ofFiberObjectRestrictedMap (J := J) X x I (Kp.f ≫ i)
    let yMap := ofFiberObjectRestrictedMap (J := J) X y Kp.base (𝟙 Kp.Y)
    have ha : aComp.1 ≫ yMap = xMap ≫ f := by
      simpa [aComp, xMap, yMap] using
        ofFiberHomComponent_fac (J := J) x y f I Kp.base
          (Kp.f ≫ i) (𝟙 Kp.Y) hαK
    have hb : bComp.1 ≫ τ = yMap ≫ g := by
      simpa [bComp, yMap, τ] using
        ofFiberHomComponent_fac (J := J) y z g Kp.base L
          (𝟙 Kp.Y) (Kp.f ≫ l) hβK
    have hc : cComp.1 ≫ τ = xMap ≫ (f ≫ g) := by
      simpa [cComp, xMap, τ] using
        ofFiberHomComponent_fac (J := J) x z (f ≫ g) I L
          (Kp.f ≫ i) (Kp.f ≫ l) hsmall
    calc
      (aComp ≫ bComp).1 ≫ τ = (aComp.1 ≫ bComp.1) ≫ τ := by rfl
      _ = aComp.1 ≫ (bComp.1 ≫ τ) := by rw [Category.assoc]
      _ = aComp.1 ≫ (yMap ≫ g) := by rw [hb]
      _ = (aComp.1 ≫ yMap) ≫ g := by rw [Category.assoc]
      _ = (xMap ≫ f) ≫ g := by rw [ha]
      _ = xMap ≫ (f ≫ g) := by rw [Category.assoc]
      _ = cComp.1 ≫ τ := by rw [hc]
  have hrightPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          ((ofFiberHom (J := J) x z (b := b ≫ c) (f ≫ g)).family I L i l h)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        (ofFiberHom (J := J) x z (b := b ≫ c) (f ≫ g)).family
          I L (Kp.f ≫ i) (Kp.f ≫ l) hsmall := by
    simpa [hsmall] using
      (ofFiberHom_familyNaturality' (J := J) x z (b := b ≫ c) (f ≫ g))
        I L i l h Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  have hpull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf α β hαnat hβnat I L i l h)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          ((ofFiberHom (J := J) x z (b := b ≫ c) (f ≫ g)).family I L i l h)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl := by
    rw [hleftPull, hrightPull, hlocal]
  have hmapLeft :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := compositionFamily (J := J) hSheaf α β hαnat hβnat I L i l h)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  have hmapRight :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := (ofFiberHom (J := J) x z (b := b ≫ c) (f ≫ g)).family I L i l h)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  rw [hmapLeft, hmapRight, hpull]

end HomOver

namespace NaturalHomOver

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.7, bundled functoriality on old-object morphisms. -/
theorem ofFiberHom_comp
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) (z : X.p.Fiber Z)
    {b : U ⟶ V} {c : V ⟶ Z}
    (f : x.1 ⟶ y.1) (g : y.1 ⟶ z.1)
    [X.p.IsHomLift b f] [X.p.IsHomLift c g]
    [X.p.IsHomLift (b ≫ c) (f ≫ g)]
    (hSheaf : HomOver.homPresheavesAreSheaves (J := J) X) :
    compose (J := J) hSheaf
        (ofFiberHom (J := J) x y (b := b) f)
        (ofFiberHom (J := J) y z (b := c) g) =
      ofFiberHom (J := J) x z (b := b ≫ c) (f ≫ g) := by
  apply ext_family
  intro W I L i l h
  simpa [compose, composeOfNaturality, composeCandidate] using
    HomOver.ofFiberHom_comp_family (J := J) x y z f g hSheaf I L i l h

end NaturalHomOver

end DescentCompletionObjectOver

namespace DescentCompletionObject

namespace Hom

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.7, total morphism functoriality on old objects. -/
theorem ofFiberHom_comp
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U V Z : C}
    (x : X.p.Fiber U) (y : X.p.Fiber V) (z : X.p.Fiber Z)
    {b : U ⟶ V} {c : V ⟶ Z}
    (f : x.1 ⟶ y.1) (g : y.1 ⟶ z.1)
    [X.p.IsHomLift b f] [X.p.IsHomLift c g]
    [X.p.IsHomLift (b ≫ c) (f ≫ g)]
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    compose (J := J) hSheaf
        (ofFiberHom (J := J) x y (b := b) f)
        (ofFiberHom (J := J) y z (b := c) g) =
      ofFiberHom (J := J) x z (b := b ≫ c) (f ≫ g) := by
  refine Hom.ext_base_family
    (compose (J := J) hSheaf
      (ofFiberHom (J := J) x y (b := b) f)
      (ofFiberHom (J := J) y z (b := c) g))
    (ofFiberHom (J := J) x z (b := b ≫ c) (f ≫ g)) rfl ?_
  intro W I L i l h
  simpa [compose, ofFiberHom] using
    congrArg
      (fun α : DescentCompletionObjectOver.NaturalHomOver (J := J)
          (DescentCompletionObjectOver.ofFiberObject (J := J) X x)
          (DescentCompletionObjectOver.ofFiberObject (J := J) X z) (b ≫ c) =>
        α.toHomOver.family I L i l h)
      (DescentCompletionObjectOver.NaturalHomOver.ofFiberHom_comp
        (J := J) x y z f g hSheaf)

end Hom

/-- The object part of the source stage 3.7 embedding `G : S ⟶ S'`: an old object is sent to
the singleton-cover descent datum. -/
noncomputable def oldObject
    (X : FibredCategoryOver.{u, v, uX, vX} C) (a : X.S) :
    DescentCompletionObject (J := J) X :=
  ofFiberObject (J := J) X (Functor.Fiber.mk (p := X.p) (a := a) rfl)

/-- The morphism part of the source stage 3.7 embedding on old objects. -/
noncomputable def oldMap
    (X : FibredCategoryOver.{u, v, uX, vX} C) {a b : X.S} (f : a ⟶ b) :
    Hom (J := J) (oldObject (J := J) X a) (oldObject (J := J) X b) := by
  have hLift : X.p.IsHomLift (X.p.map f) f := Functor.IsHomLift.map f
  exact @Hom.ofFiberHom _ _ J X (X.p.obj a) (X.p.obj b)
    (Functor.Fiber.mk (p := X.p) (a := a) rfl)
    (Functor.Fiber.mk (p := X.p) (a := b) rfl)
    (X.p.map f) f hLift

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem oldMap_id
    (X : FibredCategoryOver.{u, v, uX, vX} C) (a : X.S) :
    oldMap (J := J) X (𝟙 a) = identity (J := J) (oldObject (J := J) X a) := by
  refine Hom.ext_base_family (oldMap (J := J) X (𝟙 a))
    (identity (J := J) (oldObject (J := J) X a)) ?_ ?_
  · simp [oldMap, identity, oldObject]
  · intro W I K i k h
    let xF : X.p.Fiber (X.p.obj a) := Functor.Fiber.mk (p := X.p) (a := a) rfl
    letI : X.p.IsHomLift (𝟙 (X.p.obj a)) (𝟙 a) := CategoryTheory.IsHomLift.id xF.2
    have hId := DescentCompletionObjectOver.HomOver.ofFiberHom_id (J := J) xF
    have hFam := congrArg
      (fun α : DescentCompletionObjectOver.HomOver (J := J)
          (DescentCompletionObjectOver.ofFiberObject (J := J) X xF)
          (DescentCompletionObjectOver.ofFiberObject (J := J) X xF) (𝟙 (X.p.obj a)) =>
        α.family I K i k (by simpa [oldMap, oldObject, xF] using h)) hId
    simpa [oldMap, oldObject, identity, xF] using hFam

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
theorem oldMap_comp
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {a b c : X.S} (f : a ⟶ b) (g : b ⟶ c) :
    Hom.compose (J := J) hSheaf (oldMap (J := J) X f) (oldMap (J := J) X g) =
      oldMap (J := J) X (f ≫ g) := by
  refine Hom.ext_base_family
    (Hom.compose (J := J) hSheaf (oldMap (J := J) X f) (oldMap (J := J) X g))
    (oldMap (J := J) X (f ≫ g)) ?_ ?_
  · simp [oldMap, Hom.compose, Functor.map_comp]
  · intro W I L i l h
    let xF : X.p.Fiber (X.p.obj a) := Functor.Fiber.mk (p := X.p) (a := a) rfl
    let yF : X.p.Fiber (X.p.obj b) := Functor.Fiber.mk (p := X.p) (a := b) rfl
    let zF : X.p.Fiber (X.p.obj c) := Functor.Fiber.mk (p := X.p) (a := c) rfl
    have hfLift : X.p.IsHomLift (X.p.map f) f := Functor.IsHomLift.map f
    have hgLift : X.p.IsHomLift (X.p.map g) g := Functor.IsHomLift.map g
    letI : X.p.IsHomLift (X.p.map f) f := hfLift
    letI : X.p.IsHomLift (X.p.map g) g := hgLift
    have hfgLift : X.p.IsHomLift (X.p.map f ≫ X.p.map g) (f ≫ g) :=
      IsHomLift.comp X.p (X.p.map f) (X.p.map g) f g
    letI : X.p.IsHomLift (X.p.map f ≫ X.p.map g) (f ≫ g) := hfgLift
    simpa [oldMap, oldObject, Hom.compose, Functor.map_comp, xF, yF, zF] using
      DescentCompletionObjectOver.HomOver.ofFiberHom_comp_family
        (J := J) xF yF zF f g hSheaf I L i l
          (by simpa [oldMap, Hom.compose, Functor.map_comp, xF, yF, zF] using h)

/-- Source stage 3.7 as an ordinary functor into the descent-completion category. -/
noncomputable def oldObjectFunctor
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    letI := category (J := J) hSheaf
    X.S ⥤ DescentCompletionObject (J := J) X := by
  letI := category (J := J) hSheaf
  exact
    { obj := fun a => oldObject (J := J) X a
      map := fun {a b} f => oldMap (J := J) X f
      map_id := by
        intro a
        exact oldMap_id (J := J) X a
      map_comp := by
        intro a b c f g
        exact (oldMap_comp (J := J) X hSheaf f g).symm }

/-- Source stage 3.7 as a based functor over the site base. -/
noncomputable def oldObjectBasedFunctor
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    letI := category (J := J) hSheaf
    BasedCategory.ofFunctor X.p ⥤ᵇ
      BasedCategory.ofFunctor (projectionFunctor (J := J) hSheaf) := by
  letI := category (J := J) hSheaf
  exact
    { toFunctor := oldObjectFunctor (J := J) X hSheaf
      w := by
        rfl }

end DescentCompletionObject

end FibredCategoryMor

end CategoryTheory
