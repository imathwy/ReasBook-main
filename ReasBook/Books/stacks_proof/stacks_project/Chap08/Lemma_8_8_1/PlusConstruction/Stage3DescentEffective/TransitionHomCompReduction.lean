import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.TransitionComponent
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.TransitionLaws

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

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.13 component expansion for a composite: if a visible middle cover member
`K` lies over the source and target local pieces, then the sheaf-glued component of
`Hom.compose α β` is the ordinary local composite through `K`.

This is the source proof's "restrict the glued composite to the middle cover, where it is
`β_jk ∘ α_ij`" step, specialized to the case where the middle cover has the displayed global
section. -/
theorem Hom.compose_component_eq_of_middle
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {D E H : DescentCompletionObject (J := J) X}
    (α : Hom (J := J) D E) (β : Hom (J := J) E H)
    {W : C} (I : D.object.cover.Arrow) (K : E.object.cover.Arrow)
    (L : H.object.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y) (l : W ⟶ L.Y)
    (hα : i ≫ I.f ≫ α.base = k ≫ K.f)
    (hβ : k ≫ K.f ≫ β.base = l ≫ L.f) :
    α.components.toHomOver.family I K i k hα ≫
        β.components.toHomOver.family K L k l hβ =
      (Hom.compose (J := J) hSheaf α β).components.toHomOver.family I L i l
        (by
          calc
            i ≫ I.f ≫ (α.base ≫ β.base) = k ≫ K.f ≫ β.base := by
              simpa [Category.assoc] using congrArg (fun q => q ≫ β.base) hα
            _ = l ≫ L.f := hβ) := by
  let hcomp : i ≫ I.f ≫ α.base ≫ β.base = l ≫ L.f := by
    calc
      i ≫ I.f ≫ α.base ≫ β.base = k ≫ K.f ≫ β.base := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ β.base) hα
      _ = l ≫ L.f := hβ
  let S :=
    DescentCompletionObjectOver.HomOver.compositionMiddleCover
      (J := J) (D := D.object) (E := E.object) (H := H.object)
      (f := α.base) (g := β.base) I L i l hcomp
  let Kp : S.Arrow :=
    { Y := W
      f := 𝟙 W
      hf := by
        have hK : E.object.cover (k ≫ K.f) :=
          (E.object.cover : Sieve E.base).downward_closed K.hf k
        simpa [S, DescentCompletionObjectOver.HomOver.compositionMiddleCover,
          Category.assoc, hα] using hK }
  let hmid : k ≫ K.f = (𝟙 Kp.Y : Kp.Y ⟶ Kp.base.Y) ≫ Kp.base.f := by
    simp [Kp, S, DescentCompletionObjectOver.HomOver.compositionMiddleCover,
      hα]
  let hαK :
      i ≫ I.f ≫ α.base =
        (𝟙 Kp.Y : Kp.Y ⟶ Kp.base.Y) ≫ Kp.base.f := by
    simp [Kp, S, DescentCompletionObjectOver.HomOver.compositionMiddleCover]
  let hβK :
      (𝟙 Kp.Y : Kp.Y ⟶ Kp.base.Y) ≫ Kp.base.f ≫ β.base =
        l ≫ L.f := by
    simpa [Kp, S, DescentCompletionObjectOver.HomOver.compositionMiddleCover,
      Category.assoc, hα] using hβ
  let e :=
    (E.object.overlapIso (I₁ := K) (I₂ := Kp.base)
      k (𝟙 Kp.Y : Kp.Y ⟶ Kp.base.Y) hmid).hom
  have hαcompat :
      α.components.toHomOver.family I Kp.base i (𝟙 Kp.Y) hαK =
        α.components.toHomOver.family I K i k hα ≫ e := by
    have hcompat := α.components.toHomOver.compatible
      I I K Kp.base i i k (𝟙 Kp.Y) rfl hmid hα hαK
    rw [DescentCompletionObjectOver.overlapIso_self_hom (J := J) D.object I i] at hcompat
    simpa [e] using hcompat
  have hβcompat :
      e ≫ β.components.toHomOver.family Kp.base L (𝟙 Kp.Y) l hβK =
        β.components.toHomOver.family K L k l hβ := by
    have hcompat := β.components.toHomOver.compatible
      K Kp.base L L k (𝟙 Kp.Y) l l hmid rfl hβ hβK
    rw [DescentCompletionObjectOver.overlapIso_self_hom (J := J) H.object L l] at hcompat
    simpa [e] using hcompat
  have hlocal :
      α.components.toHomOver.family I K i k hα ≫
          β.components.toHomOver.family K L k l hβ =
        DescentCompletionObjectOver.HomOver.localComposite
          (J := J) α.components.toHomOver β.components.toHomOver
          I Kp.base L i (𝟙 Kp.Y) l hαK hβK := by
    dsimp [DescentCompletionObjectOver.HomOver.localComposite]
    calc
      α.components.toHomOver.family I K i k hα ≫
          β.components.toHomOver.family K L k l hβ =
        α.components.toHomOver.family I K i k hα ≫
          (e ≫ β.components.toHomOver.family Kp.base L (𝟙 Kp.Y) l hβK) := by
            rw [hβcompat]
      _ =
        (α.components.toHomOver.family I K i k hα ≫ e) ≫
          β.components.toHomOver.family Kp.base L (𝟙 Kp.Y) l hβK := by
            rw [Category.assoc]
      _ =
        α.components.toHomOver.family I Kp.base i (𝟙 Kp.Y) hαK ≫
          β.components.toHomOver.family Kp.base L (𝟙 Kp.Y) l hβK := by
            rw [← hαcompat]
  have hglue :=
    DescentCompletionObjectOver.HomOver.compositionGluedComponent_pullHom_of_fac
      (J := J) α.components.toHomOver β.components.toHomOver
      α.components.naturality β.components.naturality I L i l hcomp
      (hSheaf W (D.object.restrictedLocalObject I i) (H.object.restrictedLocalObject L l))
      Kp i l (by simp [Kp]) (by simp [Kp]) hαK hβK
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_id] at hglue
  rw [hlocal, ← hglue]
  rfl

/-- Source stage 3.13 cocycle law for the explicit pullback-cover component of the transported
outer transition.

This is the component-level form of the source equality
`Theta_bc * Theta_ab = Theta_ac`, before transporting back through the inner local-object
overlap isomorphisms. -/
def projectionDescentTotalCoverExplicitTransitionComponentHomCompLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) : Prop :=
  ∀ ⦃Y : C⦄
    ⦃A B K : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow⦄
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y) (k : Y ⟶ K.Y)
    (hab : a ≫ A.f = b ≫ B.f) (hbk : b ≫ B.f = k ≫ K.f),
      projectionDescentTotalCoverExplicitTransitionComponent
          (J := J) hSheaf D A B a b hab ≫
        projectionDescentTotalCoverExplicitTransitionComponent
          (J := J) hSheaf D B K b k hbk =
      projectionDescentTotalCoverExplicitTransitionComponent
        (J := J) hSheaf D A K a k (hab.trans hbk)

/-- Change only the displayed base map in a `ProjectionDescentDatum.hom`; after the base maps
are identified, the remaining proof arguments are proof-irrelevant by `congr`. -/
theorem projectionDescentDatumHom_congr_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    {I K : S.Arrow}
    {q₁ q₂ : W ⟶ U} (hq : q₁ = q₂)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (hi₁ : i ≫ I.f = q₁) (hk₁ : k ≫ K.f = q₁)
    (hi₂ : i ≫ I.f = q₂) (hk₂ : k ≫ K.f = q₂) :
    D.hom q₁ i k hi₁ hk₁ = D.hom q₂ i k hi₂ hk₂ := by
  cases hq
  congr

/-- The outer transitions supplied by the original descent datum compose after restricting to
members of the stage-3 total cover. -/
theorem projectionDescentOuterFiberHomForTotalCover_hom_comp
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B K : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y) (k : Y ⟶ K.Y)
    (hab : a ≫ A.f = b ≫ B.f) (hbk : b ≫ B.f = k ≫ K.f) :
    letI := category (J := J) hSheaf
    projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D A B a b hab ≫
      projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D B K b k hbk =
    projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D A K a k
      (hab.trans hbk) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let IB := projectionDescentTotalCoverOuter (J := J) hSheaf D B
  let IK := projectionDescentTotalCoverOuter (J := J) hSheaf D K
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fB := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b
  let fK := projectionDescentTotalCoverOuterMap (J := J) hSheaf D K k
  let hAB : fA ≫ IA.f = fB ≫ IB.f :=
    projectionDescentTotalCoverOuterMap_fac (J := J) hSheaf D A B a b hab
  let hBK : fB ≫ IB.f = fK ≫ IK.f :=
    projectionDescentTotalCoverOuterMap_fac (J := J) hSheaf D B K b k hbk
  let hAK : fA ≫ IA.f = fK ≫ IK.f :=
    projectionDescentTotalCoverOuterMap_fac (J := J) hSheaf D A K a k (hab.trans hbk)
  have hbase :
      D.hom (fB ≫ IB.f) fB fK rfl hBK.symm =
        D.hom (fA ≫ IA.f) fB fK hAB.symm hAK.symm := by
    exact
      projectionDescentDatumHom_congr_base (J := J) hSheaf D hAB.symm
        fB fK rfl hBK.symm hAB.symm hAK.symm
  dsimp [projectionDescentOuterFiberHomForTotalCover, projectionDescentOuterFiberHom]
  change D.hom (fA ≫ IA.f) fA fB rfl hAB.symm ≫
      D.hom (fB ≫ IB.f) fB fK rfl hBK.symm =
    D.hom (fA ≫ IA.f) fA fK rfl hAK.symm
  rw [hbase]
  exact D.hom_comp (fA ≫ IA.f) fA fB fK rfl hAB.symm hAK.symm

/-- After transporting the outer transitions to the explicit pullback owners, their composite is
still the transported outer transition. -/
theorem projectionDescentExplicitOuterFiberHomForTotalCover_hom_comp
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B K : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y) (k : Y ⟶ K.Y)
    (hab : a ≫ A.f = b ≫ B.f) (hbk : b ≫ B.f = k ≫ K.f) :
    letI := category (J := J) hSheaf
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A B a b hab ≫
      projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D B K b k hbk =
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A K a k
      (hab.trans hbk) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let eA :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  let eB :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D B)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
  let eK :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D K)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D K k)
  let outerAB := projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D A B a b hab
  let outerBK := projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D B K b k hbk
  let outerAK :=
    projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D A K a k (hab.trans hbk)
  have houter : outerAB ≫ outerBK = outerAK := by
    simpa [outerAB, outerBK, outerAK] using
      projectionDescentOuterFiberHomForTotalCover_hom_comp
        (J := J) hSheaf D A B K a b k hab hbk
  have houterF :
      Functor.Fiber.fiberInclusion.map outerAB ≫
          Functor.Fiber.fiberInclusion.map outerBK =
        Functor.Fiber.fiberInclusion.map outerAK := by
    have h := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) houter
    simpa only [Functor.map_comp] using h
  have hcancelF :
      Functor.Fiber.fiberInclusion.map eB.inv ≫
          Functor.Fiber.fiberInclusion.map eB.hom =
        𝟙 _ := by
    have h := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) eB.inv_hom_id
    simpa only [Functor.map_comp, Functor.map_id] using h
  apply Functor.Fiber.hom_ext
  rw [Functor.map_comp]
  dsimp [projectionDescentExplicitOuterFiberHomForTotalCover]
  change (Functor.Fiber.fiberInclusion.map eA.hom ≫
      Functor.Fiber.fiberInclusion.map outerAB ≫
      Functor.Fiber.fiberInclusion.map eB.inv) ≫
      Functor.Fiber.fiberInclusion.map eB.hom ≫
      Functor.Fiber.fiberInclusion.map outerBK ≫
      Functor.Fiber.fiberInclusion.map eK.inv =
    Functor.Fiber.fiberInclusion.map eA.hom ≫
      Functor.Fiber.fiberInclusion.map outerAK ≫
      Functor.Fiber.fiberInclusion.map eK.inv
  let inc : P.Fiber Y ⥤ DescentCompletionObject (J := J) X :=
    Functor.Fiber.fiberInclusion
  calc
    (inc.map eA.hom ≫ inc.map outerAB ≫ inc.map eB.inv) ≫ inc.map eB.hom ≫
        inc.map outerBK ≫ inc.map eK.inv
        = inc.map eA.hom ≫ inc.map outerAB ≫
            (inc.map eB.inv ≫ inc.map eB.hom) ≫ inc.map outerBK ≫ inc.map eK.inv := by
          simp [inc, Category.assoc]
    _ = inc.map eA.hom ≫ inc.map outerAB ≫ 𝟙 _ ≫ inc.map outerBK ≫ inc.map eK.inv := by
          exact congrArg
            (fun q => inc.map eA.hom ≫ inc.map outerAB ≫ q ≫ inc.map outerBK ≫
              inc.map eK.inv)
            hcancelF
    _ = inc.map eA.hom ≫ (inc.map outerAB ≫ inc.map outerBK) ≫ inc.map eK.inv := by
          simp [Category.assoc]
    _ = inc.map eA.hom ≫ inc.map outerAK ≫ inc.map eK.inv := by
          exact congrArg (fun q => inc.map eA.hom ≫ q ≫ inc.map eK.inv) houterF

/-- The explicit pullback-cover components of the transported outer transitions satisfy the
source cocycle law.  The only non-definitional step is unfolding the sheaf-glued component of
`α ≫ β` on the visible middle explicit-cover member; this is supplied by
`Hom.compose_component_eq_of_middle`. -/
theorem projectionDescentTotalCoverExplicitTransitionComponentHomCompLaw_of_outer
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) :
    projectionDescentTotalCoverExplicitTransitionComponentHomCompLaw
      (J := J) hSheaf D := by
  intro Y A B K a b k hab hbk
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let EA :=
    explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  let EB :=
    explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D B))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
  let EK :=
    explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D K))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D K k)
  let IA := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
  let IB := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b
  let IK := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D K k
  let α := projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A B a b hab
  let β := projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D B K b k hbk
  let γ :=
    projectionDescentExplicitOuterFiberHomForTotalCover
      (J := J) hSheaf D A K a k (hab.trans hbk)
  have hαbase : α.1.base = 𝟙 Y :=
    projectionDescentExplicitOuterFiberHomForTotalCover_base
      (J := J) hSheaf D A B a b hab
  have hβbase : β.1.base = 𝟙 Y :=
    projectionDescentExplicitOuterFiberHomForTotalCover_base
      (J := J) hSheaf D B K b k hbk
  have hγbase : γ.1.base = 𝟙 Y :=
    projectionDescentExplicitOuterFiberHomForTotalCover_base
      (J := J) hSheaf D A K a k (hab.trans hbk)
  let hAB : (𝟙 Y) ≫ IA.f ≫ α.1.base = (𝟙 Y) ≫ IB.f := by
    rw [hαbase]
    dsimp [IA, IB, projectionDescentTotalCoverExplicitPullbackArrow]
    simp
  let hBK : (𝟙 Y) ≫ IB.f ≫ β.1.base = (𝟙 Y) ≫ IK.f := by
    rw [hβbase]
    dsimp [IB, IK, projectionDescentTotalCoverExplicitPullbackArrow]
    simp
  have hcompComponent :
      α.1.components.toHomOver.family IA IB (𝟙 Y) (𝟙 Y) hAB ≫
          β.1.components.toHomOver.family IB IK (𝟙 Y) (𝟙 Y) hBK =
        (Hom.compose (J := J) hSheaf α.1 β.1).components.toHomOver.family
          IA IK (𝟙 Y) (𝟙 Y)
          (by
            calc
              𝟙 Y ≫ IA.f ≫ (α.1.base ≫ β.1.base) =
                  𝟙 Y ≫ IB.f ≫ β.1.base := by
                    simpa [Category.assoc] using
                      congrArg (fun q => q ≫ β.1.base) hAB
              _ = 𝟙 Y ≫ IK.f := hBK) := by
    exact Hom.compose_component_eq_of_middle (J := J) hSheaf α.1 β.1
      IA IB IK (𝟙 Y) (𝟙 Y) (𝟙 Y) hAB hBK
  have hhom : α ≫ β = γ := by
    simpa [α, β, γ] using
      projectionDescentExplicitOuterFiberHomForTotalCover_hom_comp
        (J := J) hSheaf D A B K a b k hab hbk
  let componentOf (δ : EA ⟶ EK) :
      EA.1.object.restrictedLocalObject IA (𝟙 Y) ⟶
        EK.1.object.restrictedLocalObject IK (𝟙 Y) := by
    letI : P.IsHomLift (𝟙 Y) δ.1 := δ.2
    have hbase : δ.1.base = 𝟙 Y := by
      have hfac := IsHomLift.fac' P (𝟙 Y) δ.1
      simpa [P, projectionFunctor] using hfac
    exact δ.1.components.toHomOver.family IA IK (𝟙 Y) (𝟙 Y) (by
      rw [hbase]
      dsimp [IA, IK, projectionDescentTotalCoverExplicitPullbackArrow]
      change 𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y
      simp)
  have hcomponent := congrArg componentOf hhom
  dsimp [componentOf] at hcomponent
  dsimp [projectionDescentTotalCoverExplicitTransitionComponent]
  have hcomponent' :
      (Hom.compose (J := J) hSheaf α.1 β.1).components.toHomOver.family
          IA IK (𝟙 Y) (𝟙 Y)
          (by
            calc
              𝟙 Y ≫ IA.f ≫ (α.1.base ≫ β.1.base) =
                  𝟙 Y ≫ IB.f ≫ β.1.base := by
                    simpa [Category.assoc] using
                      congrArg (fun q => q ≫ β.1.base) hAB
              _ = 𝟙 Y ≫ IK.f := hBK) =
        γ.1.components.toHomOver.family IA IK (𝟙 Y) (𝟙 Y) (by
          rw [hγbase]
          dsimp [IA, IK, projectionDescentTotalCoverExplicitPullbackArrow]
          change 𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y
          simp) := by
    simpa [P, α, β, γ, EA, EK, IA, IK] using hcomponent
  exact (by
    simpa [α, β, γ, IA, IB, IK] using hcompComponent.trans hcomponent')

/-- The explicit pullback-cover cocycle law implies the transition-level cocycle law. -/
theorem projectionDescentTotalCoverTransitionComponentHomCompLaw_of_explicit
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hexplicit :
      projectionDescentTotalCoverExplicitTransitionComponentHomCompLaw
        (J := J) hSheaf D) :
    projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D := by
  intro Y A B K a b k hab hbk
  dsimp [projectionDescentTotalCoverTransitionComponent]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  simpa [Category.assoc] using
    congrArg
      (fun q =>
        (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).hom ≫
          (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J)
            hSheaf D A a).inv ≫
          q ≫
          (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J)
            hSheaf D K k).hom ≫
          (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D K k).inv)
      (hexplicit a b k hab hbk)

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
