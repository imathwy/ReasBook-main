import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.BaseChange

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

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.9: the old object which locally models a
descent-completion object on a member of its cover. -/
noncomputable def stage3LocalOldObject
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    DescentCompletionObject (J := J) X :=
  ofFiberObject (J := J) X (D.object.localObject I)

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.9: the restriction of a completed object to a
member of its own cover. -/
noncomputable def stage3LocalPullbackObject
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    DescentCompletionObject (J := J) X :=
  pullback (J := J) D I.f

@[simp]
theorem stage3LocalOldObject_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    (stage3LocalOldObject (J := J) D I).base = I.Y :=
  rfl

@[simp]
theorem stage3LocalPullbackObject_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    (stage3LocalPullbackObject (J := J) D I).base = I.Y :=
  rfl

namespace Stage3LocalModel

/-- Base equality for the component from the local old model to the pullback of the completed
object.  It rewrites the source index `(K, k)` as the original cover index `I`. -/
theorem toPullback_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D : DescentCompletionObject (J := J) X}
    {I : D.object.cover.Arrow}
    {W : C}
    (K : (stage3LocalOldObject (J := J) D I).object.cover.Arrow)
    (L : (stage3LocalPullbackObject (J := J) D I).object.cover.Arrow)
    (k : W ⟶ K.Y) (l : W ⟶ L.Y)
    (h : k ≫ K.f ≫ 𝟙 I.Y = l ≫ L.f) :
    (k ≫ K.f) ≫ I.f =
      l ≫
        (DescentCompletionObjectOver.pullbackCoverBaseArrow
          (J := J) D.object I.f L).f := by
  dsimp [DescentCompletionObjectOver.pullbackCoverBaseArrow]
  simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) h

/-- Component formula for the local map from the old model `x_i` to `D|_{U_i}`.
This is the source-text component `φ_{ij}` after identifying the trivial old-object cover with
the chosen cover member `i`. -/
noncomputable def toPullbackComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D : DescentCompletionObject (J := J) X}
    {I : D.object.cover.Arrow}
    {W : C}
    (K : (stage3LocalOldObject (J := J) D I).object.cover.Arrow)
    (L : (stage3LocalPullbackObject (J := J) D I).object.cover.Arrow)
    (k : W ⟶ K.Y) (l : W ⟶ L.Y)
    (h : k ≫ K.f ≫ 𝟙 I.Y = l ≫ L.f) :
    (stage3LocalOldObject (J := J) D I).object.restrictedLocalObject K k ⟶
      (stage3LocalPullbackObject (J := J) D I).object.restrictedLocalObject L l :=
  (DescentCompletionObjectOver.ofFiberObjectRestrictedIso
      (J := J) X (D.object.localObject I) K k).hom ≫
    (D.object.overlapIso
      (I₁ := I)
      (I₂ := DescentCompletionObjectOver.pullbackCoverBaseArrow
        (J := J) D.object I.f L)
      (k ≫ K.f) l
      (toPullback_base (J := J) K L k l h)).hom

/-- Base equality for the component from `D|_{U_i}` back to the local old model. -/
theorem fromPullback_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D : DescentCompletionObject (J := J) X}
    {I : D.object.cover.Arrow}
    {W : C}
    (L : (stage3LocalPullbackObject (J := J) D I).object.cover.Arrow)
    (K : (stage3LocalOldObject (J := J) D I).object.cover.Arrow)
    (l : W ⟶ L.Y) (k : W ⟶ K.Y)
    (h : l ≫ L.f ≫ 𝟙 I.Y = k ≫ K.f) :
    l ≫
        (DescentCompletionObjectOver.pullbackCoverBaseArrow
          (J := J) D.object I.f L).f =
      (k ≫ K.f) ≫ I.f := by
  dsimp [DescentCompletionObjectOver.pullbackCoverBaseArrow]
  simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) h

/-- Component formula for the local map from `D|_{U_i}` back to the old model `x_i`. -/
noncomputable def fromPullbackComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D : DescentCompletionObject (J := J) X}
    {I : D.object.cover.Arrow}
    {W : C}
    (L : (stage3LocalPullbackObject (J := J) D I).object.cover.Arrow)
    (K : (stage3LocalOldObject (J := J) D I).object.cover.Arrow)
    (l : W ⟶ L.Y) (k : W ⟶ K.Y)
    (h : l ≫ L.f ≫ 𝟙 I.Y = k ≫ K.f) :
    (stage3LocalPullbackObject (J := J) D I).object.restrictedLocalObject L l ⟶
      (stage3LocalOldObject (J := J) D I).object.restrictedLocalObject K k :=
  (D.object.overlapIso
      (I₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow
        (J := J) D.object I.f L)
      (I₂ := I)
      l (k ≫ K.f)
      (fromPullback_base (J := J) L K l k h)).hom ≫
    (DescentCompletionObjectOver.ofFiberObjectRestrictedIso
      (J := J) X (D.object.localObject I) K k).inv

@[reassoc]
theorem sameIndexOverlap_hom_comp_pullbackMap
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D : DescentCompletionObject (J := J) X}
    {I : D.object.cover.Arrow}
    {W : C}
    (q₁ q₂ : W ⟶ I.Y) (h : q₁ = q₂)
    (hI : q₁ ≫ I.f = q₂ ≫ I.f) :
    (D.object.overlapIso (I₁ := I) (I₂ := I) q₁ q₂ hI).hom.1 ≫
        (canonicalPullbackChoice X.p).map q₂ (D.object.localObject I) =
      (canonicalPullbackChoice X.p).map q₁ (D.object.localObject I) := by
  cases h
  have hself :
      (D.object.overlapIso (I₁ := I) (I₂ := I) q₁ q₁ hI).hom =
        𝟙 (D.object.restrictedLocalObject I q₁) := by
    simpa using
      DescentCompletionObjectOver.overlapIso_self_hom
        (J := J) D.object I q₁
  rw [hself]
  change (𝟙 (D.object.restrictedLocalObject I q₁).1) ≫
      (canonicalPullbackChoice X.p).map q₁ (D.object.localObject I) =
    (canonicalPullbackChoice X.p).map q₁ (D.object.localObject I)
  exact Category.id_comp
    ((canonicalPullbackChoice X.p).map q₁ (D.object.localObject I))

set_option maxHeartbeats 600000 in
/-- The trivial overlap in the old local model agrees with the overlap of the original descent
datum at the fixed cover member `I`, after passing through the canonical restriction
identification.  This is the owner-level replacement for treating the old model cover as
literally singleton. -/
theorem oldOverlap_comp_localIso_hom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D : DescentCompletionObject (J := J) X}
    {I : D.object.cover.Arrow}
    {W : C}
    (K₁ K₂ : (stage3LocalOldObject (J := J) D I).object.cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f) :
    ((stage3LocalOldObject (J := J) D I).object.overlapIso k₁ k₂ hK).hom ≫
        (DescentCompletionObjectOver.ofFiberObjectRestrictedIso
          (J := J) X (D.object.localObject I) K₂ k₂).hom =
      (DescentCompletionObjectOver.ofFiberObjectRestrictedIso
          (J := J) X (D.object.localObject I) K₁ k₁).hom ≫
        (D.object.overlapIso
          (I₁ := I) (I₂ := I)
          (k₁ ≫ K₁.f) (k₂ ≫ K₂.f)
          (by simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) hK)).hom := by
  let x := D.object.localObject I
  let A := stage3LocalOldObject (J := J) D I
  let e₁ := DescentCompletionObjectOver.ofFiberObjectRestrictedIso (J := J) X x K₁ k₁
  let e₂ := DescentCompletionObjectOver.ofFiberObjectRestrictedIso (J := J) X x K₂ k₂
  let hI : (k₁ ≫ K₁.f) ≫ I.f = (k₂ ≫ K₂.f) ≫ I.f := by
    simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) hK
  apply Functor.Fiber.hom_ext
  change
    (((A.object.overlapIso k₁ k₂ hK).hom.1 ≫ e₂.hom.1) =
      (e₁.hom.1 ≫ (D.object.overlapIso
        (I₁ := I) (I₂ := I) (k₁ ≫ K₁.f) (k₂ ≫ K₂.f) hI).hom.1))
  let τ := (canonicalPullbackChoice X.p).map (k₂ ≫ K₂.f) x
  have hτ : X.p.IsStronglyCartesian (k₂ ≫ K₂.f) τ :=
    (canonicalPullbackChoice X.p).isStronglyCartesian (k₂ ≫ K₂.f) x
  letI : X.p.IsStronglyCartesian (k₂ ≫ K₂.f) τ := hτ
  let leftMap := (A.object.overlapIso k₁ k₂ hK).hom.1 ≫ e₂.hom.1
  let rightMap :=
    e₁.hom.1 ≫ (D.object.overlapIso
      (I₁ := I) (I₂ := I) (k₁ ≫ K₁.f) (k₂ ≫ K₂.f) hI).hom.1
  change leftMap = rightMap
  have hleftLift : X.p.IsHomLift (𝟙 W) leftMap :=
    ((A.object.overlapIso k₁ k₂ hK).hom ≫ e₂.hom).2
  have hrightLift : X.p.IsHomLift (𝟙 W) rightMap :=
    (e₁.hom ≫ (D.object.overlapIso
      (I₁ := I) (I₂ := I) (k₁ ≫ K₁.f) (k₂ ≫ K₂.f) hI).hom).2
  haveI : X.p.IsHomLift (𝟙 W) leftMap := hleftLift
  haveI : X.p.IsHomLift (𝟙 W) rightMap := hrightLift
  apply @Functor.IsStronglyCartesian.ext _ _ _ _ X.p
    W I.Y
    (((canonicalFiberPseudofunctor X.p).map (k₂ ≫ K₂.f).op.toLoc).toFunctor.obj x).1
    x.1
    (k₂ ≫ K₂.f) τ hτ
    W ((A.object.restrictedLocalObject K₁ k₁).1)
    (𝟙 W) leftMap rightMap hleftLift hrightLift
  have hleft :
      leftMap ≫ τ =
        DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X x K₁ k₁ := by
    calc
      leftMap ≫ τ =
          (A.object.overlapIso k₁ k₂ hK).hom.1 ≫
            (DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X x K₂ k₂) := by
          rw [Category.assoc]
          rfl
      _ = DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X x K₁ k₁ := by
          simpa [A, x, stage3LocalOldObject] using
            DescentCompletionObjectOver.ofFiberObjectRestrictedMap_overlap
              (J := J) X x k₁ k₂ hK
  have hright :
      rightMap ≫ τ =
        DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X x K₁ k₁ := by
    have hsame :=
      sameIndexOverlap_hom_comp_pullbackMap
        (J := J) (D := D) (I := I)
        (k₁ ≫ K₁.f) (k₂ ≫ K₂.f) hK hI
    calc
      rightMap ≫ τ =
          e₁.hom.1 ≫
            ((D.object.overlapIso
              (I₁ := I) (I₂ := I) (k₁ ≫ K₁.f) (k₂ ≫ K₂.f) hI).hom.1 ≫ τ) := by
          dsimp [rightMap]
          rw [Category.assoc]
      _ = e₁.hom.1 ≫
            (canonicalPullbackChoice X.p).map (k₁ ≫ K₁.f) x := by
          simpa [τ, x] using congrArg (fun q => e₁.hom.1 ≫ q) hsame
      _ = DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X x K₁ k₁ := by
          rfl
  exact hleft.trans hright.symm

set_option maxHeartbeats 600000 in
/-- The local map from the old model to the pullback object is compatible with source and
target descent transitions, hence supplies the `compatible` field of a `HomOver`. -/
theorem toPullbackComponent_compatible
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D : DescentCompletionObject (J := J) X}
    {I : D.object.cover.Arrow}
    {W : C}
    (K₁ K₂ : (stage3LocalOldObject (J := J) D I).object.cover.Arrow)
    (L₁ L₂ : (stage3LocalPullbackObject (J := J) D I).object.cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (l₁ : W ⟶ L₁.Y) (l₂ : W ⟶ L₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (hL : l₁ ≫ L₁.f = l₂ ≫ L₂.f)
    (h₁ : k₁ ≫ K₁.f ≫ 𝟙 I.Y = l₁ ≫ L₁.f)
    (h₂ : k₂ ≫ K₂.f ≫ 𝟙 I.Y = l₂ ≫ L₂.f) :
    ((stage3LocalOldObject (J := J) D I).object.overlapIso k₁ k₂ hK).hom ≫
        toPullbackComponent (J := J) K₂ L₂ k₂ l₂ h₂ =
      toPullbackComponent (J := J) K₁ L₁ k₁ l₁ h₁ ≫
        ((stage3LocalPullbackObject (J := J) D I).object.overlapIso l₁ l₂ hL).hom := by
  let A := stage3LocalOldObject (J := J) D I
  let B := stage3LocalPullbackObject (J := J) D I
  let L₁b := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) D.object I.f L₁
  let L₂b := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) D.object I.f L₂
  let e₁ := DescentCompletionObjectOver.ofFiberObjectRestrictedIso
    (J := J) X (D.object.localObject I) K₁ k₁
  let e₂ := DescentCompletionObjectOver.ofFiberObjectRestrictedIso
    (J := J) X (D.object.localObject I) K₂ k₂
  let hI : (k₁ ≫ K₁.f) ≫ I.f = (k₂ ≫ K₂.f) ≫ I.f := by
    simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) hK
  let h₁b := toPullback_base (J := J) K₁ L₁ k₁ l₁ h₁
  let h₂b := toPullback_base (J := J) K₂ L₂ k₂ l₂ h₂
  let hLb : l₁ ≫ L₁b.f = l₂ ≫ L₂b.f := by
    dsimp [L₁b, L₂b, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) hL
  have hpull :
      (B.object.overlapIso l₁ l₂ hL).hom =
        (D.object.overlapIso (I₁ := L₁b) (I₂ := L₂b) l₁ l₂ hLb).hom := by
    simpa [B, stage3LocalPullbackObject, L₁b, L₂b, hLb] using
      DescentCompletionObjectOver.pullback_overlapIso_hom
        (J := J) D.object I.f L₁ L₂ l₁ l₂ hL
  have hsource :
      (A.object.overlapIso k₁ k₂ hK).hom ≫ e₂.hom =
        e₁.hom ≫
          (D.object.overlapIso
            (I₁ := I) (I₂ := I) (k₁ ≫ K₁.f) (k₂ ≫ K₂.f) hI).hom := by
    simpa [A, stage3LocalOldObject, e₁, e₂, hI] using
      oldOverlap_comp_localIso_hom (J := J) (D := D) (I := I) K₁ K₂ k₁ k₂ hK
  have hleftD :=
    DescentCompletionObjectOver.overlapIso_hom_comp
      (J := J) D.object
      (I₁ := I) (I₂ := I) (I₃ := L₂b)
      (k₁ ≫ K₁.f) (k₂ ≫ K₂.f) l₂ hI h₂b
  have hrightD :=
    DescentCompletionObjectOver.overlapIso_hom_comp
      (J := J) D.object
      (I₁ := I) (I₂ := L₁b) (I₃ := L₂b)
      (k₁ ≫ K₁.f) l₁ l₂ h₁b hLb
  have hproof : hI.trans h₂b = h₁b.trans hLb := Subsingleton.elim _ _
  simp only [toPullbackComponent]
  rw [hpull]
  change
    (A.object.overlapIso k₁ k₂ hK).hom ≫
        (e₂.hom ≫
          (D.object.overlapIso
            (I₁ := I) (I₂ := L₂b) (k₂ ≫ K₂.f) l₂ h₂b).hom) =
      (e₁.hom ≫
        (D.object.overlapIso
          (I₁ := I) (I₂ := L₁b) (k₁ ≫ K₁.f) l₁ h₁b).hom) ≫
        (D.object.overlapIso
          (I₁ := L₁b) (I₂ := L₂b) l₁ l₂ hLb).hom
  calc
    (A.object.overlapIso k₁ k₂ hK).hom ≫
        (e₂.hom ≫
          (D.object.overlapIso
            (I₁ := I) (I₂ := L₂b) (k₂ ≫ K₂.f) l₂ h₂b).hom)
        =
          ((A.object.overlapIso k₁ k₂ hK).hom ≫ e₂.hom) ≫
            (D.object.overlapIso
              (I₁ := I) (I₂ := L₂b) (k₂ ≫ K₂.f) l₂ h₂b).hom := by
          simp [Category.assoc]
    _ =
          (e₁.hom ≫
            (D.object.overlapIso
              (I₁ := I) (I₂ := I) (k₁ ≫ K₁.f) (k₂ ≫ K₂.f) hI).hom) ≫
            (D.object.overlapIso
              (I₁ := I) (I₂ := L₂b) (k₂ ≫ K₂.f) l₂ h₂b).hom := by
          exact congrArg
            (fun t => t ≫
              (D.object.overlapIso
                (I₁ := I) (I₂ := L₂b) (k₂ ≫ K₂.f) l₂ h₂b).hom) hsource
    _ =
          e₁.hom ≫
            ((D.object.overlapIso
              (I₁ := I) (I₂ := I) (k₁ ≫ K₁.f) (k₂ ≫ K₂.f) hI).hom ≫
              (D.object.overlapIso
                (I₁ := I) (I₂ := L₂b) (k₂ ≫ K₂.f) l₂ h₂b).hom) := by
          simp [Category.assoc]
    _ =
          e₁.hom ≫
            (D.object.overlapIso
              (I₁ := I) (I₂ := L₂b) (k₁ ≫ K₁.f) l₂ (hI.trans h₂b)).hom := by
          rw [hleftD]
    _ =
          e₁.hom ≫
            (D.object.overlapIso
              (I₁ := I) (I₂ := L₂b) (k₁ ≫ K₁.f) l₂ (h₁b.trans hLb)).hom := by
          exact congrArg
            (fun hbase =>
              e₁.hom ≫
                (D.object.overlapIso
                  (I₁ := I) (I₂ := L₂b) (k₁ ≫ K₁.f) l₂ hbase).hom) hproof
    _ =
          e₁.hom ≫
            ((D.object.overlapIso
              (I₁ := I) (I₂ := L₁b) (k₁ ≫ K₁.f) l₁ h₁b).hom ≫
              (D.object.overlapIso
                (I₁ := L₁b) (I₂ := L₂b) l₁ l₂ hLb).hom) := by
          rw [← hrightD]
    _ =
          (e₁.hom ≫
            (D.object.overlapIso
              (I₁ := I) (I₂ := L₁b) (k₁ ≫ K₁.f) l₁ h₁b).hom) ≫
              (D.object.overlapIso
                (I₁ := L₁b) (I₂ := L₂b) l₁ l₂ hLb).hom := by
          simp [Category.assoc]
    _ =
          (e₁.hom ≫
            (D.object.overlapIso
              (I₁ := I) (I₂ := L₁b) (k₁ ≫ K₁.f) l₁ h₁b).hom) ≫
              (D.object.overlapIso
                (I₁ := L₁b) (I₂ := L₂b) l₁ l₂ hLb).hom := by
          rfl

/-- The stage 3.9 local map from the old model `x_i` to the pullback `D|_{U_i}`,
bundled as a compatible `HomOver`. -/
noncomputable def toPullbackHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    DescentCompletionObjectOver.HomOver (J := J)
      (stage3LocalOldObject (J := J) D I).object
      (stage3LocalPullbackObject (J := J) D I).object
      (𝟙 I.Y) where
  family K L k l h := toPullbackComponent (J := J) K L k l h
  compatible := by
    intro W K₁ K₂ L₁ L₂ k₁ k₂ l₁ l₂ hK hL h₁ h₂
    exact toPullbackComponent_compatible (J := J) K₁ K₂ L₁ L₂ k₁ k₂ l₁ l₂ hK hL h₁ h₂

set_option maxHeartbeats 400000 in
/-- The two local component formulas are inverse on the old-model side.  This is the pointwise
part of the stage 3.9 local isomorphism; the remaining work is to package these components as
compatible `HomOver`s. -/
theorem toPullbackComponent_comp_fromPullbackComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D : DescentCompletionObject (J := J) X}
    {I : D.object.cover.Arrow}
    {W : C}
    (K : (stage3LocalOldObject (J := J) D I).object.cover.Arrow)
    (L : (stage3LocalPullbackObject (J := J) D I).object.cover.Arrow)
    (k : W ⟶ K.Y) (l : W ⟶ L.Y)
    (h : k ≫ K.f ≫ 𝟙 I.Y = l ≫ L.f) :
    toPullbackComponent (J := J) K L k l h ≫
        fromPullbackComponent (J := J) L K l k (by simpa [Category.assoc] using h.symm) =
      𝟙 ((stage3LocalOldObject (J := J) D I).object.restrictedLocalObject K k) := by
  let Lb :=
    DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) D.object I.f L
  let e :=
    DescentCompletionObjectOver.ofFiberObjectRestrictedIso
      (J := J) X (D.object.localObject I) K k
  let h₁ := toPullback_base (J := J) K L k l h
  let h₂ := fromPullback_base (J := J) L K l k (by simpa [Category.assoc] using h.symm)
  have hDcomp :
      (D.object.overlapIso (I₁ := I) (I₂ := Lb) (k ≫ K.f) l h₁).hom ≫
          (D.object.overlapIso (I₁ := Lb) (I₂ := I) l (k ≫ K.f) h₂).hom =
        𝟙 (D.object.restrictedLocalObject I (k ≫ K.f)) := by
    have hcomp :=
      DescentCompletionObjectOver.overlapIso_hom_comp
        (J := J) D.object
        (I₁ := I) (I₂ := Lb) (I₃ := I)
        (k ≫ K.f) l (k ≫ K.f) h₁ h₂
    rw [hcomp]
    simpa using
      DescentCompletionObjectOver.overlapIso_self_hom
        (J := J) D.object I (k ≫ K.f)
  change
    (e.hom ≫ (D.object.overlapIso (I₁ := I) (I₂ := Lb) (k ≫ K.f) l h₁).hom) ≫
        ((D.object.overlapIso (I₁ := Lb) (I₂ := I) l (k ≫ K.f) h₂).hom ≫ e.inv) =
      𝟙 ((stage3LocalOldObject (J := J) D I).object.restrictedLocalObject K k)
  have he : e.hom ≫ e.inv =
      𝟙 ((stage3LocalOldObject (J := J) D I).object.restrictedLocalObject K k) :=
    e.hom_inv_id
  calc
    (e.hom ≫ (D.object.overlapIso (I₁ := I) (I₂ := Lb) (k ≫ K.f) l h₁).hom) ≫
        ((D.object.overlapIso (I₁ := Lb) (I₂ := I) l (k ≫ K.f) h₂).hom ≫ e.inv)
        =
          e.hom ≫
            ((D.object.overlapIso (I₁ := I) (I₂ := Lb) (k ≫ K.f) l h₁).hom ≫
              (D.object.overlapIso (I₁ := Lb) (I₂ := I) l (k ≫ K.f) h₂).hom) ≫
            e.inv := by
          simp [Category.assoc]
    _ = e.hom ≫ 𝟙 (D.object.restrictedLocalObject I (k ≫ K.f)) ≫ e.inv := by
          rw [hDcomp]
    _ = 𝟙 ((stage3LocalOldObject (J := J) D I).object.restrictedLocalObject K k) := by
          rw [Category.id_comp]
          exact he

set_option maxHeartbeats 400000 in
/-- The two local component formulas are inverse on the pulled-back completed-object side. -/
theorem fromPullbackComponent_comp_toPullbackComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D : DescentCompletionObject (J := J) X}
    {I : D.object.cover.Arrow}
    {W : C}
    (L : (stage3LocalPullbackObject (J := J) D I).object.cover.Arrow)
    (K : (stage3LocalOldObject (J := J) D I).object.cover.Arrow)
    (l : W ⟶ L.Y) (k : W ⟶ K.Y)
    (h : l ≫ L.f ≫ 𝟙 I.Y = k ≫ K.f) :
    fromPullbackComponent (J := J) L K l k h ≫
        toPullbackComponent (J := J) K L k l (by simpa [Category.assoc] using h.symm) =
      𝟙 ((stage3LocalPullbackObject (J := J) D I).object.restrictedLocalObject L l) := by
  let Lb :=
    DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) D.object I.f L
  let e :=
    DescentCompletionObjectOver.ofFiberObjectRestrictedIso
      (J := J) X (D.object.localObject I) K k
  let h₁ := fromPullback_base (J := J) L K l k h
  let h₂ := toPullback_base (J := J) K L k l (by simpa [Category.assoc] using h.symm)
  have hDcomp :
      (D.object.overlapIso (I₁ := Lb) (I₂ := I) l (k ≫ K.f) h₁).hom ≫
          (D.object.overlapIso (I₁ := I) (I₂ := Lb) (k ≫ K.f) l h₂).hom =
        𝟙 (D.object.restrictedLocalObject Lb l) := by
    have hcomp :=
      DescentCompletionObjectOver.overlapIso_hom_comp
        (J := J) D.object
        (I₁ := Lb) (I₂ := I) (I₃ := Lb)
        l (k ≫ K.f) l h₁ h₂
    rw [hcomp]
    simpa using
      DescentCompletionObjectOver.overlapIso_self_hom
        (J := J) D.object Lb l
  change
    ((D.object.overlapIso (I₁ := Lb) (I₂ := I) l (k ≫ K.f) h₁).hom ≫ e.inv) ≫
        (e.hom ≫
          (D.object.overlapIso (I₁ := I) (I₂ := Lb) (k ≫ K.f) l h₂).hom) =
      𝟙 ((stage3LocalPullbackObject (J := J) D I).object.restrictedLocalObject L l)
  have he : e.inv ≫ e.hom =
      𝟙 (D.object.restrictedLocalObject I (k ≫ K.f)) :=
    e.inv_hom_id
  calc
    ((D.object.overlapIso (I₁ := Lb) (I₂ := I) l (k ≫ K.f) h₁).hom ≫ e.inv) ≫
        (e.hom ≫
          (D.object.overlapIso (I₁ := I) (I₂ := Lb) (k ≫ K.f) l h₂).hom)
        =
          (D.object.overlapIso (I₁ := Lb) (I₂ := I) l (k ≫ K.f) h₁).hom ≫
            (e.inv ≫ e.hom) ≫
          (D.object.overlapIso (I₁ := I) (I₂ := Lb) (k ≫ K.f) l h₂).hom := by
          simp [Category.assoc]
    _ =
        (D.object.overlapIso (I₁ := Lb) (I₂ := I) l (k ≫ K.f) h₁).hom ≫
          𝟙 (D.object.restrictedLocalObject I (k ≫ K.f)) ≫
        (D.object.overlapIso (I₁ := I) (I₂ := Lb) (k ≫ K.f) l h₂).hom := by
        rw [he]
    _ =
        (D.object.overlapIso (I₁ := Lb) (I₂ := I) l (k ≫ K.f) h₁).hom ≫
          (D.object.overlapIso (I₁ := I) (I₂ := Lb) (k ≫ K.f) l h₂).hom := by
        simp
    _ = 𝟙 (D.object.restrictedLocalObject Lb l) := by
        exact hDcomp

set_option maxHeartbeats 600000 in
/-- The inverse local component is compatible with source and target descent transitions.  This
is derived formally from compatibility of `toPullbackComponent` and the pointwise inverse
identities. -/
theorem fromPullbackComponent_compatible
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D : DescentCompletionObject (J := J) X}
    {I : D.object.cover.Arrow}
    {W : C}
    (L₁ L₂ : (stage3LocalPullbackObject (J := J) D I).object.cover.Arrow)
    (K₁ K₂ : (stage3LocalOldObject (J := J) D I).object.cover.Arrow)
    (l₁ : W ⟶ L₁.Y) (l₂ : W ⟶ L₂.Y)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hL : l₁ ≫ L₁.f = l₂ ≫ L₂.f)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (h₁ : l₁ ≫ L₁.f ≫ 𝟙 I.Y = k₁ ≫ K₁.f)
    (h₂ : l₂ ≫ L₂.f ≫ 𝟙 I.Y = k₂ ≫ K₂.f) :
    ((stage3LocalPullbackObject (J := J) D I).object.overlapIso l₁ l₂ hL).hom ≫
        fromPullbackComponent (J := J) L₂ K₂ l₂ k₂ h₂ =
      fromPullbackComponent (J := J) L₁ K₁ l₁ k₁ h₁ ≫
        ((stage3LocalOldObject (J := J) D I).object.overlapIso k₁ k₂ hK).hom := by
  let A := stage3LocalOldObject (J := J) D I
  let B := stage3LocalPullbackObject (J := J) D I
  let ht₁ : k₁ ≫ K₁.f ≫ 𝟙 I.Y = l₁ ≫ L₁.f := by
    simpa [Category.assoc] using h₁.symm
  let ht₂ : k₂ ≫ K₂.f ≫ 𝟙 I.Y = l₂ ≫ L₂.f := by
    simpa [Category.assoc] using h₂.symm
  let α₁ := toPullbackComponent (J := J) K₁ L₁ k₁ l₁ ht₁
  let α₂ := toPullbackComponent (J := J) K₂ L₂ k₂ l₂ ht₂
  let β₁ := fromPullbackComponent (J := J) L₁ K₁ l₁ k₁ h₁
  let β₂ := fromPullbackComponent (J := J) L₂ K₂ l₂ k₂ h₂
  let a := (A.object.overlapIso k₁ k₂ hK).hom
  let b := (B.object.overlapIso l₁ l₂ hL).hom
  have hcompat : a ≫ α₂ = α₁ ≫ b := by
    simpa [A, B, a, b, α₁, α₂] using
      toPullbackComponent_compatible
        (J := J) K₁ K₂ L₁ L₂ k₁ k₂ l₁ l₂ hK hL ht₁ ht₂
  have hβα₁ : β₁ ≫ α₁ = 𝟙 (B.object.restrictedLocalObject L₁ l₁) := by
    simpa [A, B, α₁, β₁, ht₁] using
      fromPullbackComponent_comp_toPullbackComponent
        (J := J) L₁ K₁ l₁ k₁ h₁
  have hαβ₂ : α₂ ≫ β₂ = 𝟙 (A.object.restrictedLocalObject K₂ k₂) := by
    simpa [A, B, α₂, β₂, ht₂] using
      toPullbackComponent_comp_fromPullbackComponent
        (J := J) K₂ L₂ k₂ l₂ ht₂
  change b ≫ β₂ = β₁ ≫ a
  calc
    b ≫ β₂ = (β₁ ≫ α₁) ≫ b ≫ β₂ := by
      rw [hβα₁]
      exact (Category.id_comp (b ≫ β₂)).symm
    _ = β₁ ≫ (α₁ ≫ b) ≫ β₂ := by
      simp [Category.assoc]
    _ = β₁ ≫ (a ≫ α₂) ≫ β₂ := by
      rw [← hcompat]
    _ = β₁ ≫ a ≫ (α₂ ≫ β₂) := by
      simp [Category.assoc]
    _ = β₁ ≫ a := by
      rw [hαβ₂]
      simp only [Category.comp_id]

/-- The stage 3.9 inverse local map from the pullback `D|_{U_i}` to the old model `x_i`,
bundled as a compatible `HomOver`. -/
noncomputable def fromPullbackHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    DescentCompletionObjectOver.HomOver (J := J)
      (stage3LocalPullbackObject (J := J) D I).object
      (stage3LocalOldObject (J := J) D I).object
      (𝟙 I.Y) where
  family L K l k h := fromPullbackComponent (J := J) L K l k h
  compatible := by
    intro W L₁ L₂ K₁ K₂ l₁ l₂ k₁ k₂ hL hK h₁ h₂
    exact fromPullbackComponent_compatible (J := J)
      L₁ L₂ K₁ K₂ l₁ l₂ k₁ k₂ hL hK h₁ h₂

set_option maxHeartbeats 600000 in
/-- The local map from the old model to the pullback object commutes with further restriction, so it
is a genuine natural owner-level morphism. -/
theorem toPullbackHomOver_familyNaturality'
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    DescentCompletionObjectOver.HomOver.familyNaturality' (J := J)
      (toPullbackHomOver (J := J) D I) := by
  intro W W' K L k l h m mk ml hmk hml
  let A := stage3LocalOldObject (J := J) D I
  let B := stage3LocalPullbackObject (J := J) D I
  let x := D.object.localObject I
  let Lb := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) D.object I.f L
  let hsmall : mk ≫ K.f ≫ 𝟙 I.Y = ml ≫ L.f := by
    calc
      mk ≫ K.f ≫ 𝟙 I.Y = m ≫ k ≫ K.f ≫ 𝟙 I.Y := by
        rw [← hmk]
        simp [Category.assoc]
      _ = m ≫ l ≫ L.f := by
        simpa [Category.assoc] using congrArg (fun q => m ≫ q) h
      _ = ml ≫ L.f := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ L.f) hml
  let e := DescentCompletionObjectOver.ofFiberObjectRestrictedIso (J := J) X x K k
  let e' := DescentCompletionObjectOver.ofFiberObjectRestrictedIso (J := J) X x K mk
  let hbase := toPullback_base (J := J) K L k l h
  let hbase' := toPullback_base (J := J) K L mk ml hsmall
  let δ := (D.object.overlapIso (I₁ := I) (I₂ := Lb) (k ≫ K.f) l hbase).hom
  let δ' := (D.object.overlapIso (I₁ := I) (I₂ := Lb) (mk ≫ K.f) ml hbase').hom
  suffices
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (toPullbackComponent (J := J) K L k l h) m mk ml hmk hml =
        toPullbackComponent (J := J) K L mk ml hsmall by
    simpa [toPullbackHomOver, hsmall] using this
  change
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p) (e.hom ≫ δ) m mk ml hmk hml =
      e'.hom ≫ δ'
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (φ := e.hom) (ψ := δ)
    (k := m) (kf₁ := mk) (kf₂ := mk ≫ K.f) (kf₃ := ml)
    (hkf₁ := hmk)
    (hkf₂ := by simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk)
    (hkf₃ := hml)]
  have he :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p) e.hom m mk (mk ≫ K.f) hmk
            (by simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk) =
        e'.hom := by
    simpa [e, e', x, DescentCompletionObjectOver.ofFiberObjectRestrictedIso] using
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom_mapComp'_inv_of_fac
        (F := canonicalFiberPseudofunctor X.p) K.f k m mk hmk x)
  have hδ :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p) δ m (mk ≫ K.f) ml
            (by simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk) hml =
        δ' := by
    have hnat :=
      DescentCompletionObjectOver.HomOver.overlapIso_pullHom
        (J := J) D.object I Lb (k ≫ K.f) l hbase m
        (mk ≫ K.f) ml
        (by simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk) hml
    simpa [δ, δ', hbase, hbase'] using hnat
  rw [he, hδ]
  rfl

/-- The stage 3.9 local map from the old model to the pullback, bundled as a natural morphism. -/
noncomputable def toPullbackNaturalHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    DescentCompletionObjectOver.NaturalHomOver (J := J)
      (stage3LocalOldObject (J := J) D I).object
      (stage3LocalPullbackObject (J := J) D I).object
      (𝟙 I.Y) where
  toHomOver := toPullbackHomOver (J := J) D I
  naturality := toPullbackHomOver_familyNaturality' (J := J) D I

set_option maxHeartbeats 600000 in
/-- The inverse local map from the pullback object to the old model commutes with further
restriction. -/
theorem fromPullbackHomOver_familyNaturality'
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    DescentCompletionObjectOver.HomOver.familyNaturality' (J := J)
      (fromPullbackHomOver (J := J) D I) := by
  intro W W' L K l k h m ml mk hml hmk
  let A := stage3LocalOldObject (J := J) D I
  let B := stage3LocalPullbackObject (J := J) D I
  let x := D.object.localObject I
  let Lb := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) D.object I.f L
  let hsmall : ml ≫ L.f ≫ 𝟙 I.Y = mk ≫ K.f := by
    calc
      ml ≫ L.f ≫ 𝟙 I.Y = m ≫ l ≫ L.f ≫ 𝟙 I.Y := by
        rw [← hml]
        simp [Category.assoc]
      _ = m ≫ k ≫ K.f := by
        simpa [Category.assoc] using congrArg (fun q => m ≫ q) h
      _ = mk ≫ K.f := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk
  let e := DescentCompletionObjectOver.ofFiberObjectRestrictedIso (J := J) X x K k
  let e' := DescentCompletionObjectOver.ofFiberObjectRestrictedIso (J := J) X x K mk
  let hbase := fromPullback_base (J := J) L K l k h
  let hbase' := fromPullback_base (J := J) L K ml mk hsmall
  let δ := (D.object.overlapIso (I₁ := Lb) (I₂ := I) l (k ≫ K.f) hbase).hom
  let δ' := (D.object.overlapIso (I₁ := Lb) (I₂ := I) ml (mk ≫ K.f) hbase').hom
  suffices
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (fromPullbackComponent (J := J) L K l k h) m ml mk hml hmk =
        fromPullbackComponent (J := J) L K ml mk hsmall by
    simpa [fromPullbackHomOver, hsmall] using this
  change
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p) (δ ≫ e.inv) m ml mk hml hmk =
      δ' ≫ e'.inv
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (φ := δ) (ψ := e.inv)
    (k := m) (kf₁ := ml) (kf₂ := mk ≫ K.f) (kf₃ := mk)
    (hkf₁ := hml)
    (hkf₂ := by simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk)
    (hkf₃ := hmk)]
  have hδ :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p) δ m ml (mk ≫ K.f) hml
            (by simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk) =
        δ' := by
    have hnat :=
      DescentCompletionObjectOver.HomOver.overlapIso_pullHom
        (J := J) D.object Lb I l (k ≫ K.f) hbase m
        ml (mk ≫ K.f) hml
        (by simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk)
    simpa [δ, δ', hbase, hbase'] using hnat
  have he :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p) e.inv m (mk ≫ K.f) mk
            (by simpa [Category.assoc] using congrArg (fun q => q ≫ K.f) hmk) hmk =
        e'.inv := by
    simpa [e, e', x, DescentCompletionObjectOver.ofFiberObjectRestrictedIso] using
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom_mapComp'_hom_of_fac
        (F := canonicalFiberPseudofunctor X.p) K.f k m mk hmk x)
  rw [hδ, he]
  rfl

/-- The stage 3.9 inverse local map from the pullback to the old model, bundled as a natural
morphism. -/
noncomputable def fromPullbackNaturalHomOver
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    DescentCompletionObjectOver.NaturalHomOver (J := J)
      (stage3LocalPullbackObject (J := J) D I).object
      (stage3LocalOldObject (J := J) D I).object
      (𝟙 I.Y) where
  toHomOver := fromPullbackHomOver (J := J) D I
  naturality := fromPullbackHomOver_familyNaturality' (J := J) D I

/-- The total stage 3.9 local morphism from the old model `x_i` to the pullback `D|_{U_i}`. -/
noncomputable def toPullbackHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    Hom (J := J)
      (stage3LocalOldObject (J := J) D I)
      (stage3LocalPullbackObject (J := J) D I) where
  base := 𝟙 I.Y
  components := toPullbackNaturalHomOver (J := J) D I

@[simp]
theorem toPullbackHom_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    (toPullbackHom (J := J) D I).base = 𝟙 I.Y :=
  rfl

/-- The total stage 3.9 inverse local morphism from the pullback `D|_{U_i}` to the old model
`x_i`. -/
noncomputable def fromPullbackHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    Hom (J := J)
      (stage3LocalPullbackObject (J := J) D I)
      (stage3LocalOldObject (J := J) D I) where
  base := 𝟙 I.Y
  components := fromPullbackNaturalHomOver (J := J) D I

@[simp]
theorem fromPullbackHom_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    (fromPullbackHom (J := J) D I).base = 𝟙 I.Y :=
  rfl

set_option maxHeartbeats 600000 in
/-- On a common middle cover member, the composite from the old local model to the pullback and back
is the old-model descent transition.  This is the local calculation used before sheaf-gluing the
global inverse identity. -/
theorem toPullback_fromPullback_localComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D : DescentCompletionObject (J := J) X}
    {I : D.object.cover.Arrow}
    {W : C}
    (K M : (stage3LocalOldObject (J := J) D I).object.cover.Arrow)
    (L : (stage3LocalPullbackObject (J := J) D I).object.cover.Arrow)
    (k : W ⟶ K.Y) (l : W ⟶ L.Y) (m : W ⟶ M.Y)
    (hα : k ≫ K.f ≫ 𝟙 I.Y = l ≫ L.f)
    (hβ : l ≫ L.f ≫ 𝟙 I.Y = m ≫ M.f) :
    DescentCompletionObjectOver.HomOver.localComposite (J := J)
        (toPullbackHomOver (J := J) D I)
        (fromPullbackHomOver (J := J) D I)
        K L M k l m hα hβ =
      ((stage3LocalOldObject (J := J) D I).object.overlapIso k m
        (by
          have h₁ : k ≫ K.f = l ≫ L.f := by simpa [Category.assoc] using hα
          have h₂ : l ≫ L.f = m ≫ M.f := by simpa [Category.assoc] using hβ
          exact h₁.trans h₂)).hom := by
  let A := stage3LocalOldObject (J := J) D I
  let B := stage3LocalPullbackObject (J := J) D I
  let hA : k ≫ K.f = m ≫ M.f := by
    exact
      (((by simpa [Category.assoc] using hα) : k ≫ K.f = l ≫ L.f).trans
        ((by simpa [Category.assoc] using hβ) : l ≫ L.f = m ≫ M.f))
  let hbackK : l ≫ L.f ≫ 𝟙 I.Y = k ≫ K.f := by
    simpa [Category.assoc] using hα.symm
  let α := toPullbackComponent (J := J) K L k l hα
  let βK := fromPullbackComponent (J := J) L K l k hbackK
  let βM := fromPullbackComponent (J := J) L M l m hβ
  let a := (A.object.overlapIso k m hA).hom
  have hβM : βM = βK ≫ a := by
    have hcompat :=
      fromPullbackComponent_compatible (J := J)
        (D := D) (I := I) L L K M l l k m rfl hA hbackK hβ
    rw [DescentCompletionObjectOver.overlapIso_self_hom (J := J) B.object L l] at hcompat
    simpa [A, B, βK, βM, a] using hcompat
  have hαβK : α ≫ βK =
      𝟙 (A.object.restrictedLocalObject K k) := by
    simpa [A, B, α, βK, hbackK] using
      toPullbackComponent_comp_fromPullbackComponent
        (J := J) (D := D) (I := I) K L k l hα
  change α ≫ βM = a
  rw [hβM]
  calc
    α ≫ (βK ≫ a) = (α ≫ βK) ≫ a := by
      rw [Category.assoc]
    _ = a := by
      rw [hαβK]
      exact Category.id_comp a

set_option maxHeartbeats 600000 in
/-- On a common middle cover member, the composite from the pullback to the old local model and back
is the pullback descent transition. -/
theorem fromPullback_toPullback_localComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {D : DescentCompletionObject (J := J) X}
    {I : D.object.cover.Arrow}
    {W : C}
    (L M : (stage3LocalPullbackObject (J := J) D I).object.cover.Arrow)
    (K : (stage3LocalOldObject (J := J) D I).object.cover.Arrow)
    (l : W ⟶ L.Y) (k : W ⟶ K.Y) (m : W ⟶ M.Y)
    (hα : l ≫ L.f ≫ 𝟙 I.Y = k ≫ K.f)
    (hβ : k ≫ K.f ≫ 𝟙 I.Y = m ≫ M.f) :
    DescentCompletionObjectOver.HomOver.localComposite (J := J)
        (fromPullbackHomOver (J := J) D I)
        (toPullbackHomOver (J := J) D I)
        L K M l k m hα hβ =
      ((stage3LocalPullbackObject (J := J) D I).object.overlapIso l m
        (by
          have h₁ : l ≫ L.f = k ≫ K.f := by simpa [Category.assoc] using hα
          have h₂ : k ≫ K.f = m ≫ M.f := by simpa [Category.assoc] using hβ
          exact h₁.trans h₂)).hom := by
  let A := stage3LocalOldObject (J := J) D I
  let B := stage3LocalPullbackObject (J := J) D I
  let hB : l ≫ L.f = m ≫ M.f := by
    exact
      (((by simpa [Category.assoc] using hα) : l ≫ L.f = k ≫ K.f).trans
        ((by simpa [Category.assoc] using hβ) : k ≫ K.f = m ≫ M.f))
  let htoL : k ≫ K.f ≫ 𝟙 I.Y = l ≫ L.f := by
    simpa [Category.assoc] using hα.symm
  let β := fromPullbackComponent (J := J) L K l k hα
  let αL := toPullbackComponent (J := J) K L k l htoL
  let αM := toPullbackComponent (J := J) K M k m hβ
  let b := (B.object.overlapIso l m hB).hom
  have hαM : αM = αL ≫ b := by
    have hcompat :=
      toPullbackComponent_compatible (J := J)
        (D := D) (I := I) K K L M k k l m rfl hB htoL hβ
    rw [DescentCompletionObjectOver.overlapIso_self_hom (J := J) A.object K k] at hcompat
    simpa [A, B, αL, αM, b] using hcompat
  have hβαL : β ≫ αL =
      𝟙 (B.object.restrictedLocalObject L l) := by
    simpa [A, B, β, αL, htoL] using
      fromPullbackComponent_comp_toPullbackComponent
        (J := J) (D := D) (I := I) L K l k hα
  change β ≫ αM = b
  rw [hαM]
  calc
    β ≫ (αL ≫ b) = (β ≫ αL) ≫ b := by
      rw [Category.assoc]
    _ = b := by
      rw [hβαL]
      exact Category.id_comp b

end Stage3LocalModel

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
