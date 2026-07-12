import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3LocalModel

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
namespace Stage3LocalModel

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The glued composite `x_i -> D|_{U_i} -> x_i` has the identity component family.  This is the
global sheaf-glued upgrade of `toPullback_fromPullback_localComposite`. -/
theorem toPullback_fromPullback_compositionFamily
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow)
    {W : C}
    (K M : (stage3LocalOldObject (J := J) D I).object.cover.Arrow)
    (k : W ⟶ K.Y) (m : W ⟶ M.Y)
    (h : k ≫ K.f ≫ ((𝟙 I.Y) ≫ (𝟙 I.Y)) = m ≫ M.f) :
    DescentCompletionObjectOver.HomOver.compositionFamily (J := J) hSheaf
        (toPullbackHomOver (J := J) D I)
        (fromPullbackHomOver (J := J) D I)
        (toPullbackHomOver_familyNaturality' (J := J) D I)
        (fromPullbackHomOver_familyNaturality' (J := J) D I)
        K M k m h =
      (DescentCompletionObjectOver.idHomOver (J := J)
        (stage3LocalOldObject (J := J) D I).object).family K M k m
        (by simpa [Category.assoc] using h) := by
  let A := stage3LocalOldObject (J := J) D I
  let B := stage3LocalPullbackObject (J := J) D I
  let α := toPullbackHomOver (J := J) D I
  let β := fromPullbackHomOver (J := J) D I
  let hαnat : DescentCompletionObjectOver.HomOver.familyNaturality' (J := J) α :=
    toPullbackHomOver_familyNaturality' (J := J) D I
  let hβnat : DescentCompletionObjectOver.HomOver.familyNaturality' (J := J) β :=
    fromPullbackHomOver_familyNaturality' (J := J) D I
  let hid : k ≫ K.f = m ≫ M.f := by
    simpa [Category.assoc] using h
  let S := DescentCompletionObjectOver.HomOver.compositionMiddleCover (J := J)
    (D := A.object) (E := B.object) (H := A.object)
    (f := 𝟙 I.Y) (g := 𝟙 I.Y) K M k m h
  apply fiberHom_ext_of_cover (J := J) X.p S
    (A.object.restrictedLocalObject K k) (A.object.restrictedLocalObject M m)
    (hSheaf W (A.object.restrictedLocalObject K k) (A.object.restrictedLocalObject M m))
  intro Lp
  have hmapComp :=
    DescentCompletionObjectOver.HomOver.compositionFamily_map (J := J)
      hSheaf α β hαnat hβnat K M k m h Lp
  have hmapId :=
    DescentCompletionObjectOver.HomOver.overlapIso_map_eq (J := J)
      A.object K M k m hid Lp.f
  rw [hmapComp]
  rw [DescentCompletionObjectOver.idHomOver_family, hmapId]
  simp only [DescentCompletionObjectOver.HomOver.compositionMiddleCoverSection,
    DescentCompletionObjectOver.HomOver.compositionMiddleCoverSourceIso,
    DescentCompletionObjectOver.HomOver.compositionMiddleCoverTargetIso,
    DescentCompletionObjectOver.restrictedLocalObjectCompIso,
    Cat.Hom.toNatIso, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv]
  have hlocal := toPullback_fromPullback_localComposite (J := J)
    (D := D) (I := I) K M Lp.base
    (Lp.f ≫ k) (𝟙 Lp.Y) (Lp.f ≫ m)
    (by
      dsimp [S, DescentCompletionObjectOver.HomOver.compositionMiddleCover]
      calc
        (Lp.f ≫ k) ≫ K.f ≫ 𝟙 I.Y = (Lp.f ≫ k) ≫ K.f := by
          simp
        _ = 𝟙 Lp.Y ≫ Lp.f ≫ k ≫ K.f := by
          simp [Category.assoc]
        _ = 𝟙 Lp.Y ≫ Lp.f ≫ k ≫ K.f ≫ 𝟙 I.Y := by
          simp)
    (by
      dsimp [S, DescentCompletionObjectOver.HomOver.compositionMiddleCover]
      simpa only [Category.id_comp, Category.comp_id, Category.assoc] using
        congrArg (fun q => Lp.f ≫ q) h)
  let L :=
    ((canonicalFiberPseudofunctor X.p).mapComp' k.op.toLoc Lp.f.op.toLoc
      ((Lp.f ≫ k).op.toLoc) (by rfl)).inv.toNatTrans.app (A.object.localObject K)
  let R :=
    ((canonicalFiberPseudofunctor X.p).mapComp' m.op.toLoc Lp.f.op.toLoc
      ((Lp.f ≫ m).op.toLoc) (by rfl)).hom.toNatTrans.app (A.object.localObject M)
  have hwrapped := congrArg (fun t => L ≫ t ≫ R) hlocal
  simpa [A, B, α, β, hαnat, hβnat, S,
    DescentCompletionObjectOver.HomOver.compositionMiddleCoverComposite,
    L, R, hid, Category.assoc] using hwrapped

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The glued composite `D|_{U_i} -> x_i -> D|_{U_i}` has the identity component family. -/
theorem fromPullback_toPullback_compositionFamily
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow)
    {W : C}
    (L M : (stage3LocalPullbackObject (J := J) D I).object.cover.Arrow)
    (l : W ⟶ L.Y) (m : W ⟶ M.Y)
    (h : l ≫ L.f ≫ ((𝟙 I.Y) ≫ (𝟙 I.Y)) = m ≫ M.f) :
    DescentCompletionObjectOver.HomOver.compositionFamily (J := J) hSheaf
        (fromPullbackHomOver (J := J) D I)
        (toPullbackHomOver (J := J) D I)
        (fromPullbackHomOver_familyNaturality' (J := J) D I)
        (toPullbackHomOver_familyNaturality' (J := J) D I)
        L M l m h =
      (DescentCompletionObjectOver.idHomOver (J := J)
        (stage3LocalPullbackObject (J := J) D I).object).family L M l m
        (by simpa [Category.assoc] using h) := by
  let A := stage3LocalOldObject (J := J) D I
  let B := stage3LocalPullbackObject (J := J) D I
  let α := fromPullbackHomOver (J := J) D I
  let β := toPullbackHomOver (J := J) D I
  let hαnat : DescentCompletionObjectOver.HomOver.familyNaturality' (J := J) α :=
    fromPullbackHomOver_familyNaturality' (J := J) D I
  let hβnat : DescentCompletionObjectOver.HomOver.familyNaturality' (J := J) β :=
    toPullbackHomOver_familyNaturality' (J := J) D I
  let hid : l ≫ L.f = m ≫ M.f := by
    simpa [Category.assoc] using h
  let S := DescentCompletionObjectOver.HomOver.compositionMiddleCover (J := J)
    (D := B.object) (E := A.object) (H := B.object)
    (f := 𝟙 I.Y) (g := 𝟙 I.Y) L M l m h
  apply fiberHom_ext_of_cover (J := J) X.p S
    (B.object.restrictedLocalObject L l) (B.object.restrictedLocalObject M m)
    (hSheaf W (B.object.restrictedLocalObject L l) (B.object.restrictedLocalObject M m))
  intro Kp
  have hmapComp :=
    DescentCompletionObjectOver.HomOver.compositionFamily_map (J := J)
      hSheaf α β hαnat hβnat L M l m h Kp
  have hmapId :=
    DescentCompletionObjectOver.HomOver.overlapIso_map_eq (J := J)
      B.object L M l m hid Kp.f
  rw [hmapComp]
  rw [DescentCompletionObjectOver.idHomOver_family, hmapId]
  simp only [DescentCompletionObjectOver.HomOver.compositionMiddleCoverSection,
    DescentCompletionObjectOver.HomOver.compositionMiddleCoverSourceIso,
    DescentCompletionObjectOver.HomOver.compositionMiddleCoverTargetIso,
    DescentCompletionObjectOver.restrictedLocalObjectCompIso,
    Cat.Hom.toNatIso, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv]
  have hlocal := fromPullback_toPullback_localComposite (J := J)
    (D := D) (I := I) L M Kp.base
    (Kp.f ≫ l) (𝟙 Kp.Y) (Kp.f ≫ m)
    (by
      dsimp [S, DescentCompletionObjectOver.HomOver.compositionMiddleCover]
      calc
        (Kp.f ≫ l) ≫ L.f ≫ 𝟙 I.Y = (Kp.f ≫ l) ≫ L.f := by
          simp
        _ = 𝟙 Kp.Y ≫ Kp.f ≫ l ≫ L.f := by
          simp [Category.assoc]
        _ = 𝟙 Kp.Y ≫ Kp.f ≫ l ≫ L.f ≫ 𝟙 I.Y := by
          simp)
    (by
      dsimp [S, DescentCompletionObjectOver.HomOver.compositionMiddleCover]
      simpa only [Category.id_comp, Category.comp_id, Category.assoc] using
        congrArg (fun q => Kp.f ≫ q) h)
  let Lw :=
    ((canonicalFiberPseudofunctor X.p).mapComp' l.op.toLoc Kp.f.op.toLoc
      ((Kp.f ≫ l).op.toLoc) (by rfl)).inv.toNatTrans.app (B.object.localObject L)
  let Rw :=
    ((canonicalFiberPseudofunctor X.p).mapComp' m.op.toLoc Kp.f.op.toLoc
      ((Kp.f ≫ m).op.toLoc) (by rfl)).hom.toNatTrans.app (B.object.localObject M)
  have hwrapped := congrArg (fun t => Lw ≫ t ≫ Rw) hlocal
  simpa [A, B, α, β, hαnat, hβnat, S,
    DescentCompletionObjectOver.HomOver.compositionMiddleCoverComposite,
    Lw, Rw, hid, Category.assoc] using hwrapped

set_option maxHeartbeats 800000 in
/-- The total local maps `x_i -> D|_{U_i}` and `D|_{U_i} -> x_i` are inverse on the old-model
side. -/
theorem toPullback_comp_fromPullback
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    Hom.compose (J := J) hSheaf
        (toPullbackHom (J := J) D I)
        (fromPullbackHom (J := J) D I) =
      identity (J := J) (stage3LocalOldObject (J := J) D I) := by
  refine Hom.ext_base_family
    (Hom.compose (J := J) hSheaf
      (toPullbackHom (J := J) D I)
      (fromPullbackHom (J := J) D I))
    (identity (J := J) (stage3LocalOldObject (J := J) D I)) ?_ ?_
  · simp [Hom.compose, identity]
  · intro W K M k m h
    simpa [Hom.compose, identity, toPullbackHom, fromPullbackHom,
      DescentCompletionObjectOver.NaturalHomOver.compose,
      DescentCompletionObjectOver.NaturalHomOver.composeOfNaturality,
      DescentCompletionObjectOver.NaturalHomOver.composeCandidate] using
      toPullback_fromPullback_compositionFamily (J := J) hSheaf D I K M k m h

set_option maxHeartbeats 800000 in
/-- The total local maps `D|_{U_i} -> x_i` and `x_i -> D|_{U_i}` are inverse on the pullback side.
-/
theorem fromPullback_comp_toPullback
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X)
    (I : D.object.cover.Arrow) :
    Hom.compose (J := J) hSheaf
        (fromPullbackHom (J := J) D I)
        (toPullbackHom (J := J) D I) =
      identity (J := J) (stage3LocalPullbackObject (J := J) D I) := by
  refine Hom.ext_base_family
    (Hom.compose (J := J) hSheaf
      (fromPullbackHom (J := J) D I)
      (toPullbackHom (J := J) D I))
    (identity (J := J) (stage3LocalPullbackObject (J := J) D I)) ?_ ?_
  · simp [Hom.compose, identity]
  · intro W L M l m h
    simpa [Hom.compose, identity, fromPullbackHom, toPullbackHom,
      DescentCompletionObjectOver.NaturalHomOver.compose,
      DescentCompletionObjectOver.NaturalHomOver.composeOfNaturality,
      DescentCompletionObjectOver.NaturalHomOver.composeCandidate] using
      fromPullback_toPullback_compositionFamily (J := J) hSheaf D I L M l m h

end Stage3LocalModel
end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
