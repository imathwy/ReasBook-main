import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Arrows

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]

/-- For the canonical fiber pseudofunctor, the inverse composition comparison followed by the
chosen composite pullback arrow is the composite of the two chosen pullback arrows. -/
theorem mapCompAppIso_inv_comp_pullbackMap
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (y : p.Fiber U) :
    (mapCompAppIso p f g gf
        (FibredCategoryMor.comp_toLoc_eq f g gf hgf) y).inv.1 ≫
      (canonicalPullbackChoice p).map gf y =
    (canonicalPullbackChoice p).map g
        (f ^*[canonicalPullbackChoice p] y) ≫
      (canonicalPullbackChoice p).map f y := by
  subst gf
  dsimp only [mapCompAppIso]
  simp [PullbackChoice.fiberPseudofunctor, Pseudofunctor.mapComp']
  erw [Category.comp_id]
  change ((((canonicalPullbackChoice p).pullbackCompIso f g).inv.app y).1) ≫
      (canonicalPullbackChoice p).map (g ≫ f) y =
    (canonicalPullbackChoice p).map g (f ^*[canonicalPullbackChoice p] y) ≫
      (canonicalPullbackChoice p).map f y
  simpa [PullbackChoice.pullbackCompIso, NatTrans.comp_app] using
    (canonicalPullbackChoice p).pullbackCompComponentIso_inv_fac f g y

/-- Transporting a chosen pullback object along an equality of base arrows factors the chosen
pullback map through the same equality. -/
theorem eqToHom_pullbackMap_fac
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {U V : C} (f gf : V ⟶ U) (h : f = gf) (y : p.Fiber U) :
    (eqToHom (congrArg (fun k => k ^*[canonicalPullbackChoice p] y) h)).1 ≫
      (canonicalPullbackChoice p).map gf y =
    (canonicalPullbackChoice p).map f y := by
  cases h
  dsimp
  change 𝟙 ((f ^*[canonicalPullbackChoice p] y).1) ≫
      (canonicalPullbackChoice p).map f y =
    (canonicalPullbackChoice p).map f y
  rw [Category.id_comp]

/-- For an identity total arrow, the chosen vertical factor followed by the inverse composition
comparison is just the transported identity between the two chosen pullbacks along equal base
maps. -/
theorem stackificationLiftArrowVerticalFactor_id_mapCompAppIso_inv
    {J : GrothendieckTopology C}
    {S' : StackOver.{u, v, uS, vS} J}
    (T : S'.S) (Y : C) (f : Y ⟶ S'.p.obj T) :
    let y : S'.p.Fiber (S'.p.obj T) :=
      Functor.Fiber.mk (p := S'.p) (a := T) rfl
    ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map
        (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
      (mapCompAppIso S'.p (S'.p.map (𝟙 T)) f (f ≫ S'.p.map (𝟙 T))
        (FibredCategoryMor.comp_toLoc_eq (S'.p.map (𝟙 T)) f
          (f ≫ S'.p.map (𝟙 T)) rfl) y).inv =
        eqToHom (congrArg (fun k => k ^*[canonicalPullbackChoice S'.p] y)
          (by simp : f = f ≫ S'.p.map (𝟙 T))) := by
  intro y
  let ψ :=
    ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map
        (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
      (mapCompAppIso S'.p (S'.p.map (𝟙 T)) f (f ≫ S'.p.map (𝟙 T))
        (FibredCategoryMor.comp_toLoc_eq (S'.p.map (𝟙 T)) f
          (f ≫ S'.p.map (𝟙 T)) rfl) y).inv
  let ψ' :=
    (eqToHom (congrArg (fun k => k ^*[canonicalPullbackChoice S'.p] y)
      (by simp : f = f ≫ S'.p.map (𝟙 T))) :
      ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.obj y ⟶
        (f ≫ S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice S'.p] y)
  change ψ = ψ'
  apply Functor.Fiber.hom_ext
  change ψ.1 = ψ'.1
  haveI : S'.p.IsStronglyCartesian (f ≫ S'.p.map (𝟙 T))
      ((canonicalPullbackChoice S'.p).map (f ≫ S'.p.map (𝟙 T)) y) :=
    (canonicalPullbackChoice S'.p).isStronglyCartesian (f ≫ S'.p.map (𝟙 T)) y
  haveI : S'.p.IsHomLift (𝟙 Y) ψ.1 := ψ.2
  haveI : S'.p.IsHomLift (𝟙 Y) ψ'.1 := ψ'.2
  apply Functor.IsStronglyCartesian.ext S'.p (f ≫ S'.p.map (𝟙 T))
    ((canonicalPullbackChoice S'.p).map (f ≫ S'.p.map (𝟙 T)) y) (𝟙 Y)
  have hcomp :
      (mapCompAppIso S'.p (S'.p.map (𝟙 T)) f (f ≫ S'.p.map (𝟙 T))
          (FibredCategoryMor.comp_toLoc_eq (S'.p.map (𝟙 T)) f
            (f ≫ S'.p.map (𝟙 T)) rfl) y).inv.1 ≫
        (canonicalPullbackChoice S'.p).map (f ≫ S'.p.map (𝟙 T)) y =
      (canonicalPullbackChoice S'.p).map f
          ((S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice S'.p] y) ≫
        (canonicalPullbackChoice S'.p).map (S'.p.map (𝟙 T)) y :=
    mapCompAppIso_inv_comp_pullbackMap S'.p
      (S'.p.map (𝟙 T)) f (f ≫ S'.p.map (𝟙 T)) rfl y
  have hmap :
      (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T))).1 ≫
        (canonicalPullbackChoice S'.p).map f
          ((S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice S'.p] y) =
      (canonicalPullbackChoice S'.p).map f y ≫
        (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)).1 := by
    simpa [canonicalFiberPseudofunctor, PullbackChoice.fiberPseudofunctor] using
      (canonicalPullbackChoice S'.p).pullbackFunctor_map_fac f
        (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T))
  have hv :
      (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)).1 ≫
        (canonicalPullbackChoice S'.p).map (S'.p.map (𝟙 T)) y =
      𝟙 T := by
    simpa [y] using
      stackificationLiftArrowVerticalFactor_fac (S' := S') (𝟙 T)
  have hleft : ψ.1 ≫
        (canonicalPullbackChoice S'.p).map (f ≫ S'.p.map (𝟙 T)) y =
      (canonicalPullbackChoice S'.p).map f y := by
    dsimp [ψ]
    calc
      ((((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map
              (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T))).1 ≫
          (mapCompAppIso S'.p (S'.p.map (𝟙 T)) f (f ≫ S'.p.map (𝟙 T))
              (FibredCategoryMor.comp_toLoc_eq (S'.p.map (𝟙 T)) f
                (f ≫ S'.p.map (𝟙 T)) rfl) y).inv.1) ≫
          (canonicalPullbackChoice S'.p).map (f ≫ S'.p.map (𝟙 T)) y =
        (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map
              (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T))).1 ≫
          ((mapCompAppIso S'.p (S'.p.map (𝟙 T)) f (f ≫ S'.p.map (𝟙 T))
              (FibredCategoryMor.comp_toLoc_eq (S'.p.map (𝟙 T)) f
                (f ≫ S'.p.map (𝟙 T)) rfl) y).inv.1 ≫
            (canonicalPullbackChoice S'.p).map (f ≫ S'.p.map (𝟙 T)) y) := by
          rw [Category.assoc]
      _ =
        (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map
              (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T))).1 ≫
          ((canonicalPullbackChoice S'.p).map f
              ((S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice S'.p] y) ≫
            (canonicalPullbackChoice S'.p).map (S'.p.map (𝟙 T)) y) := by
          simpa only [Category.assoc] using
            congrArg
              (fun t =>
                (((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map
                    (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T))).1 ≫ t)
              hcomp
      _ =
        ((((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor.map
              (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T))).1 ≫
          (canonicalPullbackChoice S'.p).map f
              ((S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice S'.p] y)) ≫
            (canonicalPullbackChoice S'.p).map (S'.p.map (𝟙 T)) y := by
          simp only [Category.assoc]
      _ =
        ((canonicalPullbackChoice S'.p).map f y ≫
            (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)).1) ≫
          (canonicalPullbackChoice S'.p).map (S'.p.map (𝟙 T)) y := by
          exact congrArg
            (fun t => t ≫ (canonicalPullbackChoice S'.p).map (S'.p.map (𝟙 T)) y)
            hmap
      _ =
        (canonicalPullbackChoice S'.p).map f y ≫
          ((stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)).1 ≫
            (canonicalPullbackChoice S'.p).map (S'.p.map (𝟙 T)) y) := by
          simp only [Category.assoc]
      _ = (canonicalPullbackChoice S'.p).map f y := by
          exact
            (congrArg (fun t => (canonicalPullbackChoice S'.p).map f y ≫ t) hv).trans
              (by
                change (canonicalPullbackChoice S'.p).map f y ≫ 𝟙 y.1 =
                  (canonicalPullbackChoice S'.p).map f y
                rw [Category.comp_id])
  have hright : ψ'.1 ≫
        (canonicalPullbackChoice S'.p).map (f ≫ S'.p.map (𝟙 T)) y =
      (canonicalPullbackChoice S'.p).map f y := by
    dsimp [ψ']
    let e : f = f ≫ S'.p.map (𝟙 T) := by simp
    change (eqToHom (congrArg (fun k => k ^*[canonicalPullbackChoice S'.p] y) e)).1 ≫
        (canonicalPullbackChoice S'.p).map (f ≫ S'.p.map (𝟙 T)) y =
      (canonicalPullbackChoice S'.p).map f y
    exact eqToHom_pullbackMap_fac S'.p f (f ≫ S'.p.map (𝟙 T)) e y
  exact hleft.trans hright.symm

end

end CategoryTheory
