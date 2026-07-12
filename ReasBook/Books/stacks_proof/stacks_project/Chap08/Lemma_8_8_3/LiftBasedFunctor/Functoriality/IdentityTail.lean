import StacksProject_2024.Chap04.CanonicalFiberPseudofunctor

universe u v uS vS

namespace CategoryTheory

open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {T : Type uS} [Category.{vS} T]

/-- Helper for the identity part of Chap08 Lemma 8.8.3: after the local identity calculation has
reduced to the canonical pseudofunctor's identity/composition comparison tail, the chosen identity
pullback arrow cancels it. -/
theorem canonicalFiberPseudofunctor_mapComp_id_hom_app_comp_identityCart
    (p : T ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (z : p.Fiber U) :
    let cart : (𝟙 U) ^*[canonicalPullbackChoice p] z ⟶ z :=
      ⟨(canonicalPullbackChoice p).map (𝟙 U) z, by
        exact ((canonicalPullbackChoice p).isStronglyCartesian (𝟙 U) z).toIsHomLift⟩
    (eqToHom (by simp) ≫
        ((canonicalFiberPseudofunctor p).mapComp'
          (𝟙 U).op.toLoc f.op.toLoc
          f.op.toLoc (by simp)).hom.toNatTrans.app z) ≫
      ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map cart =
    ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map (𝟙 z) := by
  intro cart
  have hcomp :
      ((canonicalFiberPseudofunctor p).mapComp'
          (𝟙 U).op.toLoc f.op.toLoc
          f.op.toLoc (by simp)).hom.toNatTrans.app z =
        eqToHom (by simp) ≫
          ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app z) := by
    simpa only [op_id, Quiver.Hom.id_toLoc] using
      (Pseudofunctor.mapComp'_id_comp_hom_app
        (F := canonicalFiberPseudofunctor p)
        (f := f.op.toLoc) z)
  erw [hcomp]
  dsimp only [cart]
  have hunit :
      ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app z ≫
        (⟨(canonicalPullbackChoice p).map (𝟙 U) z, by
          exact ((canonicalPullbackChoice p).isStronglyCartesian (𝟙 U) z).toIsHomLift⟩ :
          (𝟙 U) ^*[canonicalPullbackChoice p] z ⟶ z) =
        𝟙 z := by
    apply Functor.Fiber.hom_ext
    simpa [canonicalFiberPseudofunctor, PullbackChoice.fiberPseudofunctor,
      PullbackChoice.pullbackIdIso, Category.assoc] using
      (canonicalPullbackChoice p).pullbackIdComponentIso_fac U z
  dsimp only [Cat.Hom.id_toFunctor, Functor.id_obj]
  simp only [Category.id_comp, eqToHom_refl]
  erw [← ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map_comp]
  change ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
      ((((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app z) ≫
        (⟨(canonicalPullbackChoice p).map (𝟙 U) z, by
          exact ((canonicalPullbackChoice p).isStronglyCartesian (𝟙 U) z).toIsHomLift⟩ :
          (𝟙 U) ^*[canonicalPullbackChoice p] z ⟶ z)) =
    ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map (𝟙 z)
  rw [hunit]
  simp

end

end CategoryTheory
