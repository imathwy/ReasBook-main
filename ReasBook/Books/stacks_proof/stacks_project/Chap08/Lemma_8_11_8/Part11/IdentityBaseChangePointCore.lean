import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part11.TransitionSquare

universe u v w uS vS

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

private theorem iso_inv_eq_of_hom_eq_local {D : Type*} [Category D] {A B : D}
    (e f : A ≅ B) (h : e.hom = f.hom) :
    e.inv = f.inv := by
  rw [← cancel_mono e.hom]
  rw [h]
  simp only [Iso.inv_hom_id]
  rw [← h]
  simp only [Iso.inv_hom_id]

/-- Identity/base-change app normal form with the composition owners already normalized.  The
remaining work in the point-core proof is the owner transport from
`𝟙 ≫ T.unop.hom.op.toLoc` to `T.unop.hom.op.toLoc`. -/
theorem identityBaseChange_mapComp_app_normal_form_normalized
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS})
    {U V : C} (f : V ⟶ U)
    {x : F.obj (LocallyDiscrete.mk (op U))}
    (α : (F.map f.op.toLoc).toFunctor.obj x ⟶
      (F.map f.op.toLoc).toFunctor.obj x) :
    ((F.mapComp' (𝟙 (LocallyDiscrete.mk (op U))) f.op.toLoc
          f.op.toLoc (by simp)).inv.toNatTrans.app x ≫
        ((F.mapComp' f.op.toLoc (𝟙 (LocallyDiscrete.mk (op V)))
              f.op.toLoc (by simp)).hom.toNatTrans.app x ≫
          (F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.map α ≫
          (F.mapComp' f.op.toLoc (𝟙 (LocallyDiscrete.mk (op V)))
              f.op.toLoc (by simp)).inv.toNatTrans.app x) ≫
        (F.mapComp' (𝟙 (LocallyDiscrete.mk (op U))) f.op.toLoc
          f.op.toLoc (by simp)).hom.toNatTrans.app x) =
      ((F.map f.op.toLoc).toFunctor.map
          ((F.mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app x) ≫
        α ≫
      (F.map f.op.toLoc).toFunctor.map
          ((F.mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app x)) := by
  rw [Pseudofunctor.mapComp'_id_comp_inv_app]
  rw [Pseudofunctor.mapComp'_id_comp_hom_app]
  rw [Pseudofunctor.mapComp'_comp_id_hom_app]
  rw [Pseudofunctor.mapComp'_comp_id_inv_app]
  simp only [Category.assoc]
  simp
  let A := (F.map f.op.toLoc).toFunctor.map
    ((F.mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app x)
  let B := (F.map f.op.toLoc).toFunctor.map
    ((F.mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app x)
  let y := (F.map f.op.toLoc).toFunctor.obj x
  let η := F.mapId (LocallyDiscrete.mk (op V))
  have hmid : η.inv.toNatTrans.app y ≫
      (F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.map α ≫
        η.hom.toNatTrans.app y = α := by
    dsimp [η, y]
    exact Pseudofunctor.mapId_inv_map_hom_hom_core (F := F) V α
  change A ≫ η.inv.toNatTrans.app y ≫
      (F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.map α ≫
        η.hom.toNatTrans.app y ≫ B = A ≫ α ≫ B
  calc
    A ≫ η.inv.toNatTrans.app y ≫
        (F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.map α ≫
          η.hom.toNatTrans.app y ≫ B
        = A ≫ (η.inv.toNatTrans.app y ≫
            (F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.map α ≫
              η.hom.toNatTrans.app y) ≫ B := by
            simp [Category.assoc]
    _ = A ≫ α ≫ B := by
      exact congrArg (fun m => A ≫ m ≫ B) hmid

/-- The canonical fiber pseudofunctor's `mapId.hom` component is the inverse of the chosen
identity-pullback component. -/
theorem canonicalFiberPseudofunctor_mapId_hom_app_eq_pullbackIdComponentIso_inv
    {C : Type u} [Category.{v} C] {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (U : C) (z : p.Fiber U) :
    ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app z =
      ((canonicalPullbackChoice p).pullbackIdComponentIso U z).inv := by
  apply Functor.Fiber.hom_ext
  simpa [canonicalFiberPseudofunctor, PullbackChoice.fiberPseudofunctor,
    PullbackChoice.pullbackIdIso] using
    (canonicalPullbackChoice p).pullbackIdComponentIso_inv_eq U z

/-- The canonical fiber pseudofunctor's `mapId.inv` component is the forward chosen
identity-pullback component. -/
theorem canonicalFiberPseudofunctor_mapId_inv_app_eq_pullbackIdComponentIso_hom
    {C : Type u} [Category.{v} C] {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] (U : C) (z : p.Fiber U) :
    ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app z =
      ((canonicalPullbackChoice p).pullbackIdComponentIso U z).hom := by
  let eMap := (Cat.Hom.toNatIso
    ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op U)))).app z
  let ePull := ((canonicalPullbackChoice p).pullbackIdComponentIso U z).symm
  have hhom : eMap.hom = ePull.hom := by
    dsimp [eMap, ePull]
    exact canonicalFiberPseudofunctor_mapId_hom_app_eq_pullbackIdComponentIso_inv p U z
  exact iso_inv_eq_of_hom_eq_local eMap ePull hhom

/-- Canonical-fiber version of the normalized identity/base-change app normal form. -/
theorem canonicalFiberPseudofunctor_identity_baseChange_normalized
    {C : Type u} [Category.{v} C] {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U)
    (α : ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x ⟶
      ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x) :
    (((canonicalFiberPseudofunctor p).mapComp' (𝟙 (LocallyDiscrete.mk (op U))) f.op.toLoc
          f.op.toLoc (by simp)).inv.toNatTrans.app x ≫
        (((canonicalFiberPseudofunctor p).mapComp' f.op.toLoc
              (𝟙 (LocallyDiscrete.mk (op V))) f.op.toLoc
              (by simp)).hom.toNatTrans.app x ≫
          ((canonicalFiberPseudofunctor p).map
              (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.map α ≫
          ((canonicalFiberPseudofunctor p).mapComp' f.op.toLoc
              (𝟙 (LocallyDiscrete.mk (op V))) f.op.toLoc
              (by simp)).inv.toNatTrans.app x) ≫
        ((canonicalFiberPseudofunctor p).mapComp' (𝟙 (LocallyDiscrete.mk (op U))) f.op.toLoc
          f.op.toLoc (by simp)).hom.toNatTrans.app x) =
      ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.mapIso
        ((canonicalPullbackChoice p).pullbackIdComponentIso U x)).conj α) := by
  rw [identityBaseChange_mapComp_app_normal_form_normalized]
  rw [canonicalFiberPseudofunctor_mapId_hom_app_eq_pullbackIdComponentIso_inv]
  rw [canonicalFiberPseudofunctor_mapId_inv_app_eq_pullbackIdComponentIso_hom]
  rfl

/-- Raw owner form of `canonicalFiberPseudofunctor_identity_baseChange_normalized` produced by
the `overMapPullbackId`/`overMapCompPresheafHomIso` point calculation.  The only difference from
the stable normal form is that the `mapComp'` owners are still the literal composites
`𝟙 ≫ T.unop.hom.op.toLoc` and `(T.unop.hom ≫ 𝟙 _).op.toLoc`. -/
private theorem canonicalFiberPseudofunctor_identity_baseChange_raw_owner_normalized
    {C : Type u} [Category.{v} C] {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered]
    {U : C} (x : p.Fiber U) (T : (Over U)ᵒᵖ)
    (α : ((canonicalFiberPseudofunctor p).map T.unop.hom.op.toLoc).toFunctor.obj x ⟶
      ((canonicalFiberPseudofunctor p).map T.unop.hom.op.toLoc).toFunctor.obj x) :
    (((canonicalFiberPseudofunctor p).mapComp' (𝟙 (LocallyDiscrete.mk (op U)))
          T.unop.hom.op.toLoc
          (𝟙 (LocallyDiscrete.mk (op U)) ≫ T.unop.hom.op.toLoc) rfl).inv.toNatTrans.app x ≫
        (((canonicalFiberPseudofunctor p).mapComp' T.unop.hom.op.toLoc
              (𝟙 (LocallyDiscrete.mk (op T.unop.left)))
              (T.unop.hom ≫ 𝟙 U).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app x ≫
          ((canonicalFiberPseudofunctor p).map
              (𝟙 (LocallyDiscrete.mk (op T.unop.left)))).toFunctor.map α ≫
          ((canonicalFiberPseudofunctor p).mapComp' T.unop.hom.op.toLoc
              (𝟙 (LocallyDiscrete.mk (op T.unop.left)))
              (T.unop.hom ≫ 𝟙 U).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app x) ≫
        ((canonicalFiberPseudofunctor p).mapComp' (𝟙 (LocallyDiscrete.mk (op U)))
          T.unop.hom.op.toLoc
          (𝟙 (LocallyDiscrete.mk (op U)) ≫ T.unop.hom.op.toLoc) rfl).hom.toNatTrans.app x) =
      ((((canonicalFiberPseudofunctor p).map T.unop.hom.op.toLoc).toFunctor.mapIso
        ((canonicalPullbackChoice p).pullbackIdComponentIso U x)).conj α) := by
  -- Narrow owner-normalization adapter: convert the literal `mapComp'` composite owners above
  -- to the stable owner `T.unop.hom.op.toLoc` used by
  -- `canonicalFiberPseudofunctor_identity_baseChange_normalized`.
  sorry

/-- Helper for Lemma 8.11.8: the identity restriction followed by the canonical base-change
comparison is conjugation by the canonical identity-pullback component. -/
theorem automorphismUnderlyingSheaf_identity_baseChange_point_core
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U)
    (T : (Over U)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj T) :
    ((((J.pseudofunctorOver (Type (max u v))).mapId
        (LocallyDiscrete.mk (op U))).inv.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian (𝟙 U) x).hom).1.app T) α =
    ((automorphismUnderlyingSheafConj
      (𝒮 := 𝒮) hAbelian
      ((canonicalPullbackChoice 𝒮.p).pullbackIdComponentIso U x).hom).hom.1.app T) α := by
  rw [automorphismUnderlyingSheafConj_hom_app]
  change ((automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian (𝟙 U) x).hom.1.app T)
      ((((J.pseudofunctorOver (Type (max u v))).mapId
        (LocallyDiscrete.mk (op U))).inv.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).1.app T α) = _
  rw [automorphismUnderlyingSheafBaseChangeIso_hom_app]
  rw [overMapCompPresheafHomIso_hom_app]
  dsimp [GrothendieckTopology.pseudofunctorOver]
  rw [GrothendieckTopology.overMapPullbackId_inv_app_hom_app]
  dsimp [automorphismUnderlyingSheaf, StackInGroupoidsOver.automorphismAddCommSheaf,
    automorphismAddCommPresheaf, automorphismSection]
  delta Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  exact canonicalFiberPseudofunctor_identity_baseChange_raw_owner_normalized
    (p := 𝒮.p) x T α

end CategoryTheory
