import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_4.Index
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_11_8.Part13

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Generic owner-input cast (local copy of Part12's `app_obj_cast`): evaluating a presheaf
morphism on a section at one owner equals the cast of its evaluation at an equal owner. -/
private theorem app_obj_cast14 {D : Type (max u v)} [Category.{v} D]
    {ℱ 𝒢 : Dᵒᵖ ⥤ Type (max u v)} (ψ : ℱ ⟶ 𝒢) {A B : Dᵒᵖ} (h : A = B)
    (s : ℱ.obj A) :
    ψ.app A s =
      (congrArg 𝒢.obj h).mpr (ψ.app B (Eq.mp (congrArg ℱ.obj h) s)) := by
  cases h
  rfl

/-- Owner-input cast on a `.mpr`-transported section: evaluating at the source owner of a
transported section equals the cast of the evaluation at the target owner. -/
private theorem app_obj_cast14' {D : Type (max u v)} [Category.{v} D]
    {ℱ 𝒢 : Dᵒᵖ ⥤ Type (max u v)} (ψ : ℱ ⟶ 𝒢) {A B : Dᵒᵖ} (h : A = B)
    (β : ℱ.obj B) :
    ψ.app A ((congrArg ℱ.obj h).mpr β) =
      (congrArg 𝒢.obj h).mpr (ψ.app B β) := by
  cases h
  rfl

/-- Local owner-cast cancellation. -/
private theorem obj_cast_mpr_mp14 {D : Type (max u v)} [Category.{v} D]
    (F : Dᵒᵖ ⥤ Type (max u v)) {A B : Dᵒᵖ} (h : A = B) (s : F.obj A) :
    (congrArg F.obj h).mpr (Eq.mp (congrArg F.obj h) s) = s := by
  cases h
  rfl

/-- Local owner-cast cancellation in the opposite order. -/
private theorem obj_cast_mp_mpr14 {D : Type (max u v)} [Category.{v} D]
    (F : Dᵒᵖ ⥤ Type (max u v)) {A B : Dᵒᵖ} (h : A = B) (s : F.obj B) :
    Eq.mp (congrArg F.obj h) ((congrArg F.obj h).mpr s) = s := by
  cases h
  rfl

/-- Local owner-cast injectivity for `.mpr` transports. -/
private theorem obj_cast_mpr_injective14 {D : Type (max u v)} [Category.{v} D]
    (F : Dᵒᵖ ⥤ Type (max u v)) {A B : Dᵒᵖ} (h : A = B) {s t : F.obj B} :
    (congrArg F.obj h).mpr s = (congrArg F.obj h).mpr t → s = t := by
  cases h
  intro hst
  simpa using hst

/-- Local copy of Part12's `pf_map_app_eq_image_app_obj`: evaluating the `pf.map g`-pullback of a
sheaf morphism at a slice object is the original morphism at the `Over.map g`-image. -/
private theorem pf_map_app_eq_image_app_obj14 {X Y : C} (g : X ⟶ Y)
    {ℱ 𝒢 : Sheaf (J.over Y) (Type (max u v))} (φ : ℱ ⟶ 𝒢) (W : Over X) :
    (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map φ).1.app (op W) =
      φ.1.app (op ((Over.map g).obj W)) := rfl

/-- Local copy of Part13's `eqmp_eq_map_eqToHom`. -/
private theorem eqmp_eq_map_eqToHom14 {D : Type (max u v)} [Category.{v} D]
    (F : Dᵒᵖ ⥤ Type (max u v)) {A B : Dᵒᵖ} (h : A = B) (β : F.obj A) :
    Eq.mp (congrArg F.obj h) β = F.map (eqToHom h) β := by
  cases h; simp

private theorem sheaf_iso_hom_inv_app14 {D : Type (max u v)} [Category.{v} D]
    {K : GrothendieckTopology D} {ℱ 𝒢 : Sheaf K (Type (max u v))}
    (e : ℱ ≅ 𝒢) (A : Dᵒᵖ) (s : ℱ.1.obj A) :
    e.inv.1.app A (e.hom.1.app A s) = s := by
  change ((e.hom ≫ e.inv : ℱ ⟶ ℱ).1.app A) s = ((𝟙 ℱ : ℱ ⟶ ℱ).1.app A) s
  rw [e.hom_inv_id]

private theorem sheaf_iso_inv_hom_app14 {D : Type (max u v)} [Category.{v} D]
    {K : GrothendieckTopology D} {ℱ 𝒢 : Sheaf K (Type (max u v))}
    (e : ℱ ≅ 𝒢) (A : Dᵒᵖ) (s : 𝒢.1.obj A) :
    e.hom.1.app A (e.inv.1.app A s) = s := by
  change ((e.inv ≫ e.hom : 𝒢 ⟶ 𝒢).1.app A) s = ((𝟙 𝒢 : 𝒢 ⟶ 𝒢).1.app A) s
  rw [e.inv_hom_id]

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

/-- Local surface adapter for the pulled-`φ` shell: the expanded `f`-base-change expression at
the literal owner `op (Over.mk q)` is the owner-transport form of the pulled conjugation along
`q`. -/
private theorem automorphismUnderlyingSheafConj_outer_app_eq_pulled_app14
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} {x y : 𝒮.p.Fiber U} (f : Y ⟶ U) (q : Z ⟶ Y) (φ : x ⟶ y) :
    let pulledφ :
        (f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).map φ
    ∀ s : ((((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).1.obj (op (Over.mk q))),
    ((((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1.app
      (op (Over.mk q))) s =
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f y).inv.1.app
        (op (Over.mk q))
        (Eq.mp
          (congrArg
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (f ^*[canonicalPullbackChoice 𝒮.p] y)).1.obj
            (over_map_obj_mk_eq_op q (𝟙 Z) q (by simp)))
          (((((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.map
                ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app
              (op (Over.mk (𝟙 Z))))
            ((congrArg
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj
                (over_map_obj_mk_eq_op q (𝟙 Z) q (by simp))).mpr
              ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom.1.app
                (op (Over.mk q)) s)))) := by
  intro pulledφ s
  have hnat :=
    automorphismUnderlyingSheafConj_pullbackFunctor_map (𝒮 := 𝒮) hAbelian f φ
  have key := congrFun (congrArg (fun m => m.1.app (op (Over.mk q))) hnat) s
  refine key.trans ?_
  change (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f y).inv.1.app
      (op (Over.mk q))
      ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom.1.app (op (Over.mk q))
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom.1.app
          (op (Over.mk q)) s)) = _
  rw [pseudofunctor_over_map_app_eq_owner_transport (J := J) q
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom (𝟙 Z) q (by simp)
    ((congrArg
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj
        (over_map_obj_mk_eq_op q (𝟙 Z) q (by simp))).mpr
      ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom.1.app
        (op (Over.mk q)) s))]
  simp only [eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq]
  congr 1

/-- Helper for Lemma 8.11.8: after the owner-change comparison is rewritten to the literal owner
`op (Over.mk (𝟙 S.unop.left))`, the pullback of the fixed `qI` common-owner shell is just the
actual `S`-component of that shell. This packages the final owner-leg transport back to the
component used by the main corridor. -/
private theorem chosen_local_owner_leg_pullback_qI_shell_eq_common_owner_component_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    {S : (Over I.Y.left)ᵒᵖ}
    (β :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj S) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    ((((((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom)).1.app
          (op (Over.mk (𝟙 S.unop.left)))))
        ((congrArg
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (qI ^*[canonicalPullbackChoice 𝒮.p]
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj)
            (over_map_obj_mk_eq_op S.unop.hom (𝟙 S.unop.left) S.unop.hom (by simp))).mpr β)) =
      ((congrArg
          ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (qI ^*[canonicalPullbackChoice 𝒮.p]
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).1.obj)
          (over_map_obj_mk_eq_op S.unop.hom (𝟙 S.unop.left) S.unop.hom (by simp))).mpr
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom).1.app S)
          β)) := by
  intro qI
  rw [pf_map_app_eq_image_app_obj14]
  exact app_obj_cast14'
    ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom) (by simp [qI])).hom).hom.1)
    (over_map_obj_mk_eq_op S.unop.hom (𝟙 S.unop.left) S.unop.hom (by simp)) β

/-- Helper for Lemma 8.11.8: after identifying the literal owner
`qS := S.unop.hom ≫ (I.Y.hom ≫ K.f)`, its common-owner component is exactly the actual
`S`-component of the fixed `qI := I.Y.hom ≫ K.f` common-owner comparison. This packages the
owner-leg transport corridor as one reusable app-level equality. -/
private theorem chosen_local_qS_common_owner_component_eq_qI_common_owner_component_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    {S : (Over I.Y.left)ᵒᵖ}
    (β :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj S) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let qS : S.unop.left ⟶ L.Y := S.unop.hom ≫ qI
    let O' : (Over S.unop.left)ᵒᵖ := op (Over.mk (𝟙 S.unop.left))
    -- Owner-change coherence bridge from the `S.unop.hom`-pull of `qI` to the composite owner `qS`.
    let cohInRev :=
      ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            qI.op.toLoc S.unop.hom.op.toLoc qS.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom
    let cohOutInv :=
      ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            qI.op.toLoc S.unop.hom.op.toLoc qS.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
    let βS :=
      cohInRev.1.app O'
        ((congrArg
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (qI ^*[canonicalPullbackChoice 𝒮.p]
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj)
            (over_map_obj_mk_eq_op S.unop.hom (𝟙 S.unop.left) S.unop.hom (by simp))).mpr β)
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qS (K := K) (g := S.unop.hom ≫ I.Y.hom)
            (by simp [qI, qS, Category.assoc])).hom).hom).1.app O')
      βS) =
      cohOutInv.1.app O'
        ((congrArg
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (qI ^*[canonicalPullbackChoice 𝒮.p]
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).1.obj)
            (over_map_obj_mk_eq_op S.unop.hom (𝟙 S.unop.left) S.unop.hom (by simp))).mpr
          ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom).1.app S)
            β)) := by
  intro qI qS O' cohInRev cohOutInv βS
  let A :=
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  let BqI :=
    ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
  let BqS :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  let M :=
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      qI.op.toLoc S.unop.hom.op.toLoc qS.op.toLoc (by cat_disch)
  let cohIn :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qS
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          qI.op.toLoc S.unop.hom.op.toLoc qS.op.toLoc (by cat_disch)).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
      ((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom
  let s0 :=
    ((congrArg
        ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (qI ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj)
        (over_map_obj_mk_eq_op S.unop.hom (𝟙 S.unop.left) S.unop.hom (by simp))).mpr β)
  have hcoh : cohInRev ≫ cohIn = 𝟙 _ := by
    dsimp [cohInRev, cohIn, BqI, BqS, M, A]
    change
      BqI.inv ≫ M.inv.toNatTrans.app A ≫ BqS.hom ≫ BqS.inv ≫
          M.hom.toNatTrans.app A ≫ BqI.hom = 𝟙 _
    calc
      BqI.inv ≫ M.inv.toNatTrans.app A ≫ BqS.hom ≫ BqS.inv ≫
          M.hom.toNatTrans.app A ≫ BqI.hom
          = BqI.inv ≫ M.inv.toNatTrans.app A ≫ (BqS.hom ≫ BqS.inv) ≫
              M.hom.toNatTrans.app A ≫ BqI.hom := by
            simp only [Category.assoc]
      _ = BqI.inv ≫ M.inv.toNatTrans.app A ≫ 𝟙 _ ≫
              M.hom.toNatTrans.app A ≫ BqI.hom := by
            exact congrArg
              (fun f => BqI.inv ≫ M.inv.toNatTrans.app A ≫ f ≫
                M.hom.toNatTrans.app A ≫ BqI.hom)
              BqS.hom_inv_id
      _ = BqI.inv ≫ (M.inv.toNatTrans.app A ≫ M.hom.toNatTrans.app A) ≫
              BqI.hom := by
            simp only [Category.assoc, Category.id_comp]
      _ = BqI.inv ≫ 𝟙 _ ≫ BqI.hom := by
            have hM : M.inv.toNatTrans.app A ≫ M.hom.toNatTrans.app A = 𝟙 _ :=
              Cat.Hom.inv_hom_id_toNatTrans_app M A
            exact congrArg (fun f => BqI.inv ≫ f ≫ BqI.hom) hM
      _ = BqI.inv ≫ BqI.hom := by simp only [Category.id_comp]
      _ = 𝟙 _ := BqI.inv_hom_id
  have hcancel : cohIn.1.app O' βS = s0 := by
    have happ := congrFun (congrArg (fun m => m.1.app O') hcoh) s0
    simpa [βS, s0, cohIn] using happ
  have hqS :=
    chosen_local_owner_leg_qS_common_owner_shell_eq_pullback_qI_app
      (𝒮 := 𝒮) hGerbe hAbelian L K (T := T) I (S := S) βS
  rw [hqS]
  change cohOutInv.1.app O'
      (((((J.pseudofunctorOver (Type (max u v))).map S.unop.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom)).1.app O')
        (cohIn.1.app O' βS)) =
    cohOutInv.1.app O'
      ((congrArg
          ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (qI ^*[canonicalPullbackChoice 𝒮.p]
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).1.obj)
          (over_map_obj_mk_eq_op S.unop.hom (𝟙 S.unop.left) S.unop.hom (by simp))).mpr
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom).1.app S) β))
  rw [hcancel]
  refine congrArg (cohOutInv.1.app O') ?_
  simpa [s0, O', qI] using
    (chosen_local_owner_leg_pullback_qI_shell_eq_common_owner_component_app
      (𝒮 := 𝒮) hGerbe hAbelian L K I β)

/-- Helper for Lemma 8.11.8: before evaluating on the literal owner
`op (Over.mk (𝟙 I.Y.left))`, commute the remaining raw source-side `mapComp'` inverse boundary
through the common-owner middle shell after specializing to an arbitrary owner leg
`S : Over I.Y.left`. This isolates the exact owner-generic naturality rewrite that is still
missing. -/
private theorem chosen_local_owner_leg_pulled_conjugation_eq_common_owner_component_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    {S : (Over I.Y.left)ᵒᵖ}
    (β :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj S) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    -- Source/target base-change bridges relating the `qI`-pullback world (where `β` lives) to the
    -- iterated `I.Y.hom`-pull of the `K.f`-pull world (where the pulled chosen-local conjugation
    -- lives). These are the canonical coherence isos the Mathlib refactor turned propositional.
    let srcB :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)) ≫
        ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom
    let tgtB :=
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
    ((srcB ≫
        ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) ≫
        tgtB).1.app S)
      β =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom).1.app S)
        β) := by
  intro qI srcB tgtB
  let inB :=
    ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom
  let outBridgeInv :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
  have hsrc_m : srcB ≫ inB = 𝟙 _ := by
    let A :=
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
    let Bq :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
    let BK :=
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
    let M :=
      (J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)
    dsimp [srcB, inB, Bq, BK, M, A]
    change Bq.inv ≫ M.hom.toNatTrans.app A ≫ BK.hom ≫ BK.inv ≫
        M.inv.toNatTrans.app A ≫ Bq.hom = 𝟙 _
    calc
      Bq.inv ≫ M.hom.toNatTrans.app A ≫ BK.hom ≫ BK.inv ≫
          M.inv.toNatTrans.app A ≫ Bq.hom
          = Bq.inv ≫ M.hom.toNatTrans.app A ≫ (BK.hom ≫ BK.inv) ≫
              M.inv.toNatTrans.app A ≫ Bq.hom := by
            simp only [Category.assoc]
      _ = Bq.inv ≫ M.hom.toNatTrans.app A ≫ 𝟙 _ ≫
              M.inv.toNatTrans.app A ≫ Bq.hom := by
            exact congrArg
              (fun f => Bq.inv ≫ M.hom.toNatTrans.app A ≫ f ≫
                M.inv.toNatTrans.app A ≫ Bq.hom)
              BK.hom_inv_id
      _ = Bq.inv ≫ (M.hom.toNatTrans.app A ≫ M.inv.toNatTrans.app A) ≫ Bq.hom := by
            simp only [Category.assoc, Category.id_comp]
      _ = Bq.inv ≫ 𝟙 _ ≫ Bq.hom := by
            have hM : M.hom.toNatTrans.app A ≫ M.inv.toNatTrans.app A = 𝟙 _ :=
              Cat.Hom.hom_inv_id_toNatTrans_app M A
            exact congrArg (fun f => Bq.inv ≫ f ≫ Bq.hom) hM
      _ = Bq.inv ≫ Bq.hom := by simp only [Category.id_comp]
      _ = 𝟙 _ := Bq.inv_hom_id
  have hsrc : inB.1.app S (srcB.1.app S β) = β := by
    have happ := congrFun (congrArg (fun m => m.1.app S) hsrc_m) β
    simpa using happ
  have hout_m : outBridgeInv ≫ tgtB = 𝟙 _ := by
    let A :=
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
    let Bq :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
    let BK :=
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
    let M :=
      (J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)
    dsimp [outBridgeInv, tgtB, Bq, BK, M, A]
    change Bq.inv ≫ M.hom.toNatTrans.app A ≫ BK.hom ≫ BK.inv ≫
        M.inv.toNatTrans.app A ≫ Bq.hom = 𝟙 _
    calc
      Bq.inv ≫ M.hom.toNatTrans.app A ≫ BK.hom ≫ BK.inv ≫
          M.inv.toNatTrans.app A ≫ Bq.hom
          = Bq.inv ≫ M.hom.toNatTrans.app A ≫ (BK.hom ≫ BK.inv) ≫
              M.inv.toNatTrans.app A ≫ Bq.hom := by
            simp only [Category.assoc]
      _ = Bq.inv ≫ M.hom.toNatTrans.app A ≫ 𝟙 _ ≫
              M.inv.toNatTrans.app A ≫ Bq.hom := by
            exact congrArg
              (fun f => Bq.inv ≫ M.hom.toNatTrans.app A ≫ f ≫
                M.inv.toNatTrans.app A ≫ Bq.hom)
              BK.hom_inv_id
      _ = Bq.inv ≫ (M.hom.toNatTrans.app A ≫ M.inv.toNatTrans.app A) ≫ Bq.hom := by
            simp only [Category.assoc, Category.id_comp]
      _ = Bq.inv ≫ 𝟙 _ ≫ Bq.hom := by
            have hM : M.hom.toNatTrans.app A ≫ M.inv.toNatTrans.app A = 𝟙 _ :=
              Cat.Hom.hom_inv_id_toNatTrans_app M A
            exact congrArg (fun f => Bq.inv ≫ f ≫ Bq.hom) hM
      _ = Bq.inv ≫ Bq.hom := by simp only [Category.id_comp]
      _ = 𝟙 _ := Bq.inv_hom_id
  change tgtB.1.app S
      (((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app S)
        (srcB.1.app S β)) =
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom).1.app S) β)
  have hnorm :=
    chosen_local_fixed_qI_component_normalized_app
      (𝒮 := 𝒮) hGerbe hAbelian L K (T := T) I (S := S) (srcB.1.app S β)
  rw [hnorm]
  rw [hsrc]
  have hout :
      tgtB.1.app S
        (outBridgeInv.1.app S
          ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom).1.app S) β)) =
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom).1.app S) β) := by
    have happ := congrFun (congrArg (fun m => m.1.app S) hout_m)
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
          (by simp [qI])).hom).hom).1.app S) β)
    simpa using happ
  exact hout

/-- Helper for Lemma 8.11.8: before evaluating on the literal owner
`op (Over.mk (𝟙 I.Y.left))`, commute the remaining raw source-side `mapComp'` inverse boundary
through the common-owner middle shell after specializing to an arbitrary owner leg
`S : Over I.Y.left`. This isolates the exact owner-generic naturality rewrite that is still
missing. -/
private theorem chosen_local_common_owner_middle_owner_leg_normalized_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    {S : (Over I.Y.left)ᵒᵖ}
    (β :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj S) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    -- Input bridge bringing `β` from the `qI`-pullback world back through the source `mapComp'`
    -- boundary into the iterated composite world, and the canonical owner-coherence output bridge
    -- returning the target shell to the `qI`-pullback world (formerly defeq, now propositional).
    let bridgeIn :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
    let outBridge :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
    ((bridgeIn ≫
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom ≫
        outBridge).1.app S)
      β =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom).1.app S)
        β) := by
  intro qI bridgeIn outBridge
  let A₀ :=
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  let Bq₀ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  let M₀ :=
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)
  have hhead :
      bridgeIn ≫ M₀.inv.toNatTrans.app A₀ ≫ Bq₀.hom = 𝟙 _ := by
    dsimp [bridgeIn, A₀, Bq₀, M₀]
    change Bq₀.inv ≫ M₀.hom.toNatTrans.app A₀ ≫
        M₀.inv.toNatTrans.app A₀ ≫ Bq₀.hom = 𝟙 _
    calc
      Bq₀.inv ≫ M₀.hom.toNatTrans.app A₀ ≫ M₀.inv.toNatTrans.app A₀ ≫ Bq₀.hom
          = Bq₀.inv ≫ (M₀.hom.toNatTrans.app A₀ ≫ M₀.inv.toNatTrans.app A₀) ≫
              Bq₀.hom := by
            simp only [Category.assoc]
      _ = Bq₀.inv ≫ 𝟙 _ ≫ Bq₀.hom := by
            have hM : M₀.hom.toNatTrans.app A₀ ≫ M₀.inv.toNatTrans.app A₀ = 𝟙 _ :=
              Cat.Hom.hom_inv_id_toNatTrans_app M₀ A₀
            exact congrArg (fun f => Bq₀.inv ≫ f ≫ Bq₀.hom) hM
      _ = Bq₀.inv ≫ Bq₀.hom := by simp only [Category.id_comp]
      _ = 𝟙 _ := Bq₀.inv_hom_id
  let A :=
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
  let Bq :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
  let M :=
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)
  let target :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom
  let innerBridge :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv
  have htarget :=
    chosen_local_target_mapComp'_hom_eq_common_owner_target_iso_hom
      (𝒮 := 𝒮) hGerbe hAbelian qI (K := K) I.Y.hom (by simp [qI])
  have hmid : target ≫ innerBridge = Bq.inv ≫ M.hom.toNatTrans.app A := by
    have h := congrArg (fun f => Bq.inv ≫ f) htarget
    simpa [target, innerBridge, Bq, M, A, Category.assoc] using h.symm
  have htail : target ≫ outBridge = 𝟙 _ := by
    dsimp [outBridge, innerBridge, target, Bq, M, A] at hmid ⊢
    calc
      target ≫ innerBridge ≫ M.inv.toNatTrans.app A ≫ Bq.hom
          = (Bq.inv ≫ M.hom.toNatTrans.app A) ≫
              M.inv.toNatTrans.app A ≫ Bq.hom := by
            simpa [Category.assoc] using
              congrArg (fun f => f ≫ M.inv.toNatTrans.app A ≫ Bq.hom) hmid
      _ = Bq.inv ≫ (M.hom.toNatTrans.app A ≫ M.inv.toNatTrans.app A) ≫ Bq.hom := by
            simp only [Category.assoc]
      _ = Bq.inv ≫ 𝟙 _ ≫ Bq.hom := by
            have hM : M.hom.toNatTrans.app A ≫ M.inv.toNatTrans.app A = 𝟙 _ :=
              Cat.Hom.hom_inv_id_toNatTrans_app M A
            exact congrArg (fun f => Bq.inv ≫ f ≫ Bq.hom) hM
      _ = Bq.inv ≫ Bq.hom := by simp only [Category.id_comp]
      _ = 𝟙 _ := Bq.inv_hom_id
  let common :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom
  change ((common ≫ target ≫ outBridge).1.app S)
      (((bridgeIn ≫ M₀.inv.toNatTrans.app A₀ ≫ Bq₀.hom).1.app S) β) =
    (common.1.app S) β
  have hhead_app :=
    congrFun (congrArg (fun m => m.1.app S) hhead) β
  have hhead_app' :
      ((bridgeIn ≫ M₀.inv.toNatTrans.app A₀ ≫ Bq₀.hom).1.app S) β = β := by
    simpa using hhead_app
  rw [hhead_app']
  have htail_common : common ≫ target ≫ outBridge = common := by
    simpa [Category.assoc] using congrArg (fun f => common ≫ f) htail
  exact congrFun (congrArg (fun m => m.1.app S) htail_common) β

/-- Helper for Lemma 8.11.8: before evaluating on the literal owner
`op (Over.mk (𝟙 I.Y.left))`, commute the remaining raw source-side `mapComp'` inverse boundary
through the common-owner middle shell as a sheaf-morphism equality. -/
private theorem chosen_local_common_owner_middle_raw_boundary_transport
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    -- The source `mapComp'` boundary commutes through the common-owner middle shell to become the
    -- target `mapComp'` boundary, as a sheaf-morphism equality `AS(qI^* objL) ⟶ AS(qI^* Lx)`,
    -- with the canonical base-change bridges (`bridgeIn`/`outBridge`/`innerBridge`) supplying the
    -- coherences the Mathlib refactor turned propositional.
    let bridgeIn :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
    let innerBridge :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv
    let outBridge :=
      innerBridge ≫
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
    (bridgeIn ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
          (by simp [qI])).hom).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_target_iso
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
          (by simp [qI])).hom).hom ≫
      outBridge) =
      ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom ≫
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom ≫
      innerBridge ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom) := by
  intro qI bridgeIn innerBridge outBridge
  let A :=
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  let B :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
  let M :=
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)
  let REST :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
          (by simp [qI])).hom).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_target_iso
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
          (by simp [qI])).hom).hom ≫
      innerBridge ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
  change B.inv ≫ M.hom.toNatTrans.app A ≫ M.inv.toNatTrans.app A ≫ B.hom ≫ REST = REST
  calc
    B.inv ≫ M.hom.toNatTrans.app A ≫ M.inv.toNatTrans.app A ≫ B.hom ≫ REST
        = B.inv ≫ (M.hom.toNatTrans.app A ≫ M.inv.toNatTrans.app A) ≫ B.hom ≫ REST := by
          simp only [Category.assoc]
    _ = B.inv ≫ 𝟙 _ ≫ B.hom ≫ REST := by
          have hM : M.hom.toNatTrans.app A ≫ M.inv.toNatTrans.app A = 𝟙 _ :=
            Cat.Hom.hom_inv_id_toNatTrans_app M A
          exact congrArg (fun f => B.inv ≫ f ≫ B.hom ≫ REST) hM
    _ = B.inv ≫ B.hom ≫ REST := by simp only [Category.id_comp]
    _ = REST := by simpa [Category.assoc] using (Iso.inv_hom_id_assoc B REST)

/-- Helper for Lemma 8.11.8: before evaluating on the literal owner
`op (Over.mk (𝟙 I.Y.left))`, commute the remaining raw source-side `mapComp'` inverse boundary
through the common-owner middle shell as a sheaf-morphism equality. -/
private theorem chosen_local_common_owner_middle_raw_boundary_component_transport
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    {S : (Over I.Y.left)ᵒᵖ}
    (β :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        ((I.Y.hom ≫ K.f) ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj S) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    -- The source `mapComp'` boundary commutes through the common-owner middle shell to become the
    -- target `mapComp'` boundary, both expressed as sheaf morphisms `AS(qI^* objL) ⟶ AS(qI^* Lx)`
    -- via the canonical base-change bridges (`bridgeIn` pulls `β` back through the source boundary,
    -- `outBridge`/`innerBridge` are the owner-coherence isos formerly absorbed by defeq).
    let bridgeIn :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
    let innerBridge :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv
    let outBridge :=
      innerBridge ≫
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom
    ((bridgeIn ≫
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
            (by simp [qI])).hom).hom ≫
        outBridge).1.app S)
      β =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_target_iso
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom ≫
          innerBridge ≫
          ((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom).1.app S)
        β) := by
  intro qI bridgeIn innerBridge outBridge
  exact congrFun
    (congrArg (fun m => m.1.app S)
      (chosen_local_common_owner_middle_raw_boundary_transport
        (𝒮 := 𝒮) hGerbe hAbelian L K I))
    β

/-- Helper for Lemma 8.11.8: evaluating the previous sheaf-morphism transport on the literal
owner `op (Over.mk (𝟙 I.Y.left))` gives the exact middle rewrite needed in the app-level boundary
cancelation proof. -/
private theorem chosen_local_common_owner_middle_raw_boundary_transport_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let O : (Over I.Y.left)ᵒᵖ := op (Over.mk (𝟙 I.Y.left))
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    -- canonical owner-cast bridge: `αI` (living over `op I.Y`) viewed in the iterated
    -- `K.f`-then-`I.Y.hom` pullback world over the literal owner `O`.
    let bridgeOwner :=
      (congrArg
          (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj
          (over_map_obj_mk_eq_op I.Y.hom (𝟙 I.Y.left) I.Y.hom (by simp))).mpr αI
    -- the same datum bridged into the common-owner conjugation world `autoSheaf (qI ^* coverObj)`.
    let test2 :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom.1.app O
        ((((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.app O bridgeOwner)
    (((((J.pseudofunctorOver (Type (max u v))).mapComp'
                K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)) ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_target_iso
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom ≫
            (((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
                  (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
                    (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≪≫
                automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
                  (K.f ^*[canonicalPullbackChoice 𝒮.p]
                    (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).inv ≫
            ((J.pseudofunctorOver (Type (max u v))).mapComp'
                K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≫
            ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app O)
        bridgeOwner) =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_target_iso
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom ≫
            (((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
                  (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
                    (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≪≫
                automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
                  (K.f ^*[canonicalPullbackChoice 𝒮.p]
                    (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).inv ≫
            ((J.pseudofunctorOver (Type (max u v))).mapComp'
                K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≫
            ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app O)
        test2) := by
  intro qI O αI pulledφ bridgeOwner test2
  rfl

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
private theorem chosen_local_source_common_owner_boundary_cancel_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let O : (Over I.Y.left)ᵒᵖ := op (Over.mk (𝟙 I.Y.left))
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    let bridgeOwner :=
      (congrArg
          (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj
          (over_map_obj_mk_eq_op I.Y.hom (𝟙 I.Y.left) I.Y.hom (by simp))).mpr αI
    let test2 :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom.1.app O
        ((((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.app O bridgeOwner)
    -- `αI` bridged into the iterated source-owner world `autoSheaf (I.Y.hom ^* (K.f ^* coverObj))`.
    let B1g :=
      ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) ≪≫
          automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)))
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_source_iso
                (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_target_iso
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom ≫
            (((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
                  (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
                    (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≪≫
                automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
                  (K.f ^*[canonicalPullbackChoice 𝒮.p]
                    (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).inv ≫
            ((J.pseudofunctorOver (Type (max u v))).mapComp'
                K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≫
            ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom) ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom).1.app O)
        (B1g.hom.1.app O bridgeOwner)) =
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom ≫
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app O)
          test2) := by
    intro qI O αI pulledφ bridgeOwner test2 B1g
    let source :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_source_iso
          (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv).hom
    let common :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
          (by simp [qI])).hom).hom
    let target :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_target_iso
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
          (by simp [qI])).hom).hom
    let targetBridge :=
      (((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≪≫
          automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)))
    let mapCompX :=
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
    let qPhi :=
      ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)
    let tail := common ≫ target ≫ targetBridge.inv ≫ mapCompX ≫ qPhi
    let bcY :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)
    have hcancel :
        B1g.inv.1.app O (B1g.hom.1.app O bridgeOwner) = bridgeOwner :=
      sheaf_iso_hom_inv_app14 B1g O bridgeOwner
    let flankMap :=
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫
        tail)
    have hflankRaw :
        ((source ≫ tail).1.app O) (B1g.hom.1.app O bridgeOwner) =
          (flankMap.1.app O)
            (B1g.inv.1.app O (B1g.hom.1.app O bridgeOwner)) := by
      have h :=
        (chosen_local_source_common_owner_left_flank_mapComp_app
          (𝒮 := 𝒮) hGerbe hAbelian φ L K T I)
          (B1g.hom.1.app O bridgeOwner)
      simpa [source, common, target, tail, flankMap, targetBridge, mapCompX, qPhi, B1g, qI, O,
        pulledφ] using h
    have hflank :
        ((source ≫ tail).1.app O) (B1g.hom.1.app O bridgeOwner) =
          (flankMap.1.app O) bridgeOwner := by
      exact hflankRaw.trans (congrArg (flankMap.1.app O) hcancel)
    have hmiddle :
        (flankMap.1.app O) bridgeOwner =
          (tail.1.app O) test2 := by
      simpa [common, target, tail, flankMap, targetBridge, mapCompX, qPhi, qI, O, pulledφ] using
        (chosen_local_common_owner_middle_raw_boundary_transport_app
          (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I)
    have htail :
        bcY.hom.1.app O ((tail.1.app O) test2) =
          (((common ≫
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app O)
            test2) := by
      simpa [common, target, tail, targetBridge, mapCompX, qPhi, bcY, qI, O, pulledφ] using
        (chosen_local_source_common_owner_pulled_phi_tail_app
          (𝒮 := 𝒮) hGerbe hAbelian φ L K T I test2)
    change bcY.hom.1.app O
        (((source ≫ tail).1.app O) (B1g.hom.1.app O bridgeOwner)) =
      (((common ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app O)
        test2)
    rw [hflank, hmiddle]
    exact htail

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
private theorem chosen_local_source_common_owner_middle_with_pulled_phi_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (_hĪ : HEq Ī.f I.f.left) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let O : (Over I.Y.left)ᵒᵖ := op (Over.mk (𝟙 I.Y.left))
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    let bridgeOwner :=
      (congrArg
          (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj
          (over_map_obj_mk_eq_op I.Y.hom (𝟙 I.Y.left) I.Y.hom (by simp))).mpr αI
    let test2 :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom.1.app O
        ((((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.app O bridgeOwner)
    -- `αI` bridged into the `I.Y.hom`-pulled chosen-local source world over `O`.
    let innerArg :=
      (((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).hom.1.app O bridgeOwner
    -- the inner `I.Y.hom`-pulled chosen-local comparison applied to that datum.
    let inner :=
      (((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app O innerArg
    -- transport `inner` back to the `qI`-pullback world and then to `pf.map L.f` over `op (Over.mk qI)`.
    let innerQ :=
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).1.app O
        ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).inv.1.app O inner)
    let innerQcast : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj (op (Over.mk qI)) :=
      Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj
          (over_map_obj_mk_eq_op qI (𝟙 I.Y.left) qI (by simp))) innerQ
    let innerLf :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv.1.app
        (op (Over.mk qI)) innerQcast
    -- apply the pulled `φ`-conjugation over the literal owner `op (Over.mk qI)`, then bridge the
    -- output back into the common-owner conjugation world `autoSheaf (qI ^* (L.f ^* y))` over `O`.
    let outerLfy :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f y).hom.1.app
        (op (Over.mk qI))
        ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1.app
          (op (Over.mk qI)) innerLf)
    let outerLfyCast :
        (((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.obj O :=
      (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).1.obj
          (over_map_obj_mk_eq_op qI (𝟙 I.Y.left) qI (by simp))).mpr outerLfy
    ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.1.app O outerLfyCast) =
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app O)
          test2) := by
  intro qI O αI pulledφ bridgeOwner test2 innerArg inner innerQ innerQcast innerLf
    outerLfy outerLfyCast
  let source :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv).hom
  let common :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom
  let target :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom
  let srcIter :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
  let tgtIter :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
  let srcK :=
    ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
  let tgtK :=
    ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
  let B1g := srcK ≪≫ srcIter
  let targetBridge := tgtK ≪≫ tgtIter
  let mapCompX :=
    ((J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
  let qPhi :=
    ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
      ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)
  let bcY :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)
  have hinner :
      inner =
        tgtIter.inv.1.app O
          (((source ≫ common ≫ target).1.app O)
            (srcIter.hom.1.app O innerArg)) := by
    have h := congrFun
      (congrArg (fun m => m.1.app O)
        (chosen_local_pulled_conjugation_eq_common_owner_middle
          (𝒮 := 𝒮) hGerbe hAbelian
          (q := qI) (K := K) (g := I.Y.hom) (by simp [qI])))
      innerArg
    simpa [inner, source, common, target, srcIter, tgtIter, qI, Category.assoc] using h
  have hB1g :
      B1g.hom.1.app O bridgeOwner = srcIter.hom.1.app O innerArg := by
    dsimp [B1g, srcK, innerArg]
    rfl
  have hinnerQ :
      innerQ =
        mapCompX.1.app O
          (targetBridge.inv.1.app O
            (((source ≫ common ≫ target).1.app O)
              (srcIter.hom.1.app O innerArg))) := by
    dsimp [innerQ, mapCompX, targetBridge, B1g, tgtK, srcK, innerArg]
    rw [hinner]
    rfl
  have houter :
      outerLfyCast = qPhi.1.app O innerQ := by
    have hmap :=
      automorphismUnderlyingSheafConj_outer_app_eq_pulled_app14
        (𝒮 := 𝒮) hAbelian L.f qI φ innerLf
    have hx :
        ((congrArg
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj
            (over_map_obj_mk_eq_op qI (𝟙 I.Y.left) qI (by simp))).mpr
          ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).hom.1.app
            (op (Over.mk qI)) innerLf)) = innerQ := by
      let Fx :=
        automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
      let ex := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x
      let hq := over_map_obj_mk_eq_op qI (𝟙 I.Y.left) qI (by simp)
      change (congrArg Fx.1.obj hq).mpr
          (ex.hom.1.app (op (Over.mk qI))
            (ex.inv.1.app (op (Over.mk qI))
              (Eq.mp (congrArg Fx.1.obj hq) innerQ))) = innerQ
      rw [sheaf_iso_inv_hom_app14 ex (op (Over.mk qI))
        (Eq.mp (congrArg Fx.1.obj hq) innerQ)]
      exact obj_cast_mpr_mp14 Fx.1 hq innerQ
    dsimp [outerLfyCast, outerLfy]
    rw [← pf_map_app_eq_image_app_obj14 L.f
      ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom) (Over.mk qI)]
    rw [hmap]
    rw [sheaf_iso_inv_hom_app14
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f y)
      (op (Over.mk qI))]
    rw [hx]
    let Gy :=
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)
    let hq := over_map_obj_mk_eq_op qI (𝟙 I.Y.left) qI (by simp)
    change (congrArg Gy.1.obj hq).mpr
        (Eq.mp (congrArg Gy.1.obj hq) (qPhi.1.app O innerQ)) =
      qPhi.1.app O innerQ
    exact obj_cast_mpr_mp14 Gy.1 hq (qPhi.1.app O innerQ)
  have hboundary :=
    chosen_local_source_common_owner_boundary_cancel_app
      (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I
  calc
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.1.app O outerLfyCast
        = bcY.hom.1.app O (qPhi.1.app O innerQ) := by
          rw [houter]
    _ = bcY.hom.1.app O
          (qPhi.1.app O
            (mapCompX.1.app O
              (targetBridge.inv.1.app O
                (((source ≫ common ≫ target).1.app O)
                  (srcIter.hom.1.app O innerArg))))) := by
          rw [hinnerQ]
    _ = bcY.hom.1.app O
          (qPhi.1.app O
            (mapCompX.1.app O
              (targetBridge.inv.1.app O
                (((source ≫ common ≫ target).1.app O)
                  (B1g.hom.1.app O bridgeOwner))))) := by
          rw [hB1g]
    _ =
        (((common ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app O)
          test2) := by
          simpa [source, common, target, B1g, targetBridge, mapCompX, qPhi, bcY, qI, O,
            αI, pulledφ, bridgeOwner, test2, Category.assoc] using hboundary

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
private theorem chosen_local_source_refinement_member_qI_shell_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (_hĪ : HEq Ī.f I.f.left) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let O : (Over I.Y.left)ᵒᵖ := op (Over.mk (𝟙 I.Y.left))
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    let bridgeOwner :=
      (congrArg
          (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj
          (over_map_obj_mk_eq_op I.Y.hom (𝟙 I.Y.left) I.Y.hom (by simp))).mpr αI
    let test2 :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom.1.app O
        ((((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.app O bridgeOwner)
    -- forced base-change bridges so the chosen-local comparison composes after the refactor.
    let bIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
    let cIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f y)
    -- the source datum normalized into the chosen-local source world over `T`.
    let inner4 :=
      ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom ≫
          bIso.inv ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)) ≫
          cIso.hom).1.app T
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom.1.app T α)
    let outer4 :=
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op inner4
    let outer4cast :
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.obj
          (op ((Over.map I.Y.hom).obj (Over.mk (𝟙 I.Y.left)))) :=
      (congrArg
          (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.obj
          (over_map_obj_mk_eq_op I.Y.hom (𝟙 I.Y.left) I.Y.hom (by simp))).mpr outer4
    ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.1.app O
        ((((J.pseudofunctorOver (Type (max u v))).mapComp'
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.app O outer4cast)) =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app O)
        test2) := by
  intro qI O αI pulledφ bridgeOwner test2 bIso cIso inner4 outer4 outer4cast
  let innerArg :=
    (((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).hom.1.app O bridgeOwner
  let inner :=
    (((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app O innerArg
  let innerQ :=
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).1.app O
      ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).inv.1.app O inner)
  let innerQcast : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj (op (Over.mk qI)) :=
    Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj
        (over_map_obj_mk_eq_op qI (𝟙 I.Y.left) qI (by simp))) innerQ
  let innerLf :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv.1.app
      (op (Over.mk qI)) innerQcast
  let outerLfy :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f y).hom.1.app
      (op (Over.mk qI))
      ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1.app
        (op (Over.mk qI)) innerLf)
  let outerLfyCast :
      (((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.obj O :=
    (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).1.obj
        (over_map_obj_mk_eq_op qI (𝟙 I.Y.left) qI (by simp))).mpr outerLfy
  let mapCompY :=
    ((J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y))
  let bcY :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)
  have hsurface :
      mapCompY.1.app O outer4cast = outerLfyCast := by
    let rawOwner : (Over K.Y)ᵒᵖ :=
      op ((Over.map I.Y.hom).obj (Over.mk (𝟙 I.Y.left)))
    let coverA :=
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
    let xA :=
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
    let yA :=
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)
    let FKcover :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj coverA
    let FKy :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj yA
    let inBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
    let localConj :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom
    let tailM :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f y).hom
    let sourceMorph :=
      inBridge.hom ≫ localConj ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map tailM
    let mapCompX :=
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app xA
    let tailPre :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv.1.app rawOwner
        (localConj.1.app rawOwner (inBridge.hom.1.app rawOwner bridgeOwner))
    let hOwner := over_map_obj_mk_eq_op I.Y.hom (𝟙 I.Y.left) I.Y.hom (by simp)
    have houter_at_owner :
        outer4 = sourceMorph.1.app (op I.Y) αI := by
      have hnat :=
        (FunctorToTypes.naturality _ _ sourceMorph.1 I.f.op α).symm
      simpa [sourceMorph, tailM, inBridge, localConj, outer4, inner4, αI, bIso, cIso,
        Category.assoc, Functor.map_comp] using hnat
    have houter4cast :
        outer4cast = sourceMorph.1.app rawOwner bridgeOwner := by
      have hcast := app_obj_cast14' sourceMorph.1 hOwner αI
      dsimp [outer4cast, bridgeOwner, rawOwner, FKcover, FKy, coverA, yA]
      rw [houter_at_owner]
      simpa [rawOwner, FKcover] using hcast.symm
    have htail_naturality :
        mapCompY.1.app O
            ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
              (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                tailM)).1.app O tailPre) =
          (((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
              tailM).1.app O (mapCompX.1.app O tailPre) := by
      have h :=
        congrFun
          (congrArg (fun m => m.1.app O)
            ((J.pseudofunctorOver (Type (max u v))).mapComp'_inv_naturality
              K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch) tailM))
          tailPre
      simpa [mapCompX, mapCompY] using h
    have hinnerQ_tail :
        mapCompX.1.app O tailPre = innerQ := by
      dsimp [mapCompX, tailPre, innerQ, inner, innerArg, inBridge, localConj, rawOwner,
        bridgeOwner, αI, O, qI]
    have htail_to_outer :
        ((((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
            tailM).1.app O innerQ) = outerLfyCast := by
      let hq := over_map_obj_mk_eq_op qI (𝟙 I.Y.left) qI (by simp)
      have hcast := app_obj_cast14 tailM.1 hq innerQ
      simpa [tailM, outerLfyCast, outerLfy, innerLf, innerQcast, O, qI] using hcast
    have hsource_eval :
        sourceMorph.1.app rawOwner bridgeOwner =
          ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              tailM)).1.app O tailPre) := by
      dsimp [sourceMorph, tailPre, tailM, inBridge, localConj, rawOwner,
        Category.assoc, Functor.map_comp]
      rfl
    rw [houter4cast, hsource_eval, htail_naturality, hinnerQ_tail]
    exact htail_to_outer
  have hsource :
      bcY.hom.1.app O outerLfyCast =
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                  (by simp [qI])).hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app O)
          test2) := by
    simpa [innerArg, inner, innerQ, innerQcast, innerLf, outerLfy, outerLfyCast, qI, O,
      αI, pulledφ, bridgeOwner, test2] using
      (chosen_local_source_common_owner_middle_with_pulled_phi_app
        (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I Ī _hĪ)
  change bcY.hom.1.app O (mapCompY.1.app O outer4cast) =
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app O)
      test2)
  rw [hsurface]
  exact hsource

/-- Transport-stable owner bridge for a direct base-change arrow whose base map is equal to a
composite owner.  This packages the `mapComp'` owner cast before the equal-arrow `eqToIso` cast is
introduced, so consumers can cancel the resulting isomorphism without dependent rewrites. -/
private theorem automorphismUnderlyingSheafBaseChangeIso_hom_owner_transport14
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} (x : 𝒮.p.Fiber U) (f : Y ⟶ U) (g : Z ⟶ Y) (l : Z ⟶ U)
    (hl : (𝟙 Z) ≫ l = g ≫ f) (hlq : l = g ≫ f)
    (α : ((((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).1.obj
        (op (Over.mk g)))) :
    let q : Z ⟶ U := g ≫ f
    let O : (Over Z)ᵒᵖ := op (Over.mk (𝟙 Z))
    let hOwner : op ((Over.map g).obj (Over.mk (𝟙 Z))) = op (Over.mk g) :=
      over_map_obj_mk_eq_op g (𝟙 Z) g (by simp)
    let owner_obj_eq :
        op ((Over.map l).obj (Over.mk (𝟙 Z))) =
          op ((Over.map f).obj (Over.mk g)) :=
      (over_map_obj_mk_eq_op l (𝟙 Z) q hl).trans
        (congrArg op (over_map_obj_mk_eq f g q rfl).symm)
    let directBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian l x ≪≫
        eqToIso (congrArg (fun m : Z ⟶ U =>
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (m ^*[canonicalPullbackChoice 𝒮.p] x)) hlq)
    let bridgeOwner :=
      (congrArg
          (((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc).toFunctor.obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).1.obj
          hOwner).mpr α
    directBridge.hom.1.app O
        ((congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj
          owner_obj_eq).mpr α) =
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).hom.1.app O
        ((((J.pseudofunctorOver (Type (max u v))).mapComp'
            f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).1.app O bridgeOwner) := by
  cases hlq
  have hhl : hl = (by simp : (𝟙 Z) ≫ (g ≫ f) = g ≫ f) := Subsingleton.elim _ _
  cases hhl
  intro q O hOwner owner_obj_eq directBridge bridgeOwner
  let A := automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x
  let M :=
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc (by cat_disch)
  have hM :
      HEq
        (((M.inv.toNatTrans.app A).1.app O) bridgeOwner)
        bridgeOwner := by
    simpa [M, A, O, bridgeOwner] using
      (GrothendieckTopology.pf_mapComp'_inv_component_apply_heq
        (J := J) (f := f.op.toLoc) (g' := g.op.toLoc)
        (k := (g ≫ f).op.toLoc) (hk := by cat_disch) A O bridgeOwner)
  have harg :
      (((M.inv.toNatTrans.app A).1.app O) bridgeOwner) =
        (congrArg A.1.obj owner_obj_eq).mpr α := by
    apply eq_of_heq
    simp only [eq_mpr_eq_cast]
    exact hM.trans ((cast_heq _ _).trans (cast_heq _ _).symm)
  simpa [A, M, directBridge] using
    (congrArg
      ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (g ≫ f) x).hom.1.app O)
      harg.symm)

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
two candidate sections from `chosen_local_automorphism_iso_pulled_conj_component_app` are both
rewritten to the same common-owner conjugation over `qI := I.Y.hom ≫ K.f`. -/
private theorem chosen_local_automorphism_iso_pulled_conj_refinement_member_eq
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (hR : (R : Sieve T.unop) = (Sieve.overEquiv T.unop).symm (B : Sieve T.unop.left))
    (I : R.Arrow)
    (hImem : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)) (I.f.left ≫ (T.unop.hom ≫ K.f)))
    (Ī : B.Arrow) (hĪ : HEq Ī.f I.f.left) :
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
        ((((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
            ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv ≫
                ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
                  ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom) ≫
                (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f y).hom)).1.app T) α)) =
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
          ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app T) α))) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let O : (Over I.Y.left)ᵒᵖ := op (Over.mk (𝟙 I.Y.left))
  let αI :=
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
  let pulledφ :
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
  let bridgeOwner :=
    (congrArg
        (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj
        (over_map_obj_mk_eq_op I.Y.hom (𝟙 I.Y.left) I.Y.hom (by simp))).mpr αI
  let test2 :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom.1.app O
      ((((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.app O bridgeOwner)
  let FK :=
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y))
  let hOwner := over_map_obj_mk_eq_op I.Y.hom (𝟙 I.Y.left) I.Y.hom (by simp)
  let mapCompY :=
    ((J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y))
  let bcY :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)
  let transport (s : FK.1.obj (op I.Y)) :=
    bcY.hom.1.app O (mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr s))
  let lhs :=
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
        ((((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
            ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv ≫
                ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
                  ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom) ≫
                (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f y).hom)).1.app T) α))
  let rhs :=
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app T) α)))
  let commonShell :=
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom).1.app O)
      test2)
  have hsource : transport lhs = commonShell := by
    simpa [transport, lhs, commonShell, qI, O, αI, pulledφ, bridgeOwner, test2,
      Category.assoc, Functor.map_comp] using
      (chosen_local_source_refinement_member_qI_shell_app
        (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I Ī hĪ)
  have htarget : transport rhs = commonShell := by
    let coverA :=
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
    let targetA :=
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)
    let Īy : ((chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).pullback (T.unop.hom ≫ K.f)).Arrow :=
      ⟨I.Y.left, I.f.left, hImem⟩
    let Ky :
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
      Īy.base
    let hKy : (𝟙 I.Y.left) ≫ Ky.f = qI :=
      chosen_local_target_refinement_member_identity_leg_eq
        (𝒮 := 𝒮) hGerbe L K T I hImem
    let owner_obj_eq :
        op ((Over.map Ky.f).obj (Over.mk (𝟙 I.Y.left))) =
          op ((Over.map K.f).obj I.Y) :=
      (over_map_obj_mk_eq_op Ky.f (𝟙 I.Y.left) qI hKy).trans
        (congrArg op (over_map_obj_mk_eq K.f I.Y.hom qI rfl).symm)
    let hKf : Ky.f = qI :=
      (Category.id_comp Ky.f).symm.trans hKy
    let inBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Ky.f
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L) ≪≫
        eqToIso (congrArg (fun m : I.Y.left ⟶ L.Y =>
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (m ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) hKf)
    let outBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Ky.f
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) ≪≫
        eqToIso (congrArg (fun m : I.Y.left ⟶ L.Y =>
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (m ^*[canonicalPullbackChoice 𝒮.p]
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y))) hKf)
    let sKy :
        ((((J.pseudofunctorOver (Type (max u v))).map Ky.f.op.toLoc).toFunctor.obj
          coverA).1.obj O) :=
      inBridge.inv.1.app O test2
    let kyBranch :=
      (((((J.pseudofunctorOver (Type (max u v))).map Ky.f.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app O) sKy)
    let targetShell :=
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := Ky) (g := 𝟙 I.Y.left) hKy).hom).hom).1.app O)
        test2)
    have hcommon_target : commonShell = targetShell := by
      simpa [commonShell, targetShell, qI, O, pulledφ] using
        (chosen_local_cross_cover_common_owner_conjugation_hom_eq_app
          (𝒮 := 𝒮) hGerbe hAbelian pulledφ qI
          (Kx := K) (Ky := Ky) I.Y.hom (𝟙 I.Y.left)
          (by simp [qI]) hKy O test2)
    have htransport_ky :
        transport rhs = outBridge.hom.1.app O kyBranch := by
      have hrestrict :
          rhs =
            (((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                ((chosen_local_automorphism_iso
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                  (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app (op I.Y)) αI) := by
        simpa [rhs, αI] using
          (chosen_local_target_refinement_member_right_branch_restrict_eq
            (𝒮 := 𝒮) hGerbe hAbelian φ L K T α I hImem)
      have howner :
          kyBranch =
            (congrArg
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).1.obj
              owner_obj_eq).mpr
            (((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                ((chosen_local_automorphism_iso
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                  (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app
              (op I.Y))
            (Eq.mp
              (congrArg
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).1.obj
                owner_obj_eq) sKy)) := by
        simpa [kyBranch, Ky, Īy, O, owner_obj_eq] using
          (chosen_local_target_refinement_member_right_branch_common_owner_app
            (𝒮 := 𝒮) hGerbe hAbelian φ L K T I hImem sKy)
      have hinput :
          Eq.mp
              (congrArg
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).1.obj
                owner_obj_eq) sKy =
            αI := by
        let coverA :=
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        have hpre :
            inBridge.hom.1.app O
              ((congrArg coverA.1.obj owner_obj_eq).mpr αI) = test2 := by
          simpa [coverA, inBridge, test2, bridgeOwner, owner_obj_eq, qI, O] using
            (automorphismUnderlyingSheafBaseChangeIso_hom_owner_transport14
              (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              K.f I.Y.hom Ky.f hKy hKf αI)
        have hs :
            sKy = (congrArg coverA.1.obj owner_obj_eq).mpr αI := by
          calc
            sKy = inBridge.inv.1.app O test2 := rfl
            _ = inBridge.inv.1.app O
                (inBridge.hom.1.app O
                  ((congrArg coverA.1.obj owner_obj_eq).mpr αI)) := by
                  rw [hpre]
            _ = (congrArg coverA.1.obj owner_obj_eq).mpr αI := by
                  exact sheaf_iso_hom_inv_app14 inBridge O
                    ((congrArg coverA.1.obj owner_obj_eq).mpr αI)
        rw [hs]
        exact obj_cast_mp_mpr14 coverA.1 owner_obj_eq αI
      let targetA :=
        automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)
      have hky_cast :
          kyBranch = (congrArg targetA.1.obj owner_obj_eq).mpr rhs := by
        have hbranch :
            (((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                ((chosen_local_automorphism_iso
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                  (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app
              (op I.Y))
            (Eq.mp
              (congrArg
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).1.obj
                owner_obj_eq) sKy)) = rhs := by
          rw [hrestrict]
          rw [← hinput]
          rfl
        rw [howner]
        exact congrArg ((congrArg targetA.1.obj owner_obj_eq).mpr) hbranch
      have hpre_target :
          outBridge.hom.1.app O
              ((congrArg targetA.1.obj owner_obj_eq).mpr rhs) =
            transport rhs := by
        simpa [targetA, outBridge, transport, mapCompY, bcY, FK, hOwner, owner_obj_eq,
          qI, O] using
          (automorphismUnderlyingSheafBaseChangeIso_hom_owner_transport14
            (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y)
            K.f I.Y.hom Ky.f hKy hKf rhs)
      rw [hky_cast]
      exact hpre_target.symm
    have hky_target : outBridge.hom.1.app O kyBranch = targetShell := by
      have himage :
          kyBranch =
            (((chosen_local_automorphism_descent_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.hom Ky).1.app O)
              sKy := by
        simpa [kyBranch, Ky, Īy, O] using
          (chosen_local_target_refinement_member_right_branch_image_app
            (𝒮 := 𝒮) hGerbe hAbelian φ L K T I hImem sKy)
      have hdescent :
          (((chosen_local_automorphism_descent_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.hom Ky).1.app O)
            sKy =
          outBridge.inv.1.app O
            (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := Ky) (g := 𝟙 I.Y.left)
                  hKy).hom).hom).1.app O
              (inBridge.hom.1.app O sKy)) := by
        simpa [Ky, Īy, qI, O, hKf, inBridge, outBridge] using
          (chosen_local_target_refinement_member_descent_component_qI_shell_app
            (𝒮 := 𝒮) hGerbe hAbelian φ L K T I hImem sKy)
      have hin : inBridge.hom.1.app O sKy = test2 := by
        simpa [sKy] using sheaf_iso_inv_hom_app14 inBridge O test2
      calc
        outBridge.hom.1.app O kyBranch =
            outBridge.hom.1.app O
              ((((chosen_local_automorphism_descent_iso
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                  (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.hom Ky).1.app O)
                sKy) := by
              rw [himage]
        _ = outBridge.hom.1.app O
              (outBridge.inv.1.app O
                (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                    (chosen_local_common_owner_isomorphism
                      (𝒮 := 𝒮) hGerbe qI (K := Ky) (g := 𝟙 I.Y.left)
                      hKy).hom).hom).1.app O
                  (inBridge.hom.1.app O sKy))) := by
              rw [hdescent]
        _ =
            (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (chosen_local_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe qI (K := Ky) (g := 𝟙 I.Y.left)
                  hKy).hom).hom).1.app O
              (inBridge.hom.1.app O sKy)) := by
              exact sheaf_iso_inv_hom_app14 outBridge O
                (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                    (chosen_local_common_owner_isomorphism
                      (𝒮 := 𝒮) hGerbe qI (K := Ky) (g := 𝟙 I.Y.left)
                      hKy).hom).hom).1.app O
                  (inBridge.hom.1.app O sKy))
        _ = targetShell := by
              rw [hin]
    exact htransport_ky.trans (hky_target.trans hcommon_target.symm)
  have htransport : transport lhs = transport rhs := hsource.trans htarget.symm
  have hmap :
      mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr lhs) =
        mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr rhs) := by
    have h := congrArg (bcY.inv.1.app O) htransport
    dsimp [transport] at h
    have hmid :
        bcY.inv.1.app O
            (bcY.hom.1.app O
              (mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr lhs))) =
          bcY.inv.1.app O
            (bcY.hom.1.app O
              (mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr rhs))) := by
      simpa [eq_mpr_eq_cast] using h
    have hleft :
        bcY.inv.1.app O
            (bcY.hom.1.app O
              (mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr lhs))) =
          mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr lhs) :=
      sheaf_iso_hom_inv_app14 bcY O
        (mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr lhs))
    have hright :
        bcY.inv.1.app O
            (bcY.hom.1.app O
              (mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr rhs))) =
          mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr rhs) :=
      sheaf_iso_hom_inv_app14 bcY O
        (mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr rhs))
    exact hleft.symm.trans (hmid.trans hright)
  let A :=
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)
  let M :=
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)
  have hcancel :
      mapCompY ≫ M.hom.toNatTrans.app A = 𝟙 _ := by
    simpa [mapCompY, M, A] using
      (Cat.Hom.inv_hom_id_toNatTrans_app M A)
  have hcast :
      (congrArg FK.1.obj hOwner).mpr lhs =
        (congrArg FK.1.obj hOwner).mpr rhs := by
    have hleft :
        (M.hom.toNatTrans.app A).1.app O
            (mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr lhs)) =
          (congrArg FK.1.obj hOwner).mpr lhs := by
      have h := congrFun (congrArg (fun m => m.1.app O) hcancel)
        ((congrArg FK.1.obj hOwner).mpr lhs)
      simpa using h
    have hright :
        (M.hom.toNatTrans.app A).1.app O
            (mapCompY.1.app O ((congrArg FK.1.obj hOwner).mpr rhs)) =
          (congrArg FK.1.obj hOwner).mpr rhs := by
      have h := congrFun (congrArg (fun m => m.1.app O) hcancel)
        ((congrArg FK.1.obj hOwner).mpr rhs)
      simpa using h
    exact hleft.symm.trans
      ((congrArg ((M.hom.toNatTrans.app A).1.app O) hmap).trans hright)
  have hmain : lhs = rhs :=
    obj_cast_mpr_injective14 FK.1 hOwner hcast
  simpa [lhs, rhs] using hmain

/-- Helper for Lemma 8.11.8: after transporting the pulled-conjugation comparison through the
chosen local cover descent equivalence for `(A, L.f ^* x)`, the remaining blocker is a
componentwise section equality on one fixed chosen-local cover arrow `K`. -/
private theorem chosen_local_automorphism_iso_pulled_conj_component_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow) :
    let Sx :=
      chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
    let lhs :=
      (chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv ≫
          ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom) ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f y).hom)
    let rhs :=
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom
    (((localizedSheafToCoverDescentEquivalence (J := J) Sx).functor.map lhs).hom K) =
      (((localizedSheafToCoverDescentEquivalence (J := J) Sx).functor.map rhs).hom K) := by
  dsimp only
  simp only [Functor.map_comp, Pseudofunctor.DescentData.comp_hom]
  rw [chosen_local_automorphism_iso_functor_map_eq_chosen_local_conjugation_component
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
    (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K]
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x))]
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x))]
  apply Sheaf.hom_ext
  ext T α
  let qT : T.unop.left ⟶ L.Y := T.unop.hom ≫ K.f
  let B : J.Cover T.unop.left :=
    (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).pullback qT
  let R : (J.over K.Y).Cover T.unop :=
    ⟨(Sieve.overEquiv T.unop).symm (B : Sieve T.unop.left),
      J.overEquiv_symm_mem_over T.unop (B : Sieve T.unop.left) B.condition⟩
  have hR : (R : Sieve T.unop) = (Sieve.overEquiv T.unop).symm
      (B : Sieve T.unop.left) := rfl
  exact sections_eq_of_cover_on_slice (J := J) _ T.unop R _ _ (fun I => by
    have hImemB : (B : Sieve T.unop.left) I.f.left := by
      have hIf : ((Sieve.overEquiv T.unop).symm (B : Sieve T.unop.left)) I.f := by
        simpa [hR] using I.hf
      exact (Sieve.overEquiv_symm_iff (B : Sieve T.unop.left) I.f).1 hIf
    have hImem : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)) (I.f.left ≫ qT) := by
      simpa [B, qT] using hImemB
    let Ī : B.Arrow := ⟨I.Y.left, I.f.left, hImemB⟩
    have hĪ : HEq Ī.f I.f.left := HEq.rfl
    simpa only [Category.assoc] using
      chosen_local_automorphism_iso_pulled_conj_refinement_member_eq
        (𝒮 := 𝒮) hGerbe hAbelian φ L K T α hR I hImem Ī hĪ)

/-- Helper for Lemma 8.11.8: on the slice `C / L.Y`, the chosen local comparison to `L.f ^* x`
followed by the pullback of conjugation by `φ` is the chosen local comparison to `L.f ^* y`.
This isolates the exact owner-level pulled-conjugation blocker exposed after the outer
identity-pullback shell is cancelled. -/
theorem chosen_local_automorphism_iso_pulled_conj
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (chosen_local_automorphism_iso
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
      ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f y).hom) =
    (chosen_local_automorphism_iso
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom := by
  haveI : (localizedSheafToCoverDescentEquivalence (J := J)
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).faithful
  apply Functor.map_injective
    (localizedSheafToCoverDescentEquivalence (J := J)
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  exact chosen_local_automorphism_iso_pulled_conj_component_app
    (𝒮 := 𝒮) hGerbe hAbelian φ L K

end

end CategoryTheory
