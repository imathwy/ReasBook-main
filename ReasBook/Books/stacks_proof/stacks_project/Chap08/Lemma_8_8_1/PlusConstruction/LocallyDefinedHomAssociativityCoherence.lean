import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomAssociativity

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace Pseudofunctor

variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX})

/-- Composing base arrows and passing to the locally-discrete opposite category gives the owner
equality used by `mapComp'`. -/
theorem locallyDiscreteOp_comp_toLoc_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Inverse comparison maps for three composable base arrows associate in the source-facing
owner convention.  This is the pure pseudofunctor coherence used by the stage-2 associativity
calculation before the local middle morphism. -/
theorem mapComp_inv_assoc_base
    {A B D E : C} (f : D ⟶ E) (g : B ⟶ D) (h : A ⟶ B)
    (X : F.obj (LocallyDiscrete.mk (op E))) :
    (F.map h.op.toLoc).toFunctor.map
        ((F.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc
          (locallyDiscreteOp_comp_toLoc_eq f g (g ≫ f) rfl)).inv.toNatTrans.app X) ≫
      (F.mapComp' (g ≫ f).op.toLoc h.op.toLoc (((h ≫ g) ≫ f).op.toLoc)
        (locallyDiscreteOp_comp_toLoc_eq (g ≫ f) h (((h ≫ g) ≫ f))
          (by simp [Category.assoc]))).inv.toNatTrans.app X =
    (F.mapComp' g.op.toLoc h.op.toLoc (h ≫ g).op.toLoc
        (locallyDiscreteOp_comp_toLoc_eq g h (h ≫ g) rfl)).inv.toNatTrans.app
        ((F.map f.op.toLoc).toFunctor.obj X) ≫
      (F.mapComp' f.op.toLoc (h ≫ g).op.toLoc (((h ≫ g) ≫ f).op.toLoc)
        (locallyDiscreteOp_comp_toLoc_eq f (h ≫ g) (((h ≫ g) ≫ f)) rfl)).inv.toNatTrans.app X := by
  simpa [Category.assoc] using
    (F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app
      f.op.toLoc g.op.toLoc h.op.toLoc (g ≫ f).op.toLoc (h ≫ g).op.toLoc
      (((h ≫ g) ≫ f).op.toLoc)
      (locallyDiscreteOp_comp_toLoc_eq f g (g ≫ f) rfl)
      (locallyDiscreteOp_comp_toLoc_eq g h (h ≫ g) rfl)
      (locallyDiscreteOp_comp_toLoc_eq (g ≫ f) h (((h ≫ g) ≫ f))
        (by simp [Category.assoc])) X)

/-- Hom comparison maps for three composable base arrows associate in the source-facing owner
convention.  This is the pure pseudofunctor coherence used by the stage-2 associativity
calculation after the local right morphism. -/
theorem mapComp_hom_assoc_base
    {A B D E : C} (f : D ⟶ E) (g : B ⟶ D) (h : A ⟶ B)
    (X : F.obj (LocallyDiscrete.mk (op E))) :
    ((F.mapComp' (g ≫ f).op.toLoc h.op.toLoc (((h ≫ g) ≫ f).op.toLoc)
        (locallyDiscreteOp_comp_toLoc_eq (g ≫ f) h (((h ≫ g) ≫ f))
          (by simp [Category.assoc]))).hom.toNatTrans.app X) ≫
      (F.map h.op.toLoc).toFunctor.map
        ((F.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc
          (locallyDiscreteOp_comp_toLoc_eq f g (g ≫ f) rfl)).hom.toNatTrans.app X) =
    (F.mapComp' f.op.toLoc (h ≫ g).op.toLoc (((h ≫ g) ≫ f).op.toLoc)
        (locallyDiscreteOp_comp_toLoc_eq f (h ≫ g) (((h ≫ g) ≫ f)) rfl)).hom.toNatTrans.app X ≫
      (F.mapComp' g.op.toLoc h.op.toLoc (h ≫ g).op.toLoc
        (locallyDiscreteOp_comp_toLoc_eq g h (h ≫ g) rfl)).hom.toNatTrans.app
        ((F.map f.op.toLoc).toFunctor.obj X) := by
  have hassoc :=
    (F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
      f.op.toLoc g.op.toLoc h.op.toLoc (g ≫ f).op.toLoc (h ≫ g).op.toLoc
      (((h ≫ g) ≫ f).op.toLoc)
      (locallyDiscreteOp_comp_toLoc_eq f g (g ≫ f) rfl)
      (locallyDiscreteOp_comp_toLoc_eq g h (h ≫ g) rfl)
      (locallyDiscreteOp_comp_toLoc_eq (g ≫ f) h (((h ≫ g) ≫ f))
        (by simp [Category.assoc])) X (𝟙 _))
  rw [Category.comp_id, Category.comp_id] at hassoc
  simpa [Category.assoc] using hassoc

set_option maxHeartbeats 800000 in
/-- Mixed hom/inv coherence for four composable locally-discrete arrows.  This is the pure
pseudofunctor calculation behind the second boundary in the stage-2 associativity proof: the
target comparison for the outer left bracketing is the two target comparisons for the right
bracketing. -/
theorem mapComp_target_assoc
    {b₀ b₁ b₂ b₃ b₄ : LocallyDiscrete Cᵒᵖ}
    (a : b₀ ⟶ b₁) (b : b₁ ⟶ b₂) (c : b₂ ⟶ b₃) (d : b₃ ⟶ b₄)
    (X : F.obj b₀) :
    ((F.mapComp' (b ≫ c) d ((b ≫ c) ≫ d) (by rfl)).hom.toNatTrans.app
        ((F.map a).toFunctor.obj X)) ≫
      (F.map d).toFunctor.map
        ((F.mapComp' a (b ≫ c) (((a ≫ b) ≫ c))
          (by simp [Category.assoc])).inv.toNatTrans.app X) =
    (((F.mapComp' b (c ≫ d) (((b ≫ c) ≫ d)) (by simp [Category.assoc])).hom.toNatTrans.app
        ((F.map a).toFunctor.obj X)) ≫
      (F.map (c ≫ d)).toFunctor.map
        ((F.mapComp' a b (a ≫ b) (by rfl)).inv.toNatTrans.app X)) ≫
      ((F.mapComp' c d (c ≫ d) (by rfl)).hom.toNatTrans.app
        ((F.map (a ≫ b)).toFunctor.obj X)) ≫
        (F.map d).toFunctor.map
          ((F.mapComp' (a ≫ b) c ((a ≫ b) ≫ c) (by rfl)).inv.toNatTrans.app X) := by
  have hnat :
      (F.map (c ≫ d)).toFunctor.map
          ((F.mapComp' a b (a ≫ b) (by rfl)).inv.toNatTrans.app X) ≫
        (F.mapComp' c d (c ≫ d) (by rfl)).hom.toNatTrans.app
          ((F.map (a ≫ b)).toFunctor.obj X) =
      (F.mapComp' c d (c ≫ d) (by rfl)).hom.toNatTrans.app
          ((F.map b).toFunctor.obj ((F.map a).toFunctor.obj X)) ≫
        (F.map d).toFunctor.map
          ((F.map c).toFunctor.map
            ((F.mapComp' a b (a ≫ b) (by rfl)).inv.toNatTrans.app X)) := by
    simpa [Cat.Hom.comp_toFunctor, Functor.comp_obj] using
      (F.mapComp'_hom_naturality c d (c ≫ d) (by rfl)
        ((F.mapComp' a b (a ≫ b) (by rfl)).inv.toNatTrans.app X))
  have hinv :
      (F.map c).toFunctor.map
          ((F.mapComp' a b (a ≫ b) (by rfl)).inv.toNatTrans.app X) ≫
        (F.mapComp' (a ≫ b) c ((a ≫ b) ≫ c) (by rfl)).inv.toNatTrans.app X =
      (F.mapComp' b c (b ≫ c) (by rfl)).inv.toNatTrans.app
          ((F.map a).toFunctor.obj X) ≫
        (F.mapComp' a (b ≫ c) (((a ≫ b) ≫ c))
          (by simp [Category.assoc])).inv.toNatTrans.app X := by
    simpa [Category.assoc] using
      (F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app
        a b c (a ≫ b) (b ≫ c) (((a ≫ b) ≫ c))
        (by rfl) (by rfl) (by simp [Category.assoc]) X)
  have hhom :
      ((F.mapComp' (b ≫ c) d ((b ≫ c) ≫ d) (by rfl)).hom.toNatTrans.app
          ((F.map a).toFunctor.obj X)) ≫
        (F.map d).toFunctor.map
          ((F.mapComp' b c (b ≫ c) (by rfl)).hom.toNatTrans.app
            ((F.map a).toFunctor.obj X)) =
      ((F.mapComp' b (c ≫ d) (((b ≫ c) ≫ d)) (by simp [Category.assoc])).hom.toNatTrans.app
          ((F.map a).toFunctor.obj X)) ≫
        (F.mapComp' c d (c ≫ d) (by rfl)).hom.toNatTrans.app
          ((F.map b).toFunctor.obj ((F.map a).toFunctor.obj X)) := by
    simpa [Category.assoc] using
      (F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
        b c d (b ≫ c) (c ≫ d) (((b ≫ c) ≫ d))
        (by rfl) (by rfl) (by simp [Category.assoc])
        ((F.map a).toFunctor.obj X) (𝟙 _))
  let Hbc := (F.mapComp' b c (b ≫ c) (by rfl)).hom.toNatTrans.app
    ((F.map a).toFunctor.obj X)
  let Ibc := (F.mapComp' b c (b ≫ c) (by rfl)).inv.toNatTrans.app
    ((F.map a).toFunctor.obj X)
  let Iabc := (F.mapComp' a (b ≫ c) (((a ≫ b) ≫ c))
    (by simp [Category.assoc])).inv.toNatTrans.app X
  have hcancel :
      (F.map d).toFunctor.map Hbc ≫ (F.map d).toFunctor.map Ibc = 𝟙 _ := by
    rw [← (F.map d).toFunctor.map_comp]
    rw [Cat.Hom.hom_inv_id_toNatTrans_app]
    simp
  calc
    ((F.mapComp' (b ≫ c) d ((b ≫ c) ≫ d) (by rfl)).hom.toNatTrans.app
        ((F.map a).toFunctor.obj X)) ≫
      (F.map d).toFunctor.map
        ((F.mapComp' a (b ≫ c) (((a ≫ b) ≫ c))
          (by simp [Category.assoc])).inv.toNatTrans.app X)
        =
      ((F.mapComp' (b ≫ c) d ((b ≫ c) ≫ d) (by rfl)).hom.toNatTrans.app
          ((F.map a).toFunctor.obj X)) ≫
        (F.map d).toFunctor.map
          (((F.mapComp' b c (b ≫ c) (by rfl)).hom.toNatTrans.app
              ((F.map a).toFunctor.obj X)) ≫
            ((F.mapComp' b c (b ≫ c) (by rfl)).inv.toNatTrans.app
              ((F.map a).toFunctor.obj X)) ≫
            (F.mapComp' a (b ≫ c) (((a ≫ b) ≫ c))
              (by simp [Category.assoc])).inv.toNatTrans.app X) := by
          simpa [Hbc, Ibc, Iabc, Category.assoc] using
            congrArg (fun t => ((F.mapComp' (b ≫ c) d ((b ≫ c) ≫ d)
              (by rfl)).hom.toNatTrans.app ((F.map a).toFunctor.obj X)) ≫ t ≫
              (F.map d).toFunctor.map Iabc) hcancel.symm
    _ =
      ((F.mapComp' (b ≫ c) d ((b ≫ c) ≫ d) (by rfl)).hom.toNatTrans.app
          ((F.map a).toFunctor.obj X)) ≫
        (F.map d).toFunctor.map
          ((F.mapComp' b c (b ≫ c) (by rfl)).hom.toNatTrans.app
            ((F.map a).toFunctor.obj X)) ≫
        (F.map d).toFunctor.map
          (((F.mapComp' b c (b ≫ c) (by rfl)).inv.toNatTrans.app
              ((F.map a).toFunctor.obj X)) ≫
            (F.mapComp' a (b ≫ c) (((a ≫ b) ≫ c))
              (by simp [Category.assoc])).inv.toNatTrans.app X) := by
          simp [Functor.map_comp]
    _ =
      ((F.mapComp' b (c ≫ d) (((b ≫ c) ≫ d)) (by simp [Category.assoc])).hom.toNatTrans.app
          ((F.map a).toFunctor.obj X)) ≫
        (F.mapComp' c d (c ≫ d) (by rfl)).hom.toNatTrans.app
          ((F.map b).toFunctor.obj ((F.map a).toFunctor.obj X)) ≫
        (F.map d).toFunctor.map
          (((F.mapComp' b c (b ≫ c) (by rfl)).inv.toNatTrans.app
              ((F.map a).toFunctor.obj X)) ≫
            (F.mapComp' a (b ≫ c) (((a ≫ b) ≫ c))
              (by simp [Category.assoc])).inv.toNatTrans.app X) := by
          simpa [Category.assoc] using
            congrArg
              (fun t => t ≫
                (F.map d).toFunctor.map
                  (((F.mapComp' b c (b ≫ c) (by rfl)).inv.toNatTrans.app
                    ((F.map a).toFunctor.obj X)) ≫
                    (F.mapComp' a (b ≫ c) (((a ≫ b) ≫ c))
                      (by simp [Category.assoc])).inv.toNatTrans.app X))
              hhom
    _ =
      ((F.mapComp' b (c ≫ d) (((b ≫ c) ≫ d)) (by simp [Category.assoc])).hom.toNatTrans.app
          ((F.map a).toFunctor.obj X)) ≫
        (F.mapComp' c d (c ≫ d) (by rfl)).hom.toNatTrans.app
          ((F.map b).toFunctor.obj ((F.map a).toFunctor.obj X)) ≫
        (F.map d).toFunctor.map
          (((F.map c).toFunctor.map
            ((F.mapComp' a b (a ≫ b) (by rfl)).inv.toNatTrans.app X)) ≫
            (F.mapComp' (a ≫ b) c ((a ≫ b) ≫ c) (by rfl)).inv.toNatTrans.app X) := by
          simpa [Category.assoc] using
            congrArg
              (fun t =>
                ((F.mapComp' b (c ≫ d) (((b ≫ c) ≫ d))
                  (by simp [Category.assoc])).hom.toNatTrans.app
                    ((F.map a).toFunctor.obj X)) ≫
                (F.mapComp' c d (c ≫ d) (by rfl)).hom.toNatTrans.app
                  ((F.map b).toFunctor.obj ((F.map a).toFunctor.obj X)) ≫
                (F.map d).toFunctor.map t)
              hinv.symm
    _ =
      ((F.mapComp' b (c ≫ d) (((b ≫ c) ≫ d)) (by simp [Category.assoc])).hom.toNatTrans.app
          ((F.map a).toFunctor.obj X)) ≫
        ((F.mapComp' c d (c ≫ d) (by rfl)).hom.toNatTrans.app
          ((F.map b).toFunctor.obj ((F.map a).toFunctor.obj X)) ≫
          (F.map d).toFunctor.map
            ((F.map c).toFunctor.map
              ((F.mapComp' a b (a ≫ b) (by rfl)).inv.toNatTrans.app X)) ≫
          (F.map d).toFunctor.map
            ((F.mapComp' (a ≫ b) c ((a ≫ b) ≫ c) (by rfl)).inv.toNatTrans.app X)) := by
          simp [Functor.map_comp]
    _ =
      (((F.mapComp' b (c ≫ d) (((b ≫ c) ≫ d)) (by simp [Category.assoc])).hom.toNatTrans.app
          ((F.map a).toFunctor.obj X)) ≫
        (F.map (c ≫ d)).toFunctor.map
          ((F.mapComp' a b (a ≫ b) (by rfl)).inv.toNatTrans.app X)) ≫
      ((F.mapComp' c d (c ≫ d) (by rfl)).hom.toNatTrans.app
        ((F.map (a ≫ b)).toFunctor.obj X)) ≫
        (F.map d).toFunctor.map
          ((F.mapComp' (a ≫ b) c ((a ≫ b) ≫ c) (by rfl)).inv.toNatTrans.app X) := by
          simpa [Category.assoc] using
            congrArg
              (fun t =>
                ((F.mapComp' b (c ≫ d) (((b ≫ c) ≫ d))
                  (by simp [Category.assoc])).hom.toNatTrans.app
                    ((F.map a).toFunctor.obj X)) ≫ t ≫
                (F.map d).toFunctor.map
                  ((F.mapComp' (a ≫ b) c ((a ≫ b) ≫ c) (by rfl)).inv.toNatTrans.app X))
              hnat.symm

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
/-- Owner-normalized heterogeneous form of `mapComp_target_assoc`, matching the right-associated
owners produced by `mapComp'_eq_mapComp` in `compositionTargetHom`. -/
theorem mapComp_target_assoc_heq
    {b₀ b₁ b₂ b₃ b₄ : LocallyDiscrete Cᵒᵖ}
    (a : b₀ ⟶ b₁) (b : b₁ ⟶ b₂) (c : b₂ ⟶ b₃) (d : b₃ ⟶ b₄)
    (X : F.obj b₀) :
    HEq
      (((F.mapComp' (b ≫ c) d ((b ≫ c) ≫ d) (by rfl)).hom.toNatTrans.app
          ((F.map a).toFunctor.obj X)) ≫
        (F.map d).toFunctor.map
          ((F.mapComp' a (b ≫ c) (a ≫ (b ≫ c))
            (by rfl)).inv.toNatTrans.app X))
      ((((F.mapComp' b (c ≫ d) (b ≫ (c ≫ d)) (by rfl)).hom.toNatTrans.app
          ((F.map a).toFunctor.obj X)) ≫
        (F.map (c ≫ d)).toFunctor.map
          ((F.mapComp' a b (a ≫ b) (by rfl)).inv.toNatTrans.app X)) ≫
        ((F.mapComp' c d (c ≫ d) (by rfl)).hom.toNatTrans.app
          ((F.map (a ≫ b)).toFunctor.obj X)) ≫
          (F.map d).toFunctor.map
            ((F.mapComp' (a ≫ b) c ((a ≫ b) ≫ c) (by rfl)).inv.toNatTrans.app X)) := by
  let Hleft :=
    ((F.mapComp' (b ≫ c) d ((b ≫ c) ≫ d) (by rfl)).hom.toNatTrans.app
      ((F.map a).toFunctor.obj X))
  let Iright :=
    ((F.mapComp' a (b ≫ c) (a ≫ (b ≫ c)) (by rfl)).inv.toNatTrans.app X)
  let Ileft :=
    ((F.mapComp' a (b ≫ c) (((a ≫ b) ≫ c))
      (by simp [Category.assoc])).inv.toNatTrans.app X)
  have hleftTail :
      HEq ((F.map d).toFunctor.map Iright) ((F.map d).toFunctor.map Ileft) := by
    exact Pseudofunctor.map_mapComp'_inv_app_heq_of_eq
      (F := F)
      (r := d)
      (hk := by simp [Category.assoc])
      (h := by rfl)
      (h' := by simp [Category.assoc])
      X
  have hleft :
      HEq (Hleft ≫ (F.map d).toFunctor.map Iright)
        (Hleft ≫ (F.map d).toFunctor.map Ileft) := by
    refine heq_comp ?_ ?_ ?_ (heq_of_eq rfl) hleftTail
    · simp [Hleft, Iright, Ileft]
    · simp [Hleft, Iright, Ileft]
    · simp [Hleft, Iright, Ileft, Category.assoc]
  let HrightLeft :=
    ((F.mapComp' b (c ≫ d) (((b ≫ c) ≫ d))
      (by simp [Category.assoc])).hom.toNatTrans.app ((F.map a).toFunctor.obj X))
  let HrightRight :=
    ((F.mapComp' b (c ≫ d) (b ≫ (c ≫ d)) (by rfl)).hom.toNatTrans.app
      ((F.map a).toFunctor.obj X))
  let Btail :=
    (F.map (c ≫ d)).toFunctor.map
      ((F.mapComp' a b (a ≫ b) (by rfl)).inv.toNatTrans.app X)
  let Ctail :=
    ((F.mapComp' c d (c ≫ d) (by rfl)).hom.toNatTrans.app
      ((F.map (a ≫ b)).toFunctor.obj X))
  let Dtail :=
    (F.map d).toFunctor.map
      ((F.mapComp' (a ≫ b) c ((a ≫ b) ≫ c) (by rfl)).inv.toNatTrans.app X)
  have hHright : HEq HrightLeft HrightRight := by
    exact Pseudofunctor.mapComp'_hom_app_heq_of_eq
      (F := F)
      (hk := by simp [Category.assoc])
      (h := by simp [Category.assoc])
      (h' := by rfl)
      ((F.map a).toFunctor.obj X)
  have hrightPrefix : HEq (HrightLeft ≫ Btail) (HrightRight ≫ Btail) := by
    refine heq_comp ?_ ?_ ?_ hHright (heq_of_eq rfl)
    · simp [HrightLeft, HrightRight, Btail]
    · simp [HrightLeft, HrightRight, Btail, Category.assoc]
    · simp [HrightLeft, HrightRight, Btail, Category.assoc]
  have hrightMid : HEq ((HrightLeft ≫ Btail) ≫ Ctail)
      ((HrightRight ≫ Btail) ≫ Ctail) := by
    refine heq_comp ?_ ?_ ?_ hrightPrefix (heq_of_eq rfl)
    · simp [HrightLeft, HrightRight, Btail, Ctail]
    · simp [HrightLeft, HrightRight, Btail, Ctail, Category.assoc]
    · simp [HrightLeft, HrightRight, Btail, Ctail, Category.assoc]
  have hright : HEq (((HrightLeft ≫ Btail) ≫ Ctail) ≫ Dtail)
      (((HrightRight ≫ Btail) ≫ Ctail) ≫ Dtail) := by
    refine heq_comp ?_ ?_ ?_ hrightMid (heq_of_eq rfl)
    · simp [HrightLeft, HrightRight, Btail, Ctail, Dtail]
    · simp [HrightLeft, HrightRight, Btail, Ctail, Dtail, Category.assoc]
    · simp [HrightLeft, HrightRight, Btail, Ctail, Dtail, Category.assoc]
  exact HEq.trans hleft
    (HEq.trans (heq_of_eq (Pseudofunctor.mapComp_target_assoc
      (F := F) a b c d X))
      (by
        simpa [HrightLeft, HrightRight, Btail, Ctail, Dtail, Category.assoc] using hright))

end Pseudofunctor

end CategoryTheory
