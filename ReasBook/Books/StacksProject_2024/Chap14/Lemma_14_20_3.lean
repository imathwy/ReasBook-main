import Mathlib
import StacksProject_2024.Chap14.Lemma_14_20_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : Y ⟶ X)
variable [∀ n : ℕ, HasWidePullback (Arrow.mk f).right
  (fun _ : Fin (n + 1) ↦ (Arrow.mk f).left) (fun _ ↦ (Arrow.mk f).hom)]

/- Domain-style sampling for Lemma 14.20.3:
- primary domain: augmented simplicial objects, the Čech nerve adjunction, and coskeleta in
  `CategoryTheory.SimplicialObject`;
- sampled owner declarations:
  `SimplicialObject.IsCoskeletal`,
  `SimplicialObject.augment`,
  `SimplicialObject.cechNerveEquiv`,
  `SimplicialObject.augmentHomEquivZeroSimplex`;
- best owner abstraction: `SimplicialObject.IsCoskeletal` for the `1`-coskeletal statement, together
  with the chapter-level augmentation API from Lemma 14.20.2 for the source-facing
  degree-`0` description of morphisms into the Čech nerve;
- primitive data: the source-facing input is a simplicial morphism
  `V ⟶ (Arrow.mk f).cechNerve`; the compatible degree-`0` morphism `V₀ ⟶ Y` is derived from that
  owner abstraction;
- source/core/bridge triage:
  `source-facing`: the textbook degree-`0` compatibility description of maps into the Čech nerve;
  `core/canonical`: `SimplicialObject.IsCoskeletal`;
  `bridge/view`: the equivalence `cechNerveHomEquivZero` below, obtained from the local fixed-arrow
    universal property and the chapter augmentation equivalence from Lemma 14.20.2.

The local source-facing API should therefore expose the hom-set equivalence directly, rather than
splitting it into a raw function and a separate bijectivity theorem. -/

-- Proof sketch: the augmented Čech nerve is characterized by the universal property of the
-- arrow `f`, and this universal property depends only on simplices of dimensions `0` and `1`.
-- Equivalently, the identity map of the Čech nerve exhibits it as the right Kan extension of its
-- `1`-truncation along `(SimplexCategory.Truncated.inclusion 1).op`.
/-- Lemma 14.20.3: the Čech nerve of `f : Y ⟶ X` is `1`-coskeletal. Equivalently, it is recovered
from its `1`-truncation by the canonical `1`-coskeleton functor, which is the library-facing form
of the textbook statement that maps into the Čech nerve are determined by compatible degree-`0`
data. -/
lemma cechNerve_isCoskeletal_one :
    (Arrow.mk f).cechNerve.IsCoskeletal 1 := sorry

-- Proof sketch: for a simplicial morphism `g : V ⟶ (Arrow.mk f).cechNerve`, compose the
-- degree-`0` component `g.app (op ⦋0⦌)` with the unique projection from the degree-`0` wide
-- pullback to `Y`. Naturality with respect to the two face maps `δ₀, δ₁ : [0] ⟶ [1]` and the
-- defining pullback relation imply that the two composites to `X` coincide.
/-- The degree-`0` component of a morphism into the Čech nerve satisfies the equalizer relation
coming from the two degree-`1` face maps. -/
theorem cechNerve_degreeZero_condition
    (V : SimplicialObject C) (g : V ⟶ (Arrow.mk f).cechNerve) :
    V.δ 0 ≫ (g.app (op ⦋0⦌) ≫
      WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f =
      V.δ 1 ≫ (g.app (op ⦋0⦌) ≫
        WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) ≫ f := by
  simpa [Category.assoc, WidePullback.π_arrow] using
    augmentation_zero_simplex_face_condition
      (g ≫ (Arrow.mk f).augmentedCechNerve.hom)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse direction of `cechNerveHomEquivZero`, built from the augmentation owner together
with the fixed-arrow Čech nerve universal property. -/
private noncomputable def cechNerveHomFromZero
    (V : SimplicialObject C)
    (e : { g0 : V _⦋0⦌ ⟶ Y // V.δ 0 ≫ g0 ≫ f = V.δ 1 ≫ g0 ≫ f }) :
    V ⟶ (Arrow.mk f).cechNerve where
  app n :=
    WidePullback.lift
      ((V.augment X (e.1 ≫ f) (zero_simplex_face_condition_all_maps (e.1 ≫ f) e.2)).hom.app n)
      (fun i ↦ V.map (SimplexCategory.const ⦋0⦌ (unop n) i).op ≫ e.1)
      (fun i ↦ by
        simpa [Category.assoc] using
          zero_simplex_face_condition_all_maps (e.1 ≫ f) e.2 (unop n)
            (SimplexCategory.const ⦋0⦌ (unop n) i)
            (SimplexCategory.const ⦋0⦌ (unop n) 0))
  naturality := by
    intro n m α
    let _ : HasWidePullback X (fun _ : Fin ((unop m).len + 1) ↦ Y) (fun _ ↦ f) :=
      ‹∀ n : ℕ, HasWidePullback (Arrow.mk f).right
        (fun _ : Fin (n + 1) ↦ (Arrow.mk f).left) (fun _ ↦ (Arrow.mk f).hom)› (unop m).len
    apply WidePullback.hom_ext
    · intro i
      dsimp [CategoryTheory.Arrow.cechNerve]
      simp only [WidePullback.lift_π, Category.assoc]
      have hconst :
          α ≫ (SimplexCategory.const ⦋0⦌ (unop m) i).op =
            (SimplexCategory.const ⦋0⦌ (unop n) (α.unop.toOrderHom i)).op := by
        exact congrArg Quiver.Hom.op (SimplexCategory.const_comp ⦋0⦌ α.unop i)
      calc
        V.map α ≫ (V.map (SimplexCategory.const ⦋0⦌ (unop m) i).op ≫ e.1)
            = V.map (α ≫ (SimplexCategory.const ⦋0⦌ (unop m) i).op) ≫ e.1 := by
                rw [Functor.map_comp, Category.assoc]
        _ = V.map (SimplexCategory.const ⦋0⦌ (unop n) (α.unop.toOrderHom i)).op ≫ e.1 := by
              rw [hconst]
    · have hnat := NatTrans.naturality
          ((V.augment X (e.1 ≫ f) (zero_simplex_face_condition_all_maps (e.1 ≫ f) e.2)).hom) α
      simpa [SimplicialObject.augment] using hnat

@[simp]
private theorem cechNerveHomFromZero_app_zero_pi
    (V : SimplicialObject C)
    (e : { g0 : V _⦋0⦌ ⟶ Y // V.δ 0 ≫ g0 ≫ f = V.δ 1 ≫ g0 ≫ f }) :
    (cechNerveHomFromZero f V e).app (op ⦋0⦌) ≫
      WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 = e.1 := by
  dsimp [cechNerveHomFromZero, SimplicialObject.augment]
  rw [WidePullback.lift_π]
  simp

private theorem augment_eq_comp_augmentedCechNerve_hom
    (V : SimplicialObject C) (g : V ⟶ (Arrow.mk f).cechNerve) :
    (V.augment X
        (g.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f)
        (zero_simplex_face_condition_all_maps
          (g.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 ≫ f)
          (by
            simpa [Category.assoc] using cechNerve_degreeZero_condition f V g))).hom =
      g ≫ (Arrow.mk f).augmentedCechNerve.hom := by
  apply (augmentHomEquivZeroSimplex V X).injective
  apply Subtype.ext
  simp [WidePullback.π_arrow]

private theorem cechNerveHomFromZero_toFun
    (V : SimplicialObject C) (g : V ⟶ (Arrow.mk f).cechNerve) :
    cechNerveHomFromZero f V
        ⟨g.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0,
          cechNerve_degreeZero_condition f V g⟩ =
      g := by
  let e : { g0 : V _⦋0⦌ ⟶ Y // V.δ 0 ≫ g0 ≫ f = V.δ 1 ≫ g0 ≫ f } :=
    ⟨g.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0,
      cechNerve_degreeZero_condition f V g⟩
  apply SimplicialObject.hom_ext
  intro n
  let _ : HasWidePullback X (fun _ : Fin ((unop n).len + 1) ↦ Y) (fun _ ↦ f) :=
    ‹∀ n : ℕ, HasWidePullback (Arrow.mk f).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f).left) (fun _ ↦ (Arrow.mk f).hom)› (unop n).len
  apply WidePullback.hom_ext
  · intro i
    have hnat :=
      g.naturality (SimplexCategory.const ⦋0⦌ (unop n) i).op
    dsimp [cechNerveHomFromZero]
    rw [WidePullback.lift_π]
    calc
      V.map (SimplexCategory.const ⦋0⦌ (unop n) i).op ≫ e.1
          = g.app n ≫
              (Arrow.mk f).cechNerve.map (SimplexCategory.const ⦋0⦌ (unop n) i).op ≫
                WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 := by
              simpa [e, Category.assoc] using
                congrArg (fun k ↦ k ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0) hnat
      _ = g.app n ≫ WidePullback.π (fun _ : Fin ((unop n).len + 1) ↦ (Arrow.mk f).hom) i := by
        have hπ :
            (Arrow.mk f).cechNerve.map (SimplexCategory.const ⦋0⦌ (unop n) i).op ≫
              WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 =
            WidePullback.π (fun _ : Fin ((unop n).len + 1) ↦ (Arrow.mk f).hom) i := by
          dsimp [CategoryTheory.Arrow.cechNerve]
          rw [WidePullback.lift_π]
        simpa [Category.assoc] using congrArg (g.app n ≫ ·) hπ
  · dsimp [cechNerveHomFromZero]
    rw [WidePullback.lift_base]
    simpa [e] using
      congrArg (fun η ↦ η.app n) (augment_eq_comp_augmentedCechNerve_hom f V g)

/-- Morphisms from `V` to the Čech nerve of `f` are canonically equivalent to degree-`0`
morphisms `g₀ : V₀ ⟶ Y` whose composites with the two face maps `V₁ ⇉ V₀` agree after composing
with `f`. -/
noncomputable def cechNerveHomEquivZero
    (V : SimplicialObject C) :
    (V ⟶ (Arrow.mk f).cechNerve) ≃
      { g0 : V _⦋0⦌ ⟶ Y // V.δ 0 ≫ g0 ≫ f = V.δ 1 ≫ g0 ≫ f } where
  toFun g :=
    ⟨g.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0,
      cechNerve_degreeZero_condition f V g⟩
  invFun := cechNerveHomFromZero f V
  left_inv := by
    intro g
    exact cechNerveHomFromZero_toFun f V g
  right_inv := by
    intro e
    apply Subtype.ext
    exact cechNerveHomFromZero_app_zero_pi f V e

/-- The forward map of `cechNerveHomEquivZero` sends a simplicial morphism to its degree-`0`
component composed with the canonical projection from the `0`-simplices of the Čech nerve to `Y`.
-/
@[simp]
theorem cechNerveHomEquivZero_apply
    (V : SimplicialObject C) (g : V ⟶ (Arrow.mk f).cechNerve) :
    cechNerveHomEquivZero f V g =
      ⟨g.app (op ⦋0⦌) ≫ WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0,
        cechNerve_degreeZero_condition f V g⟩ := rfl

/-- The inverse map of `cechNerveHomEquivZero` recovers the prescribed degree-`0` morphism after
composing with the canonical projection from the `0`-simplices of the Čech nerve to `Y`. -/
@[simp]
theorem cechNerveHomEquivZero_symm_apply_zero_pi
    (V : SimplicialObject C)
    (e : { g0 : V _⦋0⦌ ⟶ Y // V.δ 0 ≫ g0 ≫ f = V.δ 1 ≫ g0 ≫ f }) :
    ((cechNerveHomEquivZero f V).symm e).app (op ⦋0⦌) ≫
      WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk f).hom) 0 = e.1 := by
  exact cechNerveHomFromZero_app_zero_pi f V e

end CategoryTheory
