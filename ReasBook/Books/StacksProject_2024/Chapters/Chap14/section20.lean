import Mathlib
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_20_1 (from Chap14) -/
open CategoryTheory
open CategoryTheory.SimplicialObject

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (U : SimplicialObject C) (X : C)

/- Domain-style sampling for Definition 14.20.1:
- primary domain: augmented simplicial objects and augmentations in
  `CategoryTheory.SimplicialObject`;
- sampled owner API:
  `SimplicialObject.const`,
  `SimplicialObject.Augmented`,
  `SimplicialObject.Augmented.const`,
  `SimplicialObject.augment`;
- target layer: `source-facing`;
- best owner abstraction in the surrounding API: `SimplicialObject.Augmented C`, the canonical
  packaged owner of an augmented simplicial object;
- source/core/bridge triage:
  `source-facing`: for fixed `U` and `X`, an augmentation is a morphism
    `U ⟶ (const C).obj X`;
  `core/canonical`: `SimplicialObject.Augmented C`;
  `bridge/view`: an element of `SimplicialObject.Augmented C` with left side `U` and right side
    `X` recovers the textbook fixed-endpoint datum above, while `SimplicialObject.augment` is the
    downstream constructor from degree-`0` data.

Primitive data for the fixed-endpoint notion are exactly the natural-transformation components of
the morphism `U ⟶ (const C).obj X`. The packaged owner
`SimplicialObject.Augmented C` is the canonical way to store `U`, `X`, and the augmentation
together, but Definition 14.20.1 itself fixes `U` and `X`, so the main entry here should stay on
the source-facing fixed-endpoint morphism type and mention the packaged owner only as companion
bridge context.
-/

/- Definition 14.20.1: an augmentation of a simplicial object
`U` toward an object `X` of `C` is a morphism from `U` to the constant simplicial object on `X`.
-/
#check (U ⟶ (const C).obj X)

/- Companion owner context: the canonical packaged owner for augmented simplicial objects in `C`
is `SimplicialObject.Augmented C`. -/
#check (SimplicialObject.Augmented C)

/- Companion recall: the owner declaration for augmented simplicial objects is
`SimplicialObject.Augmented`. -/
recall SimplicialObject.Augmented

end

/-! ### Lemma_14_20_2 (from Chap14) -/
open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open SimplexCategory
open scoped Simplicial

universe u v

namespace CategoryTheory
namespace SimplicialObject

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.20.2:
- primary domain: augmentations of simplicial objects to a constant simplicial object;
- sampled owner API:
  `SimplicialObject.augment`,
  `SimplicialObject.augment_hom_zero`,
  `SimplicialObject.hom_ext`,
  `SimplexCategory.const_comp`;
- best owner abstraction:
  `SimplicialObject.augment` is the canonical owner for reconstructing an augmentation from
  degree-`0` data satisfying compatibility with all maps `⦋0⦌ ⟶ i`;
- primitive data vs. derived API:
  the primitive source-facing datum here is a morphism `U _⦋0⦌ ⟶ X` satisfying the two-face
  relation `U.δ 0 ≫ ε₀ = U.δ 1 ≫ ε₀`, while the full augmentation and its higher components are
  derived from the owner abstraction;
- source/core/bridge triage:
  `source-facing`: the textbook characterization by a degree-`0` map with the two-face condition;
  `core/canonical`: `SimplicialObject.augment`;
  `bridge/view`: the reduction from compatibility with all maps `⦋0⦌ ⟶ i` to the two face maps
  `δ₀, δ₁ : ⦋0⦌ ⟶ ⦋1⦌`, and the owner-based equivalence
  `SimplicialObject.augmentHomEquivZeroSimplex`.
-/

/-- The degree-`0` component of an augmentation equalizes the two face maps out of degree `1`. -/
-- Proof sketch: apply naturality of the augmentation to the two morphisms `⦋0⦌ ⟶ ⦋1⦌`; since the
-- target is constant, both induced maps on `X` are identities, so the two composites from `U_1`
-- to `X` coincide.
theorem augmentation_zero_simplex_face_condition
    {U : SimplicialObject C} {X : C} (α : U ⟶ (const C).obj X) :
    U.δ 0 ≫ α.app (op ⦋0⦌) = U.δ 1 ≫ α.app (op ⦋0⦌) := by
  have h₀ := α.naturality (SimplexCategory.δ (0 : Fin 2)).op
  have h₁ := α.naturality (SimplexCategory.δ (1 : Fin 2)).op
  simpa using h₀.trans h₁.symm

/-- A degree-`0` map satisfying the two-face relation is compatible with every map from `[0]` in the
simplex category. -/
-- Proof sketch: any two maps `⦋0⦌ ⟶ i` factor through the two maps `⦋0⦌ ⟶ ⦋1⦌`; the assumed
-- equality after composing with `U.δ 0` and `U.δ 1` then gives equality after composing with the
-- images of the original maps under `U`.
theorem zero_simplex_face_condition_all_maps
    {U : SimplicialObject C} {X : C}
    (ε₀ : U _⦋0⦌ ⟶ X) (hε₀ : U.δ 0 ≫ ε₀ = U.δ 1 ≫ ε₀)
    (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i) :
    U.map g₁.op ≫ ε₀ = U.map g₂.op ≫ ε₀ := by
  let a : Fin (i.len + 1) := g₁.toOrderHom 0
  let b : Fin (i.len + 1) := g₂.toOrderHom 0
  rw [eq_const_of_zero g₁, eq_const_of_zero g₂]
  have hconst :
      ∀ (a b : Fin (i.len + 1)),
        a ≤ b →
          U.map (SimplexCategory.const ⦋0⦌ i a).op ≫ ε₀ =
            U.map (SimplexCategory.const ⦋0⦌ i b).op ≫ ε₀ := by
    intro a b hab
    let h : ⦋1⦌ ⟶ i := mkOfLe a b hab
    have ha : U.map (SimplexCategory.const ⦋0⦌ i a).op = U.map h.op ≫ U.δ 1 := by
      have hcomp :
          SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 ≫ h = SimplexCategory.const ⦋0⦌ i a := by
        simpa [h, mkOfLe] using SimplexCategory.const_comp ⦋0⦌ h 0
      rw [← hcomp, op_comp, U.map_comp, ← δ_one_eq_const]
      rfl
    have hb : U.map (SimplexCategory.const ⦋0⦌ i b).op = U.map h.op ≫ U.δ 0 := by
      have hcomp :
          SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 ≫ h = SimplexCategory.const ⦋0⦌ i b := by
        simpa [h, mkOfLe] using SimplexCategory.const_comp ⦋0⦌ h 1
      rw [← hcomp, op_comp, U.map_comp, ← δ_zero_eq_const]
      rfl
    calc
      U.map (SimplexCategory.const ⦋0⦌ i a).op ≫ ε₀ = U.map h.op ≫ U.δ 1 ≫ ε₀ := by
        simpa [Category.assoc] using congrArg (· ≫ ε₀) ha
      _ = U.map h.op ≫ U.δ 0 ≫ ε₀ := by
        simpa [Category.assoc] using congrArg (U.map h.op ≫ ·) hε₀.symm
      _ = U.map (SimplexCategory.const ⦋0⦌ i b).op ≫ ε₀ := by
        simpa [Category.assoc] using congrArg (· ≫ ε₀) hb.symm
  by_cases hab : a ≤ b
  · exact hconst a b hab
  · exact (hconst b a (le_of_not_ge hab)).symm

/-- Lemma 14.20.2: to give an augmentation of a simplicial object `U` toward `X` is equivalent to
giving a morphism `epsilon0 : U_0 ⟶ X` whose composites with the two face maps
`d^1_0, d^1_1 : U_1 ⟶ U_0` are equal. -/
def augmentHomEquivZeroSimplex
    (U : SimplicialObject C) (X : C) :
    (U ⟶ (const C).obj X) ≃
      { ε₀ : U _⦋0⦌ ⟶ X // U.δ 0 ≫ ε₀ = U.δ 1 ≫ ε₀ } where
  toFun α := ⟨α.app (op ⦋0⦌), augmentation_zero_simplex_face_condition α⟩
  invFun e := (U.augment X e.1 (zero_simplex_face_condition_all_maps e.1 e.2)).hom
  left_inv := by
    intro α
    apply hom_ext
    intro Δ
    simpa using α.naturality (SimplexCategory.const ⦋0⦌ (unop Δ) 0).op
  right_inv := by
    intro e
    apply Subtype.ext
    exact U.augment_hom_zero X e.1 (zero_simplex_face_condition_all_maps e.1 e.2)

@[simp] theorem augmentHomEquivZeroSimplex_apply
    (U : SimplicialObject C) (X : C) (α : U ⟶ (const C).obj X) :
    augmentHomEquivZeroSimplex U X α =
      ⟨α.app (op ⦋0⦌), augmentation_zero_simplex_face_condition α⟩ := rfl

@[simp] theorem augmentHomEquivZeroSimplex_symm_apply_zero
    (U : SimplicialObject C) (X : C)
    (e : { ε₀ : U _⦋0⦌ ⟶ X // U.δ 0 ≫ ε₀ = U.δ 1 ≫ ε₀ }) :
    ((augmentHomEquivZeroSimplex U X).symm e).app (op ⦋0⦌) = e.1 := by
  simpa [augmentHomEquivZeroSimplex] using
    U.augment_hom_zero X e.1 (zero_simplex_face_condition_all_maps e.1 e.2)

end SimplicialObject
end CategoryTheory

/-! ### Lemma_14_20_3 (from Chap14) -/
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

/-! ### Remark_14_20_4 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X : C} {V : SimplicialObject C}

/- Domain-style sampling for Remark 14.20.4:
- primary domain: augmented simplicial objects, the augmented Čech nerve adjunction, and the
  degree-`0` description of morphisms into a Čech nerve;
- sampled owner declarations:
  `SimplicialObject.cechNerveEquiv`,
  `cechNerveHomEquivZero`,
  `cechNerveHomEquivZero_symm_apply_zero_pi`,
  `augmentation_zero_simplex_face_condition`;
- best owner abstraction:
  mathlib’s owner-level abstraction is `SimplicialObject.cechNerveEquiv`, but it requires the
  global functorial wide-pullback hypothesis. Since this remark only assumes wide pullbacks for the
  single arrow `ε.app (op ⦋0⦌)`, the correct local owner in the source-faithful hypothesis profile
  is the chapter bridge `cechNerveHomEquivZero`;
- primitive data vs. derived API:
  the primitive source-facing datum is the augmentation `ε : V ⟶ const X`, while the induced
  simplicial map `augmentationToCechNerve ε : V ⟶ cechNerve (ε.app (op ⦋0⦌))` is derived from the
  identity map of `V₀` under `cechNerveHomEquivZero`;
- source/core/bridge triage:
  `source-facing`: the canonical simplicial morphism induced by an augmentation;
  `core/canonical`: `SimplicialObject.cechNerveEquiv`;
  `bridge/view`: the chapter-level degree-`0` characterization via `cechNerveHomEquivZero`.
-/

section

variable (ε : V ⟶ (SimplicialObject.const C).obj X)
variable [∀ n : ℕ, HasWidePullback (Arrow.mk (ε.app (op ⦋0⦌))).right
  (fun _ : Fin (n + 1) ↦ (Arrow.mk (ε.app (op ⦋0⦌))).left)
  (fun _ ↦ (Arrow.mk (ε.app (op ⦋0⦌))).hom)]

private def augmentationToCechNerveZeroSimplex :
    { g0 : V _⦋0⦌ ⟶ V _⦋0⦌ // V.δ 0 ≫ g0 ≫ ε.app (op ⦋0⦌) = V.δ 1 ≫ g0 ≫ ε.app (op ⦋0⦌) } :=
  ⟨𝟙 (V _⦋0⦌), by simpa using augmentation_zero_simplex_face_condition ε⟩

/-- Remark 14.20.4: an augmentation `ε : V ⟶ X` induces the canonical simplicial morphism from
`V` to the Čech nerve of its degree-`0` component `ε.app (op ⦋0⦌) : V₀ ⟶ X`. This source-facing
map is the inverse image of the identity on `V₀` under the chapter bridge
`cechNerveHomEquivZero`. -/
noncomputable def augmentationToCechNerve :
    V ⟶ ((Arrow.mk (ε.app (op ⦋0⦌))).cechNerve) :=
  (cechNerveHomEquivZero (ε.app (op ⦋0⦌)) V).symm (augmentationToCechNerveZeroSimplex ε)

@[simp] theorem augmentationToCechNerve_app_zero_pi :
    (augmentationToCechNerve ε).app (op ⦋0⦌) ≫
        WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk (ε.app (op ⦋0⦌))).hom) 0 =
      𝟙 (V _⦋0⦌) := by
  simpa [augmentationToCechNerve] using
    cechNerveHomEquivZero_symm_apply_zero_pi (ε.app (op ⦋0⦌)) V
      (augmentationToCechNerveZeroSimplex ε)

/-- The induced simplicial morphism recovers the original augmentation after composing with the
augmentation of the Čech nerve. -/
@[simp] theorem augmentationToCechNerve_comp_augmentedCechNerve_hom :
    augmentationToCechNerve ε ≫ (Arrow.mk (ε.app (op ⦋0⦌))).augmentedCechNerve.hom = ε := by
  apply (augmentHomEquivZeroSimplex V X).injective
  apply Subtype.ext
  simpa [Category.assoc, WidePullback.π_arrow] using
    congrArg (fun g0 ↦ g0 ≫ ε.app (op ⦋0⦌)) (augmentationToCechNerve_app_zero_pi ε)

end

end CategoryTheory
