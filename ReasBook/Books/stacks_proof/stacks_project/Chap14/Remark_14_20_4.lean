import Mathlib
import StacksProject_2024.Chap14.Lemma_14_20_2

-- Declarations for this item will be appended below by the statement pipeline.

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
- primary domain: augmented simplicial objects, the Čech nerve of an arrow, and the canonical
  wide-pullback map determined by an augmentation;
- sampled owner declarations:
  `Arrow.cechNerve`,
  `Arrow.augmentedCechNerve`,
  `WidePullback.lift`,
  `SimplexCategory.const`;
- best owner abstraction:
  the global owner `SimplicialObject.cechNerveEquiv` is stronger than the local hypotheses of this
  remark, so the stable source-faithful route is the corresponding direct wide-pullback
  construction specialized to the fixed arrow `ε.app (op ⦋0⦌)`;
- primitive data vs. derived API:
  the primitive source-facing datum is the augmentation `ε : V ⟶ const X`; the induced simplicial
  map `augmentationToCechNerve ε : V ⟶ cechNerve (ε.app (op ⦋0⦌))` is assembled degreewise from the
  maps `V.map (SimplexCategory.const ⦋0⦌ (unop n) i).op : V_n ⟶ V_0`;
- source/core/bridge triage:
  `source-facing`: the canonical simplicial morphism induced by an augmentation;
  `core/canonical`: `Arrow.cechNerve` as the iterated fiber product owner;
  `bridge/view`: the universal property of `WidePullback.lift` applied to the constant maps
  `[0] ⟶ [n]`.
-/

section

variable (ε : V ⟶ (SimplicialObject.const C).obj X)
variable [∀ n : ℕ, HasWidePullback (Arrow.mk (ε.app (op ⦋0⦌))).right
  (fun _ : Fin (n + 1) ↦ (Arrow.mk (ε.app (op ⦋0⦌))).left)
  (fun _ ↦ (Arrow.mk (ε.app (op ⦋0⦌))).hom)]

omit [∀ n : ℕ, HasWidePullback (Arrow.mk (ε.app (op ⦋0⦌))).right
  (fun _ : Fin (n + 1) ↦ (Arrow.mk (ε.app (op ⦋0⦌))).left)
  (fun _ ↦ (Arrow.mk (ε.app (op ⦋0⦌))).hom)] in
/-- Helper for Remark 14.20.4: each constant map `[0] ⟶ [n]` induces a projection `V_n ⟶ V_0`
whose composite with `ε_0` is the base map `ε_n`. -/
private theorem augmentationToCechNerve_projection_condition
    (n : SimplexCategoryᵒᵖ) (i : Fin (unop n).len.succ) :
    V.map (SimplexCategory.const ⦋0⦌ (unop n) i).op ≫ ε.app (op ⦋0⦌) = ε.app n := by
  -- Naturality against a constant map into `n` identifies every projection with the same base map.
  simpa using ε.naturality (SimplexCategory.const ⦋0⦌ (unop n) i).op

/-- Remark 14.20.4: an augmentation `ε : V ⟶ X` induces the canonical simplicial morphism from
`V` to the Čech nerve of its degree-`0` component `ε.app (op ⦋0⦌) : V₀ ⟶ X`. -/
@[stacks 018J]
noncomputable def augmentationToCechNerve :
    V ⟶ ((Arrow.mk (ε.app (op ⦋0⦌))).cechNerve) :=
  { app := fun n ↦
      WidePullback.lift
        (ε.app n)
        (fun i ↦ V.map (SimplexCategory.const ⦋0⦌ (unop n) i).op)
        (fun i ↦ augmentationToCechNerve_projection_condition ε n i)
    naturality := by
      intro n m α
      -- Compare the two morphisms into the target wide pullback on every projection and on the base.
      apply WidePullback.hom_ext
      · intro i
        dsimp [CategoryTheory.Arrow.cechNerve]
        simp only [WidePullback.lift_π, Category.assoc]
        have hconst :
            α ≫ (SimplexCategory.const ⦋0⦌ (unop m) i).op =
              (SimplexCategory.const ⦋0⦌ (unop n) (α.unop.toOrderHom i)).op := by
          exact congrArg Quiver.Hom.op (SimplexCategory.const_comp ⦋0⦌ α.unop i)
        calc
          V.map α ≫ V.map (SimplexCategory.const ⦋0⦌ (unop m) i).op =
              V.map (α ≫ (SimplexCategory.const ⦋0⦌ (unop m) i).op) := by
                rw [Functor.map_comp]
          _ = V.map ((SimplexCategory.const ⦋0⦌ (unop n) (α.unop.toOrderHom i)).op) := by
                rw [hconst]
          _ = V.map (SimplexCategory.const ⦋0⦌ (unop n) (α.unop.toOrderHom i)).op := rfl
      · dsimp [CategoryTheory.Arrow.cechNerve]
        simp only [Category.assoc, WidePullback.lift_base]
        simpa using ε.naturality α }

@[simp] theorem augmentationToCechNerve_app_zero_pi :
    (augmentationToCechNerve ε).app (op ⦋0⦌) ≫
        WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk (ε.app (op ⦋0⦌))).hom) 0 =
      𝟙 (V _⦋0⦌) := by
  -- In degree `0`, the unique constant map `[0] ⟶ [0]` is the identity.
  dsimp [augmentationToCechNerve, CategoryTheory.Arrow.cechNerve]
  rw [WidePullback.lift_π]
  simp

/-- The induced simplicial morphism recovers the original augmentation after composing with the
augmentation of the Čech nerve. -/
@[simp] theorem augmentationToCechNerve_comp_augmentedCechNerve_hom :
    augmentationToCechNerve ε ≫ (Arrow.mk (ε.app (op ⦋0⦌))).augmentedCechNerve.hom = ε := by
  -- The composed augmentation has the same component `ε.app n` in every simplicial degree.
  ext n
  dsimp [augmentationToCechNerve, CategoryTheory.Arrow.augmentedCechNerve,
    CategoryTheory.Arrow.cechNerve]
  rw [WidePullback.lift_base]

end

end CategoryTheory
