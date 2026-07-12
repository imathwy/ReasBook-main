import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 018H]
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
