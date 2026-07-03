import Mathlib
import StacksProject_2024.Chap14.Definition_14_15_1

open Opposite
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

private instance finiteSimplexOpHom (a b : SimplexCategoryᵒᵖ) : Finite (a ⟶ b) :=
  Finite.of_equiv (unop b ⟶ unop a) (opEquiv _ _).symm

private instance finiteCostandardSimplexObj (k : ℕ) (Δ : SimplexCategory) :
    Finite ((coyoneda.obj (op ⦋k⦌) : CosimplicialObject (Type)).obj Δ) :=
  Finite.of_equiv (op Δ ⟶ op ⦋k⦌) (opEquiv (op Δ) (op ⦋k⦌))

private instance hasProductsOfShapeSimplexOp (a b : SimplexCategoryᵒᵖ) :
    HasProductsOfShape (a ⟶ b) C := by
  infer_instance

private abbrev costandardSimplexIndexEquiv (k : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    (coyoneda.obj (op ⦋k⦌) : CosimplicialObject (Type)).obj (unop Δ) ≃ (Δ ⟶ op ⦋k⦌) :=
  (opEquiv Δ (op ⦋k⦌)).symm

noncomputable def homFromCostandardSimplexIso (k : ℕ) (X : C) :
    homFromCosimplicialSet (coyoneda.obj (op ⦋k⦌)) ((SimplicialObject.const C).obj X) ≅
      (evaluationRightAdjoint C (op ⦋k⦌)).obj X :=
  NatIso.ofComponents
    (fun Δ ↦
      Pi.reindex (costandardSimplexIndexEquiv k Δ) (fun _ : Δ ⟶ op ⦋k⦌ ↦ X))
    (fun {Δ₁ Δ₂} f ↦ by
      apply Pi.hom_ext
      intro g
      dsimp [homFromCosimplicialSet, evaluationRightAdjoint, costandardSimplexIndexEquiv]
      simp [Category.assoc]
    )

end CategoryTheory
