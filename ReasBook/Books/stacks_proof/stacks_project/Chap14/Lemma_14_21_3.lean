import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap14.Lemma_14_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open SimplexCategory SimplexCategory.Truncated

noncomputable section

universe u v

namespace CategoryTheory

/-
Domain-style sampling for Lemma 14.21.3:
- primary domain: the skeleton/truncation adjunction for simplicial objects, expressed via left
  Kan extension along `SimplexCategory.Truncated.inclusion`;
- sampled owner declarations:
  `SimplicialObject.Truncated.sk`,
  `skAdj`,
  `SimplicialObject.Truncated.sk_coreflective`,
  `Functor.HasPointwiseLeftKanExtension`;
- best owner abstraction: the mathlib owner `skAdj m` together with the canonical instance
  `IsIso (skAdj m).unit`;
- primitive data: only the `m`-truncated simplicial object `U`;
- derived API: the source-facing statement that the unit map
  `U ⟶ truncation m ((SimplicialObject.Truncated.sk m).obj U)` is an isomorphism.

Source/core/bridge triage:
- `source-facing`: the Chapter 14 statement that the canonical comparison map from `U` to the
  truncation of its skeleton is an isomorphism;
- `core/canonical`: the unit of `skAdj m`, whose whole natural transformation is an isomorphism;
- `bridge/view`: the finite-category pointwise-left-Kan instance below, reusing the public
  finiteness owners from `Lemma_14_19_2`, which supplies the hypotheses needed to specialize the
  canonical owner statement. -/

private instance costructuredArrow_finite (m : ℕ) (Δ : SimplexCategory) :
    Finite (CostructuredArrow (Truncated.inclusion m).op (op Δ)) := by
  let e :
      (Σ X : (SimplexCategory.Truncated m)ᵒᵖ,
        ((Truncated.inclusion m).op.obj X ⟶ op Δ)) ≃
        CostructuredArrow (Truncated.inclusion m).op (op Δ) :=
    { toFun := fun p ↦ CostructuredArrow.mk p.2
      invFun := fun A ↦ ⟨A.left, A.hom⟩
      left_inv := by intro p; cases p; rfl
      right_inv := by intro A; cases A; rfl }
  exact Finite.of_equiv _ e

private instance costructuredArrow_hom_finite (m : ℕ) (Δ : SimplexCategory)
    (A B : CostructuredArrow (Truncated.inclusion m).op (op Δ)) :
    Finite (A ⟶ B) := by
  refine Finite.of_injective (fun f ↦ f.left) ?_
  intro f g h
  exact CostructuredArrow.hom_ext f g h

private instance costructuredArrow_finCategory (m : ℕ) (Δ : SimplexCategory) :
    FinCategory (CostructuredArrow (Truncated.inclusion m).op (op Δ)) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

/-- The opposite inclusion of the `m`-truncated simplex category admits pointwise left Kan
extensions into any category with finite colimits. -/
instance simplexTruncatedInclusionOp_hasPointwiseLeftKanExtension
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ)
    (F : (SimplexCategory.Truncated m)ᵒᵖ ⥤ C) :
    (Truncated.inclusion m).op.HasPointwiseLeftKanExtension F := by
  intro Y
  cases Y with
  | op Y =>
      change HasColimit (CostructuredArrow.proj (Truncated.inclusion m).op (op Y) ⋙ F)
      letI : FinCategory
          (CostructuredArrow (Truncated.inclusion m).op (op Y)) :=
        costructuredArrow_finCategory m Y
      infer_instance

section

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
variable (m : ℕ)

recall skAdj

/- Lemma 14.21.3: for an `m`-truncated simplicial object `U` in a category with finite colimits,
the canonical map `U ⟶ truncation m ((SimplicialObject.Truncated.sk m).obj U)`, namely the unit
of `skAdj m`, is an isomorphism. Mathlib provides the stronger natural statement that the whole
unit natural transformation is an isomorphism. -/
#check (inferInstance : IsIso (skAdj m).unit)

end

end CategoryTheory
