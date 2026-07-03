import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace SimplexCategory.Truncated

/-- The structured-arrow indexing category for the degree-`n` matching diagram of `cosk_m`. -/
abbrev matchingIndex (m n : ℕ) :=
  StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion m).op

end SimplexCategory.Truncated

/-
Domain-style sampling for Lemma 14.19.2:
- primary domain: pointwise right Kan extensions computing simplicial coskeleta;
- sampled owner declarations:
  `SimplexCategory.Truncated.matchingIndex`,
  `Truncated.cosk`,
  `Functor.ranObjObjIsoLimit`,
  `Functor.ranObjObjIsoLimit_hom_π`,
  `Functor.HasPointwiseRightKanExtension`;
- best owner abstraction: `Functor.ranObjObjIsoLimit` specialized to
  `(SimplexCategory.Truncated.inclusion m).op`, with
  `SimplexCategory.Truncated.matchingIndex m n` as the source-facing owner for the indexing
  shape;
- primitive data: the truncation inclusion, the matching-index category
  `SimplexCategory.Truncated.matchingIndex m n`, the truncated simplicial object `U`, and the
  finite-limit hypothesis on `C`;
- derived API: the `FinCategory` instance on
  `SimplexCategory.Truncated.matchingIndex m n`, the degree-`n` limit description of `coskₘ U`,
  and its projection formula.

Source/core/bridge triage:
- `source-facing`: the degree-`n` matching-object description of `coskₘ U`;
- `core/canonical`: `Functor.ranObjObjIsoLimit` and `Functor.ranObjObjIsoLimit_hom_π`;
- `bridge/view`: the finite-category construction proving that finite limits in `C` provide the
  pointwise right Kan extensions needed for `Truncated.cosk`, with the matching-index owner
  `SimplexCategory.Truncated.matchingIndex m n`.

The local infrastructure below builds the finite-category bridge needed to expose the canonical
owner theorem. The reusable finiteness support for truncated simplex categories and the resulting
structured-arrow bridge remain public, while the one-off enumeration arguments used to construct
them stay private. -/

instance simplexCategoryOp_hom_finite (X Y : SimplexCategoryᵒᵖ) : Finite (X ⟶ Y) :=
  Finite.of_equiv (Y.unop ⟶ X.unop) Quiver.Hom.opEquiv

instance truncatedSimplex_finite (m : ℕ) : Finite (SimplexCategory.Truncated m) := by
  let e : Fin (m + 1) ≃ SimplexCategory.Truncated m :=
    { toFun := fun i ↦ ⟨SimplexCategory.mk i.1, Nat.le_of_lt_succ i.2⟩
      invFun := fun X ↦ ⟨X.obj.len, Nat.lt_succ_iff.mpr X.property⟩
      left_inv := by intro i; cases i; rfl
      right_inv := by intro X; cases X; rfl }
  exact Finite.of_equiv (Fin (m + 1)) e

instance truncatedSimplex_hom_finite {m : ℕ} (X Y : SimplexCategory.Truncated m) :
    Finite (X ⟶ Y) := by
  refine Finite.of_injective (fun f ↦ f.hom) ?_
  intro f g h
  exact ObjectProperty.hom_ext _ h

private instance truncatedSimplex_finCategory (m : ℕ) : FinCategory (SimplexCategory.Truncated m)
    where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

private instance structuredArrow_finite (m n : ℕ) :
    Finite (SimplexCategory.Truncated.matchingIndex m n) := by
  let e :
      (Σ X : (SimplexCategory.Truncated m)ᵒᵖ,
        (op ⦋n⦌ ⟶ (SimplexCategory.Truncated.inclusion m).op.obj X)) ≃
        SimplexCategory.Truncated.matchingIndex m n :=
    { toFun := fun p ↦ StructuredArrow.mk p.2
      invFun := fun A ↦ ⟨A.right, A.hom⟩
      left_inv := by intro p; cases p; rfl
      right_inv := by intro A; cases A; rfl }
  exact Finite.of_equiv _ e

private instance structuredArrow_hom_finite (m n : ℕ)
    (A B : SimplexCategory.Truncated.matchingIndex m n) :
    Finite (A ⟶ B) := by
  refine Finite.of_injective (fun f ↦ f.right) ?_
  intro f g h
  exact StructuredArrow.hom_ext f g h

instance (m n : ℕ) : FinCategory (SimplexCategory.Truncated.matchingIndex m n) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

/-- Finite limits in `C` give pointwise right Kan extensions along the inclusion of
`m`-truncated simplices into all simplices. -/
instance simplexTruncatedInclusion_hasPointwiseRightKanExtension
    [HasFiniteLimits C] (m : ℕ) (F : (SimplexCategory.Truncated m)ᵒᵖ ⥤ C) :
    (SimplexCategory.Truncated.inclusion m).op.HasPointwiseRightKanExtension F := by
  intro Y
  cases Y with
  | op Y =>
      change HasLimit
        (StructuredArrow.proj (op Y) (SimplexCategory.Truncated.inclusion m).op ⋙ F)
      letI : FinCategory (SimplexCategory.Truncated.matchingIndex m Y.len) := inferInstance
      infer_instance

section

variable [HasFiniteLimits C] (m n : ℕ) (U : SimplicialObject.Truncated C m)

/- The owner for the coskeleton limit description is `Functor.ranObjObjIsoLimit`. -/
recall Functor.ranObjObjIsoLimit

/- Lemma 14.19.2: if `C` has finite limits, then the `m`-coskeleton of an
`m`-truncated simplicial object exists, and its degree-`n` term is canonically the limit of the
diagram of all maps `[k] ⟶ [n]` with `k ≤ m`. This is the direct specialization of the canonical
owner `Functor.ranObjObjIsoLimit`. -/
#check ((SimplexCategory.Truncated.inclusion m).op.ranObjObjIsoLimit U (op ⦋n⦌) :
  ((Truncated.cosk m).obj U) _⦋n⦌ ≅
    limit (StructuredArrow.proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion m).op ⋙ U))

variable (f : SimplexCategory.Truncated.matchingIndex m n)

/- Its projection formula is the companion owner theorem `Functor.ranObjObjIsoLimit_hom_π`. -/
recall Functor.ranObjObjIsoLimit_hom_π

/- Companion recall: the projection formula for the limit description of `cosk_m U` is exactly
the specialized owner theorem `Functor.ranObjObjIsoLimit_hom_π`. -/
#check ((SimplexCategory.Truncated.inclusion m).op.ranObjObjIsoLimit_hom_π U (op ⦋n⦌) f :
  ((SimplexCategory.Truncated.inclusion m).op.ranObjObjIsoLimit U (op ⦋n⦌)).hom ≫
      limit.π _ f =
    ((Truncated.cosk m).obj U).map f.hom ≫
      ((SimplexCategory.Truncated.inclusion m).op.ranCounit.app U).app f.right)

end

end CategoryTheory
