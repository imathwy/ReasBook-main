import Mathlib
import StacksProject_2024.Chap04.Definition_4_31_2
import StacksProject_2024.Chap04.Lemma_4_31_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

universe v u

namespace CategoryTheory.Limits

noncomputable section

variable {C : Type u} [Category.{v} C]
variable {S : Type u} [Category.{v} S]

variable (G₁ G₂ : C ⥤ S)

local notation "DiagonalPullback" =>
  CategoricalPullback (G₁.prod' G₂) (Functor.diag S)
local notation "IteratedPullback" =>
  (π₁ G₁ G₂) ⊡ (π₂ G₁ G₂)

/- Domain-style sampling for Lemma 4.31.12:
- primary domain: bicategorical `2`-fibre products in `Cat`, expressed through the categorical
  pullback models attached to `(G₁.prod' G₂)` and `Functor.diag S`, together with the canonical
  iterated pullback owner of the induced cospan `π₁ G₁ G₂, π₂ G₁ G₂`;
- sampled owner-level declarations:
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`,
  `CategoricalPullback.CatCommSqOver`,
  `CatCommSqOver.toFunctorToCategoricalPullback`,
  `CatCommSqOver.toBicategoricalSquare`,
  `symmetricTwoFibreProductComparison`;
- best owner abstraction: the source-facing square is still
  `BicategoricalTwoCommutativeSquare (G₁.prod' G₂).toCatHom (Functor.diag S).toCatHom`, with the
  `2`-fibre product condition expressed by `Bicategory.IsFinal`, but the target owner for the
  iterated pullback is `IteratedPullback = (π₁ G₁ G₂) ⊡ (π₂ G₁ G₂)`;
- `CategoricalPullback` is the canonical owner abstraction, `IteratedPullback` is the core owner
  for the iterated `2`-fibre product, and the textbook nested model
  `(C ×[S] C) ×[C × C] C` is only a bridge/view equivalent to it via Remark `4.31.5`.

Primitive-vs-derived split:
- primitive data: the canonical diagonal square
  `Q : CatCommSqOver (G₁.prod' G₂) (Functor.diag S) DiagonalPullback`,
  the induced square over `G₁` and `G₂`, and later an arbitrary source square
  `P : CatCommSqOver (G₁.prod' G₂) (Functor.diag S) C'`;
- derived API: the induced functor `DiagonalPullback ⥤ G₁ ⊡ G₂`, the resulting diagonal square
  over `π₁ G₁ G₂` and `π₂ G₁ G₂`, and the comparison/equivalence statements landing in the owner
  `IteratedPullback`. -/

/- Source/core/bridge triage for Lemma 4.31.12:
- `source-facing`: the displayed square over `(G₁.prod' G₂)` and `Δ_S`, viewed as a
  bicategorical square in `Cat`;
- `core/canonical`: `Bicategory.IsFinal` of that bicategorical square, with target owner
  `IteratedPullback`;
- `bridge/view`: `CatCommSqOver.toFunctorToCategoricalPullback`, together with Remark `4.31.5`
  identifying the textbook nested model `(C ×[S] C) ×[C × C] C` with `IteratedPullback`. -/

private abbrev diagonalSourceSquare :
    CatCommSqOver (G₁.prod' G₂) (Functor.diag S) DiagonalPullback :=
  (toCatCommSqOver (G₁.prod' G₂) (Functor.diag S) DiagonalPullback).obj (𝟭 _)

private abbrev diagonalFirstPullbackSquare :
    CatCommSqOver G₁ G₂ DiagonalPullback :=
  let Q := diagonalSourceSquare G₁ G₂
  { fst := Q.fst
    snd := Q.fst
    iso :=
      (Functor.isoWhiskerLeft _ (Functor.prod'CompFst G₁ G₂).symm ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight Q.iso (Prod.fst S S) ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.prod'CompFst (𝟭 S) (𝟭 S)) ≪≫
          Functor.rightUnitor _) ≪≫
        (Functor.isoWhiskerLeft _ (Functor.prod'CompSnd G₁ G₂).symm ≪≫
            (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight Q.iso (Prod.snd S S) ≪≫
            Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (Functor.prod'CompSnd (𝟭 S) (𝟭 S)) ≪≫
            Functor.rightUnitor _).symm }

private abbrev diagonalFirstPullbackComparison :
    DiagonalPullback ⥤ G₁ ⊡ G₂ :=
  (toFunctorToCategoricalPullback G₁ G₂ DiagonalPullback).obj
    (diagonalFirstPullbackSquare G₁ G₂)

private abbrev diagonalIteratedPullbackSquare :
    CatCommSqOver (π₁ G₁ G₂) (π₂ G₁ G₂) DiagonalPullback where
  fst := diagonalFirstPullbackComparison G₁ G₂
  snd := diagonalFirstPullbackComparison G₁ G₂
  iso :=
    NatIso.ofComponents
      (fun X ↦ by
        change ((diagonalFirstPullbackComparison G₁ G₂).obj X).fst ≅
          ((diagonalFirstPullbackComparison G₁ G₂).obj X).snd
        exact Iso.refl _)
      (fun {_ _} f ↦ by
        simp [diagonalFirstPullbackComparison, diagonalFirstPullbackSquare])

/-- The canonical comparison functor from the diagonal pullback model
`C ×[(S × S)] S` of Lemma 4.31.12 to the canonical iterated `2`-fibre-product owner
`IteratedPullback = (π₁ G₁ G₂) ⊡ (π₂ G₁ G₂)`, which is equivalent to the textbook nested model
`(C ×[S] C) ×[C × C] C` by Remark 4.31.5. -/
abbrev categorical_pullback_diagonal_model_comparison :
    DiagonalPullback ⥤ IteratedPullback :=
  (toFunctorToCategoricalPullback (π₁ G₁ G₂) (π₂ G₁ G₂) DiagonalPullback).obj
    (diagonalIteratedPullbackSquare G₁ G₂)

-- Proof sketch: this is the omitted construction in the Stacks proof. The diagonal pullback model
-- `C ×[(S × S)] S` maps canonically to the iterated `2`-fibre-product owner
-- `(π₁ G₁ G₂) ⊡ (π₂ G₁ G₂)`, which in turn recovers the textbook nested model
-- `(C ×[S] C) ×[C × C] C` via Remark `4.31.5`.
/-- The model-comparison functor of Lemma 4.31.12 is an equivalence. -/
noncomputable instance categorical_pullback_diagonal_model_comparison_isEquivalence :
    (categorical_pullback_diagonal_model_comparison G₁ G₂).IsEquivalence := sorry

variable {C' : Type u} [Category.{v} C']
variable (P : CatCommSqOver (G₁.prod' G₂) (Functor.diag S) C')

/-- The comparison functor from a `2`-commutative square over `(G₁.prod' G₂)` and `Δ_S`
to the canonical iterated `2`-fibre product of Lemma 4.31.12. -/
abbrev categorical_pullback_diagonal_comparison
    : C' ⥤ IteratedPullback :=
  (toFunctorToCategoricalPullback (G₁.prod' G₂) (Functor.diag S) C').obj P ⋙
    categorical_pullback_diagonal_model_comparison G₁ G₂

/-- The canonical comparison functor attached to a `2`-fibre product square over
`(G₁.prod' G₂)` and `Δ_S`, expressed through the chapter's owner predicate
`Bicategory.IsFinal`, is an equivalence. -/
noncomputable instance
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    (categorical_pullback_diagonal_comparison G₁ G₂ P).IsEquivalence := by
  infer_instance

/-- Lemma 4.31.12: if
`\mathcal{C}' \to \mathcal{S} \leftarrow \mathcal{C}`
is a `2`-fibre product square for `(G₁.prod' G₂)` and `Δ_S`, then there is a canonical
equivalence to the owner-level iterated `2`-fibre product
`C' ≌ (π₁ G₁ G₂) ⊡ (π₂ G₁ G₂)`, canonically equivalent to the textbook nested model
`(C ×[S] C) ×[C × C] C` by Remark 4.31.5. -/
noncomputable def categorical_pullback_diagonal_square_equivalence
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    C' ≌ IteratedPullback :=
  (categorical_pullback_diagonal_comparison G₁ G₂ P).asEquivalence

/-- The forward functor of `categorical_pullback_diagonal_square_equivalence` is the canonical
comparison functor to the iterated `2`-fibre product owner. -/
-- Proof sketch: unfold `categorical_pullback_diagonal_square_equivalence`; it is defined by
-- `Functor.asEquivalence` on `categorical_pullback_diagonal_comparison G₁ G₂ P`, so the forward
-- functor is exactly that comparison functor.
theorem categorical_pullback_diagonal_square_equivalence_functor
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    (categorical_pullback_diagonal_square_equivalence G₁ G₂ P).functor =
      categorical_pullback_diagonal_comparison G₁ G₂ P := sorry

end

end CategoryTheory.Limits
