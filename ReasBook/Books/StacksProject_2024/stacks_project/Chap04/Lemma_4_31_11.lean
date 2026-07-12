import Mathlib
import StacksProject_2024.Chap04.Definition_4_31_2
import StacksProject_2024.Chap04.Lemma_4_31_6
import StacksProject_2024.Chap04.Remark_4_31_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory.Limits

open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

universe v u

variable {A : Type u} [Category.{v} A]
variable {B : Type u} [Category.{v} B]
variable {S : Type u} [Category.{v} S]

/- Domain-style sampling for Lemma 4.31.11:
- primary domain: bicategorical `2`-fibre products in `Cat`, presented through categorical
  pullbacks of functors;
- owner abstractions:
  `BicategoricalTwoCommutativeSquare` and `Bicategory.IsFinal` from Definitions `4.31.2`
  and `4.31.1`,
  `CategoricalPullback.CatCommSqOver` with
  `CatCommSqOver.toFunctorToCategoricalPullback` and
  `CatCommSqOver.toBicategoricalSquare` as the categorical bridge/view API, and
  `symmetricTwoFibreProductComparison` from Remark `4.31.5` as the owner-level comparison from
  the diagonal pullback model to the ordinary pullback model.

Primitive-vs-derived split:
- primitive data: a square `P : CatCommSqOver (G₁.prod G₂) (Functor.diag S) X`;
- derived API: the associated bicategorical square in `Cat`, the comparison functor to
  `A ×[S] B`, and the resulting equivalence object obtained from that comparison functor.

Source/core/bridge triage:
- `source-facing`: the displayed `2`-commutative square over `G₁ × G₂` and `Δ_S`;
- `core/canonical`: `Bicategory.IsFinal` of the associated object of
  `BicategoricalTwoCommutativeSquare (G₁.prod G₂).toCatHom (Functor.diag S).toCatHom`;
- `bridge/view`: `CatCommSqOver.toFunctorToCategoricalPullback` and
  `symmetricTwoFibreProductComparison`. -/

noncomputable section

variable (G₁ : A ⥤ S) (G₂ : B ⥤ S)
variable {X : Type u} [Category.{v} X]
variable (P : CatCommSqOver (G₁.prod G₂) (Functor.diag S) X)

/-- The owner-level `2`-fibre product condition on a categorical commutative square upgrades the
canonical comparison functor to the categorical pullback model to an equivalence. This is the
generic `Cat`-level bridge used by the later pullback comparison lemmas. -/
noncomputable instance
    {A' : Type u} [Category.{v} A']
    {B' : Type u} [Category.{v} B']
    {C' : Type u} [Category.{v} C']
    {X' : Type u} [Category.{v} X']
    {F : A' ⥤ C'} {G : B' ⥤ C'}
    (Q : CatCommSqOver F G X')
    [Bicategory.IsFinal Q.toBicategoricalSquare] :
    ((toFunctorToCategoricalPullback F G X').obj Q).IsEquivalence := sorry

/-- The source-facing comparison functor of Lemma 4.31.11 from a square over `G₁ × G₂` and `Δ_S`
to the ordinary pullback model `A ×[S] B`. -/
abbrev two_fibre_product_comparison : X ⥤ G₁ ⊡ G₂ :=
  (toFunctorToCategoricalPullback (G₁.prod G₂) (Functor.diag S) X).obj P ⋙
    symmetricTwoFibreProductComparison G₁ G₂

/-- The canonical comparison functor attached to a `2`-fibre product square over `G₁ × G₂` and
`Δ_S`, expressed through the chapter's owner predicate `Bicategory.IsFinal`, is an equivalence.
It is the composite of the owner-level comparison functor from `P` to the diagonal pullback model
with the canonical model comparison `symmetricTwoFibreProductComparison G₁ G₂`. -/
noncomputable instance
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    (two_fibre_product_comparison G₁ G₂ P).IsEquivalence :=
  inferInstance

/-- Lemma 4.31.11: if `P` is a `2`-fibre product square over `G₁ × G₂` and `Δ_S`, then `X` is
canonically equivalent to the ordinary pullback category `A ×[S] B`. This formalizes the
canonical isomorphism of the source statement in the bicategorical `Cat` setting. -/
noncomputable def two_fibre_product_square_equivalence
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    X ≌ G₁ ⊡ G₂ :=
  (two_fibre_product_comparison G₁ G₂ P).asEquivalence

/-- The functor underlying `two_fibre_product_square_equivalence` is the canonical comparison
functor `two_fibre_product_comparison`. -/
-- Proof sketch: unfold `two_fibre_product_square_equivalence`; it is defined by applying
-- `Functor.asEquivalence` to `two_fibre_product_comparison`.
theorem two_fibre_product_square_equivalence_functor
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    (two_fibre_product_square_equivalence G₁ G₂ P).functor =
      two_fibre_product_comparison G₁ G₂ P := sorry

end

end CategoryTheory.Limits
