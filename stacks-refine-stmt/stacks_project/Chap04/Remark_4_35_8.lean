import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap04.Example_4_31_3
import stacks_project.Chap04.Lemma_4_31_11
import stacks_project.Chap04.Lemma_4_35_7

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open CategoryOver
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {X Y Z : CategoryOver C}

/- Domain-style sampling for Remark 4.35.8:
- primary domain: comparison between the explicit `2`-fibre product in `Cat/C` and the standard
  categorical pullback of the underlying functors;
- sampled owner-level declarations:
  `CategoryOver.explicitTwoFibreProductSquareOver`,
  `explicitTwoFibreProductComparisonIsoOver`,
  `CategoricalPullback.CatCommSqOver`,
  `CatCommSqOver.toFunctorToCategoricalPullback`;
- best owner abstraction: the source-facing owner is the over-`C` square
  `explicitTwoFibreProductSquareOver F G`; the comparison functor in this remark is derived by
  forgetting the over-`C` structure and applying
  `CatCommSqOver.toFunctorToCategoricalPullback`;
- primitive data: owned upstream by `explicitTwoFibreProductSquareOver F G`;
- derived API: the comparison functor and the resulting equivalence with the standard categorical
  pullback.

Source/core/bridge triage:
- `source-facing`: the comparison equivalence of Remark 4.35.8;
- `core/canonical`: `explicitTwoFibreProductSquareOver F G`;
- `bridge/view`: the forgotten categorical square and its induced functor to
  `F.toFunctor ⊡ G.toFunctor`. -/

/- Lemma 4.35.7 supplies the fibred-in-groupoids closure statement for the explicit
`2`-fibre-product apex; the comparison equivalence below is the separate categorical consequence
of the owner square `explicitTwoFibreProductSquareOver F G`. -/
#check CategoryTheory.explicitTwoFibreProductProjection_isFibredInGroupoids

/-- Remark 4.35.8: for `1`-morphisms of categories fibred in groupoids over `C`, the explicit
`2`-fibre product from Lemma 4.35.7 is canonically equivalent to the standard `2`-fibre product
category of Example 4.31.3. This comparison is already a pure `Cat`-level consequence of the
canonical owner square `explicitTwoFibreProductSquareOver F G`, so it applies a fortiori in the
fibred-in-groupoids setting of Lemma 4.35.7. -/
noncomputable def explicitTwoFibreProduct_equiv_categoricalPullback
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (explicitTwoFibreProduct F G).obj ≌ F.toFunctor ⊡ G.toFunctor :=
  let _ : Bicategory.IsFinal ((explicitTwoFibreProductSquareOver F G).toBicategoricalSquare) :=
    explicitTwoFibreProduct_isTwoFibreProduct F G
  ((toFunctorToCategoricalPullback F.toFunctor G.toFunctor (explicitTwoFibreProduct F G).obj).obj
    (explicitTwoFibreProductSquareOver F G)).asEquivalence

/-- The forward functor of `explicitTwoFibreProduct_equiv_categoricalPullback` is the canonical
comparison functor from the explicit `2`-fibre product square to the standard categorical
pullback. -/
-- Proof sketch: unfold `explicitTwoFibreProduct_equiv_categoricalPullback`; it is defined by
-- applying `Functor.asEquivalence` to the comparison functor induced by
-- `explicitTwoFibreProductSquareOver F G`.
theorem explicitTwoFibreProduct_equiv_categoricalPullback_functor
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (explicitTwoFibreProduct_equiv_categoricalPullback F G).functor =
      (toFunctorToCategoricalPullback F.toFunctor G.toFunctor
        (explicitTwoFibreProduct F G).obj).obj (explicitTwoFibreProductSquareOver F G) := sorry

end CategoryTheory
