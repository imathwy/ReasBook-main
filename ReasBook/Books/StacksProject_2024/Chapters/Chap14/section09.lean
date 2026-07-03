import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_9_1 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {U V : CosimplicialObject C}
variable [∀ n : SimplexCategory, HasBinaryProduct (U.obj n) (V.obj n)]

/- Domain-style sampling for Definition 14.9.1:
- primary domain: binary products in the functor category `CosimplicialObject C`;
- sampled owner declarations:
  `CategoryTheory.Limits.HasBinaryProduct`,
  `CategoryTheory.Limits.functorCategoryHasLimit`,
  `CategoryTheory.Limits.evaluation_preservesLimit`,
  `CategoryTheory.Limits.PreservesLimitPair.iso`;
- best owner abstraction:
  - `source-facing`: the product cosimplicial object whose values are the degreewise products
    `U.obj n ⨯ V.obj n`;
  - `core/canonical`: the binary product `U ⨯ V` in the functor category;
  - `bridge/view`: the evaluation comparison
    `PreservesLimitPair.iso ((evaluation _ _).obj n) U V`.
- primitive data: only the pointwise hypotheses
  `[∀ n, HasBinaryProduct (U.obj n) (V.obj n)]`;
- derived API: the canonical functor-category instance `HasBinaryProduct U V`, the product object
  `U ⨯ V`, and the degreewise identification supplied by evaluation preserving limits.

Source/core/bridge triage:
- `source-facing`: degreewise products assemble to the product cosimplicial object.
- `core/canonical`: the generic functor-category limit owner.
- `bridge/view`: the objectwise comparison isomorphism from evaluation.

Under the pointwise hypotheses, the public owner remains the canonical functor-category instance
`HasBinaryProduct U V`. The only extra implementation data needed here is the internal pointwise
limit instance for the pair diagram at each simplex, after which the source-facing checks can use
the ordinary product and comparison-isomorphism APIs directly. -/

/- Owner recall: the pointwise binary-product hypotheses assemble into the canonical
functor-category limit instance `functorCategoryHasLimit`. -/
recall functorCategoryHasLimit

/- Owner recall: evaluation at a simplex preserves this binary product via the canonical
functor-category theorem `evaluation_preservesLimit`. -/
recall evaluation_preservesLimit

/- Bridge recall: the degreewise identification between the evaluated cosimplicial product and the
pointwise product is the canonical isomorphism `PreservesLimitPair.iso`. -/
recall PreservesLimitPair.iso

local instance pointwisePairHasLimit (n : SimplexCategory) :
    HasLimit ((pair U V).flip.obj n) := by
  let e : ((pair U V).flip.obj n) ≅ pair (U.obj n) (V.obj n) := diagramIsoPair _
  letI : HasLimit (pair (U.obj n) (V.obj n)) := inferInstance
  exact hasLimit_of_iso e.symm

noncomputable instance : HasBinaryProduct U V :=
  @functorCategoryHasLimit _ _ _ _ _ _ (pair U V) pointwisePairHasLimit

/- Definition 14.9.1: assuming the pointwise binary products `U.obj n ⨯ V.obj n` exist, the
canonical owner is the functor-category instance `HasBinaryProduct U V`. -/
#check (inferInstance : HasBinaryProduct U V)

/- Consequently the product cosimplicial object is the canonical binary product `U ⨯ V` in
`CosimplicialObject C`, with degreewise terms identified by evaluation preserving limits in the
functor category. -/
#check (U ⨯ V : CosimplicialObject C)

/- Evaluating the cosimplicial product at `n` yields the corresponding degreewise product via the
canonical comparison isomorphism
`PreservesLimitPair.iso ((evaluation _ _).obj n) U V`. -/
example (n : SimplexCategory) :
    (U ⨯ V).obj n ≅ U.obj n ⨯ V.obj n := by
  exact @PreservesLimitPair.iso _ _ _ _ ((evaluation _ _).obj n) U V
    (@functorCategoryHasLimit _ _ _ _ _ _ (pair U V) pointwisePairHasLimit)
    (by
      change HasBinaryProduct (U.obj n) (V.obj n)
      infer_instance)
    (@evaluation_preservesLimit _ _ _ _ _ _ (pair U V) pointwisePairHasLimit n)

end CategoryTheory.CosimplicialObject

/-! ### Lemma_14_9_2 (from Chap14) -/
universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {U V W : CosimplicialObject C} [HasBinaryProduct U V]

/- Domain-style sampling for Lemma 14.9.2:
- primary domain: binary products in the functor category `CosimplicialObject C`;
- sampled owner declarations:
  `prodIsProd`,
  `prod.lift`,
  `prod.lift'`,
  `prod.hom_ext`;
- best owner abstraction: the canonical binary-product limit witness `prodIsProd U V`;
- primitive data: only the cosimplicial objects `U`, `V`, `W` and the chosen binary product
  `U ⨯ V`;
- derived API: the canonical lift `prod.lift`, its projection formulas `prod.lift_fst`,
  `prod.lift_snd`, the packaged lift `prod.lift'`, and uniqueness via `prod.hom_ext`.

Source/core/bridge triage:
- `source-facing`: morphisms `W ⟶ U ⨯ V` are exactly pairs of morphisms `W ⟶ U` and `W ⟶ V`;
- `core/canonical`: `prodIsProd U V`;
- `bridge/view`: the cosimplicial-object specialization of the generic binary-product universal
  property.

This file carries no cosimplicial-specific primitive product data, so the correct refinement is to
reuse the generic product owner directly rather than define a parallel cosimplicial-object
equivalence. -/

/- Lemma 14.9.2: for cosimplicial objects, the universal property of `U ⨯ V` is the canonical
binary-product owner `prodIsProd U V`. -/
recall prodIsProd

/- The map induced by a pair of morphisms into the two factors is the canonical product lift
`prod.lift`. -/
recall prod.lift

/- The first projection formula for that lift is the canonical lemma `prod.lift_fst`. -/
recall prod.lift_fst

/- The second projection formula for that lift is the canonical lemma `prod.lift_snd`. -/
recall prod.lift_snd

/- The packaged source-facing lift with both projection identities is `prod.lift'`. -/
recall prod.lift'

/- Uniqueness of a morphism into the product is the canonical extensionality lemma
`prod.hom_ext`. -/
recall prod.hom_ext

end CategoryTheory.Limits
