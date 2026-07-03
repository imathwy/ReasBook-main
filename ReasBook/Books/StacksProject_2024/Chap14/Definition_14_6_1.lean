import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable {U V : SimplicialObject C}
variable [∀ Δ : SimplexCategoryᵒᵖ, HasBinaryProduct (U.obj Δ) (V.obj Δ)]

/-
Domain-style sampling for Definition 14.6.1:
- primary domain: binary products in the functor category `SimplicialObject C`;
- sampled owner declarations:
  `CategoryTheory.Limits.HasBinaryProduct`,
  `CategoryTheory.Limits.functorCategoryHasLimit`,
  `CategoryTheory.Limits.evaluation_preservesLimit`,
  `CategoryTheory.Limits.PreservesLimitPair.iso`;
- best owner abstraction:
  - `source-facing`: the product simplicial object whose `Δ`-simplices are
    `U.obj Δ ⨯ V.obj Δ`;
  - `core/canonical`: the binary product `U ⨯ V` in the functor category;
  - `bridge/view`: the evaluation comparison
    `PreservesLimitPair.iso ((evaluation _ _).obj Δ) U V`.
- primitive data: only the pointwise hypotheses
  `[∀ Δ, HasBinaryProduct (U.obj Δ) (V.obj Δ)]`;
- derived API: the canonical functor-category instance `HasBinaryProduct U V`, the product object
  `U ⨯ V`, and the degreewise identification supplied by evaluation preserving limits.

Source/core/bridge triage:
- `source-facing`: degreewise products assemble to the product simplicial object.
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

/- Bridge recall: the degreewise identification between the evaluated simplicial product and the
pointwise product is the canonical isomorphism `PreservesLimitPair.iso`. -/
recall PreservesLimitPair.iso

local instance pointwisePairHasLimit (Δ : SimplexCategoryᵒᵖ) :
    HasLimit ((pair U V).flip.obj Δ) := by
  let e : ((pair U V).flip.obj Δ) ≅ pair (U.obj Δ) (V.obj Δ) := diagramIsoPair _
  letI : HasLimit (pair (U.obj Δ) (V.obj Δ)) := inferInstance
  exact hasLimit_of_iso e.symm

local instance : HasBinaryProduct U V := functorCategoryHasLimit (pair U V)

/- Definition 14.6.1: assuming the pointwise binary products `U.obj Δ ⨯ V.obj Δ` exist, the
canonical owner is the functor-category instance `HasBinaryProduct U V`. -/
#check (inferInstance : HasBinaryProduct U V)

/- Consequently the product simplicial object is the canonical binary product `U ⨯ V` in
`SimplicialObject C`, with degreewise terms identified by evaluation preserving limits in the
functor category. -/
#check (U ⨯ V : SimplicialObject C)

/- Evaluating the simplicial product at `Δ` yields the corresponding degreewise product via the
canonical comparison isomorphism
`PreservesLimitPair.iso ((evaluation _ _).obj Δ) U V`. -/
example (Δ : SimplexCategoryᵒᵖ) :
    (U ⨯ V).obj Δ ≅ U.obj Δ ⨯ V.obj Δ :=
  PreservesLimitPair.iso ((evaluation _ _).obj Δ) U V

/- The first projection identity for the evaluation comparison is the canonical specialization of
`prodComparison_fst` together with `PreservesLimitPair.iso_hom`. -/
example (Δ : SimplexCategoryᵒᵖ) :
    (PreservesLimitPair.iso ((evaluation _ _).obj Δ) U V).hom ≫ prod.fst =
      (prod.fst : U ⨯ V ⟶ U).app Δ := by
  simpa [PreservesLimitPair.iso_hom] using
    (prodComparison_fst ((evaluation _ _).obj Δ) U V)

/- The second projection identity is the corresponding specialization of `prodComparison_snd`. -/
example (Δ : SimplexCategoryᵒᵖ) :
    (PreservesLimitPair.iso ((evaluation _ _).obj Δ) U V).hom ≫ prod.snd =
      (prod.snd : U ⨯ V ⟶ V).app Δ := by
  simpa [PreservesLimitPair.iso_hom] using
    (prodComparison_snd ((evaluation _ _).obj Δ) U V)

/- Under the degreewise product identifications, the simplicial structure map of `U ⨯ V` is the
canonical square coming from `prodComparison_natural_of_natTrans`. -/
example {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    CommSq
      ((U ⨯ V).map f)
      (PreservesLimitPair.iso ((evaluation _ _).obj Δ) U V).hom
      (PreservesLimitPair.iso ((evaluation _ _).obj Δ') U V).hom
      (prod.map (U.map f) (V.map f)) := by
  refine ⟨?_⟩
  simpa [PreservesLimitPair.iso_hom] using
    (prodComparison_natural_of_natTrans ((evaluation _ _).map f))

end CategoryTheory.SimplicialObject
