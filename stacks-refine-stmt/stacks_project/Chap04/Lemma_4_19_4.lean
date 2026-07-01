import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import stacks_project.Chap04.Definition_4_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.FunctorToTypes

universe w v u

noncomputable section

namespace CategoryTheory.Limits

variable {I : Type u} [Category.{v} I] [Small.{w} I]

/-
Domain-style sampling for Lemma 4.19.4:
- source-facing hypothesis: every pair of objects admits a common successor
- sampled owner declarations in this domain:
  - `CategoryTheory.Limits.prodComparison`
  - `CategoryTheory.IsFilteredOrEmpty.cocone_objs`
  - `CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types`
- primitive data: a pair of colimit representatives together with the source-level
  common-successor hypothesis
- derived API: the resulting surjectivity bridge for `prodComparison`
- best owner abstraction: the comparison morphism `prodComparison` itself; the source-facing
  theorem below is the weak bridge from common successors to surjectivity, while the stronger
  finite-limit preservation owner is only background because it proves more than this lemma needs
- target layer here: `bridge/view`, namely the surjectivity statement for `prodComparison`,
  with a thin `IsFilteredOrEmpty` corollary through the owner field
  `CategoryTheory.IsFilteredOrEmpty.cocone_objs`
-/

/-
Source/core/bridge triage for Lemma 4.19.4:
- `source-facing`: the explicit common-successor hypothesis on the index category
- `core/canonical`: the binary-product comparison morphism `prodComparison colim M N`
- `bridge/view`: surjectivity of that comparison under the weaker source hypothesis, plus the
  `IsFilteredOrEmpty` specialization obtained from `IsFilteredOrEmpty.cocone_objs`
-/

/-- Applied form of the first projection formula for the colimit binary-product comparison in
`Type`. -/
-- Proof sketch: compose `prodComparison` with the first projection from the binary product
-- isomorphism, then rewrite using the canonical `prodComparison_fst` compatibility together with
-- the explicit `Type` colimit map formula.
theorem prodComparison_colim_ι_fst (M N : I ⥤ Type w) (k : I) (x : (M ⨯ N).obj k) :
    ((Types.binaryProductIso (colimit M) (colimit N)).hom
      (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).1 =
      colimit.ι M k ((prod.fst : M ⨯ N ⟶ M).app k x) := sorry

/-- Applied form of the second projection formula for the colimit binary-product comparison in
`Type`. -/
-- Proof sketch: this is the second-projection analogue of
-- `prodComparison_colim_ι_fst`, using `prodComparison_snd` and the `Type` colimit map formula for
-- `prod.snd`.
theorem prodComparison_colim_ι_snd (M N : I ⥤ Type w) (k : I) (x : (M ⨯ N).obj k) :
    ((Types.binaryProductIso (colimit M) (colimit N)).hom
      (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).2 =
      colimit.ι N k ((prod.snd : M ⨯ N ⟶ N).app k x) := sorry

-- Proof sketch: represent the two coordinates of a point in
-- `colimit M × colimit N` at possibly different stages, move both representatives to a common
-- successor using the source hypothesis, and then use the induced element of `(M ⨯ N).obj k` to
-- build a preimage under `prodComparison`.
/-- Lemma 4.19.4 (1): if every pair of objects in the index category admits a common successor,
then the canonical comparison map
`colimit (M ⨯ N) ⟶ colimit M × colimit N`
is surjective for `Type`-valued diagrams `M` and `N`. -/
theorem prodComparison_colim_surjective_of_commonSuccessor
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (M N : I ⥤ Type w)
    : Function.Surjective (prodComparison colim M N) := sorry

/-- For a filtered-or-empty index category, the common-successor hypothesis is already available
from the owner field `CategoryTheory.IsFilteredOrEmpty.cocone_objs`, so the surjectivity
statement is just the preceding source-facing bridge specialized to that canonical API. -/
-- Proof sketch: apply `prodComparison_colim_surjective_of_commonSuccessor` and obtain the common
-- successor from `IsFilteredOrEmpty.cocone_objs`.
theorem prodComparison_colim_surjective_of_isFilteredOrEmpty [IsFilteredOrEmpty I]
    (M N : I ⥤ Type w) :
    Function.Surjective (prodComparison colim M N) := sorry

-- Proof sketch: take the one-object category attached to a nontrivial group acting on itself by
-- translation; then the colimit of the diagonal action on `G × G` has more than one orbit, while
-- the product of the two quotient colimits is a singleton.
/-- Lemma 4.19.4 (2): even if every pair of objects in the index category admits a common
successor, colimits of `Type`-valued diagrams do not in general commute with finite nonempty
products; in fact, there is already a counterexample for binary products. -/
theorem colimits_of_set_valued_diagrams_need_not_commute_with_binary_products :
    ∃ (J : Type u) (_ : Category.{v} J) (_ : Small.{w} J)
      (_ : ∀ i j : J, ∃ k : J, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
      (F G : J ⥤ Type w),
        ¬ Function.Bijective (prodComparison colim F G) := sorry

end CategoryTheory.Limits
