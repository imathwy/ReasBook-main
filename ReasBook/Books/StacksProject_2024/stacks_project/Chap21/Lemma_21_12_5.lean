import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasProducts (Sheaf J AddCommGrpCat)]

/- Domain-style sampling for Lemma 21.12.5:
- primary domain: objectwise sheaf cohomology on a site and the canonical comparison morphism from
  cohomology of a product sheaf to the product of the cohomology groups;
- sampled owner declarations:
  `Sheaf.cohomologyPresheafFunctor`,
  `Sheaf.H'`,
  `evaluation`,
  `piComparison`;
- best owner abstraction: the canonical comparison morphism is already
  `piComparison (Sheaf.cohomologyPresheafFunctor J p ⋙ (evaluation _ _).obj (op U)) F`, so this
  file should state the degree-`0` and degree-`1` results directly for that owner instead of
  keeping parallel local abbreviations for the functor and comparison map;
- primitive data: an object `U : C`, a degree `p`, and a family of abelian sheaves `F`;
- derived API here: the degree-specific assertions that this canonical comparison morphism is an
  isomorphism for `p = 0` and injective for `p = 1`.

Source/core/bridge triage:
- `source-facing`: the Stacks statements about products in sheaf cohomology in degrees `0` and `1`;
- `core/canonical`: `Sheaf.cohomologyPresheafFunctor`, `evaluation`, and `piComparison`;
- `bridge/view`: the two named theorem specializations below. -/

-- Proof sketch: degree-zero cohomology is evaluation of the sheaf on `U`, and products of
-- sheaves are computed on the underlying presheaves, so the induced product comparison map on
-- sections is an isomorphism.
/-- Lemma 21.12.5 (1): for an object `U` of a site and a family of abelian sheaves `(𝓕 i)`, the
canonical map `H^0(U, ∏ i, 𝓕 i) ⟶ ∏ i, H^0(U, 𝓕 i)` is an isomorphism. -/
@[stacks 060L]
instance sheafProductCohomologyMap_isIso_degree_zero
    (U : C) {I : Type w} (F : I → Sheaf J AddCommGrpCat) :
    IsIso
      (piComparison
        (Sheaf.cohomologyPresheafFunctor J 0 ⋙
          (evaluation Cᵒᵖ AddCommGrpCat).obj (op U))
        F) := sorry

-- Proof sketch: choose a covering on which a class in `H^1(U, ∏ i, 𝓕 i)` vanishes,
-- represent it by a Čech `1`-cocycle, use injectivity of the Čech-to-cohomology map for each
-- factor, and identify the Čech complex of the product sheaf with the product of the Čech
-- complexes so that vanishing of all components forces vanishing of the original class.
/-- Lemma 21.12.5 (2): for an object `U` of a site and a family of abelian sheaves `(𝓕 i)`, the
canonical map `H^1(U, ∏ i, 𝓕 i) ⟶ ∏ i, H^1(U, 𝓕 i)` is injective. -/
@[stacks 060L]
theorem sheafProductCohomologyMap_injective_degree_one
    (U : C) {I : Type w} (F : I → Sheaf J AddCommGrpCat) :
    Function.Injective
      (piComparison
        (Sheaf.cohomologyPresheafFunctor J 1 ⋙
          (evaluation Cᵒᵖ AddCommGrpCat).obj (op U))
        F) := sorry

end CategoryTheory
