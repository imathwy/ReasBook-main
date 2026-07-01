import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasProducts (Sheaf J AddCommGrpCat)]

/-- The functor sending an abelian sheaf to its degree-`p` cohomology over `U`. -/
private noncomputable abbrev sheafCohomologyAtObjectFunctor (U : C) (p : ℕ) :
    Sheaf J AddCommGrpCat ⥤ AddCommGrpCat :=
  (Sheaf.cohomologyPresheafFunctor J p) ⋙
    (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj (op U)

/-- The canonical map from the cohomology of a product sheaf over `U` to the product of the
corresponding cohomology groups. -/
private noncomputable abbrev sheafProductCohomologyMap
    (U : C) (p : ℕ) {I : Type w} (F : I → Sheaf J AddCommGrpCat) :
    (∏ᶜ F).H' p U ⟶ ∏ᶜ fun i ↦ (F i).H' p U :=
  piComparison (sheafCohomologyAtObjectFunctor U p) F

-- Proof sketch: degree-zero cohomology is evaluation of the sheaf on `U`, and products of
-- sheaves are computed on the underlying presheaves, so the induced product comparison map on
-- sections is an isomorphism.
/-- Lemma 21.12.5 (1): for an object `U` of a site and a family of abelian sheaves
`(\mathcal F_i)`, the canonical map
`H^0(U, \prod_i \mathcal F_i) \to \prod_i H^0(U, \mathcal F_i)` is an isomorphism. -/
theorem sheafProductCohomologyMap_isIso_degree_zero
    (U : C) {I : Type w} (F : I → Sheaf J AddCommGrpCat) :
    IsIso (sheafProductCohomologyMap U 0 F) := sorry

-- Proof sketch: choose a covering on which a class in `H^1(U, \prod_i \mathcal F_i)` vanishes,
-- represent it by a Čech `1`-cocycle, use injectivity of the Čech-to-cohomology map for each
-- factor, and identify the Čech complex of the product sheaf with the product of the Čech
-- complexes so that vanishing of all components forces vanishing of the original class.
/-- Lemma 21.12.5 (2): for an object `U` of a site and a family of abelian sheaves
`(\mathcal F_i)`, the canonical map
`H^1(U, \prod_i \mathcal F_i) \to \prod_i H^1(U, \mathcal F_i)` is injective. -/
theorem sheafProductCohomologyMap_injective_degree_one
    (U : C) {I : Type w} (F : I → Sheaf J AddCommGrpCat) :
    Function.Injective (sheafProductCohomologyMap U 1 F) := sorry

end CategoryTheory
