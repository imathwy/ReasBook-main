import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Construction_22_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_5_4

open CategoryTheory Opposite
open HomotopicalAlgebra
open scoped TensorProduct

noncomputable section

-- Semantic recall via `lean_leansearch` surfaced only generic cohomology-class APIs.
-- Chapter 22 already exposes the source-facing owners
-- `ReducedCohomologyEilenbergMacLaneRepresentation`,
-- `cohomologyOperation_equiv_reducedCohomologyGroupOfRepresentingSpace`,
-- `RepresentedCupProduct`, and `RepresentedCapProduct`, so this item is stated directly on that
-- established surface.

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

variable [CategoryWithCofibrations BasedSpace]
variable [CategoryWithCofibrations BasedCWComplex]
variable [CategoryWithWeakEquivalences BasedCWComplex]

/- Result 22.3.4 (1): the reduced cohomology of the chosen representing space `K(π, q)`
controls natural reduced cohomology operations out of the represented theory via the canonical
equivalence with classes on that chosen `K(π, q)` model. This is exactly the equivalence already
formalized in Theorem 22.5.4, so the source-facing entry here is a labeled recall of that
canonical owner. -/
#check cohomologyOperation_equiv_reducedCohomologyGroupOfRepresentingSpace

/-- Result 22.3.4 (2): a represented cup-product pairing among the chosen `K(π, p)`, `K(ρ, q)`,
and `K(σ, p + q)` models controls the induced product pairing on represented reduced cohomology
through the representability comparison of Theorem 22.2.1. -/
theorem eilenberg_maclane_cohomology_controls_cup_pairings
    {π ρ σ : Type} [AddCommGroup π] [AddCommGroup ρ] [AddCommGroup σ]
    (μ : π →+ ρ →+ σ)
    {p q : ℕ}
    (P : ReducedCohomologyEilenbergMacLaneRepresentation π p)
    (Q : ReducedCohomologyEilenbergMacLaneRepresentation ρ q)
    (S : ReducedCohomologyEilenbergMacLaneRepresentation σ (p + q))
    (cup : RepresentedCupProduct P Q S μ)
    (X : BasedCWComplex)
    (α : representedReducedCohomologyGroup P X)
    (β : representedReducedCohomologyGroup Q X) :
    RepresentedCupProduct.onBasedHomotopyClasses P Q S cup X.1
        (((P.comparison).app (op X)).hom.toFun α)
        (((Q.comparison).app (op X)).hom.toFun β) =
      (((S.comparison).app (op X)).hom.toFun
        (cup.cupProduct X (TensorProduct.tmul ℤ α β))) := by
  simpa [RepresentedCupProduct.onBasedHomotopyClasses] using cup.cupProduct_spec X α β

/-- Result 22.3.4 (3): a represented cap-product pairing among the chosen `K(π, p)`,
`K(σ, p + q)`, and `K(ρ, q)` models controls the induced cap pairing on represented reduced
cohomology through the representability comparison of Theorem 22.2.1. -/
theorem eilenberg_maclane_cohomology_controls_cap_pairings
    {π ρ σ : Type} [AddCommGroup π] [AddCommGroup ρ] [AddCommGroup σ]
    (μ : π →+ ρ →+ σ)
    {p q : ℕ}
    (P : ReducedCohomologyEilenbergMacLaneRepresentation π p)
    (Q : ReducedCohomologyEilenbergMacLaneRepresentation ρ q)
    (S : ReducedCohomologyEilenbergMacLaneRepresentation σ (p + q))
    (cap : RepresentedCapProduct P Q S μ)
    (X : BasedCWComplex)
    (α : representedReducedCohomologyGroup P X)
    (γ : representedReducedCohomologyGroup S X) :
    RepresentedCapProduct.onBasedHomotopyClasses P Q S cap X.1
        (((P.comparison).app (op X)).hom.toFun α)
        (((S.comparison).app (op X)).hom.toFun γ) =
      (((Q.comparison).app (op X)).hom.toFun
        (cap.capProduct X (TensorProduct.tmul ℤ α γ))) := by
  simpa [RepresentedCapProduct.onBasedHomotopyClasses] using cap.capProduct_spec X α γ
