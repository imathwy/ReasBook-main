import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_5_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_2_2

open CategoryTheory Opposite
open HomotopicalAlgebra

noncomputable section

universe u v w

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "BasedCWComplex" =>
  ObjectProperty.FullSubcategory IsBasedCWComplex

-- Chapter 22 already exposes the representing-space equivalence for cohomology operations, while
-- Chapter 23 exposes evaluation on the universal bundle and its bijectivity for characteristic
-- classes. This remark is therefore best kept as a labeled recall block comparing those canonical
-- owners directly.

section

variable [CategoryWithCofibrations BasedSpace]
variable [CategoryWithCofibrations BasedCWComplex]
variable [CategoryWithWeakEquivalences BasedCWComplex]
variable {π : Type} [AddCommGroup π] {q n : ℕ}
variable (R : ReducedCohomologyEilenbergMacLaneRepresentation π q)
variable (E : BundledReducedCohomologyTheory R.setup)

variable {k : ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}}
variable {BO : Type u} [TopologicalSpace BO]
variable (γ : BO → Type v)
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
variable [∀ b, TopologicalSpace (γ b)]
variable [FiberBundle (Fin n → ℝ) γ]
variable [∀ b, AddCommGroup (γ b)]
variable [∀ b, Module ℝ (γ b)]
variable [RealPlaneBundleClassifyingSpace n BO γ]
variable [(k q).rightOp.IsHomotopyInvariant]

/- Remark 23.2.3. Characteristic classes are formally analogous to cohomology operations. In the
Chapter 22 API, cohomology operations are represented by cohomology classes on `K(π, q)` via
`cohomologyOperation_equiv_reducedCohomologyGroupOfRepresentingSpace`; in the Chapter 23 API,
characteristic classes are represented by cohomology classes on the universal bundle over a fully
classifying space `BO` via `characteristicClassEvalOnUniversalBundle_bijective`. Thus `BO(n)`
plays the representing role for characteristic classes. -/
#check (cohomologyOperation_equiv_reducedCohomologyGroupOfRepresentingSpace R E n :
    cohomologyOperation R.setup R.theory.cohomology E.cohomology (q : ℤ) (n : ℤ) ≃
      reducedCohomologyGroupOfRepresentingSpace R E n)
#check (characteristicClassEvalOnUniversalBundle γ :
    CharacteristicClass n q k → (k q).obj (op (TopCat.of BO)))
#check (characteristicClassEvalOnUniversalBundle_bijective :
    Function.Bijective (characteristicClassEvalOnUniversalBundle γ))

end
