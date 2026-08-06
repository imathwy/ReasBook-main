import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_1_5

open CategoryTheory Bundle
open scoped HomotopyClasses

noncomputable section

universe u v w

-- Chapter 23 already exposes the classifying-map API for real `n`-plane bundles and the
-- identification of characteristic classes with universal cohomology classes on `BO(n)`. Together
-- with characteristic-class naturality, that is the canonical local owner for the remark that
-- characteristic classes are pulled back from the classifying space.

section

variable {n q : ℕ}
variable {k : ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}}
variable {BO : Type u} [TopologicalSpace BO]
variable {γ : BO → Type v}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
variable [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin n → ℝ) γ]
variable [∀ b, AddCommGroup (γ b)] [∀ b, Module ℝ (γ b)]
variable [RealPlaneBundleClassifyingSpace n BO γ]
variable [(k q).rightOp.IsHomotopyInvariant]
variable {X : Type u} [TopologicalSpace X]

/- Remark 23.8.4. Characteristic classes arise by pulling universal cohomology classes on
`BO(n)` back along classifying maps. In the Chapter 23 API, the relevant owners are the
classifying map `realPlaneBundleClassifyingMap n γ X : Ho[X, BO] → RealPlaneBundle.classes n X`,
the bijection `characteristicClassEvalOnUniversalBundle_bijective` identifying characteristic
classes with universal classes on `BO(n)`, and the pullback formula
`CharacteristicClass.naturality`.
-/
#check (realPlaneBundleClassifyingMap n γ X : Ho[X, BO] → RealPlaneBundle.classes n X)
#check realPlaneBundleClassifyingMap_bijective
#check characteristicClassEvalOnUniversalBundle_bijective
#check CharacteristicClass.naturality

end
