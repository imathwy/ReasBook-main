import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_1_5

open scoped HomotopyClasses

universe u v

-- Semantic recall via `lean_leansearch`: the broad vector-bundle-classification query did not
-- expose a chapter-level owner better than the local classifying-map API from Theorem 23.1.5.

section

variable {n : ℕ}
variable {BO : Type u} [TopologicalSpace BO]
variable {γ : BO → Type v}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
variable [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin n → ℝ) γ]
variable [∀ b, AddCommGroup (γ b)] [∀ b, Module ℝ (γ b)]
variable {X : Type u} [TopologicalSpace X]
variable [RealPlaneBundleClassifyingSpace n BO γ]

/-
Remark 23.1.6. Vector-bundle classification converts questions about real `n`-plane bundles over
`X` into questions about homotopy classes of maps to the classifying space `BO`. In this chapter,
that interpretation is expressed by the canonical classifying map
`realPlaneBundleClassifyingMap n γ X : Ho[X, BO] → RealPlaneBundle.classes n X`
and its bijectivity theorem `realPlaneBundleClassifyingMap_bijective`.
-/
#check (realPlaneBundleClassifyingMap n γ X : Ho[X, BO] → RealPlaneBundle.classes n X)
#check realPlaneBundleClassifyingMap_bijective

end
