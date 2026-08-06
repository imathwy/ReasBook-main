import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_5_1

universe u v

open Bundle

-- Chapter 23 already provides the source-faithful owners
-- `RealPlaneBundleClassifyingSpace q BO γ` for the chosen universal bundle over `BO(q)` and
-- `ThomSpace q γ` for its Thom space, so this item names that canonical combination directly.

section

variable (q : ℕ) (BO : Type u) [TopologicalSpace BO] (γ : BO → Type v)
variable [TopologicalSpace (Bundle.TotalSpace (Fin q → ℝ) γ)]
variable [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin q → ℝ) γ]
variable [∀ b, AddCommGroup (γ b)] [∀ b, Module ℝ (γ b)]
variable [RealPlaneBundleClassifyingSpace q BO γ]

/-- Definition 25.2.1. `TO q` denotes the Thom space of the universal `q`-plane bundle over
`BO(q)`, formalized here as the Thom space of a chosen universal real `q`-plane bundle `γ`
carried by the classifying-space owner `RealPlaneBundleClassifyingSpace q BO γ`. -/
abbrev TO : Type (max u v) :=
  ThomSpace q γ

/-- Unfolding `TO` recovers the Thom space of the chosen universal bundle `γ`. -/
@[simp] theorem TO_def : TO q BO γ = ThomSpace q γ := rfl

end
