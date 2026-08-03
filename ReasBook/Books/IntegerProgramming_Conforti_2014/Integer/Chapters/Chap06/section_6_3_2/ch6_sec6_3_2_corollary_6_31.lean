import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_19
import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_20
import Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_theorem_6_30
import Integer.Chapters.Chap06.section_6_3_2.max_linear_representation

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

section Corollary631

-- This corollary keeps the source-facing "maximum of linear functionals" statement, but now
-- phrases it through the reusable Section 6.3.2 owner
-- `HasMaxLinearRepresentationOfSizeLE` on the chapter's canonical gauge and dot-product API.

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ

/-- Corollary 6.31 (3). Every minimal valid function for `R_f` admits a max-linear
representation on `ℝ^q` using at most `2^q` linear functionals. -/
theorem minimal_valid_function_for_continuous_infinite_relaxation_has_max_linear_bound
    (f : Rq) (ψ : Rq → ℝ)
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    HasMaxLinearRepresentationOfSizeLE (2 ^ q) ψ := sorry

end Corollary631
