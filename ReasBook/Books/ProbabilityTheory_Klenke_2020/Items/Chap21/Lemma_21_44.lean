import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap03.Definition_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open ProbabilityTheory

/-- The critical geometric offspring distribution, i.e. the geometric law with success
probability `1 / 2`. -/
noncomputable abbrev criticalGeometricOffspringPMF : PMF ℕ :=
  geometricPMF
    (show 0 < (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) ≤ 1 by norm_num)

-- Proof sketch: identify the canonical pgf
-- `probabilityGeneratingFunctionReal criticalGeometricOffspringPMF` with the fractional linear map
-- `s ↦ 1 / (2 - s)`, encode this Möbius transformation by the matrix `[[0, 1], [-1, 2]]`, compute
-- its positive powers explicitly, and translate the matrix formula back to the corresponding
-- function iterate.
/-- Lemma 21.44: For the critical geometric offspring distribution, whose probability generating
function is `probabilityGeneratingFunctionReal criticalGeometricOffspringPMF`, equivalently
`ψ(s) = 1 / (2 - s)`, the `n`th iterate satisfies
`ψ^[n] (s) = (n - (n - 1) s) / (n + 1 - n s)` for every positive `n` and every `s ∈ [0,1]`. -/
theorem critical_geometric_offspring_pgf_iterate_eq (n : ℕ) (hn : 1 ≤ n) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) s =
      (((n : ℝ) - (n - 1) * s) / (n + 1 - n * s)) := sorry
