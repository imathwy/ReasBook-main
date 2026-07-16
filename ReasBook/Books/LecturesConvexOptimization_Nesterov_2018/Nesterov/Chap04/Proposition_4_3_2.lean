import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_2_7
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_3_2

-- Declarations for this item will be appended below by the statement pipeline.

variable {n k : ℕ}

/-- Proposition 4.3.2: for `k ≤ n`, the hard-instance objective `fk hkn` has globally
`(8 * √2)`-Lipschitz Hessian, recorded on the chapter's canonical `C22[...]` surface. The
degenerate cases `k = 0, 1` are included because the same owner bound still applies there. -/
theorem fk_mem_C22
    (hkn : k ≤ n) :
    fk hkn ∈ C22[⟨8 * Real.sqrt 2, by positivity⟩] := sorry
