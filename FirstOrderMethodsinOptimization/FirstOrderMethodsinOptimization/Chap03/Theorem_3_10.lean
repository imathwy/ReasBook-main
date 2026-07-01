import FirstOrderMethodsinOptimization.Chap03.Theorem_3_9

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.10 is recall-only in the chapter directional-derivative API. Its mathematical content
is the `bridge/view` finite-index specialization of the owner theorem
`directional_derivative_iSup_eq_iSup_active_indices` from `Theorem_3_9`; the choice of `Fin m`
adds no new primitive data beyond the existing `[Finite ι] [Nonempty ι]` owner hypotheses. This
file therefore reuses that exact theorem instead of keeping a duplicate local `Fin m` wrapper. -/
recall directional_derivative_iSup_eq_iSup_active_indices
