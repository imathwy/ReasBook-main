import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.5 is recall-only in the chapter extendedRealSubdifferential API. The primitive owner data is
`extendedRealSubdifferential : Set (Module.Dual ℝ E)`. Convexity belongs to that owner abstraction itself,
while closedness is a topological bridge statement on `strongDualSubdifferential`; this file
therefore reuses those upstream declarations directly and introduces no parallel local wrapper. -/
recall isClosed_subdifferential
recall convex_subdifferential
