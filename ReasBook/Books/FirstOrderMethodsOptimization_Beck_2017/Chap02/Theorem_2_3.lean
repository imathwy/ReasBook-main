import FirstOrderMethodsinOptimization.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [TopologicalSpace E]

section

-- Proof sketch: prove lower semicontinuity pointwise. On the closed effective domain, continuity
-- gives lower semicontinuity within the domain. Outside the domain the function is identically
-- `⊤` on an open neighborhood, because the complement of a closed effective domain is open.
-- Combine these two cases to obtain lower semicontinuity everywhere.
/-- Theorem 2.3: if an extended-real-valued function is continuous on its effective domain and that
domain is closed, then the function is closed, equivalently lower semicontinuous. -/
theorem lowerSemicontinuous_of_continuousOn_effective_domain (f : E → EReal)
    (h_cont : ContinuousOn f (effective_domain f))
    (h_closed : IsClosed (effective_domain f)) :
    LowerSemicontinuous f := sorry

end
