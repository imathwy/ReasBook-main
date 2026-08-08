import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.14 is a `bridge/view` item for the chapter owner `subdifferentialAt` and the
calculus owners `DifferentiableAt` and `fderiv`. The singleton characterization is the primitive
source-facing bridge; stronger consequences such as simultaneously extracting differentiability and
identifying `fderiv` are derived API and are intentionally not kept here as parallel primitive
declarations. -/

-- Proof sketch: if `f` is differentiable at `x`, convexity gives the supporting-hyperplane
-- inequality for `fderiv ℝ f x`, and comparing directional estimates in directions `d` and `-d`
-- shows every subgradient agrees with `fderiv ℝ f x`. Conversely, if the extendedRealSubdifferential is a
-- singleton, then the directional derivative is forced to be linear in the direction variable, so
-- the convex function is differentiable and its derivative is that unique subgradient.
/-- Proposition 3.14: for a convex real-valued function, differentiability at a point is equivalent
to the extendedRealSubdifferential at that point being the singleton containing the Fréchet derivative. In the
Euclidean setting of the text, this functional is represented by the gradient. -/
theorem differentiableAt_iff_subdifferentialAt_eq_singleton_fderiv
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {x : E} :
    DifferentiableAt ℝ f x ↔ subdifferentialAt f x = {fderiv ℝ f x} := sorry

end
