import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {x : E}

/- Definition 3.5 is a `bridge/view` item in the chapter convex-analysis API: the owner object is
`extendedRealSubdifferential f x`, and the textbook phrase "f is subdifferentiable at x" is exactly the
nonemptiness proposition on that owner set. The downstream owner set `subdifferential_domain`
introduced in Definition 3.6 is derived from this same proposition, so this file only recalls it. -/
#check (extendedRealSubdifferential f x).Nonempty

end
