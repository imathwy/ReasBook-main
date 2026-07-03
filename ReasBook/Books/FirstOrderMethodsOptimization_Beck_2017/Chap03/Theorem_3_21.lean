import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → ℝ} {g : ℝ → ℝ} {x : E}

/-
Theorem 3.21 is `source-facing` in the Chapter 3 convex-analysis API. Its `core/canonical` owner
is the real-valued strong-dual subdifferential `subdifferentialAt` from Theorem 3.4, so this file
keeps only the composition rule for that owner set-valued map and does not introduce any parallel
wrapper or auxiliary packaged notion.
-/
recall subdifferentialAt

-- Proof sketch: first note that `g ∘ f` is convex because `f` is convex, `g` is convex, and `g`
-- is monotone. Restrict `f` and `g ∘ f` to any affine line `t ↦ x + t • d`, apply the
-- one-dimensional chain rule to the corresponding directional derivatives at `0`, and obtain
-- `h'(x; d) = g'(f x) * f'(x; d)`. Then identify both directional derivatives with the support
-- functions of the relevant subdifferentials using the Chapter 3 owner bridges for
-- differentiability and positive scalar multiplication, and conclude from equality of support
-- functions of closed convex sets.
/-- Theorem 3.21: chain rule of subdifferential calculus. If `f : E → ℝ` is convex and
`g : ℝ → ℝ` is convex and nondecreasing, and if `g` is differentiable at `f x`, then the
subdifferential of the composition `g ∘ f` at `x` is the scalar multiple of
`subdifferentialAt f x` by the derivative `g'(f x)`. -/
theorem subdifferentialAt_comp_eq_smul_subdifferentialAt
    (hf : ConvexOn ℝ Set.univ f) (hg : ConvexOn ℝ Set.univ g) (hg_mono : Monotone g)
    (hg_diff : DifferentiableAt ℝ g (f x)) :
    subdifferentialAt (g ∘ f) x = (deriv g (f x)) • subdifferentialAt f x := sorry

end
