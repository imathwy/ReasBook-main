module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Topology.Sets.Opens

public section

noncomputable section

section

variable {d : ℕ}
variable (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))

/-- Example 2.5 (2). The source negative-Laplacian formula `(2.10)` is the
pointwise operator on `Ω` given by
`x ↦ -InnerProductSpace.laplacianWithin f Ω x`.
The source applies this operator to smooth functions `f`. -/
@[expose]
def smoothNegativeLaplacianWithin
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Ω → ℝ :=
  fun x ↦ -InnerProductSpace.laplacianWithin f Ω x

/-- Evaluation formula for `smoothNegativeLaplacianWithin`. -/
theorem smoothNegativeLaplacianWithin_apply
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : Ω) :
    smoothNegativeLaplacianWithin Ω f x =
      -InnerProductSpace.laplacianWithin f Ω x := rfl

end
