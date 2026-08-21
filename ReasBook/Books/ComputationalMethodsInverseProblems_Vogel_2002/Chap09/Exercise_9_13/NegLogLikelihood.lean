module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

noncomputable section

namespace PoissonInverse

open scoped BigOperators

/-- The Chapter 9 negative log-likelihood objective `J(f) = -ℓ(f; d)` from
`(9.44)` for Poisson inverse data `d` and forward operator `K`. -/
def negLogLikelihood
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun f ↦
    ∑ i : Fin m,
      (Matrix.mulVec K f i - d i * Real.log (Matrix.mulVec K f i))

/-- The defining finite-sum formula for `PoissonInverse.negLogLikelihood`. -/
theorem negLogLikelihood_def
    {m n : ℕ}
    (K : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin n)) :
    negLogLikelihood K d f =
      ∑ i : Fin m,
        (Matrix.mulVec K f i - d i * Real.log (Matrix.mulVec K f i)) := by
  -- Expand the objective to its defining finite sum.
  rfl

end PoissonInverse
