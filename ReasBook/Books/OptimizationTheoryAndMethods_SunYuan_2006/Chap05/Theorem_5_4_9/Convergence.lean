import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_4_1

noncomputable section

section JacobianQuasiNewtonConvergence

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A sequence converges linearly to `xStar` when its errors admit a global geometric bound
`‖x k - xStar‖ ≤ C * q^k` with `0 < q < 1`. -/
def LinearlyConvergesTo (x : ℕ → E) (xStar : E) : Prop :=
  ∃ C q : ℝ,
    0 ≤ C ∧
      q ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ k : ℕ, ‖x k - xStar‖ ≤ C * q ^ k

end JacobianQuasiNewtonConvergence
