import FirstOrderMethodsinOptimization.Chap01.Definition_1_34

-- Declarations for this item will be appended below by the statement pipeline.

variable {m n : ℕ}
variable (a b : ENNReal) [Fact (1 ≤ a)] [Fact (1 ≤ b)]
variable (A : Matrix (Fin m) (Fin n) ℝ)

/- Proposition 1.16 is recall-only: in the chapter owner setup from Definition 1.34, the induced
`(a,b)`-norm of a real matrix is exactly the operator norm of the continuous linear map attached
to `Matrix.toLpLin a b`. -/
#check (‖(A.toLpLin a b).toContinuousLinearMap‖ : ℝ)
