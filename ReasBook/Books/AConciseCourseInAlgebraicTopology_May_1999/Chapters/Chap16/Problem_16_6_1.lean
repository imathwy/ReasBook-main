import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

noncomputable section

variable {X : Type} [TopologicalSpace X] (x : X)
variable (A : Rep ℤ (FundamentalGroup X x))
  (XtildeChains : ChainComplex (Rep ℤ (FundamentalGroup X x)) ℕ)

-- Semantic recall via `lean_leansearch`: `HomologicalComplex.coinvariantsTensorObj`
-- in `Mathlib.RepresentationTheory.Homological.GroupHomology.Basic` is the categorical
-- owner for the tensor-product model of local-coefficient chains, and this item specializes it to
-- the chosen universal-cover chain complex.

/- Problem 16.6.1. Fix a based space `(X, x)`, write `π = FundamentalGroup X x`,
choose a universal cover `X̃` of `X`, and choose a `π₁(X, x)`-equivariant cellular or
singular chain complex `XtildeChains : ChainComplex (Rep ℤ (FundamentalGroup X x)) ℕ`
modeling `C_*(X̃)`. Then the chain complex on `X` with local coefficients in a
`π`-representation `A` is modeled by `HomologicalComplex.coinvariantsTensorObj A XtildeChains`,
the categorical form of the textbook tensor product `A ⊗[ℤ[π]] C_*(X̃)`. -/
#check HomologicalComplex.coinvariantsTensorObj A XtildeChains
