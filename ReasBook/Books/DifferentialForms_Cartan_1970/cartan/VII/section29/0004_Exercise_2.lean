import DifferentialForms_Cartan_1970.VII.section27.«0003_Definition_VII_1_extra_1»
import Mathlib
import DifferentialForms_Cartan_1970.VII.section29.«0004_Exercise_2».Index
-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MvPowerSeries PowerSeries MvPowerSeries.WithPiTopology
open PowerSeries

-- Semantic recall note: the `lean_leansearch` MCP tool was unavailable in this environment, so
-- this item is stated directly with mathlib's multivariable power-series API via
-- `MvPowerSeries`, `MvPowerSeries.subst`, and `MvPolynomial`.

universe u

section ScalarQuadraticMajorantExistence

variable {𝕜 : Type u} [NormedCommRing 𝕜]
variable {n p : ℕ}

/-- Exercise 2 (3): if the recursive system `(3)` is already equipped with source-facing majorant
data `M, R > 0`, then every formal solution admits a family majorant together with a scalar
quadratic majorant bridge for the symmetric specialization `X₁ = ⋯ = Xₙ = X`. -/
theorem exists_scalar_majorant_of_formalImplicitSolution
    (S : RecursiveImplicitSystem 𝕜 n p)
    (M R : NNReal)
    (hM : 0 < M)
    (hR : 0 < R)
    (hS : S.IsMajorizedBy M R)
    {x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (hx : FormalImplicitSolution S x) :
    ∃ Ξ : Fin n → MvPowerSeries (ParamIndex n p) NNReal,
      FormalImplicitSolution.IsMajorizedBy x Ξ ∧
      ∃ X : MvPowerSeries (ParamIndex n p) NNReal,
        IsScalarMajorantBridge Ξ M R X := by
  let _ := hM
  let _ := hR
  refine ⟨solutionNormMajorant x, isMajorizedBy_solutionNormMajorant x,
    scalarMajorantLimit (n := n) (p := p) M R, ?_⟩
  -- Route correction: the scalar direct limit is already proved to satisfy the fixed-point
  -- equation. The only remaining source-facing work is the coefficientwise domination of the
  -- formal solution's norm profile by that direct limit.
  refine ⟨scalarMajorantLimit_isFixedPoint (n := n) (p := p) M R, ?_⟩
  intro j d
  exact solutionNormMajorant_le_scalarMajorantLimit (n := n) (p := p) S M R hS hx j d

/-- Cartan section29 0004_Exercise_2: the recursive-system formulation of Exercise 2 has
polynomial coefficient recurrences, admits a unique formal solution, and every source-majorized
formal solution is dominated by a scalar quadratic majorant bridge. -/
theorem cartanSection29_0004_Exercise_2
    (S : RecursiveImplicitSystem 𝕜 n p) :
    (∃ Q : Fin n → (ParamIndex n p →₀ ℕ) → MvPolynomial (RecursiveCoeffVar n p) ℤ,
      (∀ j d u,
        u ∈ (Q j d).vars →
          match u with
          | Sum.inl _ => True
          | Sum.inr ⟨_, d'⟩ => paramDegree d' < paramDegree d) ∧
      ∀ x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜,
        FormalImplicitSolution S x ↔
          RecursiveCoefficientRecurrence S Q x) ∧
    (∃! x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜,
      FormalImplicitSolution S x) ∧
    (∀ M R, 0 < M → 0 < R → S.IsMajorizedBy M R →
      ∀ {x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜},
        FormalImplicitSolution S x →
          ∃ Ξ : Fin n → MvPowerSeries (ParamIndex n p) NNReal,
            FormalImplicitSolution.IsMajorizedBy x Ξ ∧
            ∃ X : MvPowerSeries (ParamIndex n p) NNReal,
              IsScalarMajorantBridge Ξ M R X) := by
  refine ⟨exists_recursive_coefficient_polynomials (n := n) (p := p) S,
    existsUnique_formalImplicitSolution (n := n) (p := p) S, ?_⟩
  intro M R hM hR hS x hx
  exact exists_scalar_majorant_of_formalImplicitSolution (n := n) (p := p) S M R hM hR hS hx

end ScalarQuadraticMajorantExistence
