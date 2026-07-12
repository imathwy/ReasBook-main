import DifferentialForms_Cartan_1970.VII.section29.«0004_Exercise_2».ScalarQuadraticMajorant

open scoped BigOperators MvPowerSeries PowerSeries MvPowerSeries.WithPiTopology
open PowerSeries

universe u

section ScalarQuadraticMajorantExistence

variable {𝕜 : Type u} [NormedCommRing 𝕜]
variable {n p : ℕ}

/-- Helper for Cartan section29 0004_Exercise_2: the coefficientwise norm profile attached to a
formal solution. -/
noncomputable def solutionNormMajorant
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) :
    Fin n → MvPowerSeries (ParamIndex n p) NNReal :=
  fun j d ↦
    show NNReal from
      ⟨(‖MvPowerSeries.coeff d (x j)‖ : ℝ), norm_nonneg (MvPowerSeries.coeff d (x j))⟩

/-- Helper for Cartan section29 0004_Exercise_2: the coefficientwise norm profile of a formal
solution has vanishing constant coefficient in every component. -/
lemma solutionNormMajorant_constantCoeff_eq_zero
    (S : RecursiveImplicitSystem 𝕜 n p)
    {x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (hx : FormalImplicitSolution S x)
    (j : Fin n) :
    MvPowerSeries.constantCoeff (solutionNormMajorant x j) = 0 := by
  -- The constant coefficient is the norm of the solution's constant term, which vanishes.
  apply Subtype.ext
  change ‖MvPowerSeries.coeff (0 : ParamIndex n p →₀ ℕ) (x j)‖ = 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hx.constantCoeff_eq_zero]
  simp

/-- Helper for Cartan section29 0004_Exercise_2: the coefficientwise norm profile tautologically
majorizes the original formal solution. -/
lemma isMajorizedBy_solutionNormMajorant
    (x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜) :
    FormalImplicitSolution.IsMajorizedBy x (solutionNormMajorant x) := by
  -- Each coefficient is bounded by its own norm, viewed in `NNReal`.
  intro j d
  change ‖MvPowerSeries.coeff d (x j)‖ ≤ ‖MvPowerSeries.coeff d (x j)‖
  exact le_rfl

end ScalarQuadraticMajorantExistence
