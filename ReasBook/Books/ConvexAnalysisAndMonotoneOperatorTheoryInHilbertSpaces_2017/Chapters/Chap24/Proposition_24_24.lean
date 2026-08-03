import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap23.Proposition_23_34

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace ERealFunction

noncomputable section

section MetricProximityOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f : H → Set.Ioi (⊥ : EReal)}

omit [CompleteSpace H] in
/-- Helper for Proposition 24.24: composing a `Γ₀(H)` function with a continuous linear
equivalence preserves `Γ₀(H)`. -/
private theorem mem_gammaZero_comp_continuousLinearEquiv_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (L : H ≃L[ℝ] H) :
    f ∘ L ∈ Γ₀(H) := by
  simpa [Function.comp] using mem_gammaZero_comp_continuousLinearEquiv hf L

namespace metricProximityOperator

/-- Proposition 24.24 (1): for `f ∈ Γ₀(ℋ)` and a self-adjoint strongly monotone
`U : ℋ → ℋ`, an explicit positive square-root witness `L` for `U⁻¹` realizes the metric
proximity operator as the singleton-valued resolvent of `U⁻¹ ∘ ∂ f`. -/
theorem toSetValuedOperator_eq_resolvent_inverse_subdifferential
    (hf : f ∈ Γ₀(H)) (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) (L : H ≃L[ℝ] H)
    (hL_pos : L.toContinuousLinearMap.IsPositive)
    (hL_sq :
      L.toContinuousLinearMap.comp L.toContinuousLinearMap = ContinuousLinearMap.inverse U) :
    (L ∘
        Prox[f ∘ L,
          mem_gammaZero_comp_continuousLinearEquiv_of_mem_gammaZero hf L] ∘
        L.symm).toSetValuedOperator =
      J[((ContinuousLinearMap.inverse U).toSetValuedOperator.comp
        (∂ f : SetValuedOperator H H))] := sorry

/-- Proposition 24.24 (2): if `L` is a positive square-root equivalence witness for `U⁻¹`, then
the witness-based metric proximity formula also satisfies the Moreau identity
`Id - U⁻¹ ∘ Prox^U_(f*) ∘ U`, written through the same explicit witness `L`. -/
theorem eq_comp_proximityOperator_and_sub
    (hf : f ∈ Γ₀(H)) (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) (L : H ≃L[ℝ] H)
    (hL_pos : L.toContinuousLinearMap.IsPositive)
    (hL_sq :
      L.toContinuousLinearMap.comp L.toContinuousLinearMap = ContinuousLinearMap.inverse U) :
    L ∘
        Prox[f ∘ L,
          mem_gammaZero_comp_continuousLinearEquiv_of_mem_gammaZero hf L] ∘
        L.symm =
      id - (ContinuousLinearMap.inverse U ∘
        (L ∘
          Prox[(f∗[hf]) ∘ L,
            mem_gammaZero_comp_continuousLinearEquiv_of_mem_gammaZero
              (gammaZeroConjugate_mem_gammaZero hf) L] ∘
          L.symm) ∘
        U) := sorry

end metricProximityOperator

end MetricProximityOperator

end

end ERealFunction
