import BauschkeLean.Chap12.Proposition_12_30
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap23.Definition_23_1

-- `source-facing`: Example 23.3 is stated on the Chapter 23 resolvent/Yosida surface.
-- `core/canonical`: the actual owner facts are the Chapter 16 proximal-subdifferential bridge and
-- the Chapter 12 gradient formula for the Moreau envelope.
-- `bridge/view`: this file should therefore stay a thin Chapter 23 reformulation of those owners.

open scoped Gradient Pointwise
open SetValuedOperator

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Example 23.3 (1): for `f ∈ Γ₀(H)` and `γ ∈ ℝ_{++}`, the resolvent `J_{γ ∂ f}` is the scaled
proximity operator `Prox[γ, f, hf]`. -/
theorem resolvent_subdifferential_eq_scaledProximityOperator
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    J[((γ : ℝ) • (∂ f : SetValuedOperator H H))] =
      (Prox[γ, f, hf]).toSetValuedOperator := by
  rw [← subdifferential_posReal_smul_eq_smul f γ, resolvent_def]
  simpa [scaledProximityOperator] using
    (singleton_proximityOperator_eq_inverse_add_subdifferential (smul_mem_gammaZero f hf γ)).symm

/-- Example 23.3 (2): the Yosida approximation `{}^γ(∂ f)` equals the Fréchet gradient of the
real-valued `γ`-Moreau envelope `fun y ↦ (({}^[γ] f) y).toReal`. -/
theorem yosidaApproximation_subdifferential_eq_gradient_moreauEnvelopeToReal
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    {}^[γ] (∂ f) =
      (∇ (fun y : H ↦ (({}^[γ] f) y).toReal)).toSetValuedOperator := by
  ext x
  rw [yosidaApproximation_apply,
    resolvent_subdifferential_eq_scaledProximityOperator f hf γ]
  simp [gradient_moreauEnvelope_toReal_eq_inv_smul_sub_scaledProximityOperator_of_mem_gammaZero,
    hf]

end ERealFunction
