import BauschkeLean.Chap14.Corollary_14_8
import BauschkeLean.Chap14.Remark_14_4

open scoped Gradient InnerProductSpace Pointwise

noncomputable section

universe u

namespace ERealFunction

section Characterizations

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))

-- Layer triage for Proposition 24.4:
-- `source-facing`: keep the Chapter 24 statements formulated with `q = halfSquaredNorm`.
-- `core/canonical`: the Chapter 14 owners are the unit conjugate Moreau envelope
-- `{}^[(1 : PosReal)] (f∗[hf])`, the unit-envelope/infimal-convolution bridge, and the gradient
-- identity `proximityOperator_eq_gradient_conjugateMoreauEnvelope_toReal_of_mem_gammaZero`.
-- `bridge/view`: rewrite those owners through the source notation `(f + q)^*` and `f^* □ q`.

/-- Helper for Proposition 24.4: `(f + q)^*` is the unit Moreau envelope of `f∗[hf]`,
where `q = (1 / 2) ‖·‖²` is `halfSquaredNorm`. -/
theorem conjugate_add_halfSquaredNorm_eq_unit_conjugateMoreauEnvelope :
    (f + halfSquaredNorm).asEReal∗ = {}^[(1 : PosReal)] (f∗[hf]) := by
  -- Rewrite the source-facing conjugate directly to the Chapter 14 canonical owner.
  simpa using conjugate_add_halfSquaredNorm_eq_unitMoreauEnvelope_gammaZeroConjugate f hf

/-- Helper for Proposition 24.4: the unit Moreau envelope of `f∗[hf]` is the infimal
convolution `f∗[hf] □ q`, where `q = (1 / 2) ‖·‖²` is `halfSquaredNorm`. -/
theorem unit_conjugateMoreauEnvelope_eq_infimalConvolution_halfSquaredNorm :
    {}^[(1 : PosReal)] (f∗[hf]) = f∗[hf] □ halfSquaredNorm := by
  change
    {}^[(1 : PosReal)] (gammaZeroConjugate f hf) =
      gammaZeroConjugate f hf □ halfSquaredNorm
  exact unit_moreauEnvelope_eq_infimalConvolution_halfSquaredNorm_at_one
    (h := gammaZeroConjugate f hf)

/-- Proposition 24.4 (1): for `f ∈ Γ₀(H)` and `q = (1 / 2) ‖·‖²`,
`Prox[f, hf]` is the gradient of `(f + q)^*`. -/
theorem proximityOperator_eq_gradient_conjugate_add_halfSquaredNorm :
    Prox[f, hf] = ∇ (fun y : H ↦ (((f + halfSquaredNorm).asEReal∗) y).toReal) := by
  -- First identify `(f + q)^*` with the canonical unit conjugate Moreau envelope.
  rw [conjugate_add_halfSquaredNorm_eq_unit_conjugateMoreauEnvelope (f := f) (hf := hf)]
  -- Remark 14.4 then gives the proximity operator as the gradient of that envelope.
  exact proximityOperator_eq_gradient_conjugateMoreauEnvelope_toReal_of_mem_gammaZero
    (f := f) hf

/-- Proposition 24.4 (2): for `f ∈ Γ₀(H)` and `q = (1 / 2) ‖·‖²`, the gradient of `(f + q)^*`
is exactly the gradient of the infimal convolution `f∗[hf] □ q`. -/
theorem gradient_conjugate_add_halfSquaredNorm_eq_gradient_infimalConvolution_halfSquaredNorm :
    ∇ (fun y : H ↦ (((f + halfSquaredNorm).asEReal∗) y).toReal) =
      ∇ (fun y : H ↦ ((f∗[hf] □ halfSquaredNorm) y).toReal) := by
  -- Rewrite `(f + q)^*` to the same Chapter 14 owner used by the source proof.
  rw [conjugate_add_halfSquaredNorm_eq_unit_conjugateMoreauEnvelope (f := f) (hf := hf)]
  -- Transport the unit-envelope/infimal-convolution identity through the fixed gradient wrapper.
  exact congrArg
    (fun h : H → EReal ↦ ∇ (fun y : H ↦ (h y).toReal))
    (unit_conjugateMoreauEnvelope_eq_infimalConvolution_halfSquaredNorm (f := f) (hf := hf))

/-- Proposition 24.4 (3): for `f ∈ Γ₀(H)` and `q = (1 / 2) ‖·‖²`, the gradient of
`f∗[hf] □ q` is exactly the gradient of the unit Moreau envelope `{}^[1] (f∗[hf])`. -/
theorem gradient_infimalConvolution_halfSquaredNorm_eq_gradient_unit_conjugateMoreauEnvelope :
    ∇ (fun y : H ↦ ((f∗[hf] □ halfSquaredNorm) y).toReal) =
      ∇ (fun y : H ↦ (({}^[(1 : PosReal)] (f∗[hf])) y).toReal) := by
  -- Reverse the source-facing bridge so both sides are gradients of the same canonical owner.
  exact congrArg
    (fun h : H → EReal ↦ ∇ (fun y : H ↦ (h y).toReal))
    (unit_conjugateMoreauEnvelope_eq_infimalConvolution_halfSquaredNorm
      (f := f) (hf := hf)).symm

end Characterizations

end ERealFunction
