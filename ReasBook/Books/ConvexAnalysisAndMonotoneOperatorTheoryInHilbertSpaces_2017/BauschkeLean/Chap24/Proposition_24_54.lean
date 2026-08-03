import BauschkeLean.Chap24.Example_24_34

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

section RealInterval

variable {a b : ℝ}
variable {ψ : ℝ → Set.Ioi (⊥ : EReal)}

local notation "Ω" => Set.Icc a b

/- Source/core/bridge triage:
- `source-facing`: Proposition 24.54 is the interval specialization of the support-function
  proximal-threshold decomposition.
- `core/canonical`: the chapter owners are the interval thresholder
  `intervalSoftThresholder`, the proximal surface `Prox[...]`, and the scalar data
  `0 ∈ interior (effectiveDomain ψ)` together with
  `HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0` from Theorem 24.52.
- `bridge/view`: this file keeps only the interval specialization and its `Γ₀(ℝ)` witness for the
  support-function summand; it does not introduce a second owner for proximal thresholding.
-/

/-- If `ψ ∈ Γ₀(ℝ)` is finite at `0`, then adding the support function of the closed interval
`[a,b]` still yields a `Γ₀(ℝ)` function. -/
theorem add_supportFunction_Icc_mem_gammaZero_of_zero_mem_effectiveDomain
    (hψ : ψ ∈ Γ₀(ℝ))
    (h : a ≤ b)
    (hzero : 0 ∈ effectiveDomain ψ) :
    ψ + properIoi (σ[Ω]) (isProper_supportFunction_of_nonempty Ω (Set.nonempty_Icc.2 h)) ∈
      Γ₀(ℝ) := by
  refine pointwiseAdd_mem_gammaZero ψ
    (properIoi (σ[Ω]) (isProper_supportFunction_of_nonempty Ω (Set.nonempty_Icc.2 h)))
    hψ
    (example_11_2_2_supportFunction_mem_gammaZero Ω (Set.nonempty_Icc.2 h))
    ?_
  refine ⟨0, hzero, ?_⟩
  refine mem_effectiveDomain_iff.mpr ?_
  simp [supportFunction_zero_eq_zero_of_nonempty Ω (Set.nonempty_Icc.2 h)]

/-- Proposition 24.54: let `Ω = [a,b]` be a nonempty closed interval in `ℝ`, let `ψ ∈ Γ₀(ℝ)` be
differentiable at `0` with derivative `0`, assume moreover that `ψ` is finite on a neighborhood
of `0`, and set `φ = ψ + σ_Ω`. Then `Prox_φ` is the composition of `Prox_ψ` with the interval
soft thresholder on `Ω`. The primitive scalar data are the interior-domain hypothesis
`0 ∈ interior (effectiveDomain ψ)` together with `HasDerivAt ... 0 0`. -/
theorem proximityOperator_add_supportFunction_Icc_eq_proximityOperator_comp_intervalSoftThresholder
    (hψ : ψ ∈ Γ₀(ℝ))
    (h : a ≤ b)
    (hzero_int : 0 ∈ interior (effectiveDomain ψ))
    (hderiv : HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0) :
    Prox[
      ψ + properIoi (σ[Ω]) (isProper_supportFunction_of_nonempty Ω (Set.nonempty_Icc.2 h)),
      add_supportFunction_Icc_mem_gammaZero_of_zero_mem_effectiveDomain
        hψ h (interior_subset hzero_int)
    ] = Prox[ψ, hψ] ∘ intervalSoftThresholder a b := sorry

end RealInterval

end

end ERealFunction
