import BauschkeLean.Chap08.Proposition_8_24
import BauschkeLean.Chap09.Proposition_9_40
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap14.Proposition_14_15
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap16.Proposition_16_63

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

-- Semantic recall note: `lean_leansearch` did not return a usable pointwise-prox theorem for
-- integral functionals, so the owner/API here was verified against
-- `Chap09/Proposition_9_40.lean` and `Chap12/ProximityOperator.lean`.

section BasicProperties

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [MeasurableSpace G] [BorelSpace G] [TopologicalSpace.SeparableSpace G]
  [μ.IsComplete] [SigmaFinite μ]

/-- Helper for Proposition 24.13: an almost-everywhere pointwise proximal identity yields the
corresponding almost-everywhere pointwise residual-subgradient inclusion. -/
private theorem ae_sub_mem_subdifferential_of_ae_eq_pointwise_proximityOperator
    (φ : G → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(G))
    (x p : Ω →₂[μ] G)
    (hp : ∀ᵐ ω ∂μ, p ω = Prox[φ, hφ] (x ω)) :
    ∀ᵐ ω ∂μ, x ω - p ω ∈ (∂ φ) (p ω) := by
  -- Repackage the pointwise proximal identity through the Chapter 16 bridge theorem.
  filter_upwards [hp] with ω hω
  exact (eq_proximityOperator_iff_sub_mem_subdifferential hφ (x ω) (p ω)).1 hω

/-- Helper for Proposition 24.13: effective-domain membership for `integralFunctional μ φ`
selects the finite integral branch of the pointwise integrand. -/
private theorem integralFunctional_branch_of_mem_effectiveDomain
    (φ : G → Set.Ioi (⊥ : EReal)) {x : Ω →₂[μ] G}
    (hx : x ∈ effectiveDomain (integralFunctional μ φ)) :
    Integrable (fun ω ↦ EReal.toReal (φ (x ω))) μ ∧
      ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤ := by
  -- Re-express effective-domain membership using the Chapter 8 branch predicate.
  have hx' : x ∈ pointwiseIntegralFunctionalDomain φ := by
    simpa [pointwiseIntegralFunctionalDomain, integralFunctional_coe μ] using hx
  rw [pointwiseIntegralFunctionalDomain_eq] at hx'
  exact hx'

/-- Helper for Proposition 24.13: an `L²` field that agrees almost everywhere with the pointwise
proximal map already lies in the effective domain of the induced integral functional. -/
private theorem mem_effectiveDomain_integralFunctional_of_ae_eq_pointwise_proximityOperator
    (φ : G → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(G))
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : G, (φ 0 : EReal) ≤ (φ z : EReal)))
    (x p : Ω →₂[μ] G)
    (hp : ∀ᵐ ω ∂μ, p ω = Prox[φ, hφ] (x ω)) :
    p ∈ effectiveDomain (integralFunctional μ φ) := by
  let hF : integralFunctional μ φ ∈ Γ₀(Ω →₂[μ] G) :=
    integralFunctional_mem_gammaZero μ φ hφ hfinite_or_nonneg
  rcases hF.2.nonempty with ⟨q, hq_eff⟩
  have hq_branch :
      Integrable (fun ω ↦ EReal.toReal (φ (q ω))) μ ∧
        ∀ᵐ ω ∂μ, (φ (q ω) : EReal) < ⊤ :=
    integralFunctional_branch_of_mem_effectiveDomain (μ := μ) φ hq_eff
  have hsub_ae :
      ∀ᵐ ω ∂μ, x ω - p ω ∈ (∂ φ) (p ω) :=
    ae_sub_mem_subdifferential_of_ae_eq_pointwise_proximityOperator φ hφ x p hp
  have hpointwise_ineq :
      ∀ᵐ ω ∂μ,
        (⟪q ω - p ω, x ω - p ω⟫_ℝ : EReal) + (φ (p ω) : EReal) ≤ (φ (q ω) : EReal) := by
    -- Specialize the pointwise subgradient inequality to the fixed comparison field `q`.
    filter_upwards [hsub_ae] with ω hω
    exact (mem_subdifferential_iff (f := φ) (x := p ω) (u := x ω - p ω)).1 hω (q ω)
  have hp_fin :
      ∀ᵐ ω ∂μ, (φ (p ω) : EReal) < ⊤ := by
    -- Finite right-hand values force the pointwise proximal values to stay finite as well.
    filter_upwards [hpointwise_ineq, hq_branch.2] with ω hω hqω
    by_contra hpω
    have htop : (φ (p ω) : EReal) = ⊤ := top_unique (not_lt.mp hpω)
    rw [htop, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at hω
    exact (ne_of_lt hqω) (top_le_iff.mp hω)
  let upper : Ω → ℝ :=
    fun ω ↦ EReal.toReal (φ (q ω)) - ⟪q ω - p ω, x ω - p ω⟫_ℝ
  have hupper_ae :
      ∀ᵐ ω ∂μ, EReal.toReal (φ (p ω)) ≤ upper ω := by
    -- Once both pointwise values are finite, the subgradient inequality becomes a real bound.
    filter_upwards [hpointwise_ineq, hp_fin, hq_branch.2] with ω hω hpω hqω
    have hp_top : (φ (p ω) : EReal) ≠ ⊤ := lt_top_iff_ne_top.mp hpω
    have hq_top : (φ (q ω) : EReal) ≠ ⊤ := lt_top_iff_ne_top.mp hqω
    have hp_bot : (φ (p ω) : EReal) ≠ ⊥ := (φ (p ω)).2.ne'
    have hq_bot : (φ (q ω) : EReal) ≠ ⊥ := (φ (q ω)).2.ne'
    have hcast :
        (((⟪q ω - p ω, x ω - p ω⟫_ℝ + EReal.toReal (φ (p ω)) : ℝ) : EReal)) ≤
          (((EReal.toReal (φ (q ω)) : ℝ) : EReal)) := by
      rw [← EReal.coe_toReal hp_top hp_bot, ← EReal.coe_toReal hq_top hq_bot,
        ← EReal.coe_add] at hω
      exact hω
    have hreal :
        ⟪q ω - p ω, x ω - p ω⟫_ℝ + EReal.toReal (φ (p ω)) ≤
          EReal.toReal (φ (q ω)) := by
      exact_mod_cast hcast
    dsimp [upper]
    linarith
  have hinner_int :
      Integrable (fun ω ↦ ⟪q ω - p ω, x ω - p ω⟫_ℝ) μ :=
    by
      have hinner_raw : Integrable (fun ω ↦ ⟪(q - p) ω, (x - p) ω⟫_ℝ) μ :=
        MeasureTheory.L2.integrable_inner (q - p) (x - p)
      have hqp :
          (fun ω ↦ ((q - p) ω : G)) =ᵐ[μ] fun ω ↦ q ω - p ω := by
        simpa [Pi.sub_apply] using (Lp.coeFn_sub q p)
      have hxp :
          (fun ω ↦ ((x - p) ω : G)) =ᵐ[μ] fun ω ↦ x ω - p ω := by
        simpa [Pi.sub_apply] using (Lp.coeFn_sub x p)
      have hinner_ae :
          (fun ω ↦ ⟪((q - p) ω : G), ((x - p) ω : G)⟫_ℝ) =ᵐ[μ]
            fun ω ↦ ⟪q ω - p ω, x ω - p ω⟫_ℝ := by
        filter_upwards [hqp, hxp] with ω hqpω hxpω
        rw [hqpω, hxpω]
      exact hinner_raw.congr hinner_ae
  have hupper_int : Integrable upper μ := by
    simpa [upper] using hq_branch.1.sub hinner_int
  obtain ⟨lower, hlower_int, hlower_ae⟩ :
      ∃ lower : Ω → ℝ, Integrable lower μ ∧
        ∀ᵐ ω ∂μ, lower ω ≤ EReal.toReal (φ (p ω)) := by
    rcases hfinite_or_nonneg with hfinite | ⟨hzero, hnonneg⟩
    · letI : IsFiniteMeasure μ := ⟨hfinite⟩
      -- Route correction: use the stable public linear lower bound instead of the broken
      -- Chapter 9 affine-minorant import path.
      rcases exists_linear_lower_bound_of_mem_gammaZero hφ with ⟨R, C, _, hminorant⟩
      let lower : Ω → ℝ := fun ω ↦ -R * ‖p ω‖ - C
      have hp_int : Integrable (fun ω : Ω ↦ p ω) μ := by
        exact
          integrableOn_univ.mp
            (integrableOn_Lp_of_measure_ne_top p fact_one_le_two_ennreal.elim
              (measure_ne_top μ Set.univ))
      have hlower_int : Integrable lower μ := by
        have hnorm_int : Integrable (fun ω : Ω ↦ ‖p ω‖) μ :=
          hp_int.norm
        have hscaled_int : Integrable (fun ω : Ω ↦ (-R) * ‖p ω‖) μ :=
          hnorm_int.const_mul (-R)
        simpa [lower] using hscaled_int.sub (integrable_const C)
      refine ⟨lower, hlower_int, ?_⟩
      -- The global linear support inequality gives a real lower bound once `φ (p ω)` is finite.
      filter_upwards [hp_fin] with ω hpω
      have hp_top : (φ (p ω) : EReal) ≠ ⊤ := lt_top_iff_ne_top.mp hpω
      have hp_bot : (φ (p ω) : EReal) ≠ ⊥ := (φ (p ω)).2.ne'
      have hcast :
          ((lower ω : ℝ) : EReal) ≤ (((EReal.toReal (φ (p ω)) : ℝ) : EReal)) := by
        simpa [lower, EReal.coe_toReal hp_top hp_bot] using hminorant (p ω)
      exact_mod_cast hcast
    · refine ⟨fun _ ↦ 0, ?_, ?_⟩
      · simpa using (integrable_zero : Integrable (fun _ : Ω ↦ (0 : ℝ)) μ)
      · -- In the nonnegative branch, the zero function itself is the required lower bound.
        filter_upwards [hp_fin] with ω hpω
        have hp_top : (φ (p ω) : EReal) ≠ ⊤ := lt_top_iff_ne_top.mp hpω
        have hp_bot : (φ (p ω) : EReal) ≠ ⊥ := (φ (p ω)).2.ne'
        have hcast :
            (((0 : ℝ) : EReal)) ≤ (((EReal.toReal (φ (p ω)) : ℝ) : EReal)) := by
          simpa [hzero, EReal.coe_toReal hp_top hp_bot] using hnonneg (p ω)
        exact_mod_cast hcast
  have hp_meas :
      AEStronglyMeasurable (fun ω ↦ EReal.toReal (φ (p ω))) μ := by
    -- Measurability comes from the `Γ₀` lower-semicontinuity of `φ`.
    have hφ_meas : Measurable φ := hφ.1.measurable.subtype_mk
    exact pointwise_integrand_aestronglyMeasurable φ hφ_meas p
  have hp_int :
      Integrable (fun ω ↦ EReal.toReal (φ (p ω))) μ := by
    -- The pointwise proximal inequality traps `φ ∘ p` between two integrable real-valued fields.
    refine integrable_of_le_of_le hp_meas hlower_ae hupper_ae hlower_int hupper_int
  rw [mem_effectiveDomain_iff, integralFunctional_coe μ, pointwiseIntegralFunctional]
  let hbranch :
      Integrable (fun ω ↦ EReal.toReal (φ (p ω))) μ ∧
        ∀ᵐ ω ∂μ, (φ (p ω) : EReal) < ⊤ := ⟨hp_int, hp_fin⟩
  simpa [hbranch] using (EReal.coe_lt_top (∫ ω, EReal.toReal (φ (p ω)) ∂μ : ℝ))

/-- Helper for Proposition 24.13: almost-everywhere pointwise proximal identities upgrade to the
global residual-subgradient relation for the induced integral functional. -/
private theorem mem_subdifferential_integralFunctional_of_ae_eq_pointwise_proximityOperator
    (φ : G → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(G))
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : G, (φ 0 : EReal) ≤ (φ z : EReal)))
    (x p : Ω →₂[μ] G)
    (hp : ∀ᵐ ω ∂μ, p ω = Prox[φ, hφ] (x ω)) :
    x - p ∈ (∂ integralFunctional μ φ) p := by
  have hp_dom :
      p ∈ effectiveDomain (integralFunctional μ φ) :=
    mem_effectiveDomain_integralFunctional_of_ae_eq_pointwise_proximityOperator
      φ hφ hfinite_or_nonneg x p hp
  -- Proposition 16.63 is the canonical bridge from pointwise subgradients to the global one.
  refine
    (mem_subdifferential_integralFunctional_iff_ae_mem_subdifferential
      φ hφ hfinite_or_nonneg hp_dom).2 ?_
  have hsub_ae :
      ∀ᵐ ω ∂μ, x ω - p ω ∈ (∂ φ) (p ω) :=
    ae_sub_mem_subdifferential_of_ae_eq_pointwise_proximityOperator φ hφ x p hp
  have hxp :
      ∀ᵐ ω ∂μ, ((x - p) ω : G) = x ω - p ω := by
    simpa [Pi.sub_apply] using (Lp.coeFn_sub x p)
  -- Build the pointwise residual-subgradient relation in the exact normal form expected by
  -- Proposition 16.63.
  filter_upwards [hsub_ae, hxp] with ω hsub hxpω
  rw [hxpω]
  exact hsub

/-- Proposition 24.13: let `φ ∈ Γ₀(G)` and suppose that either `μ Set.univ < ∞` or
`φ ≥ φ 0 = 0`. If an `L²` field `p` satisfies `p ω = Prox[φ, hφ] (x ω)` for `μ`-almost every
`ω`, then `p` is a proximal point of the induced integral functional `integralFunctional μ φ`
at `x`. -/
theorem isProxPoint_integralFunctional_of_ae_eq_pointwise_proximityOperator
    (φ : G → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(G))
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : G, (φ 0 : EReal) ≤ (φ z : EReal)))
    (x p : Ω →₂[μ] G)
    (hp : ∀ᵐ ω ∂μ, p ω = Prox[φ, hφ] (x ω)) :
    IsProxPoint (integralFunctional μ φ) x p := by
  let hF : integralFunctional μ φ ∈ Γ₀(Ω →₂[μ] G) :=
    integralFunctional_mem_gammaZero μ φ hφ hfinite_or_nonneg
  have hsub :
      x - p ∈ (∂ integralFunctional μ φ) p :=
    mem_subdifferential_integralFunctional_of_ae_eq_pointwise_proximityOperator
      φ hφ hfinite_or_nonneg x p hp
  have hprox :
      p = Prox[integralFunctional μ φ, hF] x := by
    -- The global residual-subgradient relation is exactly the integral-functional proximal
    -- characterization from Proposition 16.44.
    exact (eq_proximityOperator_iff_sub_mem_subdifferential hF x p).2 hsub
  -- Rewrite the canonical proximal-point witness along the identified global proximal value.
  rw [hprox]
  exact proximityOperator_isProxPoint
    (integralFunctional μ φ)
    (hasUniqueProxPoint_of_mem_gammaZero (integralFunctional μ φ) hF) x

/-- Proposition 24.13: let `φ ∈ Γ₀(G)` and suppose that either `μ Set.univ < ∞` or
`φ ≥ φ 0 = 0`. If an `L²` field `p` satisfies `p ω = Prox[φ, hφ] (x ω)` for `μ`-almost every
`ω`, then `p` is the proximal point of the induced integral functional `integralFunctional μ φ`
at `x`. -/
theorem eq_proximityOperator_integralFunctional_of_ae_eq_pointwise_proximityOperator
    (φ : G → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(G))
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : G, (φ 0 : EReal) ≤ (φ z : EReal)))
    (x p : Ω →₂[μ] G)
    (hp : ∀ᵐ ω ∂μ, p ω = Prox[φ, hφ] (x ω)) :
    p =
      Prox[
        integralFunctional μ φ,
        integralFunctional_mem_gammaZero μ φ hφ hfinite_or_nonneg] x := by
  let hIntegral : integralFunctional μ φ ∈ Γ₀(Ω →₂[μ] G) :=
    integralFunctional_mem_gammaZero μ φ hφ hfinite_or_nonneg
  exact
    eq_proximityOperator_of_isProxPoint (integralFunctional μ φ)
      (hasUniqueProxPoint_of_mem_gammaZero (integralFunctional μ φ) hIntegral)
      (isProxPoint_integralFunctional_of_ae_eq_pointwise_proximityOperator
        φ hφ hfinite_or_nonneg x p hp)

end BasicProperties

end

end ERealFunction
