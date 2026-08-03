import Mathlib.Tactic.Recall
import BauschkeLean.Chap09.Proposition_9_40
import BauschkeLean.Chap13.Proposition_13_22
import BauschkeLean.Chap13.Corollary_13_38

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal InnerProductSpace

universe u v

namespace ERealFunction

section FenchelMoreau

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]

/- Helper recall: Proposition 13.50 (1) on the `f`-side uses the canonical owner from
Proposition 9.40. -/
recall integralFunctional_mem_gammaZero

variable (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))

/-- Helper for Proposition 13.50: clause (i) for
`f = integralFunctional μ φ`. Under the stated finite-measure or nonnegativity hypothesis, the
integral functional induced by `φ` belongs to `Γ₀(L²((Ω, 𝓕, μ); H))`. -/
theorem integralFunctional_phi_mem_gammaZero
    (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))) :
    integralFunctional μ φ ∈ Γ₀(Ω →₂[μ] H) := by
  -- This is exactly Proposition 9.40 applied to the given integrand `φ`.
  simpa using ERealFunction.integralFunctional_mem_gammaZero μ φ hφ hfinite_or_nonneg

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H] in
/-- Helper for Proposition 13.50: if `φ` attains its minimum value `0` at the origin, then so
does its canonical `Γ₀`-valued Fenchel conjugate. -/
theorem gammaZeroConjugate_has_zero_minimum
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)) :
    ((gammaZeroConjugate φ hφ 0 : Set.Ioi (⊥ : EReal)) : EReal) = 0 ∧
      ∀ z : H,
        ((gammaZeroConjugate φ hφ 0 : Set.Ioi (⊥ : EReal)) : EReal) ≤
          ((gammaZeroConjugate φ hφ z : Set.Ioi (⊥ : EReal)) : EReal) := by
  rcases hzero_min with ⟨hzero, hmin⟩
  constructor
  · -- Rewrite the packaged conjugate to the raw Fenchel conjugate and evaluate it at `0`.
    rw [gammaZeroConjugate_apply]
    exact conjugate_zero_eq_zero_of_minimum_at_zero φ.asEReal
      (fun z ↦ by simpa using hmin z)
      (by simpa using hzero)
  · intro z
    -- The same minimum-at-zero hypothesis transfers pointwise to the conjugate.
    rw [gammaZeroConjugate_apply, gammaZeroConjugate_apply]
    exact conjugate_zero_le_conjugate_of_minimum_at_zero φ.asEReal
      (fun y ↦ by simpa using hmin y)
      (by simpa using hzero)
      z

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H] in
/-- Helper for Proposition 13.50: coercing the packaged canonical conjugate back to `EReal`
recovers the raw Fenchel conjugate of `φ`. -/
private theorem gammaZeroConjugate_asEReal_eq_conjugate :
    (gammaZeroConjugate φ hφ).asEReal = φ.asEReal∗ :=
  rfl

/-- Helper for Proposition 13.50: the canonical `Γ₀(H)` Fenchel conjugate is involutive on
members of `Γ₀(H)`. This local copy keeps the file dependency-closed under the canonical
`Corollary_13_38` conjugate owner. -/
private theorem gammaZeroConjugate_gammaZeroConjugate_local :
    gammaZeroConjugate (gammaZeroConjugate φ hφ) (gammaZeroConjugate_mem_gammaZero hφ) = φ := by
  -- Apply Fenchel--Moreau to the original integrand and rewrite the packaged biconjugate.
  ext x
  simpa [Function.asEReal] using congrFun (biconjugate_eq_of_mem_gammaZero hφ) x

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H] in
/-- Helper for Proposition 13.50: properness of `φ ∈ Γ₀(H)` supplies a concrete point of the
epigraph of `φ.asEReal`. -/
private theorem denseEpigraph_nonempty (hφ : φ ∈ Γ₀(H)) :
    Nonempty (epigraph φ.asEReal) := by
  rcases hφ.2.nonempty with ⟨x, hx⟩
  refine ⟨⟨(x, (φ x : EReal).toReal), ?_⟩⟩
  -- Put the effective-domain witness on the canonical real-height slice of the epigraph.
  rw [mem_epigraph_iff]
  have hx_top : (φ x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  simpa using EReal.le_coe_toReal hx_top

/-- Helper for Proposition 13.50: clause (i) for
`g = integralFunctional μ (gammaZeroConjugate φ hφ)`. Under the same hypotheses, the integral
functional induced by the Fenchel conjugate `φ*` belongs to `Γ₀(L²((Ω, 𝓕, μ); H))`. -/
theorem integralFunctional_gammaZeroConjugate_mem_gammaZero
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))) :
    integralFunctional μ (gammaZeroConjugate φ hφ) ∈ Γ₀(Ω →₂[μ] H) := by
  -- Apply Proposition 9.40 to the canonical conjugate integrand, which is again in `Γ₀(H)`.
  refine integralFunctional_mem_gammaZero μ (gammaZeroConjugate φ hφ)
    (gammaZeroConjugate_mem_gammaZero hφ) ?_
  rcases hfinite_or_nonneg with hfinite | hzero_min
  · -- The finite-measure branch is unchanged for the conjugate integrand.
    exact Or.inl hfinite
  · -- Proposition 13.22 transfers the minimum-at-zero hypothesis to `φ*`.
    exact Or.inr (gammaZeroConjugate_has_zero_minimum (φ := φ) (hφ := hφ) hzero_min)

/-- Helper for Proposition 13.50: a point in the effective domain of `integralFunctional μ ψ`
lies on the real integral branch of `pointwiseIntegralFunctional ψ`. -/
private theorem integralFunctional_branch_of_mem_effectiveDomain
    (ψ : H → Set.Ioi (⊥ : EReal)) {x : Ω →₂[μ] H}
    (hx : x ∈ effectiveDomain (integralFunctional μ ψ)) :
    Integrable (fun ω ↦ EReal.toReal (ψ (x ω))) μ ∧
      ∀ᵐ ω ∂μ, (ψ (x ω) : EReal) < ⊤ := by
  -- Rewrite the effective-domain condition into the Chapter 8 branch condition.
  have hx' : x ∈ pointwiseIntegralFunctionalDomain ψ := by
    simpa [pointwiseIntegralFunctionalDomain, integralFunctional_coe μ] using hx
  rw [pointwiseIntegralFunctionalDomain_eq] at hx'
  exact hx'

/-- Helper for Proposition 13.50: on its effective domain, `integralFunctional μ ψ` evaluates to
the real integral of the pointwise `toReal` integrand. -/
private theorem integralFunctional_apply_eq_integral_toReal_of_mem_effectiveDomain
    (ψ : H → Set.Ioi (⊥ : EReal)) {x : Ω →₂[μ] H}
    (hx : x ∈ effectiveDomain (integralFunctional μ ψ)) :
    (integralFunctional μ ψ x : EReal) =
      ((∫ ω, EReal.toReal (ψ (x ω)) ∂μ : ℝ) : EReal) := by
  -- The effective-domain hypothesis selects the finite branch in the definition.
  have hbranch := integralFunctional_branch_of_mem_effectiveDomain (μ := μ) ψ hx
  rw [integralFunctional_coe μ ψ, pointwiseIntegralFunctional, if_pos hbranch]

/-- Helper for Proposition 13.50: in the zero-minimum branch, converting the conjugate integral
functional to `ENNReal` agrees with the `lintegral` of the pointwise conjugate integrand. The
extra minimum-at-zero hypothesis is essential here because it supplies the nonnegativity needed by
`ofReal_integral_eq_lintegral_ofReal`. -/
private theorem integralFunctional_gammaZeroConjugate_toENNReal_eq_lintegral_of_mem_effectiveDomain
    [μ.IsComplete] [SigmaFinite μ]
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))
    {u : Ω →₂[μ] H}
    (hu_eff : u ∈ effectiveDomain (integralFunctional μ (gammaZeroConjugate φ hφ))) :
    ((integralFunctional μ (gammaZeroConjugate φ hφ) u : EReal).toENNReal =
      ∫⁻ ω,
        ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal)).toENNReal ∂μ) := by
  let φStar : H → Set.Ioi (⊥ : EReal) := gammaZeroConjugate φ hφ
  have hu_branch :=
    integralFunctional_branch_of_mem_effectiveDomain (μ := μ) φStar (x := u) hu_eff
  rcases gammaZeroConjugate_has_zero_minimum (φ := φ) (hφ := hφ) hzero_min with
    ⟨hφStar0, hφStar_min⟩
  have hφStar_nonneg :
      0 ≤ᵐ[μ] fun ω ↦ EReal.toReal (φStar (u ω) : EReal) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hnonneg : (0 : EReal) ≤ (φStar (u ω) : EReal) := by
      have hminω := hφStar_min (u ω)
      rw [hφStar0] at hminω
      simpa [φStar] using hminω
    exact EReal.toReal_nonneg hnonneg
  have htoENN_eq :
      (fun ω ↦ (((φStar (u ω) : EReal)).toENNReal)) =ᵐ[μ]
        fun ω ↦ ENNReal.ofReal (EReal.toReal (φStar (u ω) : EReal)) := by
    filter_upwards [hu_branch.2] with ω hω
    exact EReal.toENNReal_of_ne_top (lt_top_iff_ne_top.mp hω)
  calc
    (integralFunctional μ φStar u : EReal).toENNReal
        = ENNReal.ofReal (∫ ω, EReal.toReal (φStar (u ω) : EReal) ∂μ) := by
            rw [integralFunctional_apply_eq_integral_toReal_of_mem_effectiveDomain
              (μ := μ) φStar (x := u) hu_eff]
            exact EReal.real_coe_toENNReal _
    _ = ∫⁻ ω, ENNReal.ofReal (EReal.toReal (φStar (u ω) : EReal)) ∂μ := by
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hu_branch.1 hφStar_nonneg]
    _ =
        ∫⁻ ω, ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal)).toENNReal ∂μ := by
          refine lintegral_congr_ae ?_
          simpa [φStar] using htoENN_eq.symm

/-- Helper for Proposition 13.50: outside the effective domain of an integral functional, the
packaged `]-∞,+∞]` value is necessarily `⊤`. -/
private theorem integralFunctional_eq_top_of_not_mem_effectiveDomain
    (ψ : H → Set.Ioi (⊥ : EReal)) {x : Ω →₂[μ] H}
    (hx : x ∉ effectiveDomain (integralFunctional μ ψ)) :
    (integralFunctional μ ψ x : EReal) = ⊤ := by
  -- A finite-above value would place `x` back in the effective domain.
  exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))

/-- Helper for Proposition 13.50: the real Fenchel--Young defect is nonnegative when both
pointwise values are finite. -/
private theorem fenchelYoungDefect_nonneg
    (x u : H) (hx : (φ x : EReal) < ⊤)
    (hu : (((gammaZeroConjugate φ hφ) u : Set.Ioi (⊥ : EReal)) : EReal) < ⊤) :
    0 ≤ EReal.toReal (φ x) +
      EReal.toReal ((((gammaZeroConjugate φ hφ) u : Set.Ioi (⊥ : EReal)) : EReal)) -
        ⟪x, u⟫_ℝ := by
  have hx_top : (φ x : EReal) ≠ ⊤ := ne_of_lt hx
  have hx_bot : (φ x : EReal) ≠ ⊥ := ne_of_gt (φ x).2
  have hu_top :
      ((((gammaZeroConjugate φ hφ) u : Set.Ioi (⊥ : EReal)) : EReal)) ≠ ⊤ := ne_of_lt hu
  have hu_bot :
      ((((gammaZeroConjugate φ hφ) u : Set.Ioi (⊥ : EReal)) : EReal)) ≠ ⊥ := by
    exact ne_of_gt (((gammaZeroConjugate φ hφ) u).2)
  let hxReal : ℝ := EReal.toReal (φ x)
  let huReal : ℝ :=
    EReal.toReal ((((gammaZeroConjugate φ hφ) u : Set.Ioi (⊥ : EReal)) : EReal))
  have hfy :
      ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤
        (φ x : EReal) + ((gammaZeroConjugate φ hφ) u : EReal) := by
    -- Route correction: keep `gammaZeroConjugate_apply` confined to this finite-branch bridge.
    simpa [gammaZeroConjugate_apply] using
      fenchel_young_inequality (f := φ.asEReal) (isProper_of_mem_gammaZero hφ) x u
  have hx_coe :
        (φ x : EReal) = ((hxReal : ℝ) : EReal) := by
      simpa [hxReal] using (EReal.coe_toReal hx_top hx_bot).symm
  have hu_coe :
        (((gammaZeroConjugate φ hφ) u : Set.Ioi (⊥ : EReal)) : EReal) =
          ((huReal : ℝ) : EReal) := by
      simpa [huReal] using (EReal.coe_toReal hu_top hu_bot).symm
  have hsum_eq :
      (φ x : EReal) + ((gammaZeroConjugate φ hφ) u : EReal) =
        (((hxReal + huReal : ℝ)) : EReal) := by
    calc
      (φ x : EReal) + ((gammaZeroConjugate φ hφ) u : EReal)
          = (((hxReal : ℝ) : EReal) + ((huReal : ℝ) : EReal)) := by
            rw [hx_coe, hu_coe]
      _ =
          (((hxReal + huReal : ℝ)) : EReal) := by
            rw [EReal.coe_add]
  have hfy' :
      ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤
        (((EReal.toReal (φ x) +
            EReal.toReal ((((gammaZeroConjugate φ hφ) u : Set.Ioi (⊥ : EReal)) : EReal)) : ℝ)) :
            EReal) := by
    -- Rewrite both finite `EReal` terms as real casts before returning to `ℝ`.
    simpa [hxReal, huReal] using hfy.trans_eq hsum_eq
  have hreal :
      ⟪x, u⟫_ℝ ≤
        EReal.toReal (φ x) +
          EReal.toReal ((((gammaZeroConjugate φ hφ) u : Set.Ioi (⊥ : EReal)) : EReal)) := by
    exact_mod_cast hfy'
  linarith

/-- Helper for Proposition 13.50: the Fenchel conjugate of the integral functional is bounded
above by the integral functional of the pointwise conjugate. -/
private theorem conjugate_integralFunctional_le_integralFunctional_gammaZeroConjugate
    (u : Ω →₂[μ] H) :
    conjugate ((integralFunctional μ φ).asEReal) u ≤
      (integralFunctional μ (gammaZeroConjugate φ hφ) u : EReal) := by
  let φStar : H → Set.Ioi (⊥ : EReal) := gammaZeroConjugate φ hφ
  by_cases hu_eff : u ∈ effectiveDomain (integralFunctional μ φStar)
  · rw [conjugate_apply]
    refine iSup_le fun x ↦ ?_
    by_cases hx : x ∈ effectiveDomain (integralFunctional μ φ)
    · have hx_branch :=
        integralFunctional_branch_of_mem_effectiveDomain (μ := μ) φ (x := x) hx
      have hu_branch :=
        integralFunctional_branch_of_mem_effectiveDomain (μ := μ) φStar (x := u) hu_eff
      let defect : Ω → ℝ := fun ω ↦
        EReal.toReal (φ (x ω)) +
          EReal.toReal (φStar (u ω) : EReal) -
            ⟪x ω, u ω⟫_ℝ
      have hinner_int : Integrable (fun ω ↦ ⟪x ω, u ω⟫_ℝ) μ :=
        MeasureTheory.L2.integrable_inner x u
      have hdefect_int : Integrable defect μ := by
        -- The pointwise defect is integrable on the real branch of both integral functionals.
        exact (hx_branch.1.add hu_branch.1).sub hinner_int
      have hdefect_nonneg : 0 ≤ᵐ[μ] defect := by
        -- Integrate the pointwise Fenchel--Young defect only after both branches are finite.
        filter_upwards [hx_branch.2, hu_branch.2] with ω hxω huω
        exact fenchelYoungDefect_nonneg (φ := φ) (hφ := hφ) (x ω) (u ω) hxω huω
      have hreal_ineq :
          (∫ ω, ⟪x ω, u ω⟫_ℝ ∂μ : ℝ) ≤
            (∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) +
              ∫ ω, EReal.toReal (φStar (u ω) : EReal) ∂μ := by
        have hmono : 0 ≤ ∫ ω, defect ω ∂μ := integral_nonneg_of_ae hdefect_nonneg
        have hexpand :
            (∫ ω, defect ω ∂μ : ℝ) =
              (∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) +
                ∫ ω, EReal.toReal (φStar (u ω) : EReal) ∂μ -
                  ∫ ω, ⟪x ω, u ω⟫_ℝ ∂μ := by
          simp [defect, integral_sub, integral_add, hx_branch.1, hu_branch.1, hinner_int]
        rw [hexpand] at hmono
        linarith
      have hx_eval :
          (integralFunctional μ φ x : EReal) =
            ((∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) : EReal) := by
        exact integralFunctional_apply_eq_integral_toReal_of_mem_effectiveDomain
          (μ := μ) φ (x := x) hx
      have hu_eval :
          (integralFunctional μ φStar u : EReal) =
            ((∫ ω, EReal.toReal (φStar (u ω) : EReal) ∂μ : ℝ) : EReal) := by
        exact integralFunctional_apply_eq_integral_toReal_of_mem_effectiveDomain
          (μ := μ) φStar (x := u) hu_eff
      -- Convert the integrated real inequality back to the affine-defect term in `conjugate_apply`.
      have hreal_defect :
          (∫ ω, ⟪x ω, u ω⟫_ℝ ∂μ : ℝ) -
              ∫ ω, EReal.toReal (φ (x ω)) ∂μ ≤
            ∫ ω, EReal.toReal (φStar (u ω) : EReal) ∂μ := by
        linarith
      have hdefect :
          (((⟪x, u⟫_ℝ : ℝ) : EReal) - (integralFunctional μ φ x : EReal)) ≤
            (integralFunctional μ φStar u : EReal) := by
        calc
          (((⟪x, u⟫_ℝ : ℝ) : EReal) - (integralFunctional μ φ x : EReal))
              = ((((∫ ω, ⟪x ω, u ω⟫_ℝ ∂μ : ℝ) -
                    ∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ)) : EReal) := by
                  rw [MeasureTheory.L2.inner_def, hx_eval, ← EReal.coe_sub]
          _ ≤ ((∫ ω, EReal.toReal (φStar (u ω) : EReal) ∂μ : ℝ) : EReal) := by
                exact_mod_cast hreal_defect
          _ = (integralFunctional μ φStar u : EReal) := hu_eval.symm
      simpa [Function.asEReal] using hdefect
    · have hx_top : (integralFunctional μ φ x : EReal) = ⊤ :=
        integralFunctional_eq_top_of_not_mem_effectiveDomain (μ := μ) φ hx
      have hbot :
          (((⟪x, u⟫_ℝ : ℝ) : EReal) -
              (((integralFunctional μ φ x : Set.Ioi (⊥ : EReal)) : EReal))) = ⊥ := by
        have hx_top' : pointwiseIntegralFunctional φ x = ⊤ := by
          simpa [integralFunctional_coe μ φ] using hx_top
        calc
          (((⟪x, u⟫_ℝ : ℝ) : EReal) -
              (((integralFunctional μ φ x : Set.Ioi (⊥ : EReal)) : EReal)))
              = (((⟪x, u⟫_ℝ : ℝ) : EReal) - pointwiseIntegralFunctional φ x) := by
                  rfl
          _ = ⊥ := by
                simp [hx_top']
      have hbot' :
          (((⟪x, u⟫_ℝ : ℝ) : EReal) -
              Function.asEReal (integralFunctional μ φ) x) = ⊥ := by
        simpa [Function.asEReal, integralFunctional_coe μ φ] using hbot
      rw [hbot']
      exact bot_le
  · have hu_top : (integralFunctional μ φStar u : EReal) = ⊤ :=
      integralFunctional_eq_top_of_not_mem_effectiveDomain (μ := μ) φStar hu_eff
    rw [hu_top]
    exact le_top

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H] in
/-- Helper for Proposition 13.50: the pointwise conjugate integrand is the supremum of the affine
epigraph slices of `φ`. This is the structural starting point for the reverse inequality. -/
private theorem gammaZeroConjugate_eq_sSup_image_epigraph
    (u : H) :
    ((gammaZeroConjugate φ hφ u : Set.Ioi (⊥ : EReal)) : EReal) =
      sSup ((fun p : H × ℝ ↦ ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal)) '' epigraph φ.asEReal) := by
  -- Route correction: use the already-built Proposition 13.10 epigraph-supremum identity
  -- directly on `φ.asEReal`, instead of introducing a new Corollary 13.42 import.
  calc
    ((gammaZeroConjugate φ hφ u : Set.Ioi (⊥ : EReal)) : EReal) =
        conjugate φ.asEReal u := by
          rw [gammaZeroConjugate_apply]
    _ =
        sSup ((fun p : H × ℝ ↦ ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal)) '' epigraph φ.asEReal) := by
          exact conjugate_eq_sSup_image_epigraph (f := φ.asEReal) u

omit [MeasurableSpace H] [BorelSpace H] in
/-- Helper for Proposition 13.50: a dense sequence in the epigraph of `φ` already recovers the
pointwise conjugate value as the supremum of the corresponding affine slices. This isolates the
only remaining normalization step before the measurable truncation argument. -/
private theorem denseEpigraphSlices_iSup
    (u : H) :
    let _ : Nonempty (epigraph φ.asEReal) := by
      exact denseEpigraph_nonempty (φ := φ) hφ
    let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
    ((gammaZeroConjugate φ hφ u : Set.Ioi (⊥ : EReal)) : EReal) =
      ⨆ n, ((⟪(epiDense n).1.1, u⟫_ℝ - (epiDense n).1.2 : ℝ) : EReal) := by
  classical
  -- Choose a concrete dense sequence in the epigraph once the properness witness supplies a point.
  letI : Nonempty (epigraph φ.asEReal) := denseEpigraph_nonempty (φ := φ) hφ
  let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
  let slice : epigraph φ.asEReal → EReal :=
    fun p ↦ ((⟪p.1.1, u⟫_ℝ - p.1.2 : ℝ) : EReal)
  have hs : Dense (Set.range epiDense) :=
    TopologicalSpace.denseRange_denseSeq (epigraph φ.asEReal)
  have hcont : Continuous slice := by
    -- The affine slice map is continuous on the epigraph subtype, so dense-range `iSup` applies.
    have h1 : Continuous fun p : epigraph φ.asEReal ↦ p.1.1 :=
      continuous_fst.comp continuous_subtype_val
    have h2 : Continuous fun p : epigraph φ.asEReal ↦ p.1.2 :=
      continuous_snd.comp continuous_subtype_val
    have hreal : Continuous fun p : epigraph φ.asEReal ↦ (⟪p.1.1, u⟫_ℝ - p.1.2 : ℝ) :=
      (h1.inner continuous_const).sub h2
    exact continuous_coe_real_ereal.comp hreal
  have hsup : (⨆ p : epigraph φ.asEReal, slice p) = ⨆ q : Set.range epiDense, slice q := by
    -- Replace the full epigraph supremum by the supremum over the dense sequence.
    symm
    exact hs.ciSup' hcont
  have himage :
      ((fun p : H × ℝ ↦ ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal)) '' epigraph φ.asEReal) =
        slice '' Set.univ := by
    -- Repackage the epigraph image through the subtype-valued slice map.
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, trivial, rfl⟩
    · rintro ⟨p, -, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
  have hrange :
      Set.range (fun q : Set.range epiDense ↦ slice q) = Set.range (fun n ↦ slice (epiDense n)) := by
    -- Rewrite the supremum over the dense range subtype back to an ordinary `ℕ`-indexed `iSup`.
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      rcases q.2 with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simp [hn]
    · rintro ⟨n, rfl⟩
      exact ⟨⟨epiDense n, ⟨n, rfl⟩⟩, rfl⟩
  calc
    ((gammaZeroConjugate φ hφ u : Set.Ioi (⊥ : EReal)) : EReal)
        = sSup ((fun p : H × ℝ ↦ ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal)) '' epigraph φ.asEReal) := by
            exact gammaZeroConjugate_eq_sSup_image_epigraph (φ := φ) (hφ := hφ) u
    _ = ⨆ p : epigraph φ.asEReal, slice p := by
          rw [himage, Set.image_univ, ← sSup_range]
    _ = ⨆ q : Set.range epiDense, slice q := hsup
    _ = ⨆ n, ((⟪(epiDense n).1.1, u⟫_ℝ - (epiDense n).1.2 : ℝ) : EReal) := by
          rw [← sSup_range, hrange, sSup_range]

omit [MeasurableSpace H] [BorelSpace H] in
/-- Helper for Proposition 13.50: every affine slice coming from the chosen dense epigraph
sequence is individually bounded above by the pointwise conjugate value. -/
private theorem denseEpigraphSlice_le_gammaZeroConjugate
    [Nonempty (epigraph φ.asEReal)] (u : H) (n : ℕ) :
    let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
    ((⟪(epiDense n).1.1, u⟫_ℝ - (epiDense n).1.2 : ℝ) : EReal) ≤
      ((gammaZeroConjugate φ hφ u : Set.Ioi (⊥ : EReal)) : EReal) := by
  classical
  let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
  -- Each selected epigraph point contributes one admissible affine defect in the supremum formula.
  rw [gammaZeroConjugate_eq_sSup_image_epigraph (φ := φ) (hφ := hφ) u]
  have hmem :
      ((⟪(epiDense n).1.1, u⟫_ℝ - (epiDense n).1.2 : ℝ) : EReal) ∈
        (fun p : H × ℝ ↦ ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal)) '' epigraph φ.asEReal := by
    exact ⟨(epiDense n).1, (epiDense n).2, rfl⟩
  exact le_sSup hmem

omit [MeasurableSpace H] [BorelSpace H] in
/-- Helper for Proposition 13.50: every finite prefix supremum of the dense epigraph slices
remains below the pointwise conjugate value. -/
private theorem denseEpigraphSlices_prefix_le_gammaZeroConjugate
    [Nonempty (epigraph φ.asEReal)] (u : H) (N : ℕ) :
    let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
    (⨆ n : Fin (N + 1),
        ((⟪(epiDense n.1).1.1, u⟫_ℝ - (epiDense n.1).1.2 : ℝ) : EReal)) ≤
      ((gammaZeroConjugate φ hφ u : Set.Ioi (⊥ : EReal)) : EReal) := by
  classical
  let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
  -- Bound each member of the finite prefix by the full conjugate value and then take the supremum.
  exact iSup_le fun n : Fin (N + 1) ↦ by
    simpa using denseEpigraphSlice_le_gammaZeroConjugate (φ := φ) (hφ := hφ) u n.1

/-- Helper for Proposition 13.50: each affine slice from the dense epigraph sequence is a
measurable `EReal`-valued function on `Ω`. -/
private theorem measurable_denseEpigraphSlice
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (n : ℕ) :
    let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
    Measurable fun ω ↦ ((⟪(epiDense n).1.1, u ω⟫_ℝ - (epiDense n).1.2 : ℝ) : EReal) := by
  let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
  have hu : Measurable fun ω ↦ u ω := (Lp.stronglyMeasurable u).measurable
  have hreal :
      Measurable fun ω ↦ (⟪(epiDense n).1.1, u ω⟫_ℝ - (epiDense n).1.2 : ℝ) :=
    (measurable_const.inner hu).sub measurable_const
  -- The slice is an affine map of the measurable `L²` representative.
  exact continuous_coe_real_ereal.measurable.comp hreal

/-- Helper for Proposition 13.50: the finite prefix supremum of the dense epigraph slices is a
measurable `EReal`-valued function on `Ω`. -/
private theorem measurable_denseEpigraphPrefixSup
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) :
    ∀ N : ℕ,
      let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
      Measurable fun ω ↦
        (Finset.range (N + 1)).sup
          (fun n ↦ ((⟪(epiDense n).1.1, u ω⟫_ℝ - (epiDense n).1.2 : ℝ) : EReal))
  | 0 => by
      let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
      -- The first prefix contains only the `n = 0` slice.
      simpa using measurable_denseEpigraphSlice (φ := φ) u 0
  | N + 1 => by
      let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
      have hprev := measurable_denseEpigraphPrefixSup u N
      have hlast := measurable_denseEpigraphSlice (φ := φ) u (N + 1)
      -- Rewrite the next prefix as the supremum of the previous prefix and the new slice.
      simpa [Finset.range_add_one, Finset.sup_insert] using hlast.sup hprev

/-- Helper for Proposition 13.50: the next dense-epigraph prefix supremum is obtained by a
measurable two-way split between the previous prefix and the new slice. This is the source-faithful
replacement for the stalled global argmax partition. -/
private theorem denseEpigraphPrefixSup_succ_split
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
    let prefixSup : ℕ → Ω → EReal := fun M ω ↦
      (Finset.range (M + 1)).sup
        (fun n ↦ ((⟪(epiDense n).1.1, u ω⟫_ℝ - (epiDense n).1.2 : ℝ) : EReal))
    let slice : Ω → EReal := fun ω ↦
      ((⟪(epiDense (N + 1)).1.1, u ω⟫_ℝ - (epiDense (N + 1)).1.2 : ℝ) : EReal)
    let winSet : Set Ω := {ω | prefixSup N ω ≤ slice ω}
    MeasurableSet winSet ∧
      prefixSup (N + 1) = fun ω ↦ if ω ∈ winSet then slice ω else prefixSup N ω := by
  let epiDense : ℕ → epigraph φ.asEReal := TopologicalSpace.denseSeq (epigraph φ.asEReal)
  let prefixSup : ℕ → Ω → EReal := fun M ω ↦
    (Finset.range (M + 1)).sup
      (fun n ↦ ((⟪(epiDense n).1.1, u ω⟫_ℝ - (epiDense n).1.2 : ℝ) : EReal))
  let slice : Ω → EReal := fun ω ↦
    ((⟪(epiDense (N + 1)).1.1, u ω⟫_ℝ - (epiDense (N + 1)).1.2 : ℝ) : EReal)
  let winSet : Set Ω := {ω | prefixSup N ω ≤ slice ω}
  have hprev : Measurable (prefixSup N) := by
    -- Reuse the existing measurable finite-prefix normalization for the old prefix.
    simpa [prefixSup, epiDense] using
      measurable_denseEpigraphPrefixSup (φ := φ) (u := u) N
  have hslice : Measurable slice := by
    -- The new slice is measurable by the one-step affine-slice lemma.
    simpa [slice, epiDense] using measurable_denseEpigraphSlice (φ := φ) u (N + 1)
  have hwin : MeasurableSet winSet := by
    -- The winner set is just the measurable comparison set for the two candidate slices.
    simpa [winSet] using measurableSet_le hprev hslice
  refine ⟨hwin, ?_⟩
  funext ω
  by_cases hω : ω ∈ winSet
  · have hω' : prefixSup N ω ≤ slice ω := by
      simpa [winSet] using hω
    -- On the winner set, the new slice realizes the next prefix supremum.
    calc
      prefixSup (N + 1) ω = slice ω ⊔ prefixSup N ω := by
        simp [prefixSup, slice, Finset.range_add_one, Finset.sup_insert]
      _ = slice ω := sup_eq_left.2 hω'
      _ = if ω ∈ winSet then slice ω else prefixSup N ω := by
        simp [hω]
  · have hω' : slice ω ≤ prefixSup N ω := by
      exact le_of_not_ge (by simpa [winSet] using hω)
    -- Off the winner set, the old prefix already dominates the new slice.
    calc
      prefixSup (N + 1) ω = slice ω ⊔ prefixSup N ω := by
        simp [prefixSup, slice, Finset.range_add_one, Finset.sup_insert]
      _ = prefixSup N ω := sup_eq_right.2 hω'
      _ = if ω ∈ winSet then slice ω else prefixSup N ω := by
        simp [hω]

/-- Helper for Proposition 13.50: fix the dense sequence in `epigraph φ.asEReal` used by the
finite-prefix approximation of the pointwise conjugate. -/
private noncomputable abbrev denseEpigraphSequence
    [Nonempty (epigraph φ.asEReal)] :
    ℕ → epigraph φ.asEReal :=
  TopologicalSpace.denseSeq (epigraph φ.asEReal)

/-- Helper for Proposition 13.50: the `n`th affine dense-epigraph slice associated with `u`. -/
private noncomputable def denseEpigraphSlice
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (n : ℕ) :
    Ω → EReal :=
  fun ω ↦
    ((⟪(denseEpigraphSequence (φ := φ) n).1.1, u ω⟫_ℝ -
        (denseEpigraphSequence (φ := φ) n).1.2 : ℝ) : EReal)

/-- Helper for Proposition 13.50: the finite supremum of the first `N + 1` dense-epigraph
affine slices. -/
private noncomputable def denseEpigraphPrefixSup
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    Ω → EReal :=
  fun ω ↦
    (Finset.range (N + 1)).sup
      (fun n ↦ denseEpigraphSlice (φ := φ) u n ω)

/-- Helper for Proposition 13.50: the measurable comparison set where the newest dense-epigraph
slice overtakes the previous finite prefix supremum. -/
private def denseEpigraphComparisonSet
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    Set Ω :=
  {ω | denseEpigraphPrefixSup (φ := φ) u N ω ≤
      denseEpigraphSlice (φ := φ) u (N + 1) ω}

/-- Helper for Proposition 13.50: the dense-epigraph comparison set is measurable. This is the
source-faithful winner partition behind the recursive prefix maximizer. -/
private theorem measurable_denseEpigraphComparisonSet
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    MeasurableSet (denseEpigraphComparisonSet (φ := φ) u N) := by
  -- Repackage the existing measurable two-way split theorem with named local objects.
  simpa [denseEpigraphComparisonSet, denseEpigraphPrefixSup, denseEpigraphSlice,
    denseEpigraphSequence] using
    (denseEpigraphPrefixSup_succ_split (φ := φ) u N).1

-- Comparisons against `denseEpigraphComparisonSet` use classical propositional decidability in the
-- theorem-local winner recursion.
attribute [local instance] Classical.propDecidable

/-- Helper for Proposition 13.50: the next finite prefix supremum is the piecewise maximum of the
old prefix and the new dense-epigraph slice along the measurable winner partition. -/
private theorem denseEpigraphPrefixSup_succ_eq_piecewise
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    denseEpigraphPrefixSup (φ := φ) u (N + 1) =
      fun ω ↦
        if ω ∈ denseEpigraphComparisonSet (φ := φ) u N then
          denseEpigraphSlice (φ := φ) u (N + 1) ω
        else
          denseEpigraphPrefixSup (φ := φ) u N ω := by
  -- This is exactly the previous split theorem after naming the prefix-supremum data.
  simpa [denseEpigraphComparisonSet, denseEpigraphPrefixSup, denseEpigraphSlice,
    denseEpigraphSequence] using
    (denseEpigraphPrefixSup_succ_split (φ := φ) u N).2

/-- Helper for Proposition 13.50: recursively choose one dense epigraph point realizing the
current finite prefix supremum. The point-valued winner tracks both the primal vector and the real
epigraph height, avoiding the false stronger claim that the `φ`-defect itself equals the prefix
slice exactly. -/
private noncomputable def denseEpigraphPrefixWinnerPoint
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) :
    ℕ → Ω → epigraph φ.asEReal
  | 0 => fun _ ↦ denseEpigraphSequence (φ := φ) 0
  | N + 1 => fun ω ↦
      if hω : ω ∈ denseEpigraphComparisonSet (φ := φ) u N then
        denseEpigraphSequence (φ := φ) (N + 1)
      else
        denseEpigraphPrefixWinnerPoint u N ω

/-- Helper for Proposition 13.50: the winner-point recursion is measurable because each step only
splits between a constant dense-epigraph point and the previous measurable winner point. -/
private theorem measurable_denseEpigraphPrefixWinnerPoint
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) :
    ∀ N : ℕ, Measurable (denseEpigraphPrefixWinnerPoint (φ := φ) u N)
  | 0 => by
      -- The base winner point is constant.
      simpa [denseEpigraphPrefixWinnerPoint]
  | N + 1 => by
      classical
      have hprev := measurable_denseEpigraphPrefixWinnerPoint u N
      have hwin := measurable_denseEpigraphComparisonSet (φ := φ) u N
      -- Each recursive step is a measurable piecewise choice between two measurable branches.
      simpa [denseEpigraphPrefixWinnerPoint] using
        Measurable.piecewise hwin measurable_const hprev

/-- Helper for Proposition 13.50: the affine slice associated with the recursively chosen dense
epigraph point is exactly the finite prefix supremum. This is the verified skeleton behind the
later `L²` competitor construction. -/
private theorem denseEpigraphPrefixWinnerPoint_slice_eq_prefixSup
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) :
    ∀ N : ℕ, ∀ ω : Ω,
      denseEpigraphPrefixSup (φ := φ) u N ω =
        ((⟪(denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1, u ω⟫_ℝ -
            (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.2 : ℝ) : EReal)
  | 0, ω => by
      -- At the first step, the winner point is the first dense epigraph point.
      simp [denseEpigraphPrefixSup, denseEpigraphSlice, denseEpigraphPrefixWinnerPoint,
        denseEpigraphSequence]
  | N + 1, ω => by
      classical
      have hrec := denseEpigraphPrefixWinnerPoint_slice_eq_prefixSup u N ω
      have hsplit :=
        congrFun (denseEpigraphPrefixSup_succ_eq_piecewise (φ := φ) u N) ω
      by_cases hω :
          ω ∈ denseEpigraphComparisonSet (φ := φ) u N
      · -- On the winner set, the new dense-epigraph point realizes the next prefix slice.
        simp [denseEpigraphPrefixWinnerPoint, hω, denseEpigraphSlice] at hsplit ⊢
        exact hsplit
      · -- Off the winner set, the recursion keeps the previous winner point and prefix value.
        simp [denseEpigraphPrefixWinnerPoint, hω] at hsplit ⊢
        exact hsplit.trans hrec

/-- Helper for Proposition 13.50: every recursive winner point is one of the first `N + 1`
epigraph points in the chosen dense sequence. This finite-range description is the finite-measure
bridge for the global `L²` competitor. -/
private theorem denseEpigraphPrefixWinnerPoint_eq_denseEpigraphSequence
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) :
    ∀ N : ℕ, ∀ ω : Ω,
      ∃ n : Fin (N + 1),
        denseEpigraphPrefixWinnerPoint (φ := φ) u N ω =
          denseEpigraphSequence (φ := φ) n.1
  | 0, _ => by
      -- At the base step, the winner point is exactly the first dense epigraph point.
      refine ⟨0, ?_⟩
      simp [denseEpigraphPrefixWinnerPoint, denseEpigraphSequence]
  | N + 1, ω => by
      classical
      by_cases hω : ω ∈ denseEpigraphComparisonSet (φ := φ) u N
      · -- On the winner set, the recursion picks the newest dense epigraph point.
        refine ⟨⟨N + 1, by simp⟩, ?_⟩
        simp [denseEpigraphPrefixWinnerPoint, hω, denseEpigraphSequence]
      · -- Off the winner set, the recursion keeps the earlier winner point.
        rcases denseEpigraphPrefixWinnerPoint_eq_denseEpigraphSequence (u := u) N ω with
          ⟨n, hn⟩
        refine ⟨⟨n.1, Nat.lt_trans n.2 (Nat.lt_succ_self (N + 1))⟩, ?_⟩
        simp [denseEpigraphPrefixWinnerPoint, hω, hn]

/-- Helper for Proposition 13.50: every recursive winner-point value is finite for `φ`, because
its stored real epigraph height witnesses membership in the effective domain. -/
private theorem denseEpigraphPrefixWinnerPoint_mem_effectiveDomain
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) (ω : Ω) :
    (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1 ∈ effectiveDomain φ := by
  let p := denseEpigraphPrefixWinnerPoint (φ := φ) u N ω
  -- Read the real-height epigraph witness through `mem_epigraph_iff`.
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt ((mem_epigraph_iff φ.asEReal p.1.1 p.1.2).mp p.2) (EReal.coe_lt_top _)

/-- Helper for Proposition 13.50: the global winner-point defect dominates the finite prefix
supremum pointwise. This is the finite-measure analogue of the truncated spanning-set estimate. -/
private theorem denseEpigraphPrefixWinnerPoint_defect_ge_prefixSup
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    ∀ ω : Ω,
      denseEpigraphPrefixSup (φ := φ) u N ω ≤
        (((⟪(denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1, u ω⟫_ℝ : ℝ) : EReal) -
          (φ ((denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1) : EReal)) := by
  intro ω
  let p := denseEpigraphPrefixWinnerPoint (φ := φ) u N ω
  have hp_epi : (φ p.1.1 : EReal) ≤ ((p.1.2 : ℝ) : EReal) := by
    -- The recorded real height bounds `φ` because the winner point lives in the epigraph.
    exact (mem_epigraph_iff φ.asEReal p.1.1 p.1.2).mp p.2
  have hp_slice :
      denseEpigraphPrefixSup (φ := φ) u N ω =
        (((⟪p.1.1, u ω⟫_ℝ : ℝ) : EReal) - ((p.1.2 : ℝ) : EReal)) := by
    -- Rewrite the exact winner-point slice into the subtraction form used by `conjugate_apply`.
    calc
      denseEpigraphPrefixSup (φ := φ) u N ω =
          ((⟪p.1.1, u ω⟫_ℝ - p.1.2 : ℝ) : EReal) := by
            simpa [p] using denseEpigraphPrefixWinnerPoint_slice_eq_prefixSup
              (φ := φ) u N ω
      _ = (((⟪p.1.1, u ω⟫_ℝ : ℝ) : EReal) - ((p.1.2 : ℝ) : EReal)) := by
            rw [EReal.coe_sub]
  -- Replacing the stored height by the true value `φ p.1.1` only enlarges the affine defect.
  calc
    denseEpigraphPrefixSup (φ := φ) u N ω
        = (((⟪p.1.1, u ω⟫_ℝ : ℝ) : EReal) - ((p.1.2 : ℝ) : EReal)) := hp_slice
    _ ≤ (((⟪p.1.1, u ω⟫_ℝ : ℝ) : EReal) - (φ p.1.1 : EReal)) := by
          exact EReal.sub_le_sub le_rfl hp_epi
    _ = (((⟪(denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1, u ω⟫_ℝ : ℝ) : EReal) -
          (φ ((denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1) : EReal)) := by
          simp [p]

/-- Helper for Proposition 13.50: on a finite-measure space, the first coordinate of the global
winner-point recursion is an `L²` field because it is measurable and takes only finitely many
values from the dense epigraph sequence. -/
private theorem denseEpigraphPrefixWinnerPoint_memLp_of_finiteMeasure
    [Nonempty (epigraph φ.asEReal)] [IsFiniteMeasure μ] (u : Ω →₂[μ] H) (N : ℕ) :
    MemLp (fun ω ↦ (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1) 2 μ := by
  let xNFun : Ω → H := fun ω ↦ (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1
  have hxNFun_meas : Measurable xNFun := by
    -- Compose the measurable winner-point recursion with the first-coordinate projection.
    simpa [xNFun] using
      ((measurable_fst.comp measurable_subtype_coe).comp
        (measurable_denseEpigraphPrefixWinnerPoint (φ := φ) (u := u) N))
  let C : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty
      (fun n : Fin (N + 1) ↦ ‖(denseEpigraphSequence (φ := φ) n.1).1.1‖)
  have hxNFun_bound : ∀ ω : Ω, ‖xNFun ω‖ ≤ C := by
    intro ω
    rcases denseEpigraphPrefixWinnerPoint_eq_denseEpigraphSequence (φ := φ) (u := u) N ω with
      ⟨n, hn⟩
    -- Finite-range membership turns the norm bound into a `Finset.sup'` estimate.
    calc
      ‖xNFun ω‖ = ‖(denseEpigraphSequence (φ := φ) n.1).1.1‖ := by
          simpa [xNFun] using congrArg (fun p : epigraph φ.asEReal ↦ ‖p.1.1‖) hn
      _ ≤ C := Finset.le_sup' (s := Finset.univ)
            (f := fun n : Fin (N + 1) ↦ ‖(denseEpigraphSequence (φ := φ) n.1).1.1‖)
            (Finset.mem_univ n)
  -- A bounded measurable field on a finite-measure space is automatically in `L²`.
  exact MemLp.of_bound hxNFun_meas.aestronglyMeasurable C
    (Filter.Eventually.of_forall hxNFun_bound)

/-- Helper for Proposition 13.50: on a finite-measure space, the packaged global winner-point
competitor lies in the effective domain of `integralFunctional μ φ`. -/
private theorem denseEpigraphPrefixWinnerPointLp_mem_effectiveDomain_of_finiteMeasure
    [Nonempty (epigraph φ.asEReal)] [IsFiniteMeasure μ]
    (hφ : φ ∈ Γ₀(H)) (u : Ω →₂[μ] H) (N : ℕ) :
    let xN : Ω →₂[μ] H :=
      (denseEpigraphPrefixWinnerPoint_memLp_of_finiteMeasure
        (φ := φ) (u := u) N).toLp
        (fun ω ↦ (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1)
    xN ∈ effectiveDomain (integralFunctional μ φ) := by
  let xNFun : Ω → H := fun ω ↦ (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1
  have hxNFun_meas : Measurable xNFun := by
    -- Reuse the measurable first-coordinate projection of the winner-point recursion.
    simpa [xNFun] using
      ((measurable_fst.comp measurable_subtype_coe).comp
        (measurable_denseEpigraphPrefixWinnerPoint (φ := φ) (u := u) N))
  let xNMem : MemLp xNFun 2 μ :=
    denseEpigraphPrefixWinnerPoint_memLp_of_finiteMeasure (φ := φ) (u := u) N
  let xN : Ω →₂[μ] H := xNMem.toLp xNFun
  have hxN_ae : xN =ᵐ[μ] xNFun := by
    -- The packaged `L²` field agrees a.e. with the measurable winner-point coordinate.
    simpa [xN, xNMem, xNFun] using xNMem.coeFn_toLp
  have hφxNFun_meas_ereal :
      Measurable fun ω ↦ (φ (xNFun ω) : EReal) := by
    -- The winner-point coordinate is measurable and `Γ₀` membership makes `φ` measurable.
    exact hφ.1.measurable.comp hxNFun_meas
  have hφxNFun_meas :
      AEStronglyMeasurable (fun ω ↦ EReal.toReal (φ (xNFun ω) : EReal)) μ := by
    -- The pointwise `toReal ∘ φ` integrand is measurable on the finite-range competitor.
    exact hφxNFun_meas_ereal.ereal_toReal.aestronglyMeasurable
  let Cφ : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty
      (fun n : Fin (N + 1) ↦
        |EReal.toReal (φ ((denseEpigraphSequence (φ := φ) n.1).1.1) : EReal)|)
  have hφxNFun_bound :
      ∀ ω : Ω, ‖EReal.toReal (φ (xNFun ω) : EReal)‖ ≤ Cφ := by
    intro ω
    rcases denseEpigraphPrefixWinnerPoint_eq_denseEpigraphSequence (φ := φ) (u := u) N ω with
      ⟨n, hn⟩
    -- The integrand also has finite range, so one `Finset.sup'` bound controls all values.
    calc
      ‖EReal.toReal (φ (xNFun ω) : EReal)‖ =
          |EReal.toReal (φ ((denseEpigraphSequence (φ := φ) n.1).1.1) : EReal)| := by
            simpa [Real.norm_eq_abs, xNFun] using
              congrArg (fun p : epigraph φ.asEReal ↦ ‖EReal.toReal (φ (p.1.1) : EReal)‖) hn
      _ ≤ Cφ := Finset.le_sup' (s := Finset.univ)
            (f := fun n : Fin (N + 1) ↦
              |EReal.toReal (φ ((denseEpigraphSequence (φ := φ) n.1).1.1) : EReal)|)
            (Finset.mem_univ n)
  have hφxNFun_int :
      Integrable (fun ω ↦ EReal.toReal (φ (xNFun ω) : EReal)) μ := by
    -- Finite range plus finite measure gives integrability of the pointwise `toReal` integrand.
    exact Integrable.of_bound hφxNFun_meas Cφ (Filter.Eventually.of_forall hφxNFun_bound)
  have hφxN_int :
      Integrable (fun ω ↦ EReal.toReal (φ (xN ω) : EReal)) μ := by
    refine hφxNFun_int.congr ?_
    filter_upwards [hxN_ae] with ω hω
    rw [hω]
  have hφxN_fin : ∀ᵐ ω ∂μ, (φ (xN ω) : EReal) < ⊤ := by
    filter_upwards [hxN_ae] with ω hω
    rw [hω]
    exact mem_effectiveDomain_iff.mp
      (denseEpigraphPrefixWinnerPoint_mem_effectiveDomain (φ := φ) (u := u) N ω)
  have hbranch :
      Integrable (fun ω ↦ EReal.toReal (φ (xN ω))) μ ∧
        ∀ᵐ ω ∂μ, (φ (xN ω) : EReal) < ⊤ := ⟨hφxN_int, hφxN_fin⟩
  have hbranch0 :
      Integrable (fun ω ↦ EReal.toReal (φ ((((xN : Ω →₂[μ] H) : Ω → H) ω)))) μ ∧
        ∀ᵐ ω ∂μ, (φ ((((xN : Ω →₂[μ] H) : Ω → H) ω)) : EReal) < ⊤ := by
    simpa using hbranch
  -- The finite-range winner-point competitor therefore lands on the finite branch of the integral
  -- functional definition.
  rw [mem_effectiveDomain_iff, integralFunctional_coe μ φ, pointwiseIntegralFunctional, if_pos hbranch0]
  exact EReal.coe_lt_top (∫ ω, EReal.toReal (φ (xN ω)) ∂μ : ℝ)

/-- Helper for Proposition 13.50: the dense-epigraph prefix supremum is monotone in the prefix
length. This is the finite-branch limit shape used when passing from the finite competitors to the
pointwise conjugate. -/
private theorem denseEpigraphPrefixSup_monotone
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) :
    Monotone (denseEpigraphPrefixSup (φ := φ) u) := by
  refine monotone_nat_of_le_succ ?_
  intro N ω
  -- Adding one more slice can only increase the finite supremum.
  simp [denseEpigraphPrefixSup, Finset.range_add_one, Finset.sup_insert, le_sup_left]

/-- Helper for Proposition 13.50: each individual dense-epigraph slice already appears in its own
finite prefix supremum. -/
private theorem denseEpigraphSlice_le_denseEpigraphPrefixSup
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (n : ℕ) (ω : Ω) :
    denseEpigraphSlice (φ := φ) u n ω ≤ denseEpigraphPrefixSup (φ := φ) u n ω := by
  -- Rewrite the finite prefix as an indexed `iSup` and choose the `n`th slice.
  rw [denseEpigraphPrefixSup, Finset.sup_eq_iSup]
  exact le_iSup_of_le n <| le_iSup_of_le (Finset.mem_range.mpr (Nat.lt_succ_self n)) le_rfl

/-- Helper for Proposition 13.50: every finite dense-epigraph prefix supremum is bounded above by
the pointwise conjugate value. -/
private theorem denseEpigraphPrefixSup_le_gammaZeroConjugate
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) (ω : Ω) :
    denseEpigraphPrefixSup (φ := φ) u N ω ≤
      ((gammaZeroConjugate φ hφ (u ω) : Set.Ioi (⊥ : EReal)) : EReal) := by
  -- Rewrite the finite prefix as the supremum of its slices and bound each slice separately.
  rw [denseEpigraphPrefixSup, Finset.sup_eq_iSup]
  refine iSup_le fun n ↦ iSup_le fun _hn ↦ ?_
  simpa [denseEpigraphSlice, denseEpigraphSequence] using
    denseEpigraphSlice_le_gammaZeroConjugate (φ := φ) (hφ := hφ) (u := u ω) n

/-- Helper for Proposition 13.50: the increasing dense-epigraph prefix suprema recover the full
pointwise conjugate value. This is the finite-branch normalization before integration. -/
private theorem iSup_denseEpigraphPrefixSup_eq_gammaZeroConjugate
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (ω : Ω) :
    (⨆ N, denseEpigraphPrefixSup (φ := φ) u N ω) =
      ((gammaZeroConjugate φ hφ (u ω) : Set.Ioi (⊥ : EReal)) : EReal) := by
  refine le_antisymm ?_ ?_
  · -- Every finite prefix is already bounded by the full pointwise conjugate value.
    exact iSup_le fun N ↦ denseEpigraphPrefixSup_le_gammaZeroConjugate
      (φ := φ) (hφ := hφ) u N ω
  · -- Conversely, each dense slice is contained in some finite prefix.
    have hslices :
        ((gammaZeroConjugate φ hφ (u ω) : Set.Ioi (⊥ : EReal)) : EReal) =
          ⨆ n, denseEpigraphSlice (φ := φ) u n ω := by
      simpa [denseEpigraphSlice, denseEpigraphSequence] using
        denseEpigraphSlices_iSup (φ := φ) (hφ := hφ) (u := u ω)
    rw [hslices]
    refine iSup_le fun n ↦ le_iSup_of_le n ?_
    exact denseEpigraphSlice_le_denseEpigraphPrefixSup (φ := φ) u n ω

/-- Helper for Proposition 13.50: the finite dense-epigraph prefix supremum converges pointwise
to the pointwise conjugate value. -/
private theorem tendsto_denseEpigraphPrefixSup
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (ω : Ω) :
    Filter.Tendsto (fun N ↦ denseEpigraphPrefixSup (φ := φ) u N ω) Filter.atTop
      (nhds (((gammaZeroConjugate φ hφ (u ω) : Set.Ioi (⊥ : EReal)) : EReal))) := by
  -- Monotone convergence of the prefix suprema identifies their limit with the pointwise `iSup`.
  rw [← iSup_denseEpigraphPrefixSup_eq_gammaZeroConjugate (φ := φ) (u := u) (ω := ω)]
  exact tendsto_atTop_iSup fun n m hnm ↦
    denseEpigraphPrefixSup_monotone (φ := φ) u hnm ω

/-- Helper for Proposition 13.50: every dense-epigraph prefix supremum is finite, because it is
realized by the affine slice of a winner point. -/
private theorem denseEpigraphPrefixSup_ne_bot
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) (ω : Ω) :
    denseEpigraphPrefixSup (φ := φ) u N ω ≠ ⊥ := by
  -- Rewrite the prefix through the winner-point slice, which is a real cast in `EReal`.
  rw [denseEpigraphPrefixWinnerPoint_slice_eq_prefixSup (φ := φ) (u := u) N ω]
  exact EReal.coe_ne_bot _

/-- Helper for Proposition 13.50: on the effective-domain branch, the real-valued dense-prefix
approximants converge a.e. to the real-valued pointwise conjugate integrand. -/
private theorem tendsto_denseEpigraphPrefixSup_toReal_of_mem_effectiveDomain
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H)
    (hu_eff : u ∈ effectiveDomain (integralFunctional μ (gammaZeroConjugate φ hφ))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun N ↦ EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω))
        Filter.atTop
        (nhds (EReal.toReal
          ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal)))) := by
  have hu_branch :=
    integralFunctional_branch_of_mem_effectiveDomain
      (μ := μ) (gammaZeroConjugate φ hφ) (x := u) hu_eff
  filter_upwards [hu_branch.2] with ω huω
  -- Apply continuity of `EReal.toReal` at the finite pointwise conjugate value.
  exact (EReal.tendsto_toReal
      (a := (((gammaZeroConjugate φ hφ (u ω) : Set.Ioi (⊥ : EReal)) : EReal)))
      (ne_of_lt huω)
      (by exact ne_of_gt ((gammaZeroConjugate φ hφ (u ω)).2))).comp
    (tendsto_denseEpigraphPrefixSup (φ := φ) (hφ := hφ) (u := u) (ω := ω))

/-- Helper for Proposition 13.50: the `toReal` value of the finite dense-epigraph prefix
supremum is the affine slice of the recursively chosen winner point. -/
private theorem denseEpigraphPrefixSup_toReal_eq_winnerPointSlice
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) (ω : Ω) :
    EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) =
      ⟪(denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1, u ω⟫_ℝ -
        (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.2 := by
  -- Rewrite the prefix supremum through the winner-point slice before coercing back to `ℝ`.
  rw [denseEpigraphPrefixWinnerPoint_slice_eq_prefixSup]
  simpa using EReal.toReal_coe
    (⟪(denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1, u ω⟫_ℝ -
      (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.2)

/-- Helper for Proposition 13.50: on a finite-measure space, the second coordinate of the
winner-point recursion is integrable because it takes only finitely many real values. -/
private theorem integrable_denseEpigraphPrefixWinnerPointSecond_of_finiteMeasure
    [Nonempty (epigraph φ.asEReal)] [IsFiniteMeasure μ] (u : Ω →₂[μ] H) (N : ℕ) :
    Integrable (fun ω ↦ (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.2) μ := by
  let ξNFun : Ω → ℝ := fun ω ↦ (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.2
  have hξNFun_meas : Measurable ξNFun := by
    -- Compose the measurable winner-point recursion with the second-coordinate projection.
    simpa [ξNFun] using
      ((measurable_snd.comp measurable_subtype_coe).comp
        (measurable_denseEpigraphPrefixWinnerPoint (φ := φ) (u := u) N))
  let Cξ : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty
      (fun n : Fin (N + 1) ↦ |(denseEpigraphSequence (φ := φ) n.1).1.2|)
  have hξNFun_bound : ∀ ω : Ω, ‖ξNFun ω‖ ≤ Cξ := by
    intro ω
    rcases denseEpigraphPrefixWinnerPoint_eq_denseEpigraphSequence (φ := φ) (u := u) N ω with
      ⟨n, hn⟩
    -- Finite-range membership turns the scalar coordinate into one `Finset.sup'` bound.
    calc
      ‖ξNFun ω‖ = |(denseEpigraphSequence (φ := φ) n.1).1.2| := by
          simpa [Real.norm_eq_abs, ξNFun] using
            congrArg (fun p : epigraph φ.asEReal ↦ ‖p.1.2‖) hn
      _ ≤ Cξ := Finset.le_sup' (s := Finset.univ)
            (f := fun n : Fin (N + 1) ↦ |(denseEpigraphSequence (φ := φ) n.1).1.2|)
            (Finset.mem_univ n)
  -- A bounded measurable scalar field is integrable on a finite-measure space.
  exact Integrable.of_bound hξNFun_meas.aestronglyMeasurable Cξ
    (Filter.Eventually.of_forall hξNFun_bound)

/-- Helper for Proposition 13.50: on a finite-measure space, the real-valued finite prefix
supremum is integrable. This is the finite-branch input to monotone convergence. -/
private theorem integrable_denseEpigraphPrefixSup_toReal_of_finiteMeasure
    [Nonempty (epigraph φ.asEReal)] [IsFiniteMeasure μ] (u : Ω →₂[μ] H) (N : ℕ) :
    Integrable (fun ω ↦ EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω)) μ := by
  let xNFun : Ω → H := fun ω ↦ (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1
  let xNMem : MemLp xNFun 2 μ :=
    denseEpigraphPrefixWinnerPoint_memLp_of_finiteMeasure (φ := φ) (u := u) N
  let xN : Ω →₂[μ] H := xNMem.toLp xNFun
  have hxN_ae : xN =ᵐ[μ] xNFun := by
    -- The packaged `L²` field agrees a.e. with the measurable winner-point coordinate.
    simpa [xN, xNMem, xNFun] using xNMem.coeFn_toLp
  have hinner_xN : Integrable (fun ω ↦ ⟪xN ω, u ω⟫_ℝ) μ :=
    MeasureTheory.L2.integrable_inner xN u
  have hinner_xNFun : Integrable (fun ω ↦ ⟪xNFun ω, u ω⟫_ℝ) μ := by
    refine hinner_xN.congr ?_
    filter_upwards [hxN_ae] with ω hω
    simp [xNFun, hω]
  have hsecond :
      Integrable (fun ω ↦ (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.2) μ :=
    integrable_denseEpigraphPrefixWinnerPointSecond_of_finiteMeasure
      (φ := φ) (u := u) N
  have hslice :
      (fun ω ↦ EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω)) =ᵐ[μ]
        fun ω ↦ ⟪xNFun ω, u ω⟫_ℝ -
          (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.2 := by
    filter_upwards with ω
    simpa [xNFun] using
      denseEpigraphPrefixSup_toReal_eq_winnerPointSlice (φ := φ) (u := u) N ω
  -- Rewrite the prefix supremum as an affine slice of the winner point and integrate the two
  -- resulting real terms separately.
  exact (hinner_xNFun.sub hsecond).congr hslice.symm

/-- Helper for Proposition 13.50: on the effective-domain branch of the finite-measure case, the
integrals of the real-valued dense-prefix approximants converge to the integral of the pointwise
conjugate integrand. -/
private theorem integral_tendsto_denseEpigraphPrefixSup_toReal_of_mem_effectiveDomain
    [Nonempty (epigraph φ.asEReal)] [IsFiniteMeasure μ] (u : Ω →₂[μ] H)
    (hu_eff : u ∈ effectiveDomain (integralFunctional μ (gammaZeroConjugate φ hφ))) :
    Filter.Tendsto
      (fun N ↦ ∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ)
      Filter.atTop
      (nhds (∫ ω,
        EReal.toReal ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal)) ∂μ)) := by
  have hu_branch :=
    integralFunctional_branch_of_mem_effectiveDomain
      (μ := μ) (gammaZeroConjugate φ hφ) (x := u) hu_eff
  refine MeasureTheory.integral_tendsto_of_tendsto_of_monotone
    (hf := fun N ↦ integrable_denseEpigraphPrefixSup_toReal_of_finiteMeasure
      (φ := φ) (u := u) N)
    (hF := hu_branch.1) ?_ ?_
  · -- The real-valued prefix integrands are monotone because the underlying `EReal` prefixes are.
    filter_upwards [hu_branch.2] with ω huω
    intro n m hnm
    exact EReal.toReal_le_toReal
      (denseEpigraphPrefixSup_monotone (φ := φ) u hnm ω)
      (denseEpigraphPrefixSup_ne_bot (φ := φ) u n ω)
      (ne_of_lt <| lt_of_le_of_lt
        (denseEpigraphPrefixSup_le_gammaZeroConjugate (φ := φ) (hφ := hφ) (u := u) m ω) huω)
  · -- The pointwise convergence is exactly the effective-domain `toReal` convergence above.
    exact tendsto_denseEpigraphPrefixSup_toReal_of_mem_effectiveDomain
      (φ := φ) (hφ := hφ) (u := u) hu_eff

/-- Helper for Proposition 13.50: truncate the point-valued winner on `spanningSets μ k` to get
an actual `L²(μ)` competitor. -/
private noncomputable def denseEpigraphPrefixWinnerField
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) :
    ℕ → ℕ → Ω →₂[μ] H
  | 0, k =>
      indicatorConstLp 2 (measurableSet_spanningSets μ k)
        (measure_spanningSets_lt_top μ k).ne
        (denseEpigraphSequence (φ := φ) 0).1.1
  | N + 1, k =>
      let winSet : Set Ω :=
        MeasureTheory.spanningSets μ k ∩
          denseEpigraphComparisonSet (φ := φ) u N
      let hwin : MeasurableSet winSet :=
        (measurableSet_spanningSets μ k).inter
          (measurable_denseEpigraphComparisonSet (φ := φ) u N)
      let hμwin : μ winSet ≠ ∞ :=
        (measure_mono Set.inter_subset_left).trans_lt (measure_spanningSets_lt_top μ k) |>.ne
      let prev := denseEpigraphPrefixWinnerField u N k
      let prevOff : Ω → H := winSetᶜ.indicator fun ω ↦ prev ω
      let hprevOff : MemLp prevOff 2 μ := by
        exact MemLp.indicator hwin.compl (Lp.memLp prev)
      -- Keep the previous competitor off the new winner set and overwrite it by the new constant
      -- vector on the winner set.
      indicatorConstLp 2 hwin hμwin
          (denseEpigraphSequence (φ := φ) (N + 1)).1.1 +
        hprevOff.toLp prevOff

/-- Helper for Proposition 13.50: the truncated winner field vanishes outside the finite-measure
set `spanningSets μ k`. -/
private theorem denseEpigraphPrefixWinnerField_zero_off_spanningSet
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) :
    ∀ N k : ℕ, ∀ᵐ ω ∂μ,
      ω ∉ MeasureTheory.spanningSets μ k →
        denseEpigraphPrefixWinnerField (φ := φ) u N k ω = 0
  | 0, k => by
      -- The base truncated competitor is the indicator of `spanningSets μ k`.
      simpa [denseEpigraphPrefixWinnerField] using
        (indicatorConstLp_coeFn_notMem (p := (2 : ℝ≥0∞))
          (μ := μ) (s := MeasureTheory.spanningSets μ k)
          (hs := measurableSet_spanningSets μ k)
          (hμs := (measure_spanningSets_lt_top μ k).ne)
          (c := (denseEpigraphSequence (φ := φ) 0).1.1))
  | N + 1, k => by
      classical
      let winSet : Set Ω :=
        MeasureTheory.spanningSets μ k ∩ denseEpigraphComparisonSet (φ := φ) u N
      let hwin : MeasurableSet winSet :=
        (measurableSet_spanningSets μ k).inter
          (measurable_denseEpigraphComparisonSet (φ := φ) u N)
      let hμwin : μ winSet ≠ ∞ :=
        (measure_mono Set.inter_subset_left).trans_lt (measure_spanningSets_lt_top μ k) |>.ne
      let prev := denseEpigraphPrefixWinnerField (φ := φ) u N k
      let prevOff : Ω → H := winSetᶜ.indicator fun ω ↦ prev ω
      let hprevOff : MemLp prevOff 2 μ := by
        exact MemLp.indicator hwin.compl (Lp.memLp prev)
      have hadd :
          ∀ᵐ ω ∂μ,
            denseEpigraphPrefixWinnerField (φ := φ) u (N + 1) k ω =
              indicatorConstLp 2 hwin hμwin
                  (denseEpigraphSequence (φ := φ) (N + 1)).1.1 ω +
                hprevOff.toLp prevOff ω := by
        -- Expand the recursive `Lp` sum once, then reason pointwise.
        simpa [denseEpigraphPrefixWinnerField, winSet, hwin, hμwin, prev, prevOff] using
          (Lp.coeFn_add
            (indicatorConstLp 2 hwin hμwin (denseEpigraphSequence (φ := φ) (N + 1)).1.1)
            (hprevOff.toLp prevOff))
      have hconst :
          ∀ᵐ ω ∂μ,
            ω ∉ MeasureTheory.spanningSets μ k →
              indicatorConstLp 2 hwin hμwin
                  (denseEpigraphSequence (φ := φ) (N + 1)).1.1 ω = 0 := by
        -- Outside `spanningSets μ k`, the new indicator branch is already zero.
        filter_upwards
          [indicatorConstLp_coeFn_notMem (p := (2 : ℝ≥0∞))
            (μ := μ) (s := winSet) (hs := hwin) (hμs := hμwin)
            (c := (denseEpigraphSequence (φ := φ) (N + 1)).1.1)] with ω hω hωspan
        exact hω fun hmem => hωspan hmem.1
      have hprevEq :
          ∀ᵐ ω ∂μ,
            ω ∉ MeasureTheory.spanningSets μ k →
              hprevOff.toLp prevOff ω = prev ω := by
        -- Off the spanning set, the complement indicator keeps the previous competitor unchanged.
        filter_upwards [hprevOff.coeFn_toLp] with ω hω hωspan
        simpa [prevOff, winSet, hωspan] using hω
      have hprevZero := denseEpigraphPrefixWinnerField_zero_off_spanningSet u N k
      filter_upwards [hadd, hconst, hprevEq, hprevZero] with ω haddω hconstω hprevEqω hprevZeroω
      intro hωspan
      calc
        denseEpigraphPrefixWinnerField (φ := φ) u (N + 1) k ω
            = indicatorConstLp 2 hwin hμwin
                  (denseEpigraphSequence (φ := φ) (N + 1)).1.1 ω +
                hprevOff.toLp prevOff ω := haddω
        _ = 0 + prev ω := by rw [hconstω hωspan, hprevEqω hωspan]
        _ = 0 := by
              rw [hprevZeroω hωspan]
              simp

/-- Helper for Proposition 13.50: on each finite-measure spanning set, the truncated `L²`
winner field agrees a.e. with the first coordinate of the exact dense-epigraph winner point. -/
private theorem denseEpigraphPrefixWinnerField_eq_winnerPoint_on_spanningSet
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) :
    ∀ N k : ℕ, ∀ᵐ ω ∂μ,
      ω ∈ MeasureTheory.spanningSets μ k →
        denseEpigraphPrefixWinnerField (φ := φ) u N k ω =
          (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1
  | 0, k => by
      -- On the spanning set, the base truncated competitor is the first dense epigraph point.
      filter_upwards
        [indicatorConstLp_coeFn_mem (p := (2 : ℝ≥0∞))
          (μ := μ) (s := MeasureTheory.spanningSets μ k)
          (hs := measurableSet_spanningSets μ k)
          (hμs := (measure_spanningSets_lt_top μ k).ne)
          (c := (denseEpigraphSequence (φ := φ) 0).1.1)] with ω hω hωspan
      simpa [denseEpigraphPrefixWinnerField, denseEpigraphPrefixWinnerPoint] using hω hωspan
  | N + 1, k => by
      classical
      let winSet : Set Ω :=
        MeasureTheory.spanningSets μ k ∩ denseEpigraphComparisonSet (φ := φ) u N
      let hwin : MeasurableSet winSet :=
        (measurableSet_spanningSets μ k).inter
          (measurable_denseEpigraphComparisonSet (φ := φ) u N)
      let hμwin : μ winSet ≠ ∞ :=
        (measure_mono Set.inter_subset_left).trans_lt (measure_spanningSets_lt_top μ k) |>.ne
      let prev := denseEpigraphPrefixWinnerField (φ := φ) u N k
      let prevOff : Ω → H := winSetᶜ.indicator fun ω ↦ prev ω
      let hprevOff : MemLp prevOff 2 μ := by
        exact MemLp.indicator hwin.compl (Lp.memLp prev)
      have hadd :
          ∀ᵐ ω ∂μ,
            denseEpigraphPrefixWinnerField (φ := φ) u (N + 1) k ω =
              indicatorConstLp 2 hwin hμwin
                  (denseEpigraphSequence (φ := φ) (N + 1)).1.1 ω +
                hprevOff.toLp prevOff ω := by
        -- Expand the recursive `Lp` sum once, then split into the winner and complement branches.
        simpa [denseEpigraphPrefixWinnerField, winSet, hwin, hμwin, prev, prevOff] using
          (Lp.coeFn_add
            (indicatorConstLp 2 hwin hμwin (denseEpigraphSequence (φ := φ) (N + 1)).1.1)
            (hprevOff.toLp prevOff))
      have hconstMem :
          ∀ᵐ ω ∂μ,
            ω ∈ winSet →
              indicatorConstLp 2 hwin hμwin
                  (denseEpigraphSequence (φ := φ) (N + 1)).1.1 ω =
                (denseEpigraphSequence (φ := φ) (N + 1)).1.1 := by
        -- On the winner set, the new indicator branch contributes the fresh dense epigraph point.
        exact indicatorConstLp_coeFn_mem (p := (2 : ℝ≥0∞))
          (μ := μ) (s := winSet) (hs := hwin) (hμs := hμwin)
          (c := (denseEpigraphSequence (φ := φ) (N + 1)).1.1)
      have hconstNot :
          ∀ᵐ ω ∂μ,
            ω ∉ winSet →
              indicatorConstLp 2 hwin hμwin
                  (denseEpigraphSequence (φ := φ) (N + 1)).1.1 ω = 0 := by
        -- Off the winner set, the new indicator branch vanishes.
        exact indicatorConstLp_coeFn_notMem (p := (2 : ℝ≥0∞))
          (μ := μ) (s := winSet) (hs := hwin) (hμs := hμwin)
          (c := (denseEpigraphSequence (φ := φ) (N + 1)).1.1)
      have hprevZero :
          ∀ᵐ ω ∂μ,
            ω ∈ winSet →
              hprevOff.toLp prevOff ω = 0 := by
        -- On the winner set, the complement indicator kills the inherited competitor.
        filter_upwards [hprevOff.coeFn_toLp] with ω hω hωwin
        simpa [prevOff, hωwin] using hω
      have hprevEq :
          ∀ᵐ ω ∂μ,
            ω ∉ winSet →
              hprevOff.toLp prevOff ω = prev ω := by
        -- Off the winner set, the complement indicator exposes the inherited competitor.
        filter_upwards [hprevOff.coeFn_toLp] with ω hω hωwin
        simpa [prevOff, hωwin] using hω
      have hih := denseEpigraphPrefixWinnerField_eq_winnerPoint_on_spanningSet u N k
      filter_upwards [hadd, hconstMem, hconstNot, hprevZero, hprevEq, hih]
        with ω haddω hconstMemω hconstNotω hprevZeroω hprevEqω hihω
      intro hωspan
      by_cases hωcomp : ω ∈ denseEpigraphComparisonSet (φ := φ) u N
      · have hωwin : ω ∈ winSet := ⟨hωspan, hωcomp⟩
        calc
          denseEpigraphPrefixWinnerField (φ := φ) u (N + 1) k ω
              = indicatorConstLp 2 hwin hμwin
                  (denseEpigraphSequence (φ := φ) (N + 1)).1.1 ω +
                hprevOff.toLp prevOff ω := haddω
          _ = (denseEpigraphSequence (φ := φ) (N + 1)).1.1 + 0 := by
                rw [hconstMemω hωwin, hprevZeroω hωwin]
          _ = (denseEpigraphPrefixWinnerPoint (φ := φ) u (N + 1) ω).1.1 := by
                simp [denseEpigraphPrefixWinnerPoint, hωcomp]
      · have hωnotwin : ω ∉ winSet := by
          exact fun hmem => hωcomp hmem.2
        calc
          denseEpigraphPrefixWinnerField (φ := φ) u (N + 1) k ω
              = indicatorConstLp 2 hwin hμwin
                  (denseEpigraphSequence (φ := φ) (N + 1)).1.1 ω +
                hprevOff.toLp prevOff ω := haddω
          _ = 0 + prev ω := by rw [hconstNotω hωnotwin, hprevEqω hωnotwin]
          _ = (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1 := by
                rw [hihω hωspan]
                simp
          _ = (denseEpigraphPrefixWinnerPoint (φ := φ) u (N + 1) ω).1.1 := by
                simp [denseEpigraphPrefixWinnerPoint, hωcomp]

/-- Helper for Proposition 13.50: the affine defect of the truncated winner field dominates the
finite dense-epigraph prefix supremum on each spanning set. This is the corrected statement needed
for the later `conjugate_apply` step: the chosen epigraph heights need only give a lower bound for
the true `φ`-defect, not exact equality. -/
private theorem denseEpigraphPrefixWinnerField_defect_ge_prefixSup
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) :
    ∀ N k : ℕ, ∀ᵐ ω ∂μ,
      ω ∈ MeasureTheory.spanningSets μ k →
        denseEpigraphPrefixSup (φ := φ) u N ω ≤
          (((⟪denseEpigraphPrefixWinnerField (φ := φ) u N k ω, u ω⟫_ℝ : ℝ) : EReal) -
            (φ (denseEpigraphPrefixWinnerField (φ := φ) u N k ω) : EReal))
  | N, k => by
      have hfield := denseEpigraphPrefixWinnerField_eq_winnerPoint_on_spanningSet
        (φ := φ) u N k
      filter_upwards [hfield] with ω hfieldω hω
      let p := denseEpigraphPrefixWinnerPoint (φ := φ) u N ω
      have hp_epi : (φ p.1.1 : EReal) ≤ ((p.1.2 : ℝ) : EReal) := by
        -- Read the stored epigraph witness through `mem_epigraph_iff` without unfolding the subtype.
        exact (mem_epigraph_iff φ.asEReal p.1.1 p.1.2).mp p.2
      have hp_slice :
          denseEpigraphPrefixSup (φ := φ) u N ω =
            (((⟪p.1.1, u ω⟫_ℝ : ℝ) : EReal) - ((p.1.2 : ℝ) : EReal)) := by
        -- Rewrite the exact winner-point slice into the subtraction shape used by conjugate.
        calc
          denseEpigraphPrefixSup (φ := φ) u N ω =
              ((⟪p.1.1, u ω⟫_ℝ - p.1.2 : ℝ) : EReal) := by
                simpa [p] using denseEpigraphPrefixWinnerPoint_slice_eq_prefixSup
                  (φ := φ) u N ω
          _ = (((⟪p.1.1, u ω⟫_ℝ : ℝ) : EReal) - ((p.1.2 : ℝ) : EReal)) := by
                rw [EReal.coe_sub]
      -- The winner point lies in the epigraph, so replacing its recorded height by `φ` only
      -- enlarges the affine defect.
      calc
        denseEpigraphPrefixSup (φ := φ) u N ω
            = (((⟪p.1.1, u ω⟫_ℝ : ℝ) : EReal) - ((p.1.2 : ℝ) : EReal)) := hp_slice
        _ ≤ (((⟪p.1.1, u ω⟫_ℝ : ℝ) : EReal) - (φ p.1.1 : EReal)) := by
              exact EReal.sub_le_sub le_rfl hp_epi
        _ = (((⟪denseEpigraphPrefixWinnerField (φ := φ) u N k ω, u ω⟫_ℝ : ℝ) :
              EReal) -
              (φ (denseEpigraphPrefixWinnerField (φ := φ) u N k ω) : EReal)) := by
              simp [p, hfieldω hω]

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H] in
/-- Helper for Proposition 13.50: if `φ` has minimum value `0` at the origin, then the canonical
zero point lies in `epigraph φ.asEReal`. -/
private theorem zeroPoint_mem_epigraph_of_zero_minimum
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)) :
    ((0 : H), (0 : ℝ)) ∈ epigraph φ.asEReal := by
  rcases hzero_min with ⟨hzero, _⟩
  -- The zero-minimum hypothesis puts the graph point `(0, 0)` on the real-height epigraph slice.
  rw [mem_epigraph_iff]
  simpa [hzero]

/-- Helper for Proposition 13.50: after truncating by `spanningSets μ k`, the dense-epigraph
prefix supremum is globally dominated by the affine defect of the truncated winner field. This
packages the on-spanning-set domination together with the zero-minimum normalization outside the
truncation set. -/
private theorem denseEpigraphIndicatorPrefixSup_le_winnerFieldDefect
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)]
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))
    (u : Ω →₂[μ] H) (N k : ℕ) :
    ∀ᵐ ω ∂μ,
      Set.indicator (MeasureTheory.spanningSets μ k)
          (denseEpigraphPrefixSup (φ := φ) u N) ω ≤
        (((⟪denseEpigraphPrefixWinnerField (φ := φ) u N k ω, u ω⟫_ℝ : ℝ) : EReal) -
          (φ (denseEpigraphPrefixWinnerField (φ := φ) u N k ω) : EReal)) := by
  have hdefect := denseEpigraphPrefixWinnerField_defect_ge_prefixSup
    (φ := φ) u N k
  have hzero := denseEpigraphPrefixWinnerField_zero_off_spanningSet
    (φ := φ) u N k
  rcases hzero_min with ⟨hφ0, _⟩
  -- Split pointwise into the truncated region and its complement.
  filter_upwards [hdefect, hzero] with ω hdefectω hzeroω
  by_cases hω : ω ∈ MeasureTheory.spanningSets μ k
  · -- On the spanning set, this is exactly the previously proved defect domination.
    simpa [Set.indicator_of_mem, hω] using hdefectω hω
  · -- Off the spanning set, the winner field vanishes and the defect collapses to `0`.
    have hfield0 :
        denseEpigraphPrefixWinnerField (φ := φ) u N k ω = 0 :=
      hzeroω hω
    simpa [Set.indicator_of_notMem, hω, hfield0, hφ0]

/-- Helper for Proposition 13.50: the nonnegative normalization set for the `N`th dense-epigraph
prefix is the region where the prefix supremum is already nonnegative. -/
private def denseEpigraphNonnegSet
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    Set Ω :=
  {ω | 0 ≤ denseEpigraphPrefixSup (φ := φ) u N ω}

/-- Helper for Proposition 13.50: the nonnegative normalization set is measurable because the
dense-epigraph prefix supremum is measurable. -/
private theorem measurable_denseEpigraphNonnegSet
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    MeasurableSet (denseEpigraphNonnegSet (φ := φ) u N) := by
  -- The positivity set is a measurable comparison with the constant zero function.
  simpa [denseEpigraphNonnegSet] using
    measurableSet_le measurable_const
      (measurable_denseEpigraphPrefixSup (φ := φ) (u := u) N)

/-- Helper for Proposition 13.50: normalize the `N`th dense-epigraph prefix by replacing its
negative part with `0`. This is the source-guided monotone form needed for the zero-minimum
branch. -/
private noncomputable def denseEpigraphNonnegPrefixSup
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    Ω → EReal :=
  fun ω ↦ max 0 (denseEpigraphPrefixSup (φ := φ) u N ω)

/-- Helper for Proposition 13.50: the normalized dense-epigraph prefix still lies below the
pointwise conjugate because the latter is nonnegative in the zero-minimum branch. -/
private theorem denseEpigraphNonnegPrefixSup_le_gammaZeroConjugate
    [Nonempty (epigraph φ.asEReal)]
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))
    (u : Ω →₂[μ] H) (N : ℕ) (ω : Ω) :
    denseEpigraphNonnegPrefixSup (φ := φ) u N ω ≤
      ((gammaZeroConjugate φ hφ (u ω) : Set.Ioi (⊥ : EReal)) : EReal) := by
  rcases gammaZeroConjugate_has_zero_minimum (φ := φ) (hφ := hφ) hzero_min with
    ⟨hφStar0, hφStar_min⟩
  have hφStar_nonneg :
      (0 : EReal) ≤ ((gammaZeroConjugate φ hφ (u ω) : Set.Ioi (⊥ : EReal)) : EReal) := by
    -- The pointwise conjugate inherits the minimum value `0` at the origin.
    have hminω := hφStar_min (u ω)
    rw [hφStar0] at hminω
    exact hminω
  -- The normalized prefix is the maximum of `0` and the original prefix bound.
  exact max_le_iff.mpr
    ⟨hφStar_nonneg, denseEpigraphPrefixSup_le_gammaZeroConjugate (φ := φ) (hφ := hφ) u N ω⟩

/-- Helper for Proposition 13.50: replacing each dense-epigraph prefix by its nonnegative part
does not change the eventual pointwise supremum in the zero-minimum branch. -/
private theorem iSup_denseEpigraphNonnegPrefixSup_eq_gammaZeroConjugate
    [Nonempty (epigraph φ.asEReal)]
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))
    (u : Ω →₂[μ] H) (ω : Ω) :
    (⨆ N, denseEpigraphNonnegPrefixSup (φ := φ) u N ω) =
      ((gammaZeroConjugate φ hφ (u ω) : Set.Ioi (⊥ : EReal)) : EReal) := by
  refine le_antisymm ?_ ?_
  · -- Every normalized finite prefix is still bounded above by the pointwise conjugate.
    exact iSup_le fun N ↦
      denseEpigraphNonnegPrefixSup_le_gammaZeroConjugate
        (φ := φ) (hφ := hφ) hzero_min u N ω
  · -- The original finite prefixes sit below their normalized versions, so the same supremum is
    -- recovered after taking `max 0 _`.
    rw [← iSup_denseEpigraphPrefixSup_eq_gammaZeroConjugate (φ := φ) (hφ := hφ) (u := u) (ω := ω)]
    refine iSup_le fun N ↦ le_iSup_of_le N ?_
    simpa [denseEpigraphNonnegPrefixSup] using
      (le_max_right (0 : EReal) (denseEpigraphPrefixSup (φ := φ) u N ω))

/-- Helper for Proposition 13.50: the `ENNReal` supremum of the normalized dense-epigraph
prefixes is exactly the `ENNReal`-valued pointwise conjugate integrand. -/
private theorem iSup_toENNReal_denseEpigraphNonnegPrefixSup_eq_gammaZeroConjugate
    [Nonempty (epigraph φ.asEReal)]
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))
    (u : Ω →₂[μ] H) (ω : Ω) :
    (⨆ N, (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal) =
      ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal)).toENNReal := by
  have hmap :
      (⨆ N, denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal =
        ⨆ N, (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal := by
    -- `EReal.toENNReal` preserves suprema of monotone families.
    simpa using
      (Monotone.map_iSup_of_continuousAt
        (f := EReal.toENNReal)
        (g := fun N ↦ denseEpigraphNonnegPrefixSup (φ := φ) u N ω)
        EReal.continuous_toENNReal.continuousAt
        (fun _ _ h ↦ EReal.toENNReal_le_toENNReal h)
        (by simp))
  calc
    ⨆ N, (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal
        = (⨆ N, denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal := hmap.symm
    _ =
        ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal)).toENNReal := by
          rw [iSup_denseEpigraphNonnegPrefixSup_eq_gammaZeroConjugate
            (φ := φ) (hφ := hφ) hzero_min u ω]

/-- Helper for Proposition 13.50: the normalized dense-prefix integrand has the exact
`AEMeasurable` `toENNReal` shape required by monotone convergence in the zero-minimum branch. -/
private theorem aemeasurable_toENNReal_denseEpigraphNonnegPrefixSup
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    AEMeasurable
      (fun ω ↦ (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal) μ := by
  have hmeas :
      Measurable fun ω ↦ denseEpigraphNonnegPrefixSup (φ := φ) u N ω := by
    -- The zero-minimum normalization is just `max 0` of the measurable dense-prefix bound.
    simpa [denseEpigraphNonnegPrefixSup, sup_comm] using
      (measurable_denseEpigraphPrefixSup (φ := φ) (u := u) N).sup measurable_const
  exact hmeas.aemeasurable.ereal_toENNReal

/-- Helper for Proposition 13.50: for a fixed normalized prefix level `N`, the `σ`-finite
spanning-set exhaustion packages the full `lintegral` as the supremum of the restricted
`lintegral`s. This isolates the `k → ∞` passage from the main zero-minimum theorem. -/
private theorem lintegral_denseEpigraphNonnegPrefixSup_eq_iSup_restrict_spanningSets
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    ∫⁻ ω, (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal ∂μ =
      ⨆ k : ℕ,
        ∫⁻ ω, (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal ∂μ.restrict
          (MeasureTheory.spanningSets μ k) := by
  let f : Ω → ℝ≥0∞ := fun ω ↦ (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal
  let s : ℕ → Ω → ℝ≥0∞ := fun k ↦ Set.indicator (MeasureTheory.spanningSets μ k) f
  have hs_aemeas : ∀ k : ℕ, AEMeasurable (s k) μ := by
    intro k
    -- Restrict each normalized prefix integrand to the `k`th spanning set before applying MCT.
    exact (aemeasurable_toENNReal_denseEpigraphNonnegPrefixSup
      (μ := μ) (φ := φ) (u := u) N).indicator (measurableSet_spanningSets μ k)
  have hs_mono : ∀ᵐ ω ∂μ, Monotone fun k ↦ s k ω := by
    refine Filter.Eventually.of_forall ?_
    intro ω n m hnm
    by_cases hωn : ω ∈ MeasureTheory.spanningSets μ n
    · have hωm : ω ∈ MeasureTheory.spanningSets μ m :=
        (MeasureTheory.monotone_spanningSets μ) hnm hωn
      simp [s, hωn, hωm]
    · by_cases hωm : ω ∈ MeasureTheory.spanningSets μ m
      · simp [s, hωn, hωm]
      · simp [s, hωn, hωm]
  have hs_iSup : ∀ ω : Ω, (⨆ k, s k ω) = f ω := by
    intro ω
    have hω_union : ω ∈ ⋃ k : ℕ, MeasureTheory.spanningSets μ k := by
      simpa [MeasureTheory.iUnion_spanningSets]
    rcases Set.mem_iUnion.mp hω_union with ⟨k0, hk0⟩
    refine le_antisymm ?_ ?_
    · exact iSup_le fun k ↦ by
        by_cases hk : ω ∈ MeasureTheory.spanningSets μ k
        · simp [s, f, hk]
        · simp [s, f, hk]
    · exact le_iSup_of_le k0 (by simp [s, f, hk0])
  calc
    ∫⁻ ω, f ω ∂μ = ∫⁻ ω, ⨆ k, s k ω ∂μ := by
      refine lintegral_congr_ae ?_
      exact Filter.Eventually.of_forall fun ω ↦ (hs_iSup ω).symm
    _ = ⨆ k : ℕ, ∫⁻ ω, s k ω ∂μ := MeasureTheory.lintegral_iSup' hs_aemeas hs_mono
    _ = ⨆ k : ℕ,
          ∫⁻ ω, (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal ∂μ.restrict
            (MeasureTheory.spanningSets μ k) := by
          congr with k
          rw [← MeasureTheory.lintegral_indicator (measurableSet_spanningSets μ k)]

/-- Helper for Proposition 13.50: the normalized zero-branch competitor is the old truncated
winner field, but only on the region where the dense prefix is nonnegative. -/
private noncomputable def denseEpigraphNonnegWinnerFieldFun
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)]
    (u : Ω →₂[μ] H) (N k : ℕ) :
    Ω → H :=
  Set.indicator (denseEpigraphNonnegSet (φ := φ) u N)
    (fun ω ↦ denseEpigraphPrefixWinnerField (φ := φ) u N k ω)

/-- Helper for Proposition 13.50: the normalized zero-branch competitor still lies in `L²(μ)`
because it is an indicator truncation of the existing truncated winner field. -/
private theorem denseEpigraphNonnegWinnerField_memLp
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N k : ℕ) :
    MemLp (denseEpigraphNonnegWinnerFieldFun (φ := φ) u N k) 2 μ := by
  -- The positivity cutoff is measurable, so `MemLp.indicator` applies directly.
  simpa [denseEpigraphNonnegWinnerFieldFun] using
    (Lp.memLp (denseEpigraphPrefixWinnerField (φ := φ) u N k)).indicator
      (measurable_denseEpigraphNonnegSet (φ := φ) (u := u) N)

/-- Helper for Proposition 13.50: package the nonnegative zero-branch competitor as an `L²`
function so it can enter `conjugate_apply`. -/
private noncomputable def denseEpigraphNonnegWinnerField
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N k : ℕ) :
    Ω →₂[μ] H :=
  (denseEpigraphNonnegWinnerField_memLp (φ := φ) (u := u) N k).toLp
    (denseEpigraphNonnegWinnerFieldFun (φ := φ) u N k)

/-- Helper for Proposition 13.50: on the nonnegative region, the normalized winner field agrees
almost everywhere with the old truncated winner field. -/
private theorem denseEpigraphNonnegWinnerField_eq_prefixWinnerField
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N k : ℕ) :
    ∀ᵐ ω ∂μ,
      ω ∈ denseEpigraphNonnegSet (φ := φ) u N →
        denseEpigraphNonnegWinnerField (φ := φ) u N k ω =
          denseEpigraphPrefixWinnerField (φ := φ) u N k ω := by
  -- The packaged `L²` function agrees a.e. with its indicator definition.
  filter_upwards
      [(denseEpigraphNonnegWinnerField_memLp (φ := φ) (u := u) N k).coeFn_toLp]
    with ω hω hωnonneg
  simpa [denseEpigraphNonnegWinnerFieldFun, hωnonneg] using hω

/-- Helper for Proposition 13.50: off the nonnegative region, the normalized winner field
vanishes almost everywhere. -/
private theorem denseEpigraphNonnegWinnerField_zero_of_notMem
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N k : ℕ) :
    ∀ᵐ ω ∂μ,
      ω ∉ denseEpigraphNonnegSet (φ := φ) u N →
        denseEpigraphNonnegWinnerField (φ := φ) u N k ω = 0 := by
  -- Outside the positivity set, the indicator definition collapses to `0`.
  filter_upwards
      [(denseEpigraphNonnegWinnerField_memLp (φ := φ) (u := u) N k).coeFn_toLp]
    with ω hω hωnonneg
  simpa [denseEpigraphNonnegWinnerFieldFun, hωnonneg] using hω

/-- Helper for Proposition 13.50: the normalized truncated winner field also vanishes outside the
finite-measure spanning set used in the `σ`-finite truncation argument. -/
private theorem denseEpigraphNonnegWinnerField_zero_off_spanningSet
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N k : ℕ) :
    ∀ᵐ ω ∂μ,
      ω ∉ MeasureTheory.spanningSets μ k →
        denseEpigraphNonnegWinnerField (φ := φ) u N k ω = 0 := by
  have hfield_eq :=
    denseEpigraphNonnegWinnerField_eq_prefixWinnerField
      (φ := φ) (u := u) N k
  have hfield_zero :=
    denseEpigraphNonnegWinnerField_zero_of_notMem
      (φ := φ) (u := u) N k
  have hprefix_zero :=
    denseEpigraphPrefixWinnerField_zero_off_spanningSet
      (φ := φ) u N k
  -- Split by whether the dense prefix is already nonnegative; either way the field vanishes off
  -- the truncation set.
  filter_upwards [hfield_eq, hfield_zero, hprefix_zero]
    with ω hfield_eqω hfield_zeroω hprefix_zeroω hωspan
  by_cases hωnonneg : ω ∈ denseEpigraphNonnegSet (φ := φ) u N
  · calc
      denseEpigraphNonnegWinnerField (φ := φ) u N k ω
          = denseEpigraphPrefixWinnerField (φ := φ) u N k ω := hfield_eqω hωnonneg
      _ = 0 := hprefix_zeroω hωspan
  · exact hfield_zeroω hωnonneg

/-- Helper for Proposition 13.50: after replacing the dense prefix by `max 0 _`, the same
truncated winner-field defect still dominates the normalized prefix. This is the first stable
bridge needed for the zero-minimum branch. -/
private theorem denseEpigraphNonnegPrefixSup_le_nonnegWinnerFieldDefect
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)]
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))
    (u : Ω →₂[μ] H) (N k : ℕ) :
    ∀ᵐ ω ∂μ,
      Set.indicator (MeasureTheory.spanningSets μ k)
          (denseEpigraphNonnegPrefixSup (φ := φ) u N) ω ≤
        (((⟪denseEpigraphNonnegWinnerField (φ := φ) u N k ω, u ω⟫_ℝ : ℝ) : EReal) -
          (φ (denseEpigraphNonnegWinnerField (φ := φ) u N k ω) : EReal)) := by
  have hzero_min' := hzero_min
  rcases hzero_min with ⟨hφ0, _⟩
  have hdefect :=
    denseEpigraphIndicatorPrefixSup_le_winnerFieldDefect
      (φ := φ) (hzero_min := hzero_min') u N k
  have hfield_eq :=
    denseEpigraphNonnegWinnerField_eq_prefixWinnerField
      (φ := φ) (u := u) N k
  have hfield_zero :=
    denseEpigraphNonnegWinnerField_zero_of_notMem
      (φ := φ) (u := u) N k
  have hprefix_zero :=
    denseEpigraphPrefixWinnerField_zero_off_spanningSet
      (φ := φ) (u := u) N k
  -- Split pointwise by whether the dense prefix is already nonnegative.
  filter_upwards [hdefect, hfield_eq, hfield_zero, hprefix_zero]
    with ω hdefectω hfield_eqω hfield_zeroω hprefix_zeroω
  by_cases hωspan : ω ∈ MeasureTheory.spanningSets μ k
  · by_cases hωnonneg : ω ∈ denseEpigraphNonnegSet (φ := φ) u N
    · -- On the positive part of the spanning set, the normalization does not change the prefix
      -- or the winner field.
      have hprefix_nonneg : 0 ≤ denseEpigraphPrefixSup (φ := φ) u N ω := by
        simpa [denseEpigraphNonnegSet] using hωnonneg
      have hfield :
          denseEpigraphNonnegWinnerField (φ := φ) u N k ω =
            denseEpigraphPrefixWinnerField (φ := φ) u N k ω :=
        hfield_eqω hωnonneg
      simpa [denseEpigraphNonnegPrefixSup, Set.indicator_of_mem, hωspan, hfield,
        max_eq_right hprefix_nonneg] using hdefectω
    · -- On the negative part, both the normalized prefix and the normalized competitor collapse
      -- to `0`.
      have hprefix_nonpos : denseEpigraphPrefixSup (φ := φ) u N ω ≤ 0 := by
        exact le_of_not_ge (by simpa [denseEpigraphNonnegSet] using hωnonneg)
      have hfield :
          denseEpigraphNonnegWinnerField (φ := φ) u N k ω = 0 :=
        hfield_zeroω hωnonneg
      simpa [denseEpigraphNonnegPrefixSup, Set.indicator_of_mem, hωspan, hfield, hφ0,
        max_eq_left hprefix_nonpos]
  · -- Outside the spanning set, the indicator normalization is already zero.
    have hfield0 :
        denseEpigraphNonnegWinnerField (φ := φ) u N k ω = 0 := by
      by_cases hωnonneg : ω ∈ denseEpigraphNonnegSet (φ := φ) u N
      · calc
          denseEpigraphNonnegWinnerField (φ := φ) u N k ω
              = denseEpigraphPrefixWinnerField (φ := φ) u N k ω := hfield_eqω hωnonneg
          _ = 0 := hprefix_zeroω hωspan
      · exact hfield_zeroω hωnonneg
    simpa [denseEpigraphNonnegPrefixSup, Set.indicator_of_notMem, hωspan, hfield0, hφ0]

/-- Helper for Proposition 13.50: the normalized truncated winner field is admissible for
`integralFunctional μ φ` because it is supported on the finite-measure spanning set and takes only
finitely many pointwise values there. -/
private theorem denseEpigraphNonnegWinnerField_mem_effectiveDomain
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)]
    (hφ_mem : φ ∈ Γ₀(H))
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))
    (u : Ω →₂[μ] H) (N k : ℕ) :
    denseEpigraphNonnegWinnerField (φ := φ) u N k ∈ effectiveDomain (integralFunctional μ φ) := by
  rcases hzero_min with ⟨hφ0, _⟩
  let xNk : Ω →₂[μ] H := denseEpigraphNonnegWinnerField (φ := φ) u N k
  let g : Ω → ℝ := fun ω ↦ EReal.toReal (φ (xNk ω) : EReal)
  have hg_sm : AEStronglyMeasurable g μ := by
    have hφ_meas : Measurable φ := hφ_mem.1.measurable.subtype_mk
    -- The pointwise `toReal ∘ φ` integrand is measurable along the packaged `L²` competitor.
    simpa [g, xNk] using
      pointwise_integrand_aestronglyMeasurable φ hφ_meas xNk
  let Cφ : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty
      (fun n : Fin (N + 1) ↦
        |EReal.toReal (φ ((denseEpigraphSequence (φ := φ) n.1).1.1) : EReal)|)
  have hCφ_nonneg : 0 ≤ Cφ := by
    let n0 : Fin (N + 1) := ⟨0, Nat.succ_pos _⟩
    exact le_trans (abs_nonneg _)
      (Finset.le_sup' (s := Finset.univ)
        (f := fun n : Fin (N + 1) ↦
          |EReal.toReal (φ ((denseEpigraphSequence (φ := φ) n.1).1.1) : EReal)|)
        (Finset.mem_univ n0))
  have hbound_span :
      ∀ᵐ ω ∂μ.restrict (MeasureTheory.spanningSets μ k), ‖g ω‖ ≤ Cφ := by
    have hfield_eq :=
      denseEpigraphNonnegWinnerField_eq_prefixWinnerField
        (φ := φ) (u := u) N k
    have hfield_zero :=
      denseEpigraphNonnegWinnerField_zero_of_notMem
        (φ := φ) (u := u) N k
    have hprefix_eq :=
      denseEpigraphPrefixWinnerField_eq_winnerPoint_on_spanningSet
        (φ := φ) u N k
    refine (ae_restrict_iff' (measurableSet_spanningSets μ k)).2 ?_
    filter_upwards [hfield_eq, hfield_zero, hprefix_eq] with ω hfield_eqω hfield_zeroω
        hprefix_eqω hωspan
    by_cases hωnonneg : ω ∈ denseEpigraphNonnegSet (φ := φ) u N
    · have hx_eq :
          xNk ω = denseEpigraphPrefixWinnerField (φ := φ) u N k ω :=
        hfield_eqω hωnonneg
      have hprefix_eq' :
          denseEpigraphPrefixWinnerField (φ := φ) u N k ω =
            (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1 :=
        hprefix_eqω hωspan
      rcases denseEpigraphPrefixWinnerPoint_eq_denseEpigraphSequence (φ := φ) (u := u) N ω with
        ⟨n, hn⟩
      have hg_eq :
          g ω =
            EReal.toReal (φ ((denseEpigraphSequence (φ := φ) n.1).1.1) : EReal) := by
        calc
          g ω = EReal.toReal (φ (xNk ω) : EReal) := rfl
          _ =
              EReal.toReal
                (φ ((denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1) : EReal) := by
                  rw [hx_eq, hprefix_eq']
          _ =
              EReal.toReal (φ ((denseEpigraphSequence (φ := φ) n.1).1.1) : EReal) := by
                  simpa using
                    congrArg
                      (fun p : epigraph φ.asEReal ↦ EReal.toReal (φ (p.1.1) : EReal)) hn
      calc
        ‖g ω‖ =
            |EReal.toReal (φ ((denseEpigraphSequence (φ := φ) n.1).1.1) : EReal)| := by
              rw [hg_eq, Real.norm_eq_abs]
        _ ≤ Cφ := Finset.le_sup' (s := Finset.univ)
              (f := fun n : Fin (N + 1) ↦
                |EReal.toReal (φ ((denseEpigraphSequence (φ := φ) n.1).1.1) : EReal)|)
              (Finset.mem_univ n)
    · have hx_zero : xNk ω = 0 :=
        hfield_zeroω hωnonneg
      calc
        ‖g ω‖ = 0 := by simp [g, xNk, hx_zero, hφ0]
        _ ≤ Cφ := hCφ_nonneg
  have hg_intOn :
      IntegrableOn g (MeasureTheory.spanningSets μ k) μ := by
    -- Restrict to the finite-measure spanning set and use the uniform bound on the finite range.
    exact IntegrableOn.of_bound
      (s := MeasureTheory.spanningSets μ k)
      (measure_spanningSets_lt_top μ k)
      (hg_sm.restrict)
      Cφ
      hbound_span
  have hg_zero_off :
      ∀ᵐ ω ∂μ, ω ∉ MeasureTheory.spanningSets μ k → g ω = 0 := by
    have hfield_eq :=
      denseEpigraphNonnegWinnerField_eq_prefixWinnerField
        (φ := φ) (u := u) N k
    have hfield_zero :=
      denseEpigraphNonnegWinnerField_zero_of_notMem
        (φ := φ) (u := u) N k
    have hprefix_zero :=
      denseEpigraphPrefixWinnerField_zero_off_spanningSet
        (φ := φ) u N k
    filter_upwards [hfield_eq, hfield_zero, hprefix_zero] with ω hfield_eqω hfield_zeroω
        hprefix_zeroω hωspan
    by_cases hωnonneg : ω ∈ denseEpigraphNonnegSet (φ := φ) u N
    · have hx_eq :
          xNk ω = denseEpigraphPrefixWinnerField (φ := φ) u N k ω :=
        hfield_eqω hωnonneg
      have hprefix_eq' :
          denseEpigraphPrefixWinnerField (φ := φ) u N k ω = 0 :=
        hprefix_zeroω hωspan
      simp [g, xNk, hx_eq, hprefix_eq', hφ0]
    · have hx_zero : xNk ω = 0 :=
        hfield_zeroω hωnonneg
      simp [g, xNk, hx_zero, hφ0]
  have hg_eq_indicator :
      g =ᵐ[μ]
        Set.indicator (MeasureTheory.spanningSets μ k) g := by
    filter_upwards [hg_zero_off] with ω hω
    by_cases hωspan : ω ∈ MeasureTheory.spanningSets μ k
    · simp [Set.indicator_of_mem, hωspan]
    · simp [Set.indicator_of_notMem, hωspan, hω hωspan]
  have hg_int :
      Integrable g μ := by
    have hg_indicator :
        Integrable (Set.indicator (MeasureTheory.spanningSets μ k) g) μ := by
      exact (integrable_indicator_iff (measurableSet_spanningSets μ k)).2 hg_intOn
    exact hg_indicator.congr hg_eq_indicator.symm
  have hxNk_fin :
      ∀ᵐ ω ∂μ, (φ (xNk ω) : EReal) < ⊤ := by
    have hfield_eq :=
      denseEpigraphNonnegWinnerField_eq_prefixWinnerField
        (φ := φ) (u := u) N k
    have hfield_zero :=
      denseEpigraphNonnegWinnerField_zero_of_notMem
        (φ := φ) (u := u) N k
    have hprefix_eq :=
      denseEpigraphPrefixWinnerField_eq_winnerPoint_on_spanningSet
        (φ := φ) u N k
    have hprefix_zero :=
      denseEpigraphPrefixWinnerField_zero_off_spanningSet
        (φ := φ) u N k
    filter_upwards [hfield_eq, hfield_zero, hprefix_eq, hprefix_zero]
      with ω hfield_eqω hfield_zeroω hprefix_eqω hprefix_zeroω
    by_cases hωspan : ω ∈ MeasureTheory.spanningSets μ k
    · by_cases hωnonneg : ω ∈ denseEpigraphNonnegSet (φ := φ) u N
      · have hx_eq :
            xNk ω = denseEpigraphPrefixWinnerField (φ := φ) u N k ω :=
          hfield_eqω hωnonneg
        have hprefix_eq' :
            denseEpigraphPrefixWinnerField (φ := φ) u N k ω =
              (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1 :=
          hprefix_eqω hωspan
        simpa [xNk, hx_eq, hprefix_eq'] using
          (mem_effectiveDomain_iff.mp
            (denseEpigraphPrefixWinnerPoint_mem_effectiveDomain (φ := φ) (u := u) N ω))
      · have hx_zero : xNk ω = 0 :=
          hfield_zeroω hωnonneg
        simpa [xNk, hx_zero, hφ0]
    · have hx_zero : xNk ω = 0 := by
        by_cases hωnonneg : ω ∈ denseEpigraphNonnegSet (φ := φ) u N
        · calc
            xNk ω = denseEpigraphPrefixWinnerField (φ := φ) u N k ω := hfield_eqω hωnonneg
            _ = 0 := hprefix_zeroω hωspan
        · exact hfield_zeroω hωnonneg
      simpa [xNk, hx_zero, hφ0]
  have hbranch :
      Integrable (fun ω ↦ EReal.toReal (φ (xNk ω))) μ ∧
        ∀ᵐ ω ∂μ, (φ (xNk ω) : EReal) < ⊤ := ⟨by simpa [g, xNk] using hg_int, hxNk_fin⟩
  have hbranch0 :
      Integrable (fun ω ↦ EReal.toReal (φ ((((xNk : Ω →₂[μ] H) : Ω → H) ω)))) μ ∧
        ∀ᵐ ω ∂μ, (φ ((((xNk : Ω →₂[μ] H) : Ω → H) ω)) : EReal) < ⊤ := by
    simpa [xNk] using hbranch
  -- The admissible winner field lands on the finite branch of `pointwiseIntegralFunctional`.
  rw [mem_effectiveDomain_iff, integralFunctional_coe μ φ, pointwiseIntegralFunctional, if_pos hbranch0]
  exact EReal.coe_lt_top (∫ ω, EReal.toReal (φ (xNk ω)) ∂μ : ℝ)

/-- Helper for Proposition 13.50: on a fixed spanning set, the normalized dense-prefix defect
bound can be transported from `EReal` to an `ENNReal.ofReal` affine-defect bound. This isolates
the coercion step needed before integration in the zero-minimum branch. -/
private theorem
    denseEpigraphNonnegPrefixSup_toENNReal_le_ofReal_nonnegWinnerField_defect_restrict
    [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)]
    (hφ_mem : φ ∈ Γ₀(H))
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))
    (u : Ω →₂[μ] H) (N k : ℕ) :
    let xNk := denseEpigraphNonnegWinnerField (φ := φ) u N k
    ∀ᵐ ω ∂μ.restrict (MeasureTheory.spanningSets μ k),
      (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal ≤
        ENNReal.ofReal (⟪xNk ω, u ω⟫_ℝ - EReal.toReal (φ (xNk ω) : EReal)) := by
  let xNk : Ω →₂[μ] H := denseEpigraphNonnegWinnerField (φ := φ) u N k
  have hxNk_eff :
      xNk ∈ effectiveDomain (integralFunctional μ φ) := by
    -- The normalized truncated winner field is admissible for the primal integral functional.
    simpa [xNk] using
      denseEpigraphNonnegWinnerField_mem_effectiveDomain
        (μ := μ) (φ := φ) hφ_mem hzero_min u N k
  have hxNk_branch :=
    integralFunctional_branch_of_mem_effectiveDomain (μ := μ) φ (x := xNk) hxNk_eff
  have hdefect :
      ∀ᵐ ω ∂μ.restrict (MeasureTheory.spanningSets μ k),
        denseEpigraphNonnegPrefixSup (φ := φ) u N ω ≤
          (((⟪xNk ω, u ω⟫_ℝ : ℝ) : EReal) - (φ (xNk ω) : EReal)) := by
    refine (ae_restrict_iff' (measurableSet_spanningSets μ k)).2 ?_
    filter_upwards
      [denseEpigraphNonnegPrefixSup_le_nonnegWinnerFieldDefect
        (μ := μ) (φ := φ) hzero_min u N k]
      with ω hω hωspan
    -- On the restricted measure, the indicator form collapses to the raw normalized prefix.
    simpa [xNk, Set.indicator_of_mem, hωspan] using hω
  have hxNk_fin :
      ∀ᵐ ω ∂μ.restrict (MeasureTheory.spanningSets μ k), (φ (xNk ω) : EReal) < ⊤ := by
    refine (ae_restrict_iff' (measurableSet_spanningSets μ k)).2 ?_
    filter_upwards [hxNk_branch.2] with ω hω hωspan
    exact hω
  filter_upwards [hdefect, hxNk_fin] with ω hdefectω hxNk_finω
  have hxNk_bot : (φ (xNk ω) : EReal) ≠ ⊥ := ne_of_gt (φ (xNk ω)).2
  have hleft_top : denseEpigraphNonnegPrefixSup (φ := φ) u N ω ≠ ⊤ := by
    by_cases hωnonneg : 0 ≤ denseEpigraphPrefixSup (φ := φ) u N ω
    · -- On the nonnegative side, the normalized prefix is the original finite prefix.
      rw [denseEpigraphNonnegPrefixSup, max_eq_right hωnonneg]
      rw [denseEpigraphPrefixWinnerPoint_slice_eq_prefixSup (φ := φ) (u := u) N ω]
      exact EReal.coe_ne_top _
    · -- Otherwise the normalized prefix is the constant value `0`.
      rw [denseEpigraphNonnegPrefixSup, max_eq_left (le_of_not_ge hωnonneg)]
      exact EReal.coe_ne_top (0 : ℝ)
  have hleft_bot : denseEpigraphNonnegPrefixSup (φ := φ) u N ω ≠ ⊥ := by
    by_cases hωnonneg : 0 ≤ denseEpigraphPrefixSup (φ := φ) u N ω
    · -- On the nonnegative side, the normalized prefix is the original finite prefix.
      rw [denseEpigraphNonnegPrefixSup, max_eq_right hωnonneg]
      rw [denseEpigraphPrefixWinnerPoint_slice_eq_prefixSup (φ := φ) (u := u) N ω]
      exact EReal.coe_ne_bot _
    · -- Otherwise the normalized prefix is the constant value `0`.
      rw [denseEpigraphNonnegPrefixSup, max_eq_left (le_of_not_ge hωnonneg)]
      exact EReal.coe_ne_bot (0 : ℝ)
  have hdefect_eq :
      (((⟪xNk ω, u ω⟫_ℝ : ℝ) : EReal) - (φ (xNk ω) : EReal)) =
        (((⟪xNk ω, u ω⟫_ℝ - EReal.toReal (φ (xNk ω) : EReal) : ℝ)) : EReal) := by
    -- Rewrite the finite `EReal` value `φ (xNk ω)` as a real cast before collapsing the defect.
    calc
      (((⟪xNk ω, u ω⟫_ℝ : ℝ) : EReal) - (φ (xNk ω) : EReal))
          = (((⟪xNk ω, u ω⟫_ℝ : ℝ) : EReal) -
              (((EReal.toReal (φ (xNk ω) : EReal) : ℝ) : EReal))) := by
                rw [EReal.coe_toReal (ne_of_lt hxNk_finω) hxNk_bot]
      _ = (((⟪xNk ω, u ω⟫_ℝ - EReal.toReal (φ (xNk ω) : EReal) : ℝ)) : EReal) := by
            rw [← EReal.coe_sub]
  have hdefect_top :
      (((⟪xNk ω, u ω⟫_ℝ : ℝ) : EReal) - (φ (xNk ω) : EReal)) ≠ ⊤ := by
    rw [hdefect_eq]
    exact EReal.coe_ne_top _
  have htoReal_le :
      EReal.toReal (denseEpigraphNonnegPrefixSup (φ := φ) u N ω) ≤
        ⟪xNk ω, u ω⟫_ℝ - EReal.toReal (φ (xNk ω) : EReal) := by
    -- With both sides finite on the restricted set, `EReal.toReal` turns the defect bound into a
    -- real inequality.
    simpa [hdefect_eq] using
      EReal.toReal_le_toReal hdefectω hleft_bot hdefect_top
  have hleft_eq :
      (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal =
        ENNReal.ofReal (EReal.toReal (denseEpigraphNonnegPrefixSup (φ := φ) u N ω)) := by
    -- The normalized prefix is finite, so coercing it to `ENNReal` is just `ENNReal.ofReal`.
    rw [show denseEpigraphNonnegPrefixSup (φ := φ) u N ω =
        (((EReal.toReal (denseEpigraphNonnegPrefixSup (φ := φ) u N ω) : ℝ)) : EReal) by
          rw [EReal.coe_toReal hleft_top hleft_bot]]
    exact EReal.real_coe_toENNReal _
  calc
    (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal
        = ENNReal.ofReal (EReal.toReal (denseEpigraphNonnegPrefixSup (φ := φ) u N ω)) := hleft_eq
    _ ≤ ENNReal.ofReal (⟪xNk ω, u ω⟫_ℝ - EReal.toReal (φ (xNk ω) : EReal)) := by
          exact ENNReal.ofReal_le_ofReal htoReal_le

/-- Helper for Proposition 13.50: in the finite-measure branch, once the pointwise conjugate
integrand already lies in the effective domain, the dense winner-point competitors and monotone
convergence give the reverse inequality directly. -/
private theorem denseEpigraphPrefixSup_integral_le_conjugate_of_finiteMeasure
    [μ.IsComplete] [SigmaFinite μ] [IsFiniteMeasure μ]
    [Nonempty (epigraph φ.asEReal)]
    (hφ : φ ∈ Γ₀(H))
    (u : Ω →₂[μ] H) (N : ℕ) :
    (((∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ)) : EReal) ≤
      conjugate ((integralFunctional μ φ).asEReal) u := by
  classical
  let xNFun : Ω → H := fun ω ↦ (denseEpigraphPrefixWinnerPoint (φ := φ) u N ω).1.1
  let xNMem : MemLp xNFun 2 μ :=
    denseEpigraphPrefixWinnerPoint_memLp_of_finiteMeasure (φ := φ) (u := u) N
  let xN : Ω →₂[μ] H := xNMem.toLp xNFun
  have hxN_ae : xN =ᵐ[μ] xNFun := by
    -- The packaged `L²` competitor agrees a.e. with the winner-point first coordinate.
    simpa [xN, xNMem, xNFun] using xNMem.coeFn_toLp
  have hxN_eff : xN ∈ effectiveDomain (integralFunctional μ φ) := by
    -- The finite-measure winner-point competitor is admissible for `integralFunctional μ φ`.
    simpa [xN, xNMem, xNFun] using
      denseEpigraphPrefixWinnerPointLp_mem_effectiveDomain_of_finiteMeasure
        (μ := μ) (φ := φ) (hφ := hφ) (u := u) N
  have hxN_branch :=
    integralFunctional_branch_of_mem_effectiveDomain (μ := μ) φ (x := xN) hxN_eff
  have hpointwise :
      ∀ᵐ ω ∂μ,
        EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ≤
          ⟪xN ω, u ω⟫_ℝ - EReal.toReal (φ (xN ω) : EReal) := by
    -- Convert the pointwise `EReal` defect domination into a real inequality.
    filter_upwards [hxN_ae, hxN_branch.2] with ω hω hxω
    have hprefix_defect :
        denseEpigraphPrefixSup (φ := φ) u N ω ≤
          (((⟪xNFun ω, u ω⟫_ℝ : ℝ) : EReal) - (φ (xNFun ω) : EReal)) := by
      simpa [xNFun] using
        denseEpigraphPrefixWinnerPoint_defect_ge_prefixSup
          (φ := φ) (u := u) N ω
    have hprefix_defect' :
        denseEpigraphPrefixSup (φ := φ) u N ω ≤
          (((⟪xN ω, u ω⟫_ℝ : ℝ) : EReal) - (φ (xN ω) : EReal)) := by
      simpa [xNFun, hω] using hprefix_defect
    have hφω_bot : (φ (xN ω) : EReal) ≠ ⊥ := ne_of_gt (φ (xN ω)).2
    have hdefect_eq :
        (((⟪xN ω, u ω⟫_ℝ : ℝ) : EReal) - (φ (xN ω) : EReal)) =
          (((⟪xN ω, u ω⟫_ℝ - EReal.toReal (φ (xN ω) : EReal) : ℝ)) : EReal) := by
      calc
        (((⟪xN ω, u ω⟫_ℝ : ℝ) : EReal) - (φ (xN ω) : EReal))
            = (((⟪xN ω, u ω⟫_ℝ : ℝ) : EReal) -
                (((EReal.toReal (φ (xN ω) : EReal) : ℝ) : EReal))) := by
                  rw [EReal.coe_toReal (ne_of_lt hxω) hφω_bot]
        _ = (((⟪xN ω, u ω⟫_ℝ - EReal.toReal (φ (xN ω) : EReal) : ℝ)) : EReal) := by
              rw [← EReal.coe_sub]
    have hdefect_top :
        (((⟪xN ω, u ω⟫_ℝ : ℝ) : EReal) - (φ (xN ω) : EReal)) ≠ ⊤ := by
      rw [hdefect_eq]
      exact EReal.coe_ne_top _
    have htoReal :=
      EReal.toReal_le_toReal
        hprefix_defect'
        (denseEpigraphPrefixSup_ne_bot (φ := φ) u N ω)
        hdefect_top
    simpa [hdefect_eq] using htoReal
  have hprefix_int :
      Integrable (fun ω ↦ EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω)) μ :=
    integrable_denseEpigraphPrefixSup_toReal_of_finiteMeasure (μ := μ) (φ := φ) (u := u) N
  have hinner_int : Integrable (fun ω ↦ ⟪xN ω, u ω⟫_ℝ) μ :=
    MeasureTheory.L2.integrable_inner xN u
  have hreal_le :
      (∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ) ≤
        ∫ ω, (⟪xN ω, u ω⟫_ℝ - EReal.toReal (φ (xN ω) : EReal)) ∂μ := by
    -- Integrate the pointwise affine-defect domination for the `N`th competitor.
    exact integral_mono_ae hprefix_int (hinner_int.sub hxN_branch.1) hpointwise
  have haffine_le :
      (((⟪xN, u⟫_ℝ : ℝ) : EReal) - (integralFunctional μ φ xN : EReal)) ≤
        conjugate ((integralFunctional μ φ).asEReal) u := by
    -- The `N`th competitor contributes one term in `conjugate_apply`.
    change
      (((⟪xN, u⟫_ℝ : ℝ) : EReal) - Function.asEReal (integralFunctional μ φ) xN) ≤
        conjugate ((integralFunctional μ φ).asEReal) u
    rw [conjugate_apply]
    simpa [Function.asEReal] using
      (le_iSup (fun x : Ω →₂[μ] H ↦
        (((⟪x, u⟫_ℝ : ℝ) : EReal) - Function.asEReal (integralFunctional μ φ) x)) xN)
  calc
    (((∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ)) : EReal)
        ≤ (((∫ ω, (⟪xN ω, u ω⟫_ℝ - EReal.toReal (φ (xN ω) : EReal)) ∂μ : ℝ)) : EReal) := by
            exact_mod_cast hreal_le
    _ = (((⟪xN, u⟫_ℝ : ℝ) : EReal) - (integralFunctional μ φ xN : EReal)) := by
          -- Rewrite the right-hand integral as the affine defect of the packaged competitor.
          rw [integral_sub hinner_int hxN_branch.1, MeasureTheory.L2.inner_def,
            integralFunctional_apply_eq_integral_toReal_of_mem_effectiveDomain
              (μ := μ) φ (x := xN) hxN_eff,
            ← EReal.coe_sub]
    _ ≤ conjugate ((integralFunctional μ φ).asEReal) u := haffine_le

/-- Helper for Proposition 13.50: in the finite-measure branch, once the pointwise conjugate
integrand already lies in the effective domain, the dense winner-point competitors and monotone
convergence give the reverse inequality directly. -/
private theorem
    integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_of_finiteMeasure_of_mem_effectiveDomain
    [μ.IsComplete] [SigmaFinite μ] [IsFiniteMeasure μ]
    (u : Ω →₂[μ] H)
    (hu_eff : u ∈ effectiveDomain (integralFunctional μ (gammaZeroConjugate φ hφ))) :
    (integralFunctional μ (gammaZeroConjugate φ hφ) u : EReal) ≤
      conjugate ((integralFunctional μ φ).asEReal) u := by
  classical
  let φStar : H → Set.Ioi (⊥ : EReal) := gammaZeroConjugate φ hφ
  let rhs : EReal := conjugate ((integralFunctional μ φ).asEReal) u
  letI : Nonempty (epigraph φ.asEReal) := denseEpigraph_nonempty (φ := φ) hφ
  have hprefix_le :
      ∀ N : ℕ,
        (((∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ)) : EReal) ≤ rhs := by
    intro N
    simpa [rhs] using denseEpigraphPrefixSup_integral_le_conjugate_of_finiteMeasure
      (μ := μ) (φ := φ) (hφ := hφ) u N
  have hu_eval :
      (integralFunctional μ φStar u : EReal) =
        ((∫ ω, EReal.toReal (φStar (u ω) : EReal) ∂μ : ℝ) : EReal) := by
    -- The effective-domain hypothesis selects the real branch of the conjugate integral.
    exact integralFunctional_apply_eq_integral_toReal_of_mem_effectiveDomain
      (μ := μ) φStar (x := u) hu_eff
  have hlim_real :=
    integral_tendsto_denseEpigraphPrefixSup_toReal_of_mem_effectiveDomain
      (μ := μ) (φ := φ) (hφ := hφ) (u := u) hu_eff
  have hlim :
      Filter.Tendsto
        (fun N ↦ (((∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ)) : EReal))
        Filter.atTop
        (nhds (integralFunctional μ φStar u : EReal)) := by
    -- Coerce the convergent real integrals into `EReal` before taking the closed-order limit.
    let F : ℕ → ℝ := fun N ↦
      ∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ
    have hlim' :
        Filter.Tendsto (fun N ↦ ((F N : ℝ) : EReal)) Filter.atTop
          (nhds (((∫ ω, EReal.toReal (φStar (u ω) : EReal) ∂μ : ℝ) : EReal))) := by
      exact (continuous_coe_real_ereal.tendsto
        (∫ ω, EReal.toReal (φStar (u ω) : EReal) ∂μ : ℝ)).comp hlim_real
    exact hu_eval.symm ▸ by
      simpa [F]
  have hmem : (integralFunctional μ φStar u : EReal) ∈ Set.Iic rhs := by
    -- Every finite prefix integral lies below the conjugate, so the limit does as well.
    exact isClosed_Iic.mem_of_tendsto hlim (Filter.Eventually.of_forall hprefix_le)
  simpa [Set.mem_Iic, rhs, φStar] using hmem

/-- Helper for Proposition 13.50: applying the already-proved easy inequality to the pointwise
conjugate integrand gives the symmetric conjugate-side estimate `g* ≤ f`. -/
private theorem conjugate_integralFunctional_gammaZeroConjugate_le_integralFunctional
    (u : Ω →₂[μ] H) :
    conjugate ((integralFunctional μ (gammaZeroConjugate φ hφ)).asEReal) u ≤
      (integralFunctional μ φ u : EReal) := by
  let φStar : H → Set.Ioi (⊥ : EReal) := gammaZeroConjugate φ hφ
  have hφStar : φStar ∈ Γ₀(H) := by
    -- The canonical conjugate of a `Γ₀` integrand is again in `Γ₀`.
    simpa [φStar] using gammaZeroConjugate_mem_gammaZero hφ
  have hle :=
    conjugate_integralFunctional_le_integralFunctional_gammaZeroConjugate
      (μ := μ) (φ := φStar) (hφ := hφStar) u
  -- Collapse the double pointwise conjugate back to `φ`.
  simpa [φStar, gammaZeroConjugate_gammaZeroConjugate_local (φ := φ) (hφ := hφ),
    Function.asEReal] using hle

/-- Helper for Proposition 13.50: every dense-epigraph prefix supremum is finite above as well as
below, because it is realized by a real affine slice of the recursive winner point. -/
private theorem denseEpigraphPrefixSup_ne_top
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) (ω : Ω) :
    denseEpigraphPrefixSup (φ := φ) u N ω ≠ ⊤ := by
  -- Rewrite the prefix through the winner-point slice, which is a real cast in `EReal`.
  rw [denseEpigraphPrefixWinnerPoint_slice_eq_prefixSup (φ := φ) (u := u) N ω]
  exact EReal.coe_ne_top _

/-- Helper for Proposition 13.50: every dense-epigraph prefix dominates the base prefix `N = 0`.
This isolates the monotone normalization used in the finite `⊤`-branch. -/
private theorem denseEpigraphPrefixSup_zero_le
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    ∀ ω : Ω,
      denseEpigraphPrefixSup (φ := φ) u 0 ω ≤
        denseEpigraphPrefixSup (φ := φ) u N ω := by
  intro ω
  -- The full prefix family is monotone, so the base prefix sits below every later stage.
  exact denseEpigraphPrefixSup_monotone (φ := φ) u (Nat.zero_le N) ω

/-- Helper for Proposition 13.50: the shifted finite-prefix real integrand is nonnegative almost
everywhere. This is the ENNReal-ready normalization for the bounded-prefix argument. -/
private theorem denseEpigraphPrefixSup_shift_nonneg
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (N : ℕ) :
    0 ≤ᵐ[μ] fun ω ↦
      EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) -
        EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω) := by
  filter_upwards with ω
  -- Convert the monotone `EReal` prefix comparison into a real inequality using finiteness of
  -- both endpoints.
  have hprefix_le :
      denseEpigraphPrefixSup (φ := φ) u 0 ω ≤ denseEpigraphPrefixSup (φ := φ) u N ω :=
    denseEpigraphPrefixSup_zero_le (φ := φ) u N ω
  have htoReal_le :
      EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω) ≤
        EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) := by
    exact EReal.toReal_le_toReal hprefix_le
      (denseEpigraphPrefixSup_ne_bot (φ := φ) u 0 ω)
      (denseEpigraphPrefixSup_ne_top (φ := φ) u N ω)
  exact sub_nonneg.mpr htoReal_le

/-- Helper for Proposition 13.50: on a finite-measure space, the shifted finite-prefix real
integrand is integrable. This prepares the prefix bounds for `ofReal`/`lintegral` conversion. -/
private theorem integrable_denseEpigraphPrefixSup_shift_toReal_of_finiteMeasure
    [Nonempty (epigraph φ.asEReal)] [IsFiniteMeasure μ] (u : Ω →₂[μ] H) (N : ℕ) :
    Integrable
      (fun ω ↦
        EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) -
          EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω))
      μ := by
  -- Both real-valued prefix integrands are integrable on a finite-measure space, so their
  -- difference is integrable as well.
  exact (integrable_denseEpigraphPrefixSup_toReal_of_finiteMeasure
      (μ := μ) (φ := φ) (u := u) N).sub
    (integrable_denseEpigraphPrefixSup_toReal_of_finiteMeasure
      (μ := μ) (φ := φ) (u := u) 0)

/-- Helper for Proposition 13.50: converting the nonnegative shifted finite-prefix real integral
to a `lintegral` matches the expected affine correction. This is the boundedness input for the
finite effective-domain bridge. -/
private theorem lintegral_denseEpigraphPrefixSup_shift_eq_of_finiteMeasure
    [Nonempty (epigraph φ.asEReal)] [IsFiniteMeasure μ] (u : Ω →₂[μ] H) (N : ℕ) :
    ∫⁻ ω,
        ENNReal.ofReal
          (EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) -
            EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω)) ∂μ =
      ENNReal.ofReal
        ((∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ) -
          ∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω) ∂μ) := by
  have hshift_int :=
    integrable_denseEpigraphPrefixSup_shift_toReal_of_finiteMeasure
      (μ := μ) (φ := φ) (u := u) N
  have hshift_nonneg :=
    denseEpigraphPrefixSup_shift_nonneg (μ := μ) (φ := φ) (u := u) N
  -- Rewrite the nonnegative shifted real integral as a `lintegral` of `ENNReal.ofReal`.
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hshift_int hshift_nonneg]
  simp [integral_sub,
    integrable_denseEpigraphPrefixSup_toReal_of_finiteMeasure (μ := μ) (φ := φ) (u := u) N,
    integrable_denseEpigraphPrefixSup_toReal_of_finiteMeasure (μ := μ) (φ := φ) (u := u) 0]

/-- Helper for Proposition 13.50: once a finite `EReal` value is shifted by a real correction,
applying `toENNReal` agrees with taking `ENNReal.ofReal` of the shifted `toReal` value. -/
private theorem shifted_toENNReal_eq_ofReal_shifted_toReal_local
    {ξ : EReal} {ρ : ℝ}
    (hξ_top : ξ ≠ ⊤) (hξ_bot : ξ ≠ ⊥) :
    (ξ + (((-ρ : ℝ) : EReal))).toENNReal =
      ENNReal.ofReal (EReal.toReal ξ - ρ) := by
  -- Rewrite the finite `EReal` value `ξ` as a real cast before shifting.
  have hsum_eq :
      ξ + (((-ρ : ℝ) : EReal)) =
        (((EReal.toReal ξ - ρ : ℝ)) : EReal) := by
    calc
      ξ + (((-ρ : ℝ) : EReal)) =
          (((EReal.toReal ξ : ℝ) : EReal)) + (((-ρ : ℝ) : EReal)) := by
            rw [EReal.coe_toReal hξ_top hξ_bot]
      _ = (((EReal.toReal ξ - ρ : ℝ)) : EReal) := by
            simpa [sub_eq_add_neg]
  rw [hsum_eq]
  exact EReal.real_coe_toENNReal (EReal.toReal ξ - ρ)

/-- Helper for Proposition 13.50: the shifted `ENNReal` integrand of the pointwise conjugate is
the supremum of the shifted dense-epigraph prefix approximants. -/
private theorem iSup_shifted_denseEpigraphPrefixSup_eq_shifted_gammaZeroConjugate
    [Nonempty (epigraph φ.asEReal)] (u : Ω →₂[μ] H) (ω : Ω) :
    (⨆ N,
      ENNReal.ofReal
        (EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) -
          EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω))) =
      ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal) +
        (((-EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω) : ℝ) : EReal))).toENNReal := by
  let ρ0 : ℝ := EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω)
  let s : ℕ → ℝ≥0∞ := fun N ↦
    ENNReal.ofReal (EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) - ρ0)
  have hs_eq :
      ∀ N : ℕ,
        s N =
          ((denseEpigraphPrefixSup (φ := φ) u N ω + (((-ρ0 : ℝ) : EReal))).toENNReal) := by
    intro N
    -- Each finite prefix value is finite, so the shift can be rewritten through `toReal`.
    dsimp [s, ρ0]
    symm
    exact shifted_toENNReal_eq_ofReal_shifted_toReal_local
      (ξ := denseEpigraphPrefixSup (φ := φ) u N ω)
      (ρ := EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω))
      (denseEpigraphPrefixSup_ne_top (φ := φ) u N ω)
      (denseEpigraphPrefixSup_ne_bot (φ := φ) u N ω)
  have hs_mono : Monotone s := by
    intro n m hnm
    rw [hs_eq, hs_eq]
    simpa [add_comm] using
      EReal.toENNReal_le_toENNReal <|
        add_le_add_left (denseEpigraphPrefixSup_monotone (φ := φ) u hnm ω)
          (((-ρ0 : ℝ) : EReal))
  have hs_tendsto :
      Filter.Tendsto s Filter.atTop
        (nhds
          (((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal) +
            (((-ρ0 : ℝ) : EReal))).toENNReal)) := by
    have hprefix_tendsto :=
      tendsto_denseEpigraphPrefixSup (φ := φ) (hφ := hφ) (u := u) (ω := ω)
    have hs_shift_tendsto :
        Filter.Tendsto
          (fun N ↦
            (denseEpigraphPrefixSup (φ := φ) u N ω + (((-ρ0 : ℝ) : EReal))).toENNReal)
          Filter.atTop
          (nhds
            (((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal) +
              (((-ρ0 : ℝ) : EReal))).toENNReal)) := by
      have hpair_tendsto :
          Filter.Tendsto
            (fun N ↦
              (denseEpigraphPrefixSup (φ := φ) u N ω, (((-ρ0 : ℝ) : EReal))))
            Filter.atTop
            (nhds
              ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal),
                (((-ρ0 : ℝ) : EReal)))) :=
        hprefix_tendsto.prodMk_nhds tendsto_const_nhds
      exact
        ((EReal.continuousAt_add
          (p := ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal),
            (((-ρ0 : ℝ) : EReal))))
          (Or.inr (EReal.coe_ne_bot _))
          (Or.inr (EReal.coe_ne_top _))).ereal_toENNReal.tendsto).comp hpair_tendsto
    exact hs_shift_tendsto.congr' <|
      Filter.Eventually.of_forall fun N ↦ by
        simpa using (hs_eq N).symm
  -- Monotone convergence identifies the pointwise limit with the supremum of the shifted
  -- prefix approximants.
  have hiSup_eq :
      (((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal) +
          (((-ρ0 : ℝ) : EReal))).toENNReal) =
        ⨆ N, s N :=
    tendsto_nhds_unique hs_tendsto (tendsto_atTop_iSup hs_mono)
  simpa [s, ρ0] using hiSup_eq.symm

/-- Helper for Proposition 13.50: a finite upper bound on the real dense-prefix integrals forces
the shifted `ENNReal` integral of the pointwise conjugate integrand to be finite. -/
private theorem shifted_gammaZeroConjugate_lintegral_ne_top_of_bddAbove_prefixIntegrals
    [μ.IsComplete] [SigmaFinite μ] [IsFiniteMeasure μ]
    [Nonempty (epigraph φ.asEReal)]
    (u : Ω →₂[μ] H)
    (hbdd : BddAbove (Set.range
      (fun N ↦ (∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ)))) :
    ∫⁻ ω,
        (((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal) +
          (((-EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω) : ℝ) : EReal))).toENNReal) ∂μ ≠
      ∞ := by
  let ρ0 : Ω → ℝ := fun ω ↦ EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω)
  let s : ℕ → Ω → ℝ≥0∞ := fun N ω ↦
    ENNReal.ofReal
      (EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) - ρ0 ω)
  rcases hbdd with ⟨B, hB⟩
  let C : ℝ := B - ∫ ω, ρ0 ω ∂μ
  have hs_aemeas : ∀ N : ℕ, AEMeasurable (s N) μ := by
    intro N
    -- Each shifted prefix is an `ENNReal.ofReal` of an integrable real field.
    exact
      ((integrable_denseEpigraphPrefixSup_toReal_of_finiteMeasure
          (μ := μ) (φ := φ) (u := u) N).aestronglyMeasurable.sub
        (integrable_denseEpigraphPrefixSup_toReal_of_finiteMeasure
          (μ := μ) (φ := φ) (u := u) 0).aestronglyMeasurable).aemeasurable.ennreal_ofReal
  have hs_mono : ∀ᵐ ω ∂μ, Monotone fun N ↦ s N ω := by
    refine Filter.Eventually.of_forall ?_
    intro ω n m hnm
    -- The real shifted prefixes inherit monotonicity from the dense-epigraph prefix family.
    dsimp [s, ρ0]
    exact ENNReal.ofReal_le_ofReal <|
      sub_le_sub_right
        (EReal.toReal_le_toReal
          (denseEpigraphPrefixSup_monotone (φ := φ) u hnm ω)
          (denseEpigraphPrefixSup_ne_bot (φ := φ) u n ω)
          (denseEpigraphPrefixSup_ne_top (φ := φ) u m ω)) _
  have hs_lintegral :
      ∫⁻ ω, ⨆ N, s N ω ∂μ = ⨆ N, ∫⁻ ω, s N ω ∂μ := by
    exact MeasureTheory.lintegral_iSup' hs_aemeas hs_mono
  have hbound :
      (⨆ N, ∫⁻ ω, s N ω ∂μ) ≤ ENNReal.ofReal C := by
    refine iSup_le ?_
    intro N
    have hprefix_le : (∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ) ≤ B := by
      exact hB ⟨N, rfl⟩
    calc
      ∫⁻ ω, s N ω ∂μ
          = ENNReal.ofReal
              ((∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ) -
                ∫ ω, ρ0 ω ∂μ) := by
              simpa [s, ρ0] using
                lintegral_denseEpigraphPrefixSup_shift_eq_of_finiteMeasure
                  (μ := μ) (φ := φ) (u := u) N
      _ ≤ ENNReal.ofReal C := by
            apply ENNReal.ofReal_le_ofReal
            dsimp [C]
            linarith
  have hlintegral_le :
      ∫⁻ ω,
          (((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal) +
            (((-EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω) : ℝ) : EReal))).toENNReal) ∂μ ≤
        ENNReal.ofReal C := by
    -- Replace the shifted conjugate integrand by the supremum of the shifted prefix approximants.
    calc
      ∫⁻ ω,
          (((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal) +
            (((-EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω) : ℝ) : EReal))).toENNReal) ∂μ
          = ∫⁻ ω, ⨆ N, s N ω ∂μ := by
              refine lintegral_congr_ae ?_
              exact Filter.Eventually.of_forall fun ω ↦ by
                simpa [s, ρ0] using
                  (iSup_shifted_denseEpigraphPrefixSup_eq_shifted_gammaZeroConjugate
                    (φ := φ) (hφ := hφ) (u := u) ω).symm
      _ = ⨆ N, ∫⁻ ω, s N ω ∂μ := hs_lintegral
      _ ≤ ENNReal.ofReal C := hbound
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlintegral_le

/-- Helper for Proposition 13.50: for a fixed `L²` field, finiteness of a shifted `ENNReal`
integral forces the pointwise conjugate integral back into the effective domain. -/
private theorem mem_effectiveDomain_of_shifted_lintegral_ne_top
    (ψ : H → Set.Ioi (⊥ : EReal)) {x : Ω →₂[μ] H} {ρ : Ω → ℝ}
    (hρ_le : ∀ ω : Ω, (((ρ ω : ℝ) : EReal)) ≤ (ψ (x ω) : EReal))
    (hρ_int : Integrable ρ μ)
    (hshift_sm : AEStronglyMeasurable (fun ω ↦ EReal.toReal (ψ (x ω)) - ρ ω) μ)
    (hshift_meas :
      AEMeasurable
        (fun ω ↦ (((ψ (x ω) : EReal) + (((-ρ ω : ℝ) : EReal))).toENNReal)) μ)
    (hshift_ne_top :
      ∫⁻ ω, (((ψ (x ω) : EReal) + (((-ρ ω : ℝ) : EReal))).toENNReal) ∂μ ≠ ∞) :
    x ∈ effectiveDomain (integralFunctional μ ψ) := by
  have hshift_finite :
      ∀ᵐ ω ∂μ,
        (((ψ (x ω) : EReal) + (((-ρ ω : ℝ) : EReal))).toENNReal) < ∞ :=
    ae_lt_top' hshift_meas hshift_ne_top
  have hψ_finite : ∀ᵐ ω ∂μ, (ψ (x ω) : EReal) < ⊤ := by
    filter_upwards [hshift_finite] with ω hω
    by_contra htop
    have hsum_top :
        (ψ (x ω) : EReal) + (((-ρ ω : ℝ) : EReal)) = ⊤ := by
      have hψ_top : (ψ (x ω) : EReal) = ⊤ := top_unique (not_lt.mp htop)
      rw [hψ_top]
      exact EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
    have : (((ψ (x ω) : EReal) + (((-ρ ω : ℝ) : EReal))).toENNReal) = ∞ := by
      simpa [hsum_top]
    exact hω.ne this
  have hshift_eq :
      (fun ω ↦ (((ψ (x ω) : EReal) + (((-ρ ω : ℝ) : EReal))).toENNReal)) =ᵐ[μ]
        fun ω ↦ ENNReal.ofReal (EReal.toReal (ψ (x ω)) - ρ ω) := by
    filter_upwards [hψ_finite] with ω hω
    exact shifted_toENNReal_eq_ofReal_shifted_toReal_local
      (ξ := (ψ (x ω) : EReal)) (ρ := ρ ω)
      (lt_top_iff_ne_top.mp hω) (ne_of_gt ((ψ (x ω)).2))
  have hshift_nonneg :
      0 ≤ᵐ[μ] fun ω ↦ EReal.toReal (ψ (x ω)) - ρ ω := by
    filter_upwards [hψ_finite] with ω hω
    have hreal_le : ρ ω ≤ EReal.toReal (ψ (x ω)) := by
      exact EReal.toReal_le_toReal (hρ_le ω) (EReal.coe_ne_bot _)
        (lt_top_iff_ne_top.mp hω)
    exact sub_nonneg.mpr hreal_le
  have hshift_ofReal_ne_top :
      ∫⁻ ω, ENNReal.ofReal (EReal.toReal (ψ (x ω)) - ρ ω) ∂μ ≠ ∞ := by
    rw [← lintegral_congr_ae hshift_eq]
    exact hshift_ne_top
  have hψ_int :
      Integrable (fun ω ↦ EReal.toReal (ψ (x ω))) μ := by
    have hshift_int :
        Integrable (fun ω ↦ EReal.toReal (ψ (x ω)) - ρ ω) μ :=
      (lintegral_ofReal_ne_top_iff_integrable hshift_sm hshift_nonneg).mp hshift_ofReal_ne_top
    have hadd_int :
        Integrable (fun ω ↦ (EReal.toReal (ψ (x ω)) - ρ ω) + ρ ω) μ :=
      hshift_int.add hρ_int
    have hsum_eq :
        (fun ω ↦ (EReal.toReal (ψ (x ω)) - ρ ω) + ρ ω) =ᵐ[μ]
          fun ω ↦ EReal.toReal (ψ (x ω)) := by
      exact Filter.Eventually.of_forall fun ω ↦ by ring
    exact hadd_int.congr hsum_eq
  have hbranch :
      Integrable (fun ω ↦ EReal.toReal (ψ (x ω))) μ ∧
        ∀ᵐ ω ∂μ, (ψ (x ω) : EReal) < ⊤ := ⟨hψ_int, hψ_finite⟩
  -- This is exactly the finite branch of `pointwiseIntegralFunctional`.
  rw [mem_effectiveDomain_iff, integralFunctional_coe μ, pointwiseIntegralFunctional]
  simpa [hbranch] using
    (EReal.coe_lt_top (∫ ω, EReal.toReal (ψ (x ω)) ∂μ : ℝ))

/-- Helper for Proposition 13.50: in the finite-measure branch, if the pointwise conjugate
integral is already `⊤`, then the affine dense-epigraph prefix bounds should force the conjugate
of `integralFunctional μ φ` to be `⊤` as well. -/
private theorem mem_effectiveDomain_gammaZeroConjugate_of_bddAbove_prefixIntegrals
    [μ.IsComplete] [SigmaFinite μ] [IsFiniteMeasure μ]
    [Nonempty (epigraph φ.asEReal)]
    (u : Ω →₂[μ] H)
    (hbdd : BddAbove (Set.range
      (fun N ↦ (∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ)))) :
    u ∈ effectiveDomain (integralFunctional μ (gammaZeroConjugate φ hφ)) := by
  let ρ0 : Ω → ℝ := fun ω ↦ EReal.toReal (denseEpigraphPrefixSup (φ := φ) u 0 ω)
  let φStar : H → Set.Ioi (⊥ : EReal) := gammaZeroConjugate φ hφ
  have hρ0_le : ∀ ω : Ω, (((ρ0 ω : ℝ) : EReal)) ≤ (φStar (u ω) : EReal) := by
    intro ω
    -- The base dense prefix already sits below the full pointwise conjugate.
    calc
      (((ρ0 ω : ℝ) : EReal)) = denseEpigraphPrefixSup (φ := φ) u 0 ω := by
          dsimp [ρ0]
          rw [EReal.coe_toReal
            (denseEpigraphPrefixSup_ne_top (φ := φ) u 0 ω)
            (denseEpigraphPrefixSup_ne_bot (φ := φ) u 0 ω)]
      _ ≤ (φStar (u ω) : EReal) := by
          simpa [φStar] using
            denseEpigraphPrefixSup_le_gammaZeroConjugate
              (φ := φ) (hφ := hφ) (u := u) 0 ω
  have hρ0_int : Integrable ρ0 μ := by
    -- The base dense prefix is integrable on a finite-measure space.
    simpa [ρ0] using
      integrable_denseEpigraphPrefixSup_toReal_of_finiteMeasure
        (μ := μ) (φ := φ) (u := u) 0
  have hφStar_meas : Measurable φStar := by
    -- The conjugate integrand is measurable because it belongs to `Γ₀(H)`.
    exact (gammaZeroConjugate_mem_gammaZero hφ).1.measurable.subtype_mk
  have hshift_sm :
      AEStronglyMeasurable
        (fun ω ↦ EReal.toReal (φStar (u ω) : EReal) - ρ0 ω) μ := by
    have htoReal :
        AEStronglyMeasurable (fun ω ↦ EReal.toReal (φStar (u ω) : EReal)) μ :=
      pointwise_integrand_aestronglyMeasurable φStar hφStar_meas u
    exact htoReal.sub hρ0_int.aestronglyMeasurable
  have hshift_meas :
      AEMeasurable
        (fun ω ↦ (((φStar (u ω) : EReal) + (((-ρ0 ω : ℝ) : EReal))).toENNReal)) μ := by
    have hφStar_ae :
        AEMeasurable (fun ω ↦ (φStar (u ω) : EReal)) μ := by
      exact measurable_subtype_coe.comp_aemeasurable <|
        hφStar_meas.comp_aemeasurable (Lp.aestronglyMeasurable u).aemeasurable
    have hρ0_ae :
        AEMeasurable (fun ω ↦ (((-ρ0 ω : ℝ) : EReal))) μ := by
      exact
        (continuous_coe_real_ereal.comp continuous_neg).measurable.comp_aemeasurable
          hρ0_int.aestronglyMeasurable.aemeasurable
    exact (hφStar_ae.add hρ0_ae).ereal_toENNReal
  have hshift_ne_top :
      ∫⁻ ω, (((φStar (u ω) : EReal) + (((-ρ0 ω : ℝ) : EReal))).toENNReal) ∂μ ≠ ∞ := by
    -- The bounded prefix integrals control the shifted conjugate `lintegral`.
    simpa [φStar, ρ0] using
      shifted_gammaZeroConjugate_lintegral_ne_top_of_bddAbove_prefixIntegrals
        (μ := μ) (φ := φ) (hφ := hφ) u hbdd
  -- Apply the localized shifted-`lintegral` effective-domain criterion with the base prefix shift.
  exact mem_effectiveDomain_of_shifted_lintegral_ne_top
    (μ := μ) φStar hρ0_le hρ0_int hshift_sm hshift_meas hshift_ne_top

/-- Helper for Proposition 13.50: in the finite-measure branch, if the pointwise conjugate
integral is already `⊤`, then the affine dense-epigraph prefix bounds should force the conjugate
of `integralFunctional μ φ` to be `⊤` as well. -/
private theorem
    integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_of_finiteMeasure_of_not_mem_effectiveDomain
    [μ.IsComplete] [SigmaFinite μ] [IsFiniteMeasure μ]
    (u : Ω →₂[μ] H)
    (hu_eff : u ∉ effectiveDomain (integralFunctional μ (gammaZeroConjugate φ hφ))) :
    (integralFunctional μ (gammaZeroConjugate φ hφ) u : EReal) ≤
      conjugate ((integralFunctional μ φ).asEReal) u := by
  let φStar : H → Set.Ioi (⊥ : EReal) := gammaZeroConjugate φ hφ
  let rhs : EReal := conjugate ((integralFunctional μ φ).asEReal) u
  letI : Nonempty (epigraph φ.asEReal) := denseEpigraph_nonempty (φ := φ) hφ
  have hu_top : (integralFunctional μ φStar u : EReal) = ⊤ :=
    integralFunctional_eq_top_of_not_mem_effectiveDomain (μ := μ) φStar hu_eff
  rw [hu_top]
  by_cases hrhs_top : rhs = ⊤
  · -- Once the conjugate value is already `⊤`, the order statement is immediate.
    simpa [rhs, hrhs_top]
  · have hφInt_gamma : integralFunctional μ φ ∈ Γ₀(Ω →₂[μ] H) := by
      -- The finite-measure hypothesis is one of the proposition's source branches for clause (i).
      exact integralFunctional_phi_mem_gammaZero (μ := μ) (φ := φ) hφ
        (Or.inl IsFiniteMeasure.measure_univ_lt_top)
    have hrhs_bot : rhs ≠ ⊥ := by
      -- Properness of `integralFunctional μ φ` rules out `⊥` for its conjugate.
      exact conjugate_ne_bot_of_isProper (isProper_of_mem_gammaZero hφInt_gamma) u
    have hprefix_le_real :
        ∀ N : ℕ,
          (∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ) ≤ rhs.toReal := by
      intro N
      have hprefix_le :
          (((∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ)) : EReal) ≤ rhs := by
        exact denseEpigraphPrefixSup_integral_le_conjugate_of_finiteMeasure
          (μ := μ) (φ := φ) (hφ := hφ) u N
      exact EReal.toReal_le_toReal hprefix_le (EReal.coe_ne_bot _) hrhs_top
    have hbdd :
        BddAbove (Set.range
          (fun N ↦ (∫ ω, EReal.toReal (denseEpigraphPrefixSup (φ := φ) u N ω) ∂μ : ℝ))) := by
      refine ⟨rhs.toReal, ?_⟩
      rintro _ ⟨N, rfl⟩
      exact hprefix_le_real N
    exact False.elim <|
      hu_eff <|
        mem_effectiveDomain_gammaZeroConjugate_of_bddAbove_prefixIntegrals
          (μ := μ) (φ := φ) (hφ := hφ) u hbdd

/-- Helper for Proposition 13.50: in the zero-minimum branch, the normalized truncated
dense-epigraph winner fields should assemble the complete `σ`-finite reverse inequality. -/
private theorem nonnegWinnerFieldRestrictLIntegral_le_conjugateToENNReal
    [μ.IsComplete] [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)]
    (hφ_mem : φ ∈ Γ₀(H))
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))
    (u : Ω →₂[μ] H) (N k : ℕ)
    (hrhs_top : conjugate ((integralFunctional μ φ).asEReal) u ≠ ⊤) :
    let rhs : EReal := conjugate ((integralFunctional μ φ).asEReal) u
    let xNk := denseEpigraphNonnegWinnerField (φ := φ) u N k
    ∫⁻ ω, ENNReal.ofReal (⟪xNk ω, u ω⟫_ℝ - EReal.toReal (φ (xNk ω) : EReal)) ∂
        μ.restrict (MeasureTheory.spanningSets μ k) ≤ rhs.toENNReal := by
  let rhs : EReal := conjugate ((integralFunctional μ φ).asEReal) u
  let xNk : Ω →₂[μ] H := denseEpigraphNonnegWinnerField (φ := φ) u N k
  let defect : Ω → ℝ := fun ω ↦
    ⟪xNk ω, u ω⟫_ℝ - EReal.toReal (φ (xNk ω) : EReal)
  have hzero_min' := hzero_min
  rcases hzero_min with ⟨hφ0, _⟩
  have hxNk_eff :
      xNk ∈ effectiveDomain (integralFunctional μ φ) := by
    -- The normalized truncated winner field is admissible for the primal integral functional.
    simpa [xNk] using
      denseEpigraphNonnegWinnerField_mem_effectiveDomain
        (μ := μ) (φ := φ) (hφ_mem := hφ_mem) hzero_min' u N k
  have hxNk_branch :=
    integralFunctional_branch_of_mem_effectiveDomain (μ := μ) φ (x := xNk) hxNk_eff
  have hinner_int : Integrable (fun ω ↦ ⟪xNk ω, u ω⟫_ℝ) μ :=
    MeasureTheory.L2.integrable_inner xNk u
  have hdefect_eReal_nonneg :
      ∀ᵐ ω ∂μ,
        (0 : EReal) ≤ (((⟪xNk ω, u ω⟫_ℝ : ℝ) : EReal) - (φ (xNk ω) : EReal)) := by
    -- The normalized prefix is pointwise nonnegative and sits below the affine defect globally.
    filter_upwards
      [denseEpigraphNonnegPrefixSup_le_nonnegWinnerFieldDefect
        (μ := μ) (φ := φ) hzero_min' u N k]
      with ω hω
    have hindicator_nonneg :
        (0 : EReal) ≤
          Set.indicator (MeasureTheory.spanningSets μ k)
            (denseEpigraphNonnegPrefixSup (φ := φ) u N) ω := by
      by_cases hωspan : ω ∈ MeasureTheory.spanningSets μ k
      · simpa [Set.indicator_of_mem, hωspan, denseEpigraphNonnegPrefixSup] using
          (le_max_left (0 : EReal) (denseEpigraphPrefixSup (φ := φ) u N ω))
      · simp [Set.indicator_of_notMem, hωspan]
    exact le_trans hindicator_nonneg hω
  have hdefect_nonneg :
      0 ≤ᵐ[μ] fun ω ↦ defect ω := by
    -- Rewrite the finite affine defect into a real inequality before integrating it.
    filter_upwards [hdefect_eReal_nonneg, hxNk_branch.2] with ω hω hfin
    have hφ_bot : (φ (xNk ω) : EReal) ≠ ⊥ := ne_of_gt (φ (xNk ω)).2
    have hcast : (0 : EReal) ≤ ((defect ω : ℝ) : EReal) := by
      simpa [defect, EReal.coe_sub, EReal.coe_toReal (ne_of_lt hfin) hφ_bot] using hω
    have hreal_nonneg : 0 ≤ defect ω := EReal.coe_nonneg.mp hcast
    simpa using hreal_nonneg
  have hdefect_int : Integrable defect μ := by
    -- The affine defect is integrable because both terms come from admissible `L²` data.
    exact hinner_int.sub hxNk_branch.1
  have hdefect_zero_off :
      ∀ᵐ ω ∂μ, ω ∉ MeasureTheory.spanningSets μ k → defect ω = 0 := by
    -- Outside the `k`th spanning set, the truncated winner field vanishes, so the defect does too.
    filter_upwards
      [denseEpigraphNonnegWinnerField_zero_off_spanningSet
        (μ := μ) (φ := φ) (u := u) N k]
      with ω hω hωspan
    have hx_zero : xNk ω = 0 := by
      simpa [xNk] using hω hωspan
    simp [defect, hx_zero, hφ0]
  have hdefect_indicator :
      Set.indicator (MeasureTheory.spanningSets μ k) (fun ω ↦ ENNReal.ofReal (defect ω)) =ᵐ[μ]
        fun ω ↦ ENNReal.ofReal (defect ω) := by
    -- The nonzero part of the defect is already supported on the chosen spanning set.
    filter_upwards [hdefect_zero_off] with ω hω
    by_cases hωspan : ω ∈ MeasureTheory.spanningSets μ k
    · simp [Set.indicator_of_mem, hωspan]
    · simp [Set.indicator_of_notMem, hωspan, hω hωspan]
  have hdefect_integral :
      (((∫ ω, defect ω ∂μ : ℝ)) : EReal) =
        (((⟪xNk, u⟫_ℝ : ℝ) : EReal) - (integralFunctional μ φ xNk : EReal)) := by
    -- The global defect integral is the affine-defect term appearing in `conjugate_apply`.
    rw [integral_sub hinner_int hxNk_branch.1, MeasureTheory.L2.inner_def,
      integralFunctional_apply_eq_integral_toReal_of_mem_effectiveDomain
        (μ := μ) φ (x := xNk) hxNk_eff,
      ← EReal.coe_sub]
  have haffine_le :
      (((⟪xNk, u⟫_ℝ : ℝ) : EReal) - (integralFunctional μ φ xNk : EReal)) ≤ rhs := by
    -- The chosen normalized winner field contributes one admissible competitor to the conjugate.
    change
      (((⟪xNk, u⟫_ℝ : ℝ) : EReal) -
          Function.asEReal (integralFunctional μ φ) xNk) ≤ rhs
    dsimp [rhs]
    simpa [Function.asEReal] using
      (le_iSup
        (fun x : Ω →₂[μ] H ↦
          (((⟪x, u⟫_ℝ : ℝ) : EReal) - Function.asEReal (integralFunctional μ φ) x))
        xNk)
  calc
    ∫⁻ ω, ENNReal.ofReal (defect ω) ∂μ.restrict (MeasureTheory.spanningSets μ k)
        = ∫⁻ ω, ENNReal.ofReal (defect ω) ∂μ := by
            -- Replace the restricted `lintegral` by the full one using the support computation.
            rw [← MeasureTheory.lintegral_indicator (measurableSet_spanningSets μ k)]
            exact lintegral_congr_ae hdefect_indicator
    _ = ENNReal.ofReal (∫ ω, defect ω ∂μ) := by
          -- The global affine defect is nonnegative, so `ofReal_integral` applies.
          exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hdefect_int hdefect_nonneg).symm
    _ = ((((∫ ω, defect ω ∂μ : ℝ)) : EReal)).toENNReal := by
          exact EReal.real_coe_toENNReal (∫ ω, defect ω ∂μ)
    _ = ((((⟪xNk, u⟫_ℝ : ℝ) : EReal) - (integralFunctional μ φ xNk : EReal))).toENNReal := by
          rw [hdefect_integral]
    _ ≤ rhs.toENNReal := by
          exact EReal.toENNReal_le_toENNReal haffine_le

/-- Helper for Proposition 13.50: each normalized dense-prefix `lintegral` is bounded by the
finite conjugate value once the restricted winner-field bridge has been integrated. -/
private theorem lintegralDenseEpigraphNonnegPrefixSup_le_conjugateToENNReal
    [μ.IsComplete] [SigmaFinite μ] [Nonempty (epigraph φ.asEReal)]
    (hφ_mem : φ ∈ Γ₀(H))
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))
    (u : Ω →₂[μ] H) (N : ℕ)
    (hrhs_top : conjugate ((integralFunctional μ φ).asEReal) u ≠ ⊤) :
    let rhs : EReal := conjugate ((integralFunctional μ φ).asEReal) u
    ∫⁻ ω, (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal ∂μ ≤ rhs.toENNReal := by
  let rhs : EReal := conjugate ((integralFunctional μ φ).asEReal) u
  rw [lintegral_denseEpigraphNonnegPrefixSup_eq_iSup_restrict_spanningSets (μ := μ) (φ := φ) u N]
  refine iSup_le fun k ↦ ?_
  let xNk : Ω →₂[μ] H := denseEpigraphNonnegWinnerField (φ := φ) u N k
  have hprefix_adapter :
      ∀ᵐ ω ∂μ.restrict (MeasureTheory.spanningSets μ k),
        (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal ≤
          ENNReal.ofReal (⟪xNk ω, u ω⟫_ℝ - EReal.toReal (φ (xNk ω) : EReal)) := by
    -- This is the pointwise restricted bridge already normalized in the local winner-field API.
    simpa [xNk] using
      denseEpigraphNonnegPrefixSup_toENNReal_le_ofReal_nonnegWinnerField_defect_restrict
        (μ := μ) (φ := φ) (hφ_mem := hφ_mem) hzero_min u N k
  calc
    ∫⁻ ω, (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal ∂
        μ.restrict (MeasureTheory.spanningSets μ k)
        ≤ ∫⁻ ω, ENNReal.ofReal (⟪xNk ω, u ω⟫_ℝ - EReal.toReal (φ (xNk ω) : EReal)) ∂
            μ.restrict (MeasureTheory.spanningSets μ k) := by
              exact MeasureTheory.lintegral_mono_ae hprefix_adapter
    _ ≤ rhs.toENNReal := by
          simpa [rhs, xNk] using
            nonnegWinnerFieldRestrictLIntegral_le_conjugateToENNReal
              (μ := μ) (φ := φ) (hφ_mem := hφ_mem) hzero_min u N k hrhs_top

private theorem
    integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_complete_sigmaFinite_of_zero_minimum
    [μ.IsComplete] [SigmaFinite μ]
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))
    (u : Ω →₂[μ] H) :
    (integralFunctional μ (gammaZeroConjugate φ hφ) u : EReal) ≤
      conjugate ((integralFunctional μ φ).asEReal) u := by
  classical
  let φStar : H → Set.Ioi (⊥ : EReal) := gammaZeroConjugate φ hφ
  let rhs : EReal := conjugate ((integralFunctional μ φ).asEReal) u
  letI : Nonempty (epigraph φ.asEReal) := denseEpigraph_nonempty (φ := φ) hφ
  -- Route correction: the nonnegative winner-field API and its defect domination are already in
  -- place, so the only remaining zero-minimum work is admissibility plus the `k → ∞` and
  -- `N → ∞` limit passage.
  by_cases hrhs_top : rhs = ⊤
  · -- If the conjugate value is already `⊤`, the reverse inequality is immediate.
    change (integralFunctional μ φStar u : EReal) ≤ rhs
    rw [hrhs_top]
    exact le_top
  · have hiSup_endpoint :
      ∀ ω : Ω,
        (⨆ N, (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal) =
          ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal)).toENNReal := by
      -- The zero-minimum normalization preserves the pointwise supremum of the dense-prefix
      -- approximation sequence.
      intro ω
      simpa using
        iSup_toENNReal_denseEpigraphNonnegPrefixSup_eq_gammaZeroConjugate
          (φ := φ) (hφ := hφ) hzero_min u ω
    have hprefix_lintegral :
        ∀ N : ℕ,
          ∫⁻ ω, (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal ∂μ ≤ rhs.toENNReal := by
      -- Package the restricted `(N,k)` estimates into a full `lintegral` bound for each prefix.
      intro N
      simpa [rhs] using
        lintegralDenseEpigraphNonnegPrefixSup_le_conjugateToENNReal
          (μ := μ) (φ := φ) (hφ_mem := hφ) hzero_min u N hrhs_top
    have hprefix_mono :
        ∀ᵐ ω ∂μ,
          Monotone fun N ↦ (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal := by
      -- The normalized dense-prefix family is pointwise monotone in the prefix length.
      refine Filter.Eventually.of_forall ?_
      intro ω n m hnm
      exact EReal.toENNReal_le_toENNReal <|
        max_le_max le_rfl (denseEpigraphPrefixSup_monotone (φ := φ) u hnm ω)
    have hgamma_lintegral_le :
        ∫⁻ ω,
            ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal)).toENNReal ∂μ ≤
          rhs.toENNReal := by
      -- Pass first to the `N`-supremum and then to the pointwise conjugate endpoint.
      calc
        ∫⁻ ω,
            ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal)).toENNReal ∂μ
            = ∫⁻ ω, ⨆ N, (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal ∂μ := by
                refine lintegral_congr_ae ?_
                exact Filter.Eventually.of_forall fun ω ↦ (hiSup_endpoint ω).symm
        _ = ⨆ N, ∫⁻ ω, (denseEpigraphNonnegPrefixSup (φ := φ) u N ω).toENNReal ∂μ := by
              exact MeasureTheory.lintegral_iSup'
                (fun N ↦
                  aemeasurable_toENNReal_denseEpigraphNonnegPrefixSup
                    (μ := μ) (φ := φ) (u := u) N)
                hprefix_mono
        _ ≤ rhs.toENNReal := by
              exact iSup_le hprefix_lintegral
    have hφStar_meas : Measurable φStar := by
      -- The pointwise conjugate integrand is measurable because it still lies in `Γ₀(H)`.
      exact (gammaZeroConjugate_mem_gammaZero hφ).1.measurable.subtype_mk
    have hρ_le : ∀ ω : Ω, (((0 : ℝ) : EReal)) ≤ (φStar (u ω) : EReal) := by
      -- The zero-minimum hypothesis transfers to the pointwise conjugate integrand.
      rcases gammaZeroConjugate_has_zero_minimum (φ := φ) (hφ := hφ) hzero_min with
        ⟨hφStar0, hφStar_min⟩
      intro ω
      have hminω := hφStar_min (u ω)
      rw [hφStar0] at hminω
      simpa [φStar] using hminω
    have hshift_sm :
        AEStronglyMeasurable
          (fun ω ↦ EReal.toReal (φStar (u ω) : EReal) - (0 : ℝ)) μ := by
      -- With `ρ = 0`, the shifted real integrand is just the ordinary `toReal` branch.
      simpa using pointwise_integrand_aestronglyMeasurable φStar hφStar_meas u
    have hshift_meas :
        AEMeasurable
          (fun ω ↦ (((φStar (u ω) : EReal) + (((-(0 : ℝ) : ℝ) : EReal))).toENNReal)) μ := by
      have hφStar_ae :
          AEMeasurable (fun ω ↦ (φStar (u ω) : EReal)) μ := by
        exact measurable_subtype_coe.comp_aemeasurable <|
          hφStar_meas.comp_aemeasurable (Lp.aestronglyMeasurable u).aemeasurable
      simpa [φStar] using hφStar_ae.ereal_toENNReal
    have hu_eff : u ∈ effectiveDomain (integralFunctional μ φStar) := by
      -- The finite `lintegral` bound at `ρ = 0` forces `u` into the effective domain.
      have hzero_int : Integrable (fun _ : Ω ↦ (0 : ℝ)) μ := by
        simpa using (integrable_zero : Integrable (fun _ : Ω ↦ (0 : ℝ)) μ)
      exact mem_effectiveDomain_of_shifted_lintegral_ne_top
        (μ := μ) φStar
        hρ_le
        hzero_int
        hshift_sm
        hshift_meas
        (by
          have htop : rhs.toENNReal ≠ ⊤ := (EReal.toENNReal_ne_top_iff).2 hrhs_top
          simpa [φStar] using ne_top_of_le_ne_top htop hgamma_lintegral_le)
    have hleft_toENN :
        (integralFunctional μ φStar u : EReal).toENNReal ≤ rhs.toENNReal := by
      -- Rewrite the left side through the effective-domain `lintegral` formula.
      rw [integralFunctional_gammaZeroConjugate_toENNReal_eq_lintegral_of_mem_effectiveDomain
        (μ := μ) (φ := φ) (hφ := hφ) hzero_min hu_eff]
      exact hgamma_lintegral_le
    have hφStar_nonneg :
        0 ≤ᵐ[μ] fun ω ↦ EReal.toReal (φStar (u ω) : EReal) := by
      -- The zero-minimum hypothesis makes the pointwise conjugate integrand nonnegative.
      filter_upwards with ω
      exact EReal.toReal_nonneg (hρ_le ω)
    have hleft_nonneg : (0 : EReal) ≤ (integralFunctional μ φStar u : EReal) := by
      -- The conjugate integral functional is an integral of a pointwise nonnegative real field.
      rw [integralFunctional_apply_eq_integral_toReal_of_mem_effectiveDomain
        (μ := μ) φStar (x := u) hu_eff]
      exact_mod_cast integral_nonneg_of_ae hφStar_nonneg
    have hzero_eff : (0 : Ω →₂[μ] H) ∈ effectiveDomain (integralFunctional μ φ) := by
      -- The zero field lies in the effective domain because `φ 0 = 0` on the zero-minimum branch.
      have hzero_toReal : EReal.toReal (φ (0 : H) : EReal) = 0 := by
        simpa using congrArg EReal.toReal hzero_min.1
      have hzero_field_ae :
          (((0 : Ω →₂[μ] H) : Ω → H)) =ᵐ[μ] fun _ : Ω ↦ (0 : H) := by
        simpa using (Lp.coeFn_zero H 2 μ)
      have hbranch0 :
          Integrable (fun ω ↦ EReal.toReal (φ ((((0 : Ω →₂[μ] H) : Ω → H) ω)))) μ ∧
            ∀ᵐ ω ∂μ, (φ ((((0 : Ω →₂[μ] H) : Ω → H) ω)) : EReal) < ⊤ := by
        constructor
        · have hzero_integrand_ae :
              (fun ω ↦ EReal.toReal (φ ((((0 : Ω →₂[μ] H) : Ω → H) ω)) : EReal)) =ᵐ[μ]
                fun _ : Ω ↦ (0 : ℝ) := by
            filter_upwards [hzero_field_ae] with ω hωzero
            have hφzeroE : (φ ((((0 : Ω →₂[μ] H) : Ω → H) ω)) : EReal) = (φ (0 : H) : EReal) := by
              simpa using congrArg (fun x : H => (φ x : EReal)) hωzero
            calc
              EReal.toReal (φ ((((0 : Ω →₂[μ] H) : Ω → H) ω)) : EReal)
                  = EReal.toReal (φ (0 : H) : EReal) := by
                      simpa using congrArg EReal.toReal hφzeroE
              _ = 0 := hzero_toReal
          have hzero_int : Integrable (fun _ : Ω ↦ (0 : ℝ)) μ := by
            simpa using (integrable_zero : Integrable (fun _ : Ω ↦ (0 : ℝ)) μ)
          exact hzero_int.congr hzero_integrand_ae.symm
        · filter_upwards [hzero_field_ae] with ω hωzero
          have hφzeroE : (φ ((((0 : Ω →₂[μ] H) : Ω → H) ω)) : EReal) = (φ (0 : H) : EReal) := by
            simpa using congrArg (fun x : H => (φ x : EReal)) hωzero
          have hzero_lt_top : (φ (0 : H) : EReal) < ⊤ := by
            simpa [hzero_min.1]
          rw [hφzeroE]
          exact hzero_lt_top
      rw [mem_effectiveDomain_iff, integralFunctional_coe μ φ, pointwiseIntegralFunctional,
        if_pos hbranch0]
      exact EReal.coe_lt_top (∫ ω, EReal.toReal (φ ((((0 : Ω →₂[μ] H) : Ω → H) ω)) : EReal) ∂μ : ℝ)
    have hzero_eval : (integralFunctional μ φ (0 : Ω →₂[μ] H) : EReal) = 0 := by
      -- Evaluating the primal integral functional at the zero field gives `0`.
      rw [integralFunctional_apply_eq_integral_toReal_of_mem_effectiveDomain
        (μ := μ) φ (x := (0 : Ω →₂[μ] H)) hzero_eff]
      have hzero_toReal : EReal.toReal (φ (0 : H) : EReal) = 0 := by
        simpa using congrArg EReal.toReal hzero_min.1
      have hzero_integrand_ae :
          (fun ω ↦ EReal.toReal (φ ((((0 : Ω →₂[μ] H) : Ω → H) ω)) : EReal)) =ᵐ[μ]
            fun _ : Ω ↦ (0 : ℝ) := by
        filter_upwards [Lp.coeFn_zero H 2 μ] with ω hωzero
        have hφzeroE : (φ ((((0 : Ω →₂[μ] H) : Ω → H) ω)) : EReal) = (φ (0 : H) : EReal) := by
          simpa using congrArg (fun x : H => (φ x : EReal)) hωzero
        calc
          EReal.toReal (φ ((((0 : Ω →₂[μ] H) : Ω → H) ω)) : EReal)
              = EReal.toReal (φ (0 : H) : EReal) := by simpa using congrArg EReal.toReal hφzeroE
          _ = 0 := hzero_toReal
      rw [integral_congr_ae hzero_integrand_ae]
      simp
    have hrhs_nonneg : (0 : EReal) ≤ rhs := by
      -- Test the defining supremum of the conjugate at the zero competitor.
      dsimp [rhs]
      have hsup0 :
          (((⟪(0 : Ω →₂[μ] H), u⟫_ℝ : ℝ) : EReal) -
              Function.asEReal (integralFunctional μ φ) (0 : Ω →₂[μ] H)) ≤
            ⨆ x : Ω →₂[μ] H,
              (((⟪x, u⟫_ℝ : ℝ) : EReal) - Function.asEReal (integralFunctional μ φ) x) :=
        le_iSup
          (fun x : Ω →₂[μ] H ↦
            (((⟪x, u⟫_ℝ : ℝ) : EReal) - Function.asEReal (integralFunctional μ φ) x))
          (0 : Ω →₂[μ] H)
      have hzero_term :
          (((⟪(0 : Ω →₂[μ] H), u⟫_ℝ : ℝ) : EReal) -
              Function.asEReal (integralFunctional μ φ) (0 : Ω →₂[μ] H)) = 0 := by
        simpa [Function.asEReal, hzero_eval]
      rw [hzero_term] at hsup0
      exact hsup0
    have hleft_coe :
        (((integralFunctional μ φStar u : EReal).toENNReal : EReal)) =
          (integralFunctional μ φStar u : EReal) := by
      exact EReal.coe_toENNReal hleft_nonneg
    have hright_coe : ((rhs.toENNReal : EReal)) = rhs := by
      exact EReal.coe_toENNReal hrhs_nonneg
    -- Convert the final finite nonnegative `toENNReal` inequality back to the target `EReal` one.
    calc
      (integralFunctional μ φStar u : EReal)
          = (((integralFunctional μ φStar u : EReal).toENNReal : EReal)) := by
              exact hleft_coe.symm
      _ ≤ (rhs.toENNReal : EReal) := by
            exact_mod_cast hleft_toENN
      _ = rhs := hright_coe

/-- Helper for Proposition 13.50: the complete `σ`-finite interchange step from the source proof,
specialized to the constant integrand `ω ↦ φ`. The new winner-point and winner-field API above
reduces the remaining gap to turning their finite-prefix domination into the global `conjugate`
bound. -/
theorem integralFunctional_conjugation_interchange_complete_sigmaFinite
    [μ.IsComplete] [SigmaFinite μ]
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    (u : Ω →₂[μ] H) :
    (integralFunctional μ (gammaZeroConjugate φ hφ) u : EReal) ≤
      conjugate ((integralFunctional μ φ).asEReal) u := by
  -- Route correction: the main theorem is now an explicit dispatcher. The finite effective-domain
  -- branch is complete, while the remaining finite `⊤` case and the zero-minimum branch are
  -- isolated in the two helper lemmas immediately above.
  rcases hfinite_or_nonneg with hfinite | hzero_min
  · letI : IsFiniteMeasure μ := ⟨hfinite⟩
    by_cases hu_eff : u ∈ effectiveDomain (integralFunctional μ (gammaZeroConjugate φ hφ))
    · exact
        integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_of_finiteMeasure_of_mem_effectiveDomain
          (μ := μ) (φ := φ) (hφ := hφ) u hu_eff
    · exact
        integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_of_finiteMeasure_of_not_mem_effectiveDomain
          (μ := μ) (φ := φ) (hφ := hφ) u hu_eff
  · exact
      integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_complete_sigmaFinite_of_zero_minimum
        (μ := μ) (φ := φ) (hφ := hφ) hzero_min u

/-- Helper for Proposition 13.50: in the finite-measure branch, the source proof reduces the
reverse inequality to the local complete `σ`-finite interchange theorem. -/
theorem integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_of_finiteMeasure
    [μ.IsComplete] [SigmaFinite μ] (hfinite : μ Set.univ < ∞)
    (u : Ω →₂[μ] H) :
    (integralFunctional μ (gammaZeroConjugate φ hφ) u : EReal) ≤
      conjugate ((integralFunctional μ φ).asEReal) u := by
  haveI : IsFiniteMeasure μ := ⟨hfinite⟩
  let φStar : H → Set.Ioi (⊥ : EReal) := gammaZeroConjugate φ hφ
  by_cases hu_eff : u ∈ effectiveDomain (integralFunctional μ (gammaZeroConjugate φ hφ))
  · -- Route correction: once the conjugate integral is finite, the direct winner-point limit
    -- argument closes the finite-measure branch without the stale mixed theorem.
    exact
      integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_of_finiteMeasure_of_mem_effectiveDomain
        (μ := μ) (φ := φ) (hφ := hφ) u hu_eff
  · -- The remaining finite-measure blocker is exactly the missing `conjugate = ⊤` bridge.
    exact
      integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_of_finiteMeasure_of_not_mem_effectiveDomain
        (μ := μ) (φ := φ) (hφ := hφ) u hu_eff

/-- Helper for Proposition 13.50: in the zero-minimum branch, the same local interchange step
yields the reverse inequality for the integral functional. -/
theorem integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_of_zero_minimum
    [μ.IsComplete] [SigmaFinite μ]
    (hzero_min : (φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))
    (u : Ω →₂[μ] H) :
    (integralFunctional μ (gammaZeroConjugate φ hφ) u : EReal) ≤
      conjugate ((integralFunctional μ φ).asEReal) u := by
  -- Reuse the theorem-local zero-minimum branch helper directly.
  exact
    integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_complete_sigmaFinite_of_zero_minimum
      (μ := μ) (φ := φ) (hφ := hφ) hzero_min u

/-- Helper for Proposition 13.50: dispatch the reverse inequality to the source-faithful
finite-measure or zero-minimum interchange theorem. -/
theorem integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional
    [μ.IsComplete] [SigmaFinite μ]
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    (u : Ω →₂[μ] H) :
    (integralFunctional μ (gammaZeroConjugate φ hφ) u : EReal) ≤
      conjugate ((integralFunctional μ φ).asEReal) u := by
  -- Split only on the proposition's two source branches, then reuse the dedicated interchange API.
  rcases hfinite_or_nonneg with hfinite | hzero_min
  · exact integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_of_finiteMeasure
      (μ := μ) (φ := φ) (hφ := hφ) hfinite u
  · exact integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional_of_zero_minimum
      (μ := μ) (φ := φ) (hφ := hφ) hzero_min u

/-- Helper for Proposition 13.50: the reverse inequality is exactly the complete `σ`-finite
integral-conjugation step that still needs the measurable almost-maximizer theorem. -/
private theorem integralFunctional_gammaZeroConjugate_le_conjugate_integralFunctional
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    [μ.IsComplete] [SigmaFinite μ] (u : Ω →₂[μ] H) :
    (integralFunctional μ (gammaZeroConjugate φ hφ) u : EReal) ≤
      conjugate ((integralFunctional μ φ).asEReal) u := by
  -- Route correction: delegate the reverse inequality to the theorem-local interchange API,
  -- which splits only on the source proof's finite-measure and zero-minimum branches.
  simpa using integralFunctional_pointwiseConjugate_le_conjugate_integralFunctional
    (μ := μ) (φ := φ) (hφ := hφ) hfinite_or_nonneg u

/-- Proposition 13.50 (3): clause (ii). If `(Ω, 𝓕, μ)` is complete and `σ`-finite, then the
Fenchel conjugate of the integral functional induced by `φ` is the integral functional induced by
the Fenchel conjugate integrand `φ*`. -/
theorem conjugate_integralFunctional_eq_integralFunctional_gammaZeroConjugate
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    [μ.IsComplete] [SigmaFinite μ] :
    ((integralFunctional μ φ).asEReal)∗ =
      (integralFunctional μ (gammaZeroConjugate φ hφ)).asEReal := by
  -- Route correction: the proof now splits into the dependency-closed `≤` direction and the
  -- remaining complete `σ`-finite interchange theorem for the reverse inequality.
  funext u
  apply le_antisymm
  · -- The easy direction follows by integrating the pointwise Fenchel--Young inequality.
    exact conjugate_integralFunctional_le_integralFunctional_gammaZeroConjugate
      (μ := μ) (φ := φ) (hφ := hφ) u
  · -- The reverse direction is the isolated measurable almost-maximizer frontier.
    exact integralFunctional_gammaZeroConjugate_le_conjugate_integralFunctional
      (μ := μ) (φ := φ) (hφ := hφ) hfinite_or_nonneg u

end FenchelMoreau

end ERealFunction
