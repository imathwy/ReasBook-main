import Mathlib
import BauschkeLean.Chap04.Proposition_4_4
import BauschkeLean.Chap08.Example_8_10
import BauschkeLean.Chap09.Corollary_9_4
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap11.Proposition_11_12
import BauschkeLean.Chap11.Proposition_11_15
import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap12.Definition_12_23
import BauschkeLean.Chap12.Proposition_12_9
import BauschkeLean.Chap12.Proposition_12_27
import BauschkeLean.Chap12.Remark_12_24
import BauschkeLean.Chap12.ScaledProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Proposition_12_33

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2_real
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2_real
attribute [local instance] ERealFunction.prod_seminormedAddCommGroup_l2_real
attribute [local instance] ERealFunction.prod_normedSpace_l2_real
attribute [local instance] ERealFunction.prod_completeSpace_l2_real
attribute [local instance] ERealFunction.prod_innerProductSpace_l2_real

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12.33: a real-height epigraph point has finite base value. -/
private theorem mem_effectiveDomain_of_mem_real_epigraph_local
    {g : H → Set.Ioi (⊥ : EReal)} {x : H} {ξ : ℝ}
    (hxξ : (x, ξ) ∈ epigraph (fun y : H ↦ (g y : EReal))) :
    x ∈ effectiveDomain g := by
  -- Epigraph membership bounds `g x` by a real ordinate, hence by something strictly below `⊤`.
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (mem_epigraph_iff _ _ _ |>.mp hxξ) (EReal.coe_lt_top _)

/-- Helper for Proposition 12.33: the projection inequality on the epigraph yields an affine
minorant on the effective domain. -/
private theorem affine_minorant_on_effectiveDomain_of_projection_local
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {x p : H} {ξ π : ℝ}
    (hx : x ∈ effectiveDomain g) (hξ : ξ < (g x : EReal).toReal)
    (hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (g y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hg) (x, ξ)) :
    let u : H := ((π - ξ)⁻¹) • (x - p)
    ∀ y ∈ effectiveDomain g,
      ((⟪y - p, u⟫_ℝ + (g p : EReal).toReal : ℝ) : EReal) ≤ (g y : EReal) := by
  have hproj_data :
      max (ξ : EReal) (g p : EReal) ≤ (π : EReal) ∧
        ∀ y ∈ effectiveDomain g,
          ⟪y - p, x - p⟫_ℝ + ((g y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hg).mp
      hproj
  rcases hproj_data with ⟨hmax, hvar⟩
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (g y : EReal)) := by
    -- The projection point itself belongs to the epigraph.
    rw [hproj]
    exact projectionPoint_mem (epigraph (fun y : H ↦ (g y : EReal)))
      (isChebyshev_epigraph_of_mem_gammaZero hg) (x, ξ)
  have hp : p ∈ effectiveDomain g :=
    mem_effectiveDomain_of_mem_real_epigraph_local hp_mem_epigraph
  have hξ_le_pi : ξ ≤ π := by
    have hξ_le_pi' : (ξ : EReal) ≤ (π : EReal) := by
      exact le_trans
        (show (ξ : EReal) ≤ max (ξ : EReal) (g p : EReal) from le_max_left _ _)
        hmax
    exact_mod_cast hξ_le_pi'
  have hgp_top : (g p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hgp_bot : (g p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (g p : EReal) > ⊥ from (g p).2)
  have hgp_le_pi : (g p : EReal).toReal ≤ π := by
    have hgp_le_pi' : (g p : EReal) ≤ (π : EReal) :=
      mem_epigraph_iff _ _ _ |>.mp hp_mem_epigraph
    have hcast :
        (((g p : EReal).toReal : ℝ) : EReal) ≤ (π : EReal) := by
      simpa [EReal.coe_toReal hgp_top hgp_bot] using hgp_le_pi'
    exact_mod_cast hcast
  have hξ_lt_pi : ξ < π := by
    by_cases hπξ : π = ξ
    · have hvarx :
          ⟪x - p, x - p⟫_ℝ + ((g x : EReal).toReal - π) * (ξ - π) ≤ 0 :=
        hvar x hx
      rw [hπξ, sub_self, mul_zero, add_zero] at hvarx
      have hinner_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ := by
        exact (real_inner_self_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ)
      have hinner_eq_zero : ⟪x - p, x - p⟫_ℝ = 0 := by
        nlinarith [hinner_nonneg, hvarx]
      have hxp : x = p := by
        have hsub : x - p = 0 := by
          simpa using inner_self_eq_zero.mp hinner_eq_zero
        exact sub_eq_zero.mp hsub
      have hgp_le_xi : (g p : EReal) ≤ (ξ : EReal) := by
        have hmax_to_xi : max (ξ : EReal) (g p : EReal) ≤ (ξ : EReal) := by
          simpa [hπξ] using hmax
        exact le_trans
          (show (g p : EReal) ≤ max (ξ : EReal) (g p : EReal) from le_max_right _ _)
          hmax_to_xi
      have hgx_top : (g x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
      have hgx_bot : (g x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (g x : EReal) > ⊥ from (g x).2)
      have hgx_le_xi : (g x : EReal).toReal ≤ ξ := by
        have hgx_le_xi' : (g x : EReal) ≤ (ξ : EReal) := by
          simpa [hxp] using hgp_le_xi
        have hcast :
            (((g x : EReal).toReal : ℝ) : EReal) ≤ (ξ : EReal) := by
          simpa [EReal.coe_toReal hgx_top hgx_bot] using hgx_le_xi'
        exact_mod_cast hcast
      linarith
    · exact lt_of_le_of_ne hξ_le_pi (by
        intro hξπ
        exact hπξ hξπ.symm)
  dsimp
  intro y hy
  have hvar :
      ⟪y - p, x - p⟫_ℝ + ((g y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    hvar y hy
  have hgap_pos : 0 < π - ξ := sub_pos.mpr hξ_lt_pi
  have hinner_le :
      ⟪y - p, x - p⟫_ℝ ≤ ((g y : EReal).toReal - π) * (π - ξ) := by
    -- Move the negative factor to the right-hand side and use the positive gap `π - ξ`.
    nlinarith
  have hscaled :
      ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ ≤ (g y : EReal).toReal - π := by
    have hdiv : ⟪y - p, x - p⟫_ℝ / (π - ξ) ≤ (g y : EReal).toReal - π := by
      refine (div_le_iff₀ hgap_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hinner_le
    simpa [div_eq_mul_inv, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hreal :
      ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ + (g p : EReal).toReal ≤ (g y : EReal).toReal := by
    -- Replace the epigraph ordinate `π` by the smaller intercept `(g p).toReal`.
    linarith
  have hgy_top : (g y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hgy_bot : (g y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (g y : EReal) > ⊥ from (g y).2)
  have hcast :
      ((⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ + (g p : EReal).toReal : ℝ) : EReal) ≤
        (((g y : EReal).toReal : ℝ) : EReal) := by
    exact_mod_cast hreal
  simpa [EReal.coe_toReal hgy_top hgy_bot] using hcast

/-- Helper for Proposition 12.33: every `Γ₀(H)` function admits a continuous affine minorant. -/
private theorem exists_affine_minorant_of_mem_gammaZero_local
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ∃ p ∈ effectiveDomain f, ∃ u : H, ∀ y : H,
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (f y : EReal) := by
  rcases hf.2.nonempty with ⟨x, hx⟩
  let ξ : ℝ := (f x : EReal).toReal - 1
  have hξ : ξ < (f x : EReal).toReal := by
    -- Choose a point one unit below the finite value at `x`.
    dsimp [ξ]
    linarith
  let z : H × ℝ :=
    projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
      (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  let p : H := z.1
  let π : ℝ := z.2
  have hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) := by
    simp [p, π, z]
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    rw [hproj]
    exact projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
      (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  have hp : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_real_epigraph_local hp_mem_epigraph
  refine ⟨p, hp, ((π - ξ)⁻¹) • (x - p), ?_⟩
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · -- On the effective domain, use the normalized projection inequality.
    exact affine_minorant_on_effectiveDomain_of_projection_local (g := f) hf hx hξ hproj y hy
  · -- Outside the effective domain, `f y = ⊤`, so the minorant is automatic.
    rw [show (f y : EReal) = ⊤ by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))]
    exact le_top

/-- Helper for Proposition 12.33: the proximal value is bounded above by the matching Moreau
envelope value. -/
lemma prox_value_le_moreauEnvelope_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) (x : H) :
    f.asEReal (Prox[γ, f, hf] x) ≤ ({}^[γ] f) x := by
  let p := Prox[γ, f, hf] x
  have hquad_nonneg :
      (0 : EReal) ≤ ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
    -- The quadratic correction term in Remark 12.24 is nonnegative.
    refine EReal.coe_nonneg.mpr ?_
    refine div_nonneg (sq_nonneg ‖x - p‖) ?_
    nlinarith [γ.2]
  have hmoreau :
      ({}^[γ] f) x =
        (f p : EReal) +
          ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
    -- Rewrite the Moreau envelope through the proximal-point identity.
    simpa [p] using
      moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
        (f := f) (hf := hf) (γ := γ) x
  -- Drop the nonnegative quadratic term.
  calc
    f.asEReal (Prox[γ, f, hf] x) = (f p : EReal) := by simp [Function.asEReal, p]
    _ ≤ (f p : EReal) + ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
      simpa using
        (le_add_of_nonneg_right hquad_nonneg :
          (f p : EReal) ≤
            (f p : EReal) +
              ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)))
    _ = ({}^[γ] f) x := hmoreau.symm

omit [CompleteSpace H] in
/-- Proposition 12.33 (1): for `f ∈ Γ₀(H)` and `x ∈ H`, the Moreau-envelope net
`γ ↦ ({}^[γ] f) x` is decreasing on `ℝ_{++}`. -/
theorem antitone_moreauEnvelope_along_parameter
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    Antitone (fun γ : PosReal ↦ ({}^[γ] f) x) := by
  -- Rewrite Proposition 12.9(iv) at the quadratic exponent `p = 2`.
  simpa [normPowerEnvelope_two_eq_moreauEnvelope] using
    (tendsto_normPowerEnvelope_atTop
      (f := f) (hdom := hf.2.nonempty) (p := ⟨(2 : ℝ), two_mem_Ici_one⟩) (x := x)).1

/-- Proposition 12.33 (2): for `f ∈ Γ₀(H)` and `x ∈ H`, the proximal-value net
`γ ↦ f (Prox_{γ f} x)` is decreasing on `ℝ_{++}`. -/
theorem antitone_scaledProxValue_along_parameter_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    Antitone (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x)) := by
  intro γ μ hγμ
  let pγ := Prox[γ, f, hf] x
  let pμ := Prox[μ, f, hf] x
  have hmono_real :=
    antitone_proxValue_along_parameter_of_mem_gammaZero (f := f) (hf := hf) (x := x) hγμ
  have hpγ_dom : pγ ∈ effectiveDomain f := by
    simpa [pγ] using
      scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero
        (f := f) (hf := hf) (x := x) (γ := γ)
  have hpμ_dom : pμ ∈ effectiveDomain f := by
    simpa [pμ] using
      scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero
        (f := f) (hf := hf) (x := x) (γ := μ)
  have hpγ_top : (f pγ : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hpγ_dom)
  have hpγ_bot : (f pγ : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f pγ : EReal) from (f pγ).2)
  have hpμ_top : (f pμ : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hpμ_dom)
  have hpμ_bot : (f pμ : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f pμ : EReal) from (f pμ).2)
  have hmono_ereal :
      ((((f pμ : EReal).toReal : ℝ) : EReal)) ≤
        ((((f pγ : EReal).toReal : ℝ) : EReal)) := by
    exact_mod_cast hmono_real
  -- Convert the real-valued monotonicity from Proposition 12.27 back to `EReal`.
  simpa [Function.asEReal, pγ, pμ, EReal.coe_toReal hpμ_top hpμ_bot,
    EReal.coe_toReal hpγ_top hpγ_bot] using hmono_ereal

omit [CompleteSpace H] in
/-- Proposition 12.33 (3): clause (i), the Moreau-envelope values `({}^[γ] f) x` converge
downward to `inf f(H)` as `γ → +∞`. -/
theorem tendsto_moreauEnvelope_atTop_inf
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    Filter.Tendsto
      (fun γ : PosReal ↦ ({}^[γ] f) x)
      Filter.atTop
      (nhds (sInf (Set.range f.asEReal))) := by
  -- Proposition 12.9(iv) gives the at-top limit after the `p = 2` identification.
  simpa [normPowerEnvelope_two_eq_moreauEnvelope] using
    (tendsto_normPowerEnvelope_atTop
      (f := f) (hdom := hf.2.nonempty) (p := ⟨(2 : ℝ), two_mem_Ici_one⟩) (x := x)).2

/-- Proposition 12.33 (4): clause (i), the proximal values `f (Prox_{γ f} x)` converge downward
to `inf f(H)` as `γ → +∞`. -/
theorem tendsto_scaledProxValue_atTop_inf_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    Filter.Tendsto
      (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x))
      Filter.atTop
      (nhds (sInf (Set.range f.asEReal))) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    -- Every proximal value stays above the global infimum of `f`.
    exact Filter.Eventually.of_forall fun γ ↦
      lt_of_lt_of_le ha (sInf_le ⟨Prox[γ, f, hf] x, rfl⟩)
  · intro ξ hξ
    -- The Moreau envelope has the desired at-top limit, and proximal values lie below it.
    have hmoreau_eventually :
        ∀ᶠ γ : PosReal in Filter.atTop, ({}^[γ] f) x < ξ := by
      exact (tendsto_moreauEnvelope_atTop_inf (f := f) (hf := hf) (x := x)).eventually
        (Iio_mem_nhds hξ)
    filter_upwards [hmoreau_eventually] with γ hγ
    exact lt_of_le_of_lt
      (prox_value_le_moreauEnvelope_of_mem_gammaZero (f := f) (hf := hf) (γ := γ) (x := x))
      hγ

omit [CompleteSpace H] in
/-- Helper for Proposition 12.33: evaluating the Moreau envelope at the base point bounds it by
`f x`. -/
lemma moreauEnvelope_le_self_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) (x : H) :
    ({}^[γ] f) x ≤ f.asEReal x := by
  have _ : Set.Nonempty (effectiveDomain f) := hf.2.nonempty
  -- Evaluating the defining infimum at `y = x` kills the quadratic penalty.
  calc
    ({}^[γ] f) x = normPowerEnvelope f ⟨(2 : ℝ), two_mem_Ici_one⟩ γ x := by
      simp [normPowerEnvelope_two_eq_moreauEnvelope]
    _ ≤ (f x : EReal) + ((((‖x - x‖ ^ (2 : ℝ)) / ((γ : ℝ) * (2 : ℝ)) : ℝ) : EReal)) := by
      exact normPowerEnvelope_le_test_point f ⟨(2 : ℝ), two_mem_Ici_one⟩ γ x x
    _ = f.asEReal x := by
      rw [normPowerEnvelope_self_penalty_eq_zero ⟨(2 : ℝ), two_mem_Ici_one⟩ γ x, add_zero]

/-- Helper for Proposition 12.33: the translated proximal objective is coercive. -/
lemma proximalObjective_coercive_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    Coercive (proximalObjective f x) := by
  -- The source proof bounds `f` from below by an affine minorant and lets the quadratic term
  -- dominate that affine tail on cobounded sets.
  rw [Coercive, EReal.tendsto_nhds_top_iff_real]
  rcases exists_affine_minorant_of_mem_gammaZero_local (hf := hf) with ⟨p, hp, u, hminorant⟩
  intro ξ
  let K : ℝ := ‖u‖ * ‖p‖ - (f p : EReal).toReal
  let R : ℝ := max (2 * ‖x‖) (max (16 * ‖u‖) (max (16 : ℝ) (|ξ| + |K| + 1)))
  have hR : ∀ᶠ y : H in Bornology.cobounded H, R ≤ ‖y‖ := by
    simpa [R] using
      (eventually_cobounded_le_norm R : ∀ᶠ y : H in Bornology.cobounded H, R ≤ ‖y‖)
  filter_upwards [hR] with y hyR
  have hyx : 2 * ‖x‖ ≤ ‖y‖ := le_trans (le_max_left _ _) hyR
  have hyu : 16 * ‖u‖ ≤ ‖y‖ := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hyR)
  have hybig : max (16 : ℝ) (|ξ| + |K| + 1) ≤ ‖y‖ := by
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hyR)
  have hyconst : |ξ| + |K| + 1 ≤ ‖y‖ := le_trans (le_max_right _ _) hybig
  have hy_le : ‖y‖ ≤ ‖x - y‖ + ‖x‖ := by
    calc
      ‖y‖ = ‖(y - x) + x‖ := by congr 1; abel_nf
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ = ‖x - y‖ + ‖x‖ := by rw [norm_sub_rev]
  have hxy : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by
    linarith
  have hquad : ‖y‖ ^ 2 / 8 ≤ (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
    have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
    nlinarith
  have hinner_abs : |⟪y - p, u⟫_ℝ| ≤ ‖y - p‖ * ‖u‖ := by
    simpa [mul_comm] using abs_real_inner_le_norm (y - p) u
  have hdist : ‖y - p‖ ≤ ‖y‖ + ‖p‖ := by
    simpa [sub_eq_add_neg, add_comm] using norm_sub_le y p
  have hinner :
      -‖u‖ * ‖y‖ - ‖u‖ * ‖p‖ ≤ ⟪y - p, u⟫_ℝ := by
    have hneg : -|⟪y - p, u⟫_ℝ| ≤ ⟪y - p, u⟫_ℝ := neg_abs_le _
    have hbound : |⟪y - p, u⟫_ℝ| ≤ ‖u‖ * ‖y‖ + ‖u‖ * ‖p‖ := by
      have hmul :
          ‖y - p‖ * ‖u‖ ≤ (‖y‖ + ‖p‖) * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right hdist (norm_nonneg _)
      have htmp : |⟪y - p, u⟫_ℝ| ≤ (‖y‖ + ‖p‖) * ‖u‖ := le_trans hinner_abs hmul
      nlinarith
    nlinarith
  have hlinear : ‖u‖ * ‖y‖ ≤ ‖y‖ ^ 2 / 16 := by
    have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
    nlinarith
  have hquadratic : |ξ| + |K| + 1 ≤ ‖y‖ ^ 2 / 16 := by
    have hstep : ‖y‖ ≤ ‖y‖ ^ 2 / 16 := by
      have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
      have hy16 : (16 : ℝ) ≤ ‖y‖ := le_trans (le_max_left _ _) hybig
      nlinarith
    exact le_trans hyconst hstep
  have hquadratic' : ξ + K + 1 ≤ ‖y‖ ^ 2 / 16 := by
    have habs : ξ + K + 1 ≤ |ξ| + |K| + 1 := by
      nlinarith [le_abs_self ξ, le_abs_self K]
    exact le_trans habs hquadratic
  have hreal :
      ξ < ⟪y - p, u⟫_ℝ + (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
    dsimp [K] at hquadratic'
    linarith
  have hlower :
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) ≤
        proximalObjective f x y := by
    -- Add the quadratic term to the affine minorant of `f`.
    have hsum :=
      add_le_add_left (hminorant y) ((((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal))
    calc
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) =
          ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) +
            (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
              rw [EReal.coe_add]
      _ ≤ (f y : EReal) + (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := hsum
      _ = proximalObjective f x y := by simp [proximalObjective]
  have hreal_cast :
      (ξ : EReal) <
        ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    exact_mod_cast hreal
  exact lt_of_lt_of_le hreal_cast hlower

/-- Helper for Proposition 12.33: for `γ < 1`, the scaled proximal point lies in the fixed lower
level set of the translated proximal objective. -/
lemma proximalObjective_scaledProx_le_moreauEnvelope_of_lt_one
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (γ : PosReal)
    (hγ : (γ : ℝ) < 1) :
    proximalObjective f x (Prox[γ, f, hf] x) ≤ ({}^[γ] f) x := by
  let p := Prox[γ, f, hf] x
  have hmoreau :
      ({}^[γ] f) x =
        (f p : EReal) +
          ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
    -- Rewrite Remark 12.24 at the chosen proximal point.
    simpa [p] using
      moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
        (f := f) (hf := hf) (γ := γ) x
  have hquad :
      ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) ≤
        ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
    have htwoγ_pos : 0 < 2 * (γ : ℝ) := by
      nlinarith [γ.2]
    have hreal : (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤ ‖x - p‖ ^ 2 / (2 * (γ : ℝ)) := by
      refine (le_div_iff₀ htwoγ_pos).2 ?_
      nlinarith [sq_nonneg ‖x - p‖, hγ]
    exact_mod_cast hreal
  calc
    proximalObjective f x (Prox[γ, f, hf] x) =
        (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := by
          simp [proximalObjective, p]
    _ ≤ (f p : EReal) + ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
      simpa [add_comm] using add_le_add_right hquad (f p : EReal)
    _ = ({}^[γ] f) x := hmoreau.symm

/-- Helper for Proposition 12.33: a real upper bound on the small-parameter Moreau envelope values
forces a uniform norm bound on the corresponding proximal points. -/
lemma exists_norm_bound_scaledProx_of_small_moreau_upper_bound
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (M : ℝ)
    (hM : ∀ γ : PosReal, (γ : ℝ) < 1 → ({}^[γ] f) x ≤ (M : EReal)) :
    ∃ ν : ℝ, 0 ≤ ν ∧ ∀ γ : PosReal, (γ : ℝ) < 1 → ‖Prox[γ, f, hf] x‖ ≤ ν := by
  have hbounded :
      Bornology.IsBounded (lowerLevelSet (proximalObjective f x) M) := by
    exact (coercive_iff_bounded_lowerLevelSet (proximalObjective f x)).1
      (proximalObjective_coercive_of_mem_gammaZero (f := f) (hf := hf) (x := x)) M
  rcases hbounded.subset_closedBall (0 : H) with ⟨ν, hν⟩
  let γ₀ : PosReal := ⟨(1 / 2 : ℝ), by norm_num⟩
  have hγ₀ : (γ₀ : ℝ) < 1 := by
    norm_num [γ₀]
  have hp₀ :
      Prox[γ₀, f, hf] x ∈ lowerLevelSet (proximalObjective f x) M := by
    -- The source upper bound places one proximal point in the fixed lower level set.
    rw [mem_lowerLevelSet_iff]
    exact le_trans
      (proximalObjective_scaledProx_le_moreauEnvelope_of_lt_one
        (f := f) (hf := hf) (x := x) (γ := γ₀) hγ₀)
      (hM γ₀ hγ₀)
  refine ⟨ν, ?_, ?_⟩
  · have hball : Prox[γ₀, f, hf] x ∈ Metric.closedBall (0 : H) ν := hν hp₀
    exact le_trans (norm_nonneg _) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hball)
  · intro γ hγ
    have hpγ :
        Prox[γ, f, hf] x ∈ lowerLevelSet (proximalObjective f x) M := by
      -- Every small-parameter proximal point lands in the same bounded lower level set.
      rw [mem_lowerLevelSet_iff]
      exact le_trans
        (proximalObjective_scaledProx_le_moreauEnvelope_of_lt_one
          (f := f) (hf := hf) (x := x) (γ := γ) hγ)
        (hM γ hγ)
    have hball : Prox[γ, f, hf] x ∈ Metric.closedBall (0 : H) ν := hν hpγ
    simpa [Metric.mem_closedBall, dist_eq_norm] using hball

/-- Helper for Proposition 12.33: a real upper bound on the small-parameter Moreau envelope values
forces the squared residual `‖x - Prox_{γ f} x‖²` to vanish as `γ ↓ 0`. -/
lemma tendsto_sqDist_scaledProx_atZeroRight_of_small_moreau_upper_bound
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (M : ℝ)
    (hM : ∀ γ : PosReal, (γ : ℝ) < 1 → ({}^[γ] f) x ≤ (M : EReal)) :
    Filter.Tendsto
      (fun γ : PosReal ↦ ‖x - Prox[γ, f, hf] x‖ ^ 2)
      (Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
      (nhds (0 : ℝ)) := by
  let F := Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
  rcases exists_norm_bound_scaledProx_of_small_moreau_upper_bound
      (f := f) (hf := hf) (x := x) (M := M) hM with ⟨ν, _, hν⟩
  rcases exists_affine_minorant_of_mem_gammaZero_local (hf := hf) with ⟨p, hp, u, hminorant⟩
  let C₀ : ℝ := M + ‖u‖ * (ν + ‖p‖) - (f p : EReal).toReal
  let C : ℝ := max 0 C₀
  have hbound :
      ∀ γ : PosReal, (γ : ℝ) < 1 →
        ‖x - Prox[γ, f, hf] x‖ ^ 2 ≤ 2 * (γ : ℝ) * C := by
    intro γ hγ
    let q := Prox[γ, f, hf] x
    have hq_dom : q ∈ effectiveDomain f := by
      simpa [q] using
        scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero
          (f := f) (hf := hf) (x := x) (γ := γ)
    have hq_top : (f q : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hq_dom)
    have hq_bot : (f q : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f q : EReal) from (f q).2)
    have hmoreau :
        ({}^[γ] f) x =
          (f q : EReal) +
            ((((‖x - q‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
      -- Rewrite the Moreau value at the proximal point attached to `γ`.
      simpa [q] using
        moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
          (f := f) (hf := hf) (γ := γ) x
    have hsum :
        (f q : EReal) + ((((‖x - q‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) ≤ (M : EReal) := by
      calc
        (f q : EReal) + ((((‖x - q‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) =
            ({}^[γ] f) x := hmoreau.symm
        _ ≤ (M : EReal) := hM γ hγ
    have hsum_bot :
        (f q : EReal) + ((((‖x - q‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) ≠ ⊥ := by
      exact (EReal.add_ne_bot_iff.2 ⟨hq_bot, EReal.coe_ne_bot _⟩)
    have hsum_real :
        (f q : EReal).toReal + ‖x - q‖ ^ 2 / (2 * (γ : ℝ)) ≤ M := by
      have hsum_toReal :
          ((f q : EReal) + ((((‖x - q‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal))).toReal =
            (f q : EReal).toReal + ‖x - q‖ ^ 2 / (2 * (γ : ℝ)) := by
        rw [EReal.toReal_add hq_top hq_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
        simp
      calc
        (f q : EReal).toReal + ‖x - q‖ ^ 2 / (2 * (γ : ℝ)) =
            ((f q : EReal) + ((((‖x - q‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal))).toReal := by
              symm
              exact hsum_toReal
        _ ≤ (M : EReal).toReal := EReal.toReal_le_toReal hsum hsum_bot (EReal.coe_ne_top _)
        _ = M := by simp
    have hq_norm : ‖q‖ ≤ ν := hν γ hγ
    have hinner_abs : |⟪q - p, u⟫_ℝ| ≤ ‖q - p‖ * ‖u‖ := by
      simpa [mul_comm] using abs_real_inner_le_norm (q - p) u
    have hdist : ‖q - p‖ ≤ ν + ‖p‖ := by
      refine le_trans ?_ (add_le_add hq_norm le_rfl)
      simpa [sub_eq_add_neg, add_comm] using norm_sub_le q p
    have hinner :
        -(ν + ‖p‖) * ‖u‖ ≤ ⟪q - p, u⟫_ℝ := by
      have hneg : -|⟪q - p, u⟫_ℝ| ≤ ⟪q - p, u⟫_ℝ := neg_abs_le _
      have hbound :
          |⟪q - p, u⟫_ℝ| ≤ (ν + ‖p‖) * ‖u‖ := by
        exact le_trans hinner_abs (mul_le_mul_of_nonneg_right hdist (norm_nonneg _))
      nlinarith
    have hminorant_real :
        ⟪q - p, u⟫_ℝ + (f p : EReal).toReal ≤ (f q : EReal).toReal := by
      have hcast :
          ((⟪q - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤
            (((f q : EReal).toReal : ℝ) : EReal) := by
        simpa [EReal.coe_toReal hq_top hq_bot] using hminorant q
      exact_mod_cast hcast
    have hq_lower :
        -(ν + ‖p‖) * ‖u‖ + (f p : EReal).toReal ≤ (f q : EReal).toReal := by
      linarith
    have hdiv_le : ‖x - q‖ ^ 2 / (2 * (γ : ℝ)) ≤ C₀ := by
      dsimp [C₀]
      linarith
    have htwoγ_pos : 0 < 2 * (γ : ℝ) := by
      nlinarith [γ.2]
    have hmul : ‖x - q‖ ^ 2 ≤ C₀ * (2 * (γ : ℝ)) := by
      exact (div_le_iff₀ htwoγ_pos).1 hdiv_le
    have hC₀_le_C : C₀ ≤ C := le_max_right _ _
    calc
      ‖x - Prox[γ, f, hf] x‖ ^ 2 = ‖x - q‖ ^ 2 := by simp [q]
      _ ≤ C₀ * (2 * (γ : ℝ)) := hmul
      _ ≤ C * (2 * (γ : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hC₀_le_C htwoγ_pos.le
      _ = 2 * (γ : ℝ) * C := by ring
  have hsmall :
      ∀ᶠ γ : PosReal in F, (γ : ℝ) < 1 := by
    exact (Filter.tendsto_comap :
      Filter.Tendsto ((↑) : PosReal → ℝ) F (nhdsWithin (0 : ℝ) (Set.Ioi 0))).eventually
        (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one))
  have hupper :
      ∀ᶠ γ : PosReal in F, ‖x - Prox[γ, f, hf] x‖ ^ 2 ≤ 2 * (γ : ℝ) * C := by
    exact hsmall.mono fun γ hγ ↦ hbound γ hγ
  have hupper_tendsto :
      Filter.Tendsto (fun γ : PosReal ↦ 2 * (γ : ℝ) * C) F (nhds (0 : ℝ)) := by
    have hγ_tendsto :
        Filter.Tendsto (fun γ : PosReal ↦ (γ : ℝ)) F (nhds (0 : ℝ)) :=
      (Filter.tendsto_comap :
        Filter.Tendsto ((↑) : PosReal → ℝ) F (nhdsWithin (0 : ℝ) (Set.Ioi 0))).mono_right
          nhdsWithin_le_nhds
    simpa [mul_assoc, mul_comm, mul_left_comm] using hγ_tendsto.const_mul (2 * C)
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun γ ↦ sq_nonneg ‖x - Prox[γ, f, hf] x‖)
    hupper
    hupper_tendsto

/-- Helper for Proposition 12.33: when `x ∈ dom f`, the residual energy admits a real-valued
identity as twice the Moreau/proximal-value gap. -/
lemma inv_mul_sqDist_eq_two_mul_moreauEnvelope_sub_proxValue_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (hx : x ∈ effectiveDomain f)
    (γ : PosReal) :
    (γ : ℝ)⁻¹ * ‖x - Prox[γ, f, hf] x‖ ^ 2 =
      2 * ((({}^[γ] f) x).toReal - (f.asEReal (Prox[γ, f, hf] x)).toReal) := by
  have _ : x ∈ effectiveDomain f := hx
  let p := Prox[γ, f, hf] x
  have hp_dom : p ∈ effectiveDomain f := by
    simpa [p] using
      scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero
        (f := f) (hf := hf) (x := x) (γ := γ)
  have hp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
  have hp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hmoreau :
      ({}^[γ] f) x =
        (f p : EReal) +
          ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
    -- Rewrite the Moreau/proximal-value gap via Remark 12.24.
    simpa [p] using
      moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
        (f := f) (hf := hf) (γ := γ) x
  have hmoreau_toReal :
      (({}^[γ] f) x).toReal =
        (f p : EReal).toReal + ‖x - p‖ ^ 2 / (2 * (γ : ℝ)) := by
    rw [hmoreau, EReal.toReal_add hp_top hp_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
  have hgap :
      (({}^[γ] f) x).toReal - (f.asEReal p).toReal = ‖x - p‖ ^ 2 / (2 * (γ : ℝ)) := by
    -- Once both values are finite, the gap is exactly the quadratic term.
    rw [hmoreau_toReal]
    simp [Function.asEReal]
  calc
    (γ : ℝ)⁻¹ * ‖x - Prox[γ, f, hf] x‖ ^ 2 = (γ : ℝ)⁻¹ * ‖x - p‖ ^ 2 := by simp [p]
    _ = 2 * (‖x - p‖ ^ 2 / (2 * (γ : ℝ))) := by
      field_simp [hγ_ne]
    _ = 2 * ((({}^[γ] f) x).toReal - (f.asEReal p).toReal) := by rw [hgap]
    _ = 2 * ((({}^[γ] f) x).toReal - (f.asEReal (Prox[γ, f, hf] x)).toReal) := by simp [p]

/-- Proposition 12.33 (5): clause (ii), the Moreau-envelope values `({}^[γ] f) x` converge upward
to `f(x)` as `γ ↓ 0` through `ℝ_{++}`. -/
theorem tendsto_moreauEnvelope_atZeroRight_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    Filter.Tendsto
      (fun γ : PosReal ↦ ({}^[γ] f) x)
      (Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
      (nhds (f.asEReal x)) := by
  let F := Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
  by_cases hx : x ∈ effectiveDomain f
  · have hfx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hfx_bot : f.asEReal x ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < f.asEReal x from (f x).2)
    let M : ℝ := (f.asEReal x).toReal
    have hM :
        ∀ γ : PosReal, (γ : ℝ) < 1 → ({}^[γ] f) x ≤ (M : EReal) := by
      intro γ hγ
      -- The source proof starts from the uniform bound `{}^γ f(x) ≤ f(x)` on the small tail.
      simpa [M, EReal.coe_toReal hfx_top hfx_bot] using
        moreauEnvelope_le_self_of_mem_gammaZero (f := f) (hf := hf) (γ := γ) (x := x)
    have hsq :
        Filter.Tendsto
          (fun γ : PosReal ↦ ‖x - Prox[γ, f, hf] x‖ ^ 2)
          F
          (nhds (0 : ℝ)) :=
      tendsto_sqDist_scaledProx_atZeroRight_of_small_moreau_upper_bound
        (f := f) (hf := hf) (x := x) M hM
    have hprox :
        Filter.Tendsto (fun γ : PosReal ↦ Prox[γ, f, hf] x) F (nhds x) := by
      -- The residual estimate upgrades to strong convergence of the proximal points.
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hsq_eventually : ∀ᶠ γ : PosReal in F, dist (‖x - Prox[γ, f, hf] x‖ ^ 2) 0 < ε ^ 2 := by
        exact (Metric.tendsto_nhds.1 hsq) (ε ^ 2) (sq_pos_of_pos hε)
      filter_upwards [hsq_eventually] with γ hγ
      have hsquare_lt : ‖x - Prox[γ, f, hf] x‖ ^ 2 < ε ^ 2 := by
        simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg ‖x - Prox[γ, f, hf] x‖)] using hγ
      have hnorm_lt : ‖x - Prox[γ, f, hf] x‖ < ε := by
        exact (sq_lt_sq₀ (norm_nonneg _) hε.le).1 hsquare_lt
      simpa [dist_eq_norm, norm_sub_rev] using hnorm_lt
    have hvalue_liminf :
        f.asEReal x ≤ Filter.liminf (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x)) F := by
      calc
        f.asEReal x ≤ Filter.liminf (fun z : H ↦ f.asEReal z) (nhds x) :=
          LowerSemicontinuousAt.le_liminf (hf.1.lowerSemicontinuousAt x)
        _ ≤ Filter.liminf (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x)) F :=
          Filter.liminf_le_liminf_of_le hprox
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      -- Route correction: use the source lower-semicontinuity route through proximal values,
      -- then compare them upward to the Moreau envelope.
      have hprox_eventually :
          ∀ᶠ γ : PosReal in F, a < f.asEReal (Prox[γ, f, hf] x) := by
        exact Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le ha hvalue_liminf)
      filter_upwards [hprox_eventually] with γ hγ
      exact lt_of_lt_of_le hγ
        (prox_value_le_moreauEnvelope_of_mem_gammaZero (f := f) (hf := hf) (γ := γ) (x := x))
    · intro ξ hξ
      -- The pointwise envelope bound gives the upper half of order convergence immediately.
      refine Filter.Eventually.of_forall ?_
      intro γ
      exact lt_of_le_of_lt
        (moreauEnvelope_le_self_of_mem_gammaZero (f := f) (hf := hf) (γ := γ) (x := x))
        hξ
  · have hfx_top : f.asEReal x = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    rw [hfx_top, EReal.tendsto_nhds_top_iff_real]
    intro ξ
    have hexists : ∃ γ₀ : PosReal, (ξ : EReal) < ({}^[γ₀] f) x := by
      by_contra hno
      push Not at hno
      have hsq :
          Filter.Tendsto
            (fun γ : PosReal ↦ ‖x - Prox[γ, f, hf] x‖ ^ 2)
            F
            (nhds (0 : ℝ)) :=
        tendsto_sqDist_scaledProx_atZeroRight_of_small_moreau_upper_bound
          (f := f) (hf := hf) (x := x) ξ (fun γ _ ↦ hno γ)
      have hprox :
          Filter.Tendsto (fun γ : PosReal ↦ Prox[γ, f, hf] x) F (nhds x) := by
        -- A finite global upper bound would force the proximal points back to `x`.
        rw [Metric.tendsto_nhds]
        intro ε hε
        have hsq_eventually :
            ∀ᶠ γ : PosReal in F, dist (‖x - Prox[γ, f, hf] x‖ ^ 2) 0 < ε ^ 2 := by
          exact (Metric.tendsto_nhds.1 hsq) (ε ^ 2) (sq_pos_of_pos hε)
        filter_upwards [hsq_eventually] with γ hγ
        have hsquare_lt : ‖x - Prox[γ, f, hf] x‖ ^ 2 < ε ^ 2 := by
          simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg ‖x - Prox[γ, f, hf] x‖)] using hγ
        have hnorm_lt : ‖x - Prox[γ, f, hf] x‖ < ε := by
          exact (sq_lt_sq₀ (norm_nonneg _) hε.le).1 hsquare_lt
        simpa [dist_eq_norm, norm_sub_rev] using hnorm_lt
      have hvalue_liminf :
          f.asEReal x ≤ Filter.liminf (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x)) F := by
        calc
          f.asEReal x ≤ Filter.liminf (fun z : H ↦ f.asEReal z) (nhds x) :=
            LowerSemicontinuousAt.le_liminf (hf.1.lowerSemicontinuousAt x)
          _ ≤ Filter.liminf (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x)) F :=
            Filter.liminf_le_liminf_of_le hprox
      have hF_neBot : F.NeBot := by
        have hnhds_neBot : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
          exact mem_closure_iff_nhdsWithin_neBot.mp <|
            by simp [closure_Ioi]
        dsimp [F]
        rw [Filter.comap_neBot_iff_frequently]
        exact @Filter.Eventually.frequently _ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) hnhds_neBot _
          (by
            filter_upwards [self_mem_nhdsWithin] with y hy
            exact ⟨⟨y, hy⟩, rfl⟩)
      have hprox_upper :
          ∀ᶠ γ : PosReal in F, f.asEReal (Prox[γ, f, hf] x) ≤ (ξ : EReal) := by
        exact Filter.Eventually.of_forall fun γ ↦
          le_trans
            (prox_value_le_moreauEnvelope_of_mem_gammaZero (f := f) (hf := hf) (γ := γ) (x := x))
            (hno γ)
      have hliminf_le :
          Filter.liminf (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x)) F ≤ (ξ : EReal) := by
        exact Filter.liminf_le_of_frequently_le'
          (@Filter.Eventually.frequently _ F hF_neBot _ hprox_upper)
      have : f.asEReal x ≤ (ξ : EReal) := le_trans hvalue_liminf hliminf_le
      have : (⊤ : EReal) ≤ (ξ : EReal) := by
        exact hfx_top ▸ this
      simp at this
    rcases hexists with ⟨γ₀, hγ₀⟩
    have hsmall :
        ∀ᶠ γ : PosReal in F, (γ : ℝ) < (γ₀ : ℝ) := by
      exact (Filter.tendsto_comap :
        Filter.Tendsto ((↑) : PosReal → ℝ) F (nhdsWithin (0 : ℝ) (Set.Ioi 0))).eventually
          (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds γ₀.2))
    filter_upwards [hsmall] with γ hγ
    have hmon :
        ({}^[γ₀] f) x ≤ ({}^[γ] f) x :=
      antitone_moreauEnvelope_along_parameter (f := f) (hf := hf) (x := x) (le_of_lt hγ)
    exact lt_of_lt_of_le hγ₀ hmon

/-- Proposition 12.33 (6): clause (iii), if `x ∈ dom f`, then the proximal values
`f (Prox_{γ f} x)` converge upward to `f(x)` as `γ ↓ 0` through `ℝ_{++}`. -/
theorem tendsto_scaledProxValue_atZeroRight_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (hx : x ∈ effectiveDomain f) :
    Filter.Tendsto
      (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x))
      (Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
      (nhds (f.asEReal x)) := by
  let F := Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
  let M : ℝ := (f.asEReal x).toReal
  have hfx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfx_bot : f.asEReal x ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < f.asEReal x from (f x).2)
  have hM :
      ∀ γ : PosReal, (γ : ℝ) < 1 → ({}^[γ] f) x ≤ (M : EReal) := by
    intro γ hγ
    -- The source proof's boundedness branch is triggered by the pointwise bound `{}^γ f(x) ≤ f(x)`.
    simpa [M, EReal.coe_toReal hfx_top hfx_bot] using
      moreauEnvelope_le_self_of_mem_gammaZero (f := f) (hf := hf) (γ := γ) (x := x)
  have hsq :
      Filter.Tendsto
        (fun γ : PosReal ↦ ‖x - Prox[γ, f, hf] x‖ ^ 2)
        F
        (nhds (0 : ℝ)) :=
    tendsto_sqDist_scaledProx_atZeroRight_of_small_moreau_upper_bound
      (f := f) (hf := hf) (x := x) M hM
  have hprox :
      Filter.Tendsto (fun γ : PosReal ↦ Prox[γ, f, hf] x) F (nhds x) := by
    -- Once the squared residual tends to `0`, the proximal points converge strongly to `x`.
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hsq_eventually : ∀ᶠ γ : PosReal in F, dist (‖x - Prox[γ, f, hf] x‖ ^ 2) 0 < ε ^ 2 := by
      exact (Metric.tendsto_nhds.1 hsq) (ε ^ 2) (sq_pos_of_pos hε)
    filter_upwards [hsq_eventually] with γ hγ
    have hsquare_lt : ‖x - Prox[γ, f, hf] x‖ ^ 2 < ε ^ 2 := by
      simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg ‖x - Prox[γ, f, hf] x‖)] using hγ
    have hnorm_lt : ‖x - Prox[γ, f, hf] x‖ < ε := by
      exact (sq_lt_sq₀ (norm_nonneg _) hε.le).1 hsquare_lt
    simpa [dist_eq_norm, norm_sub_rev] using hnorm_lt
  have hvalue_liminf :
      f.asEReal x ≤ Filter.liminf (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x)) F := by
    calc
      f.asEReal x ≤ Filter.liminf (fun z : H ↦ f.asEReal z) (nhds x) :=
        LowerSemicontinuousAt.le_liminf (hf.1.lowerSemicontinuousAt x)
      _ ≤ Filter.liminf (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x)) F :=
        Filter.liminf_le_liminf_of_le hprox
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    -- Lower semicontinuity at `x` upgrades the strong convergence of proximal points to a liminf
    -- lower bound for the proximal values.
    exact Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le ha hvalue_liminf)
  · intro ξ hξ
    -- The proximal values never exceed `f x`, so any strict upper neighborhood of `f x` is
    -- eventually satisfied.
    refine Filter.Eventually.of_forall ?_
    intro γ
    exact lt_of_le_of_lt
      (le_trans
        (prox_value_le_moreauEnvelope_of_mem_gammaZero (f := f) (hf := hf) (γ := γ) (x := x))
        (moreauEnvelope_le_self_of_mem_gammaZero (f := f) (hf := hf) (γ := γ) (x := x)))
      hξ

/-- Proposition 12.33 (7): clause (iii), if `x ∈ dom f`, then the scaled residual energy
`γ⁻¹ ‖x - Prox_{γ f} x‖²` tends to `0` as `γ ↓ 0` through `ℝ_{++}`. -/
theorem tendsto_inv_mul_sqDist_scaledProximityOperator_atZeroRight_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (hx : x ∈ effectiveDomain f) :
    Filter.Tendsto
      (fun γ : PosReal ↦ (γ : ℝ)⁻¹ * ‖x - Prox[γ, f, hf] x‖ ^ 2)
      (Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
      (nhds (0 : ℝ)) := by
  -- Rewrite the residual as twice the Moreau/proximal-value gap, then pass to the limit.
  have hfx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfx_bot : f.asEReal x ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < f.asEReal x from (f x).2)
  have hgap :
      (fun γ : PosReal ↦ (γ : ℝ)⁻¹ * ‖x - Prox[γ, f, hf] x‖ ^ 2) =
        fun γ : PosReal ↦
          2 * ((({}^[γ] f) x).toReal - (f.asEReal (Prox[γ, f, hf] x)).toReal) := by
    funext γ
    exact inv_mul_sqDist_eq_two_mul_moreauEnvelope_sub_proxValue_of_mem_gammaZero
      (f := f) (hf := hf) (x := x) (hx := hx) (γ := γ)
  rw [hgap]
  have hmoreau :
      Filter.Tendsto
        (fun γ : PosReal ↦ (({}^[γ] f) x).toReal)
        (Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
        (nhds ((f.asEReal x).toReal)) := by
    exact (EReal.tendsto_toReal hfx_top hfx_bot).comp
      (tendsto_moreauEnvelope_atZeroRight_of_mem_gammaZero (f := f) (hf := hf) (x := x))
  have hprox :
      Filter.Tendsto
        (fun γ : PosReal ↦ (f.asEReal (Prox[γ, f, hf] x)).toReal)
        (Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
        (nhds ((f.asEReal x).toReal)) := by
    exact (EReal.tendsto_toReal hfx_top hfx_bot).comp
      (tendsto_scaledProxValue_atZeroRight_of_mem_effectiveDomain
        (f := f) (hf := hf) (x := x) hx)
  simpa using (hmoreau.sub hprox).const_mul 2

end Proposition_12_33

end ERealFunction
