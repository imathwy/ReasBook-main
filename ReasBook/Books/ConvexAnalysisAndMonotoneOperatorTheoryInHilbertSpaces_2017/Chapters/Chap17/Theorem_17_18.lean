import Mathlib
import BauschkeLean.Chap01.Definition_1_7
import BauschkeLean.Chap02.Fact_2_35
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap13.Proposition_13_16
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap17.Proposition_17_2
import BauschkeLean.Chap17.Proposition_17_17
import BauschkeLean.Chap18.Proposition_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise InnerProductSpace

universe u

namespace ERealFunction

section DirectionalDerivativesAndSubgradients

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Theorem 17 18: every support function belongs to `Γ(H)` because it is the
Fenchel conjugate of the corresponding indicator. -/
lemma supportFunction_mem_gamma_local
    (C : Set H) :
    σ[C] ∈ Γ(H) := by
  -- Rewrite the support function as the Fenchel conjugate of the indicator, then use the
  -- Chapter 13 conjugation owner.
  simpa [conjugate_indicator_eq_supportFunction] using
    (conjugate_mem_gamma (f := (ι[C]).asEReal))

/-- Helper for Theorem 17 18: the weakly continuous inner-product functional attains its maximum
on the weakly compact subdifferential fiber. -/
lemma exists_isMaxOn_inner_subdifferential_of_mem_cont
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : x ∈ cont f) (y : H) :
    ∃ u ∈ (∂ f) x,
      IsMaxOn
        (fun v : WeakSpace ℝ H ↦ ⟪(toWeakSpace ℝ H).symm v, y⟫_ℝ)
        (toWeakSpace ℝ H '' ((∂ f) x)) (toWeakSpace ℝ H u) := by
  -- Source continuity gives the nonempty weak compactness needed for Weierstrass on the weak
  -- image of the subdifferential.
  have hsub :
      ((∂ f) x).Nonempty ∧ IsCompact (toWeakSpace ℝ H '' ((∂ f) x)) :=
    subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain
      f hconv (by simpa [cont] using hxcont)
  have hcont :
      Continuous
        (fun v : WeakSpace ℝ H ↦ ⟪(toWeakSpace ℝ H).symm v, y⟫_ℝ) :=
    weakSpace_continuous_inner_right y
  have himage_nonempty :
      (toWeakSpace ℝ H '' ((∂ f) x)).Nonempty :=
    hsub.1.image (toWeakSpace ℝ H)
  -- Compactness of the weak image lets the weakly continuous coordinate functional attain its
  -- maximum there.
  obtain ⟨uWeak, huWeak_mem, huWeak_max⟩ :=
    hsub.2.exists_isMaxOn himage_nonempty hcont.continuousOn
  rcases huWeak_mem with ⟨u, hu, rfl⟩
  exact ⟨u, hu, huWeak_max⟩

omit [CompleteSpace H] in
/-- Helper for Theorem 17 18: a weak-space maximizer of the inner-product functional realizes the
corresponding supremum over the original subdifferential fiber. -/
lemma inner_eq_sSup_image_subdifferential_of_weak_isMaxOn
    (f : H → Set.Ioi (⊥ : EReal)) {x u y : H}
    (hu : u ∈ (∂ f) x)
    (hmax :
      IsMaxOn
        (fun v : WeakSpace ℝ H ↦ ⟪(toWeakSpace ℝ H).symm v, y⟫_ℝ)
        (toWeakSpace ℝ H '' ((∂ f) x)) (toWeakSpace ℝ H u)) :
    (⟪u, y⟫_ℝ : EReal) =
      sSup ((fun v : H ↦ (⟪v, y⟫_ℝ : EReal)) '' ((∂ f) x)) := by
  have hu_image : toWeakSpace ℝ H u ∈ toWeakSpace ℝ H '' ((∂ f) x) :=
    Set.mem_image_of_mem (toWeakSpace ℝ H) hu
  have hmaxE :
      IsMaxOn
        (fun v : WeakSpace ℝ H ↦ (⟪(toWeakSpace ℝ H).symm v, y⟫_ℝ : EReal))
        (toWeakSpace ℝ H '' ((∂ f) x)) (toWeakSpace ℝ H u) := by
    -- Reinterpret the real-valued maximality statement through the coercion `ℝ → EReal`.
    rw [isMaxOn_iff] at hmax ⊢
    intro v hv
    exact_mod_cast hmax v hv
  have hsSupWeak :
      (⟪(toWeakSpace ℝ H).symm (toWeakSpace ℝ H u), y⟫_ℝ : EReal) =
        sSup
          ((fun v : WeakSpace ℝ H ↦ (⟪(toWeakSpace ℝ H).symm v, y⟫_ℝ : EReal)) ''
            (toWeakSpace ℝ H '' ((∂ f) x))) :=
    eq_sSup_image_of_isMaxOn hu_image hmaxE
  have himage :
      (fun v : WeakSpace ℝ H ↦ (⟪(toWeakSpace ℝ H).symm v, y⟫_ℝ : EReal)) ''
          (toWeakSpace ℝ H '' ((∂ f) x)) =
        (fun v : H ↦ (⟪v, y⟫_ℝ : EReal)) '' ((∂ f) x) := by
    ext ξ
    constructor
    · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, by simp⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨toWeakSpace ℝ H v, ⟨v, hv, rfl⟩, by simp⟩
  -- Rewrite the weak-space image back to the original subdifferential image.
  simpa [himage] using hsSupWeak

omit [CompleteSpace H] in
/-- Helper for Theorem 17 18: Proposition 17.17 identifies the Fenchel conjugate of the
directional derivative with the indicator of the subdifferential fiber. -/
lemma conjugate_directionalDerivative_eq_indicator_subdifferential_of_continuousAtOnEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x) :
    (directionalDerivative f x)∗ = (ι[(∂ f) x]).asEReal := by
  -- Proposition 17.17 applies directly once the restricted continuity witness is reduced to the
  -- effective-domain membership required by the owner theorem.
  simpa using
    conjugate_directionalDerivative_eq_setIndicator_subdifferential
      (f := f) hconv hxcont.mem_effectiveDomain

/-- Helper for Theorem 17 18: once the conjugate is identified with the subdifferential
indicator, the biconjugate is the support function of that fiber. -/
lemma
    biconjugate_directionalDerivative_eq_supportFunction_subdifferential_of_continuousAtOnEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousAtOnEffectiveDomain f x) :
    (directionalDerivative f x)∗∗ = σ[(∂ f) x] := by
  -- First rewrite the first conjugate by Proposition 17.17 at the effective-domain point `x`.
  rw [conjugate_directionalDerivative_eq_indicator_subdifferential_of_continuousAtOnEffectiveDomain
    (f := f) hconv hxcont]
  -- Then identify the conjugate of the indicator with the support function of the same set.
  simpa using conjugate_indicator_eq_supportFunction (C := (∂ f) x)

omit [CompleteSpace H] in
/-- Helper for Theorem 17 18: a source continuity point lies in the core of the effective
domain. -/
lemma mem_core_effectiveDomain_of_mem_cont
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : x ∈ cont f) :
    x ∈ Set.core (effectiveDomain f) := by
  rcases (mem_cont_iff f x).1 hxcont with ⟨ρ, hρ, hball, _⟩
  rw [Set.mem_core_iff]
  refine ⟨mem_effectiveDomain_of_mem_cont hxcont, ?_⟩
  ext z
  constructor
  · intro hz
    simp
  · intro _
    let α : ℝ := ρ / (‖z‖ + 1)
    have hα : 0 < α := by
      dsimp [α]
      positivity
    have hz_mem_ball : x + α • z ∈ Metric.ball x ρ := by
      have hz_lt : α * ‖z‖ < ρ := by
        dsimp [α]
        rw [div_mul_eq_mul_div]
        have hden : 0 < ‖z‖ + 1 := by positivity
        rw [div_lt_iff₀ hden]
        nlinarith [hρ, norm_nonneg z]
      have hz_norm : ‖α • z‖ < ρ := by
        simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα.le, mul_comm] using hz_lt
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using hz_norm
    have hαz_mem : α • z ∈ effectiveDomain f - ({x} : Set H) := by
      refine Set.mem_sub.mpr ?_
      refine ⟨x + α • z, hball hz_mem_ball, x, by simp, ?_⟩
      abel_nf
    have hconv_sub :
        Convex ℝ (effectiveDomain f - ({x} : Set H)) :=
      hconv.convex_effectiveDomain.sub (convex_singleton x)
    refine (mem_cone_iff_exists_pos_smul_mem hconv_sub).2 ⟨α⁻¹, inv_pos.mpr hα, ?_⟩
    refine ⟨α • z, hαz_mem, ?_⟩
    simp [smul_smul, inv_mul_cancel₀ hα.ne']

/-- Helper for Theorem 17 18: at a source continuity point, the directional derivative is the
`toEReal` coercion of its real-valued representative. -/
lemma directionalDerivative_eq_toEReal_toReal_of_mem_cont
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : x ∈ cont f) :
    directionalDerivative f x =
      (fun y ↦ (directionalDerivative f x y).toReal).toEReal := by
  -- Route correction: use the core-point real-valuedness theorem instead of the stalled raw
  -- lower-semicontinuity route.
  funext y
  rcases directionalDerivative_eq_coe_real_of_mem_core
      hconv (mem_core_effectiveDomain_of_mem_cont (f := f) hconv hxcont) y with
    ⟨r, hr⟩
  have htoReal : (((directionalDerivative f x y).toReal : ℝ) : EReal) = directionalDerivative f x y := by
    rw [hr]
    exact EReal.coe_toReal (EReal.coe_ne_top r) (EReal.coe_ne_bot r)
  simpa [Function.asEReal_apply, Function.toEReal_apply] using
    htoReal.symm

/-- Helper for Theorem 17 18: source continuity packages the directional derivative into `Γ₀(H)`,
so Fenchel--Moreau identifies it with its biconjugate. -/
lemma directionalDerivative_eq_biconjugate_of_mem_cont
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : x ∈ cont f) :
    directionalDerivative f x = (directionalDerivative f x)∗∗ := by
  let φ : H → ℝ := fun y ↦ (directionalDerivative f x y).toReal
  have hxeff : x ∈ effectiveDomain f := mem_effectiveDomain_of_mem_cont hxcont
  have hdir_eq : directionalDerivative f x = (φ.toEReal).asEReal := by
    -- First normalize the `EReal`-valued directional derivative through its real representative.
    funext y
    simpa [φ, Function.asEReal_apply] using
      congrFun (directionalDerivative_eq_toEReal_toReal_of_mem_cont (f := f) hconv hxcont) y
  have hdom : dom (directionalDerivative f x) = Set.univ := by
    -- The normalization shows the directional derivative is finite in every direction.
    ext y
    constructor
    · intro _
      simp
    · intro _
      rw [dom]
      have hy_eq : directionalDerivative f x y = ((φ y : ℝ) : EReal) := by
        simpa [Function.asEReal_apply, Function.toEReal_apply, φ] using congrFun hdir_eq y
      simp [hy_eq]
  have hφconv : _root_.ConvexOn ℝ Set.univ φ := by
    have hdir_conv :
        _root_.ConvexOn ℝ (dom (directionalDerivative f x))
          (directionalDerivative f x) := by
      simpa [dom] using directionalDerivative_convexOn_dom hconv hxeff
    rw [convexOn_iff_forall_pos]
    constructor
    · simpa using convex_univ
    · intro u hu v hv a b ha hb hab
      have hineq :
          directionalDerivative f x (a • u + b • v) ≤
            a • directionalDerivative f x u + b • directionalDerivative f x v :=
        hdir_conv.2 (by simp [hdom]) (by simp [hdom]) ha.le hb.le hab
      have hu_eq :
          directionalDerivative f x u = ((φ u : ℝ) : EReal) := by
        simpa [φ, Function.asEReal_apply, Function.toEReal_apply] using congrFun hdir_eq u
      have hv_eq :
          directionalDerivative f x v = ((φ v : ℝ) : EReal) := by
        simpa [φ, Function.asEReal_apply, Function.toEReal_apply] using congrFun hdir_eq v
      have huv_eq :
          directionalDerivative f x (a • u + b • v) =
            ((φ (a • u + b • v) : ℝ) : EReal) := by
        simpa [φ, Function.asEReal_apply, Function.toEReal_apply] using
          congrFun hdir_eq (a • u + b • v)
      have hineq' :
          (((φ (a • u + b • v) : ℝ) : EReal)) ≤
            a • (((φ u : ℝ) : EReal)) + b • (((φ v : ℝ) : EReal)) := by
        rw [huv_eq, hu_eq, hv_eq] at hineq
        simpa using hineq
      exact EReal.coe_le_coe_iff.mp <| by
        simpa [smul_eq_mul, EReal.coe_mul, add_comm, add_left_comm, add_assoc] using hineq'
  have hφbounded : (nhds (0 : H)).IsBoundedUnder (· ≤ ·) φ := by
    classical
    let hcontData := (mem_cont_iff f x).1 hxcont
    let ρ : ℝ := Classical.choose hcontData
    have hρ : 0 < ρ := (Classical.choose_spec hcontData).1
    have hball : Metric.ball x ρ ⊆ effectiveDomain f := (Classical.choose_spec hcontData).2.1
    have hcontx : ContinuousAt (fun y ↦ (f y : EReal).toReal) x :=
      (Classical.choose_spec hcontData).2.2
    have hupper_event :
        ∀ᶠ z in nhds x, (f z : EReal).toReal < (f x : EReal).toReal + 1 := by
      simpa using
        hcontx.eventually
          (eventually_lt_nhds (show (f x : EReal).toReal < (f x : EReal).toReal + 1 by linarith))
    rcases Metric.eventually_nhds_iff.mp hupper_event with ⟨δ, hδ, hδball⟩
    let ε : ℝ := min ρ δ / 2
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    refine ⟨1 / ε, ?_⟩
    refine Metric.eventually_nhds_iff.mpr ⟨1, by norm_num, ?_⟩
    intro y hy
    have hy_norm : ‖y‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    have hερ : ε * ‖y‖ < ρ := by
      have hε_le_half_rho : ε ≤ ρ / 2 := by
        dsimp [ε]
        gcongr
        exact min_le_left ρ δ
      have hε_norm_lt : ε * ‖y‖ < ε := by
        nlinarith [hy_norm, hε, norm_nonneg y]
      have hε_lt_rho : ε < ρ := by
        have hhalf_lt : ρ / 2 < ρ := by nlinarith
        exact lt_of_le_of_lt hε_le_half_rho hhalf_lt
      exact lt_trans hε_norm_lt hε_lt_rho
    have hεδ : ε * ‖y‖ < δ := by
      have hε_le_half_delta : ε ≤ δ / 2 := by
        dsimp [ε]
        gcongr
        exact min_le_right ρ δ
      have hε_norm_lt : ε * ‖y‖ < ε := by
        nlinarith [hy_norm, hε, norm_nonneg y]
      have hε_lt_delta : ε < δ := by
        have hhalf_lt : δ / 2 < δ := by nlinarith
        exact lt_of_le_of_lt hε_le_half_delta hhalf_lt
      exact lt_trans hε_norm_lt hε_lt_delta
    have hp_ball_rho : x + ε • y ∈ Metric.ball x ρ := by
      have hnorm : ‖ε • y‖ < ρ := by
        simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε.le, mul_comm] using hερ
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using hnorm
    have hp_ball_delta : x + ε • y ∈ Metric.ball x δ := by
      have hnorm : ‖ε • y‖ < δ := by
        simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε.le, mul_comm] using hεδ
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using hnorm
    have hp_eff : x + ε • y ∈ effectiveDomain f :=
      hball hp_ball_rho
    have hupper_real :
        (f (x + ε • y) : EReal).toReal - (f x : EReal).toReal < 1 := by
      have hp_dist_delta : dist (x + ε • y) x < δ := by
        simpa [Metric.mem_ball] using hp_ball_delta
      linarith [hδball hp_dist_delta]
    have hquot_real :
        ((f (x + ε • y) : EReal).toReal - (f x : EReal).toReal) / ε < 1 / ε := by
      have htmp :
          ((f (x + ε • y) : EReal).toReal - (f x : EReal).toReal) * ε⁻¹ < 1 * ε⁻¹ := by
        exact mul_lt_mul_of_pos_right hupper_real (inv_pos.mpr hε)
      simpa [div_eq_mul_inv] using htmp
    have hfx_top : (f x : EReal) ≠ ⊤ :=
      ne_of_lt (mem_effectiveDomain_iff.mp hxeff)
    have hfx_bot : (f x : EReal) ≠ ⊥ :=
      ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hfp_top : (f (x + ε • y) : EReal) ≠ ⊤ :=
      ne_of_lt (mem_effectiveDomain_iff.mp hp_eff)
    have hfp_bot : (f (x + ε • y) : EReal) ≠ ⊥ :=
      ne_of_gt (show (⊥ : EReal) < (f (x + ε • y) : EReal) from (f (x + ε • y)).2)
    have hsample :
        (((f (x + ε • y) : EReal) - (f x : EReal)) / ε) ≤ ((1 / ε : ℝ) : EReal) := by
      have hfp_coe : (((f (x + ε • y) : EReal).toReal : ℝ) : EReal) = (f (x + ε • y) : EReal) :=
        EReal.coe_toReal hfp_top hfp_bot
      have hfx_coe : (((f x : EReal).toReal : ℝ) : EReal) = (f x : EReal) :=
        EReal.coe_toReal hfx_top hfx_bot
      rw [← hfp_coe, ← hfx_coe, ← EReal.coe_sub]
      change
        ((((f (x + ε • y) : EReal).toReal - (f x : EReal).toReal) / ε : ℝ) : EReal) ≤
          ((1 / ε : ℝ) : EReal)
      exact_mod_cast hquot_real.le
    have hdir_le : directionalDerivative f x y ≤ ((1 / ε : ℝ) : EReal) := by
      rw [directionalDerivative_eq_sInf_image_Ioi (f := f) x y]
      exact le_trans (sInf_le ⟨ε, hε, rfl⟩) hsample
    have hy_eq : directionalDerivative f x y = ((φ y : ℝ) : EReal) := by
      simpa [φ, Function.asEReal_apply, Function.toEReal_apply] using congrFun hdir_eq y
    have hφy : ((φ y : ℝ) : EReal) ≤ ((1 / ε : ℝ) : EReal) := by
      simpa [hy_eq] using hdir_le
    exact EReal.coe_le_coe_iff.mp hφy
  have hφcontOn : ContinuousOn φ (Set.univ : Set H) := by
    have hφboundData :
        ∃ x₀ ∈ (Set.univ : Set H), (nhds x₀).IsBoundedUnder (· ≤ ·) φ :=
      ⟨0, by simp, hφbounded⟩
    exact ((hφconv.continuousOn_tfae isOpen_univ Set.univ_nonempty).out 3 1).mp
      hφboundData
  have hφcont : Continuous φ := by
    simpa [continuousOn_univ] using hφcontOn
  have hφ_gamma : φ.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ φ hφcont hφconv
  have hφ_biconj : (φ.toEReal).asEReal∗∗ = (φ.toEReal).asEReal := by
    simpa [Function.asEReal_apply] using biconjugate_eq_of_mem_gammaZero hφ_gamma
  -- Transport the Fenchel--Moreau identity back across the normalization.
  calc
    directionalDerivative f x = (φ.toEReal).asEReal := hdir_eq
    _ = (φ.toEReal).asEReal∗∗ := hφ_biconj.symm
    _ = (directionalDerivative f x)∗∗ := by rw [← hdir_eq]

/-- Companion to Theorem 17 18: under `x ∈ cont f`, the directional derivative is the support
function of the subdifferential fiber. -/
theorem directionalDerivative_eq_supportFunction_subdifferential_of_mem_cont
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : x ∈ cont f) :
    directionalDerivative f x = σ[(∂ f) x] := by
  -- Source continuity supplies the missing Fenchel--Moreau fixpoint for the directional
  -- derivative, and Proposition 17.17 rewrites the biconjugate as the support function.
  calc
    directionalDerivative f x = (directionalDerivative f x)∗∗ :=
      directionalDerivative_eq_biconjugate_of_mem_cont (f := f) hconv hxcont
    _ = σ[(∂ f) x] :=
      biconjugate_directionalDerivative_eq_supportFunction_subdifferential_of_continuousAtOnEffectiveDomain
        (f := f) hconv (ContinuousAtOnEffectiveDomain.of_mem_cont hxcont)

-- Proof sketch: `x ∈ cont f` is the source-facing continuity hypothesis, while
-- `ContinuousAtOnEffectiveDomain f x` remains the bridge used by the Chapter 16/17 API.
/-- Theorem 17.18: if `f` is convex and `x ∈ cont f`, then the directional derivative
`f′(x; y)` is the maximum of `u ↦ (⟪y, u⟫_ℝ : EReal)` on the subdifferential `(∂ f) x`. -/
theorem exists_subgradient_isMaxOn_inner_eq_directionalDerivative_of_mem_cont
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : x ∈ cont f) (y : H) :
    ∃ u ∈ (∂ f) x,
      f′(x; y) = (⟪y, u⟫_ℝ : EReal) ∧
        IsMaxOn (fun v : H ↦ (⟪y, v⟫_ℝ : EReal)) ((∂ f) x) u := by
  obtain ⟨u, hu, hmaxWeak⟩ :=
    exists_isMaxOn_inner_subdifferential_of_mem_cont (f := f) hconv hxcont y
  have hmax :
      IsMaxOn (fun v : H ↦ (⟪y, v⟫_ℝ : EReal)) ((∂ f) x) u := by
    -- Pull the weak-space maximizing witness back to the original subdifferential fiber.
    rw [isMaxOn_iff] at hmaxWeak
    rw [isMaxOn_iff]
    intro v hv
    have hweak :
        ⟪v, y⟫_ℝ ≤ ⟪u, y⟫_ℝ :=
      hmaxWeak (toWeakSpace ℝ H v) (Set.mem_image_of_mem (toWeakSpace ℝ H) hv)
    exact_mod_cast (by simpa [real_inner_comm] using hweak)
  have hsupport :
      (⟪y, u⟫_ℝ : EReal) = σ[(∂ f) x] y := by
    -- Identify the attained inner product with the support-function supremum.
    calc
      (⟪y, u⟫_ℝ : EReal) = (⟪u, y⟫_ℝ : EReal) := by rw [real_inner_comm]
      _ = sSup ((fun v : H ↦ (⟪v, y⟫_ℝ : EReal)) '' ((∂ f) x)) :=
        inner_eq_sSup_image_subdifferential_of_weak_isMaxOn (f := f) hu hmaxWeak
      _ = σ[(∂ f) x] y := by rw [supportFunction_eq_sSup_image]
  refine ⟨u, hu, ?_, hmax⟩
  calc
    f′(x; y) = σ[(∂ f) x] y := by
      exact congrFun
        (directionalDerivative_eq_supportFunction_subdifferential_of_mem_cont
          (f := f) hconv hxcont) y
    _ = (⟪y, u⟫_ℝ : EReal) := hsupport.symm

/-- Helper for Theorem 17 18: the Chapter 16/17 bridge version of the max formula, stated with
`ContinuousPoint f x`. -/
theorem exists_subgradient_isMaxOn_inner_eq_directionalDerivative_of_continuousAtOnEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x) (y : H) :
    ∃ u ∈ (∂ f) x,
      f′(x; y) = (⟪y, u⟫_ℝ : EReal) ∧
        IsMaxOn (fun v : H ↦ (⟪y, v⟫_ℝ : EReal)) ((∂ f) x) u := by
  -- Route correction: `ContinuousPoint` is exactly the source continuity spelling behind
  -- `x ∈ cont f`, so the proved max formula applies without rebuilding the argument.
  simpa [ContinuousPoint, cont] using
    exists_subgradient_isMaxOn_inner_eq_directionalDerivative_of_mem_cont
      (f := f) hconv (x := x) hxcont y

/-- Helper for Theorem 17 18: the canonical support-function reformulation of the max formula in
the Chapter 16/17 source-continuity language. -/
theorem directionalDerivative_eq_supportFunction_subdifferential_of_continuousAtOnEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x) :
    directionalDerivative f x = σ[(∂ f) x] := by
  -- Route correction: this is a thin spelling adapter from `ContinuousPoint` to the already
  -- proved source-facing support-function identity.
  simpa [ContinuousPoint, cont] using
    directionalDerivative_eq_supportFunction_subdifferential_of_mem_cont
      (f := f) hconv (x := x) hxcont

/-- Helper for Theorem 17 18: after the support-function identity is established, the pointwise
reverse inequality is just its evaluation at the chosen direction. -/
lemma directionalDerivative_le_supportFunction_subdifferential_of_continuousAtOnEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x) (y : H) :
    directionalDerivative f x y ≤ σ[(∂ f) x] y := by
  -- Evaluate the corrected source-continuity support identity at the chosen direction.
  exact (congrFun
    (directionalDerivative_eq_supportFunction_subdifferential_of_continuousAtOnEffectiveDomain
      (f := f) hconv (x := x) hxcont) y).le

-- Proof sketch: the source-facing existence form is the pointwise part of the max formula.
/-- Companion to Theorem 17 18: if `x ∈ cont f`, then each directional derivative is attained by
some subgradient. -/
theorem exists_subgradient_eq_directionalDerivative_of_mem_cont
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : x ∈ cont f) (y : H) :
    ∃ u ∈ (∂ f) x, f′(x; y) = (⟪y, u⟫_ℝ : EReal) := by
  -- Extract the equality component from the proved max formula.
  rcases exists_subgradient_isMaxOn_inner_eq_directionalDerivative_of_mem_cont
      (f := f) hconv hxcont y with ⟨u, hu, hEq, _⟩
  exact ⟨u, hu, hEq⟩

/-- Helper for Theorem 17 18: the Chapter 16/17 bridge existence form, stated with
`ContinuousPoint f x`. -/
theorem exists_subgradient_eq_directionalDerivative_of_continuousAtOnEffectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : ContinuousPoint f x) (y : H) :
    ∃ u ∈ (∂ f) x, f′(x; y) = (⟪y, u⟫_ℝ : EReal) := by
  -- Project the equality component from the corrected `ContinuousPoint` max formula.
  rcases exists_subgradient_isMaxOn_inner_eq_directionalDerivative_of_continuousAtOnEffectiveDomain
      (f := f) hconv hxcont y with ⟨u, hu, hEq, _⟩
  exact ⟨u, hu, hEq⟩

end DirectionalDerivativesAndSubgradients

end ERealFunction
