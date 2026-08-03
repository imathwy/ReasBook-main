import BauschkeLean.Chap01.Text_1_0_14
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap17.Proposition_17_31
import BauschkeLean.Chap17.Proposition_17_39.Index

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open InnerProductSpace
open SetValuedOperator
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Helper for Corollary 17 44: continuity of a map on the subdifferential domain means continuity
at each subtype point over the base point `x`. -/
def selection_continuous_at_point
    {X : Type*} [TopologicalSpace X] {Y Z : Type*} [TopologicalSpace Z]
    (A : SetValuedOperator X Y) (T : A.dom → Z) (x : X) : Prop :=
  ∀ hx : x ∈ A.dom, ContinuousAt T ⟨x, hx⟩

omit [FiniteDimensional ℝ H] in
/-- Helper for Corollary 17 44: a subgradient at `x` gives the lower affine support inequality in
real form at every other finite point. -/
lemma subgradient_real_lower_bound
    {f : H → Set.Ioi (⊥ : EReal)} {x y u : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (hu : u ∈ (∂ f) x) :
    ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
  have hxy :
      (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) :=
    (mem_subdifferential_iff f x u).1 hu y
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hreal : ⟪y - x, u⟫_ℝ + (f x : EReal).toReal ≤ (f y : EReal).toReal := by
    -- Both endpoint values are finite on the effective domain, so the `EReal` inequality reduces
    -- to an inequality in `ℝ`.
    have hcast :
        (((⟪y - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) ≤
          (((f y : EReal).toReal : ℝ) : EReal) := by
      calc
        (((⟪y - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal))
            = (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) := by
                rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
                simp
        _ ≤ (f y : EReal) := hxy
        _ = (((f y : EReal).toReal : ℝ) : EReal) := by
              exact (EReal.coe_toReal hy_top hy_bot).symm
    exact_mod_cast hcast
  linarith

omit [FiniteDimensional ℝ H] in
/-- Helper for Corollary 17 44: a real-valued affine support inequality at finite endpoint values
can be recast as the defining `EReal` subgradient inequality. -/
lemma ereal_affine_ineq_of_real_lower_bound
    {f : H → Set.Ioi (⊥ : EReal)} {x y u : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    (hineq : ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal) :
    (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hcast :
      (⟪y - x, u⟫_ℝ : EReal) ≤
        (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) := by
    exact_mod_cast hineq
  have hsub :
      (⟪y - x, u⟫_ℝ : EReal) ≤ (f y : EReal) - (f x : EReal) := by
    simpa [EReal.coe_toReal hy_top hy_bot, EReal.coe_toReal hx_top hx_bot, EReal.coe_sub]
      using hcast
  exact (EReal.le_sub_iff_add_le (.inl hx_bot) (.inl hx_top)).1 hsub

omit [FiniteDimensional ℝ H] in
/-- Helper for Corollary 17 44: a subgradient at `y` gives the corresponding upper affine support
inequality in real form when evaluated at `x`. -/
lemma subgradient_real_upper_bound
    {f : H → Set.Ioi (⊥ : EReal)} {x y v : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (hv : v ∈ (∂ f) y) :
    (f y : EReal).toReal - (f x : EReal).toReal ≤ ⟪y - x, v⟫_ℝ := by
  have hswap :
      ⟪x - y, v⟫_ℝ ≤ (f x : EReal).toReal - (f y : EReal).toReal :=
    subgradient_real_lower_bound (x := y) (y := x) hy hx hv
  have hneg : ⟪x - y, v⟫_ℝ = -⟪y - x, v⟫_ℝ := by
    have hxy : x - y = -(y - x) := by
      abel
    calc
      ⟪x - y, v⟫_ℝ = ⟪-(y - x), v⟫_ℝ := by rw [hxy]
      _ = -⟪y - x, v⟫_ℝ := by rw [inner_neg_left]
  have hswap' :
      -⟪y - x, v⟫_ℝ ≤ (f x : EReal).toReal - (f y : EReal).toReal := by
    simpa [hneg] using hswap
  linarith

omit [FiniteDimensional ℝ H] in
/-- Helper for Corollary 17 44: two nearby subgradients bound the first-order remainder by the
distance between the subgradients. -/
lemma remainder_norm_bound_of_subgradients
    {f : H → Set.Ioi (⊥ : EReal)} {x y u v : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    (hu : u ∈ (∂ f) x) (hv : v ∈ (∂ f) y) :
    0 ≤ (f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ ∧
      ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖
        ≤ ‖y - x‖ * ‖v - u‖ := by
  have hlower :
      ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal :=
    subgradient_real_lower_bound hx hy hu
  have hupper :
      (f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ ≤
        ⟪y - x, v - u⟫_ℝ := by
    have hupper' :
        (f y : EReal).toReal - (f x : EReal).toReal ≤ ⟪y - x, v⟫_ℝ :=
      subgradient_real_upper_bound hx hy hv
    have hupper_sub :
        (f y : EReal).toReal - (f x : EReal).toReal - ⟪y - x, u⟫_ℝ ≤
          ⟪y - x, v⟫_ℝ - ⟪y - x, u⟫_ℝ :=
      sub_le_sub_right hupper' _
    calc
      (f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ
          = (f y : EReal).toReal - (f x : EReal).toReal - ⟪y - x, u⟫_ℝ := by
              rw [real_inner_comm]
      _ ≤ ⟪y - x, v⟫_ℝ - ⟪y - x, u⟫_ℝ := hupper_sub
      _ = ⟪y - x, v - u⟫_ℝ := by rw [inner_sub_right]
  have hnonneg :
      0 ≤ (f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ := by
    exact sub_nonneg.mpr (by simpa [real_inner_comm] using hlower)
  refine ⟨hnonneg, ?_⟩
  -- The affine-support squeeze reduces the remainder estimate to Cauchy-Schwarz.
  rw [Real.norm_of_nonneg hnonneg]
  exact hupper.trans (real_inner_le_norm (y - x) (v - u))

/-- Helper for Corollary 17 44: strong limits of subgradients over points converging to an interior
effective-domain point remain subgradients at the limit point. -/
lemma mem_subdifferential_of_tendsto_of_tendsto_of_mem_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u : H}
    (hx : x ∈ interior (effectiveDomain f))
    (xSeq uSeq : ℕ → H) (hsub : ∀ n, uSeq n ∈ (∂ f) (xSeq n))
    (hxSeq : Tendsto xSeq atTop (𝓝 x)) (huSeq : Tendsto uSeq atTop (𝓝 u)) :
    u ∈ (∂ f) x := by
  have hxeff : x ∈ effectiveDomain f := interior_subset hx
  have hxcont : ContinuousAtOnEffectiveDomain f x :=
    continuousAtOnEffectiveDomain_of_mem_interior_effectiveDomain hf hx
  have hxSeq_eff : ∀ n, xSeq n ∈ effectiveDomain f := by
    intro n
    exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf ⟨uSeq n, hsub n⟩
  have hxSeq_within : Tendsto xSeq atTop (𝓝[effectiveDomain f] x) := by
    exact
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        hxSeq (Filter.Eventually.of_forall hxSeq_eff)
  have hfx :
      Tendsto (fun n ↦ (f (xSeq n) : EReal).toReal) atTop (𝓝 ((f x : EReal).toReal)) := by
    have htoReal :
        Set.MapsTo (fun y ↦ (f y : EReal).toReal) (effectiveDomain f) (Set.univ : Set ℝ) := by
      intro y hy
      simp
    simpa using
      (ContinuousWithinAt.tendsto_nhdsWithin hxcont.continuousWithinAt htoReal).comp hxSeq_within
  refine (mem_subdifferential_iff (f := f) (x := x) (u := u)).2 ?_
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · have hyx : Tendsto (fun n ↦ y - xSeq n) atTop (𝓝 (y - x)) := by
      simpa [sub_eq_add_neg] using tendsto_const_nhds.sub hxSeq
    have hinner :
        Tendsto (fun n ↦ inner ℝ (y - xSeq n) (uSeq n)) atTop (𝓝 (inner ℝ (y - x) u)) := by
      have hpair :
          Tendsto (fun n ↦ (y - xSeq n, uSeq n)) atTop (𝓝 (y - x, u)) :=
        hyx.prodMk_nhds huSeq
      simpa using ((continuous_fst.inner continuous_snd).tendsto (y - x, u)).comp hpair
    have hrhs :
        Tendsto (fun n ↦ (f y : EReal).toReal - (f (xSeq n) : EReal).toReal) atTop
          (𝓝 ((f y : EReal).toReal - (f x : EReal).toReal)) := by
      exact tendsto_const_nhds.sub hfx
    have hineq :
        ∀ n, inner ℝ (y - xSeq n) (uSeq n) ≤
          (f y : EReal).toReal - (f (xSeq n) : EReal).toReal := by
      intro n
      exact subgradient_real_lower_bound (hxSeq_eff n) hy (hsub n)
    exact ereal_affine_ineq_of_real_lower_bound hxeff hy <|
      le_of_tendsto_of_tendsto hinner hrhs (Filter.Eventually.of_forall hineq)
  · have hy_top : (f y : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
    have hy_top' : CoeTC.coe (f y) = (⊤ : EReal) := by
      simpa using hy_top
    rw [hy_top']
    exact le_top

/-- Helper for Corollary 17 44: a norm-continuous subdifferential selection at an interior point
produces a Fréchet derivative of the finite representative there. -/
lemma differentiableAt_of_exists_selection_continuous_at_point
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f))
    (hsel :
      ∃ G : Selection (∂ f),
        selection_continuous_at_point (A := ∂ f) (T := fun z : (∂ f).dom ↦ (G z : H)) x) :
    DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x := by
  rcases hsel with ⟨G, hG⟩
  let x0 : (∂ f).dom := ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩
  let u : H := (G x0 : H)
  have hcont : ContinuousAt (fun z : (∂ f).dom ↦ (G z : H)) x0 := hG x0.2
  have hxeff : x ∈ effectiveDomain f := interior_subset hx
  have hu : u ∈ (∂ f) x := by
    have hu' := selection_apply_mem G x0
    change (G x0 : H) ∈ (∂ f) x at hu'
    exact hu'
  have hgrad : HasGradientAt (fun y ↦ (f y : EReal).toReal) u x := by
    -- The source proof squeezes the normalized remainder by the displacement times the variation
    -- of the chosen selection.
    rw [hasGradientAt_iff_tendsto, Metric.tendsto_nhds_nhds]
    intro ε hε
    rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx) with ⟨ρ, hρpos, hρball⟩
    rw [Metric.continuousAt_iff] at hcont
    rcases hcont ε hε with ⟨δ, hδpos, hδbound⟩
    refine ⟨min ρ δ, lt_min hρpos hδpos, ?_⟩
    intro y hy
    by_cases hxy : y = x
    · -- At the base point, the remainder vanishes identically.
      subst hxy
      simpa using hε
    · have hyball : dist y x < min ρ δ := by
        simpa [Metric.mem_ball] using hy
      have hyρ : y ∈ Metric.ball x ρ := by
        rw [Metric.mem_ball]
        exact (lt_min_iff.mp hyball).1
      have hyδ : y ∈ Metric.ball x δ := by
        rw [Metric.mem_ball]
        exact (lt_min_iff.mp hyball).2
      have hyint : y ∈ interior (effectiveDomain f) := hρball hyρ
      have hyDom : y ∈ (∂ f).dom :=
        mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hyint
      let y0 : (∂ f).dom := ⟨y, hyDom⟩
      have hGy_lt : ‖(G y0 : H) - u‖ < ε := by
        have hy0_dist : dist y0 x0 < δ := by
          simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hyδ
        simpa [u, x0, y0, dist_eq_norm] using hδbound hy0_dist
      have hyeff : y ∈ effectiveDomain f := interior_subset hyint
      have hv : (G y0 : H) ∈ (∂ f) y := by
        have hv' := selection_apply_mem G y0
        change (G y0 : H) ∈ (∂ f) y at hv'
        exact hv'
      have hrem := remainder_norm_bound_of_subgradients hxeff hyeff hu hv
      have hy_norm_pos : 0 < ‖y - x‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hquot_le :
          ‖y - x‖⁻¹ *
              ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖ ≤
            ‖(G y0 : H) - u‖ := by
        have hdiv_le :
            ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖ / ‖y - x‖ ≤
              ‖(G y0 : H) - u‖ := by
          refine (div_le_iff₀ hy_norm_pos).2 ?_
          simpa [mul_comm, mul_left_comm, mul_assoc] using hrem.2
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv_le
      have hprod_nonneg :
          0 ≤ ‖y - x‖⁻¹ *
              ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖ := by
        positivity
      have hlt :
          ‖y - x‖⁻¹ *
              ‖(f y : EReal).toReal - (f x : EReal).toReal - ⟪u, y - x⟫_ℝ‖ < ε :=
        lt_of_le_of_lt hquot_le hGy_lt
      simpa [Real.dist_eq, abs_of_nonneg hprod_nonneg] using hlt
  exact hgrad.differentiableAt

/-- Helper for Corollary 17 44: if the subdifferential fiber at `x` is the singleton `{u}`, then
every subdifferential selection is norm-continuous at `x` in finite dimension. -/
lemma selection_continuous_at_point_of_subdifferential_singleton
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u : H}
    (hx : x ∈ interior (effectiveDomain f)) (hsub : (∂ f) x = ({u} : Set H))
    (G : Selection (∂ f)) :
    selection_continuous_at_point (A := ∂ f) (T := fun z : (∂ f).dom ↦ (G z : H)) x := by
  intro hxdom
  let x0 : (∂ f).dom := ⟨x, hxdom⟩
  have hGx : (G x0 : H) = u := by
    have hmem := selection_apply_mem G x0
    change (G x0 : H) ∈ (∂ f) x at hmem
    have hsingle : (G x0 : H) ∈ ({u} : Set H) := by
      simpa [hsub] using hmem
    simpa [Set.mem_singleton_iff] using hsingle
  have hxcont : ContinuousAtOnEffectiveDomain f x :=
    continuousAtOnEffectiveDomain_of_mem_interior_effectiveDomain hf hx
  obtain ⟨ρ, hρpos, hbounded⟩ :=
    subdifferential_ball_union_bounded_of_continuousAtOnEffectiveDomain f hf.2 hxcont
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : H)
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro z hz
  have hzbase : Tendsto (fun n ↦ ((z n : (∂ f).dom) : H)) atTop (𝓝 x) := by
    simpa using (continuous_subtype_val.tendsto x0).comp hz
  have hseq : Tendsto (fun n ↦ (G (z n) : H)) atTop (𝓝 u) := by
    refine tendsto_of_subseq_tendsto ?_
    intro ns hns
    have hzsub : Tendsto (z ∘ ns) atTop (𝓝 x0) := hz.comp hns
    have hzbase_sub : Tendsto (fun n ↦ ((z (ns n) : (∂ f).dom) : H)) atTop (𝓝 x) := by
      simpa using (continuous_subtype_val.tendsto x0).comp hzsub
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hzbase_sub ρ hρpos
    have hz_event_ball : ∀ᶠ n in atTop, ((z (ns n) : (∂ f).dom) : H) ∈ Metric.ball x ρ := by
      exact Filter.eventually_atTop.2 ⟨N, fun n hn ↦ hN n hn⟩
    have hG_event_closedBall :
        ∀ᶠ n in atTop, (G (z (ns n)) : H) ∈ Metric.closedBall (0 : H) R := by
      filter_upwards [hz_event_ball] with n hn
      apply hR
      exact Set.mem_iUnion.2
        ⟨(z (ns n) : H), Set.mem_iUnion.2 ⟨hn, by
          have hmem := selection_apply_mem G (z (ns n))
          exact hmem⟩⟩
    obtain ⟨w, hw_ball, ms, hmsmono, hms_tendsto⟩ :=
      (isCompact_closedBall (0 : H) R).tendsto_subseq' hG_event_closedBall.frequently
    have hw_sub : w ∈ (∂ f) x := by
      refine
        mem_subdifferential_of_tendsto_of_tendsto_of_mem_interior_effectiveDomain
          hf hx
          (fun n ↦ ((z (ns (ms n)) : (∂ f).dom) : H))
          (fun n ↦ (G (z (ns (ms n))) : H))
          ?_ ?_ ?_
      · intro n
        have hmem := selection_apply_mem G (z (ns (ms n)))
        exact hmem
      · exact hzbase_sub.comp hmsmono.tendsto_atTop
      · exact hms_tendsto
    have hw_eq_u : w = u := by
      have hw_single : w ∈ ({u} : Set H) := by
        simpa [hsub] using hw_sub
      simpa using hw_single
    exact ⟨ms, by simpa [hw_eq_u] using hms_tendsto⟩
  simpa [Function.comp, x0, hGx] using hseq

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 17.44 is the finite-dimensional identification of Gâteaux and
  Fréchet differentiability for a convex function on `interior (effectiveDomain f)`.
- `core/canonical`: the owner abstractions are `GateauxDifferentiableAt`,
  `DifferentiableAt`, `∂`, and the closed-graph and local-boundedness properties of the
  subdifferential.
- `bridge/view`: Gâteaux differentiability collapses `∂ f x` to a singleton, and in finite
  dimension the earlier Chapter 16 compactness and graph-closure results force any selection of
  `∂ f` to converge in norm to that singleton. The standard remainder estimate for a continuous
  selection then gives the Fréchet derivative.
-/

-- Proof sketch: Proposition 17.31 identifies Gâteaux differentiability with a singleton
-- subdifferential at `x`. Proposition 16.17 gives local boundedness of nearby subdifferentials,
-- and Proposition 16.36 gives sequential closedness of their graph in the strong-weak topology.
-- In finite dimensions, these facts force every selection of `∂ f` to converge in norm to the
-- unique subgradient at `x`, hence any selection is continuous there. The standard convex
-- remainder bound for a continuous local selection then upgrades the Gâteaux derivative to a
-- Fréchet derivative. The reverse implication is the general Fréchet-to-Gâteaux implication.
/-- Corollary 17 44: on a finite-dimensional real Hilbert space, Gâteaux differentiability and
Fréchet differentiability coincide for a function in `Γ₀(H)` at every point of
`interior (effectiveDomain f)`. -/
theorem gateauxDifferentiableAt_iff_frechetDifferentiableAt_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    GateauxDifferentiableAt (fun y ↦ (f y : EReal).toReal) x ↔
      DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x := by
  constructor
  · intro hgateaux
    rcases hgateaux with ⟨A, hA⟩
    let u : H := (toDual ℝ H).symm A
    have hAeq : toDualMap ℝ H u = A := by
      change (toDual ℝ H) u = A
      simp [u]
    have hgateaux' :
        HasGateauxDerivativeAt (fun y ↦ (f y : EReal).toReal) (toDualMap ℝ H u) x := by
      rw [hAeq]
      exact hA
    have hsub :
        (∂ f) x = ({u} : Set H) := by
      simpa using
        subdifferential_eq_singleton_of_hasGateauxDerivativeAt
          f (interior_subset hx) u hgateaux'
    classical
    let hnonempty : ∀ z : (∂ f).dom, Nonempty ((∂ f) z) := fun z ↦ by
      rcases (SetValuedOperator.mem_dom_iff (A := ∂ f) (x := (z : H))).1 z.2 with ⟨v, hv⟩
      exact ⟨⟨v, hv⟩⟩
    let G : Selection (∂ f) := fun z ↦ Classical.choice (hnonempty z)
    have hG :
        selection_continuous_at_point (A := ∂ f) (T := fun z : (∂ f).dom ↦ (G z : H)) x :=
      selection_continuous_at_point_of_subdifferential_singleton hf hx hsub G
    exact differentiableAt_of_exists_selection_continuous_at_point hf hx ⟨G, hG⟩
  · intro hdiff
    exact ⟨fderiv ℝ (fun y ↦ (f y : EReal).toReal) x, by
      simpa using hdiff.hasFDerivAt.hasGateauxDerivativeAt⟩

end DifferentiabilityOfConvexFunctions

end ERealFunction
