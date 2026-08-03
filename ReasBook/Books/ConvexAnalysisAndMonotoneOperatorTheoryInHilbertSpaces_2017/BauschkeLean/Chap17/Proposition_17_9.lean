import Mathlib
import BauschkeLean.Chap03.Proposition_3_44
import BauschkeLean.Chap09.Proposition_9_14
import BauschkeLean.Chap09.Proposition_9_33
import BauschkeLean.Chap02.Definition_2_56
import BauschkeLean.Chap17.Proposition_17_7

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace Set
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

section ConvexityCriterion

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 17 9: differentiability on an open effective domain yields the
canonical Gâteaux derivative field built from `gradientWithin`. -/
lemma hasGateauxDerivativeOn_toDual_gradientWithin_of_differentiableOn_open
    (h : H → Set.Ioi (⊥ : EReal)) (hopen : IsOpen (effectiveDomain h))
    (hdiff : DifferentiableOn ℝ (fun x ↦ (h x : EReal).toReal) (effectiveDomain h)) :
    HasGateauxDerivativeOn
      (fun x ↦ (h x : EReal).toReal)
      (fun x ↦
        toDual ℝ H
          (gradientWithin (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x))
      (effectiveDomain h) := by
  intro x hx
  -- On the open effective domain, the within-gradient is a genuine Fréchet derivative field.
  have hx_nhds : effectiveDomain h ∈ 𝓝 x := hopen.mem_nhds hx
  simpa using
    ((hdiff x hx).hasGradientWithinAt.hasFDerivWithinAt.hasGateauxDerivativeWithinAt hx_nhds :
      HasGateauxDerivativeWithinAt
        (fun z ↦ (h z : EReal).toReal)
        (toDual ℝ H
          (gradientWithin (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x))
        (effectiveDomain h) x)

/-- Helper for Proposition 17 9: a second Fréchet derivative on an open set differentiates the
canonical `gradientWithin` Gâteaux field at the same point. -/
lemma hasGateauxDerivativeWithinAt_toDual_gradientWithin_of_hasSecondFrechetDerivWithinAt
    {D : Set H} (hopen : IsOpen D) {g : H → ℝ}
    (hdiff : DifferentiableOn ℝ g D) {x : H} (hx : x ∈ D)
    {A₂ : H →L[ℝ] H →L[ℝ] ℝ}
    (hA₂ : HasSecondFrechetDerivWithinAt ℝ g D x A₂) :
    HasGateauxDerivativeWithinAt
      (fun y ↦ toDual ℝ H (gradientWithin g D y))
      A₂
      D
      x := by
  rcases hA₂ with ⟨U, hU_nhds, hU_sub, T', hT', hT'₂⟩
  rcases mem_nhds_iff.mp hU_nhds with ⟨V, hV_sub, hV_open, hxV⟩
  have hV_subD : V ⊆ D := by
    intro z hz
    exact hU_sub (hV_sub hz)
  have hEqV :
      EqOn T' (fun y ↦ toDual ℝ H (gradientWithin g D y)) V := by
    intro z hz
    have hzU : z ∈ U := hV_sub hz
    have hzD : z ∈ D := hV_subD hz
    have hT'_at : HasFDerivAt g (T' z) z := by
      -- Restrict the local Fréchet witness to the open neighborhood `V`.
      exact ((hT' z hzU).mono hV_sub).hasFDerivAt (hV_open.mem_nhds hz)
    have hDT_at :
        HasFDerivAt g
          (toDual ℝ H (gradientWithin g D z))
          z := by
      -- On the open set `D`, `gradientWithin` is the genuine Fréchet derivative.
      exact
        ((hdiff z hzD).hasGradientWithinAt.hasFDerivWithinAt.hasFDerivAt
          (hopen.mem_nhds hzD) :
          HasFDerivAt g
            (toDual ℝ H (gradientWithin g D z))
            z)
    exact hT'_at.unique hDT_at
  have hDT₂V :
      HasFDerivWithinAt
        (fun y ↦ toDual ℝ H (gradientWithin g D y))
        A₂
        V
        x := by
    -- Replace the auxiliary derivative field by the canonical one on `V`.
    apply (hT'₂.mono hV_sub).congr
    · intro z hz
      exact (hEqV hz).symm
    · exact (hEqV hxV).symm
  have hDT₂D :
      HasFDerivWithinAt
        (fun y ↦ toDual ℝ H (gradientWithin g D y))
        A₂
        D
        x := by
    -- Upgrade from the open neighborhood `V` back to the ambient open set `D`.
    exact hDT₂V.hasFDerivAt (hV_open.mem_nhds hxV) |>.hasFDerivWithinAt
  -- A Fréchet derivative on an open set yields the corresponding Gâteaux derivative.
  exact hDT₂D.hasGateauxDerivativeWithinAt (hopen.mem_nhds hx)

/-- Helper for Proposition 17 9: the pointwise Definition 2.56 hypothesis packages into a global
second Gâteaux derivative field with nonnegative quadratic form. -/
lemma exists_gateaux_secondDerivative_field_of_pointwise_secondFrechet_nonnegative
    {D : Set H} (hopen : IsOpen D) {g : H → ℝ}
    (hdiff : DifferentiableOn ℝ g D)
    (hsecond :
      ∀ x ∈ D,
        TwiceFrechetDifferentiableWithinAt ℝ g D x ∧
          ∀ A₂ : H →L[ℝ] H →L[ℝ] ℝ,
            HasSecondFrechetDerivWithinAt ℝ g D x A₂ →
              ∀ z : H, 0 ≤ A₂ z z) :
    ∃ A₂ : H → H →L[ℝ] H →L[ℝ] ℝ,
      HasGateauxDerivativeOn
          (fun x ↦ toDual ℝ H (gradientWithin g D x))
          A₂
          D ∧
        GateauxSecondDerivativeNonnegativeOn A₂ D := by
  classical
  have hchoose :
      ∀ x : D, ∃ A₂ : H →L[ℝ] H →L[ℝ] ℝ, HasSecondFrechetDerivWithinAt ℝ g D x A₂ := by
    intro x
    exact
      (twiceFrechetDifferentiableWithinAt_iff_exists_hasSecondFrechetDerivWithinAt).mp
        ((hsecond x x.2).1)
  choose A₂ hA₂ using hchoose
  let A₂Field : H → H →L[ℝ] H →L[ℝ] ℝ :=
    fun x ↦ if hx : x ∈ D then A₂ ⟨x, hx⟩ else 0
  refine ⟨A₂Field, ?_, ?_⟩
  · intro x hx
    -- Route correction: use the local Fréchet witness at `x` and identify it with the canonical
    -- `gradientWithin` field on a smaller open neighborhood.
    simpa [A₂Field, hx] using
      hasGateauxDerivativeWithinAt_toDual_gradientWithin_of_hasSecondFrechetDerivWithinAt
        (hopen := hopen) (hdiff := hdiff) hx (hA₂ ⟨x, hx⟩)
  · intro x hx z
    -- The chosen witness inherits the pointwise nonnegative quadratic form from the hypothesis.
    simpa [A₂Field, hx] using
      (hsecond x hx).2 (A₂ ⟨x, hx⟩) (hA₂ ⟨x, hx⟩) z

-- Proof sketch: Proposition 17.7 supplies the first-order route on `effectiveDomain h`.
-- For clause (ii), the source-facing second-order hypothesis is expressed pointwise through
-- Definition 2.56: at each point of `effectiveDomain h`, the finite representative of `h` is
-- twice Fréchet differentiable and every second Fréchet derivative there has nonnegative
-- quadratic form. This pointwise source clause is then bridged to the canonical second-order
-- criterion used in Proposition 17.7.
/-- Proposition 17 9: under the hypotheses of Proposition 17.9, the proper function `h` is convex
on its effective domain. The second-order clause is stated directly in the language of Definition
2.56 on `effectiveDomain h`, rather than through a separately chosen global Hessian field. -/
theorem convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
    (h : H → Set.Ioi (⊥ : EReal)) (hdom_nonempty : (effectiveDomain h).Nonempty)
    (hopen : IsOpen (effectiveDomain h)) (hconv : Convex ℝ (effectiveDomain h))
    (hdiff : DifferentiableOn ℝ (fun x ↦ (h x : EReal).toReal) (effectiveDomain h))
    (hcriterion :
      GateauxDerivativeMonotoneOn
          (fun x ↦
            toDual ℝ H
              (gradientWithin (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x))
          (effectiveDomain h) ∨
        ∀ x ∈ effectiveDomain h,
          TwiceFrechetDifferentiableWithinAt ℝ
              (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x ∧
            ∀ A₂ : H →L[ℝ] H →L[ℝ] ℝ,
              HasSecondFrechetDerivWithinAt ℝ
                  (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x A₂ →
                ∀ z : H, 0 ≤ A₂ z z) :
    ConvexOn h (effectiveDomain h) := by
  let g : H → ℝ := fun x ↦ (h x : EReal).toReal
  let DT : H → H →L[ℝ] ℝ := fun x ↦ toDual ℝ H (gradientWithin g (effectiveDomain h) x)
  -- Proposition 17.7 applies once the canonical gradient field is available on the open domain.
  have hDT : HasGateauxDerivativeOn g DT (effectiveDomain h) := by
    simpa [g, DT] using
      hasGateauxDerivativeOn_toDual_gradientWithin_of_differentiableOn_open h hopen hdiff
  have htfae :
      List.TFAE
          [ConvexOn h (effectiveDomain h),
            GateauxSupportInequalityOn h DT,
            GateauxDerivativeMonotoneOn DT (effectiveDomain h)] ∧
        (∀ A₂ : H → H →L[ℝ] H →L[ℝ] ℝ,
          HasGateauxDerivativeOn DT A₂ (effectiveDomain h) →
            List.TFAE
              [ConvexOn h (effectiveDomain h),
                GateauxSupportInequalityOn h DT,
                GateauxDerivativeMonotoneOn DT (effectiveDomain h),
                GateauxSecondDerivativeNonnegativeOn A₂ (effectiveDomain h)]) :=
    convex_tfae_of_open_convex_effectiveDomain h DT hdom_nonempty hopen hconv hDT
  rcases hcriterion with hmono | hsecond
  · -- The first-order branch is exactly clause (iii) in Proposition 17.7.
    simpa [DT] using (List.TFAE.out htfae.1 2 0).mp hmono
  · -- TODO: choose a pointwise second-derivative field from `hsecond`, bridge it to a global
    -- `HasGateauxDerivativeOn DT A₂ (effectiveDomain h)`, and then apply clause (iv) of
    -- Proposition 17.7.
    rcases
      exists_gateaux_secondDerivative_field_of_pointwise_secondFrechet_nonnegative
        (hopen := hopen) (g := g) (hdiff := hdiff) hsecond with
      ⟨A₂, hA₂, hA₂_nonneg⟩
    -- Proposition 17.7 turns clause (iv) back into convexity once the canonical field is in place.
    simpa [DT] using (List.TFAE.out (htfae.2 A₂ (by simpa [DT] using hA₂)) 3 0).mp hA₂_nonneg

end ConvexityCriterion

section Proposition_17_9

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] Classical.propDecidable

variable (h : H → Set.Ioi (⊥ : EReal))
variable (hopen : IsOpen (effectiveDomain h)) (hconv : Convex ℝ (effectiveDomain h))
variable (hdiff : DifferentiableOn ℝ (fun x ↦ (h x : EReal).toReal) (effectiveDomain h))
variable (hcriterion :
  GateauxDerivativeMonotoneOn
      (fun x ↦
        toDual ℝ H
          (gradientWithin (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x))
      (effectiveDomain h) ∨
    ∀ x ∈ effectiveDomain h,
      TwiceFrechetDifferentiableWithinAt ℝ
          (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x ∧
        ∀ A₂ : H →L[ℝ] H →L[ℝ] ℝ,
          HasSecondFrechetDerivWithinAt ℝ
              (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x A₂ →
            ∀ z : H, 0 ≤ A₂ z z)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 17 9: outside `closure (effectiveDomain h)`, the explicit
boundary-liminf extension is forced onto its `+∞` branch. -/
lemma boundaryLiminfExtensionEReal_eq_top_of_not_mem_closure
    {x : H} (hx : x ∉ closure (effectiveDomain h)) :
    boundaryLiminfExtensionEReal h x = ⊤ := by
  have hx_not_dom : x ∉ effectiveDomain h := by
    intro hx_dom
    exact hx (subset_closure hx_dom)
  have hx_not_frontier : x ∉ frontier (effectiveDomain h) := by
    intro hx_frontier
    exact hx hx_frontier.1
  -- Both branch tests fail outside the closure, so only the exterior branch remains.
  simp [boundaryLiminfExtensionEReal, hx_not_dom, hx_not_frontier]

omit [CompleteSpace H] in
/-- Helper for Proposition 17 9: if `y` lies in the open effective domain and `x` lies in its
closure, then every strict interior point of the segment from `x` to `y` is still in the
effective domain. -/
lemma lineMap_mem_effectiveDomain_of_mem_Ioo_of_mem_closure
    (hopen : IsOpen (effectiveDomain h)) (hconv : Convex ℝ (effectiveDomain h))
    {x : H} (y : effectiveDomain h) (hx : x ∈ closure (effectiveDomain h)) {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    AffineMap.lineMap x y α ∈ effectiveDomain h := by
  have hy_int : (y : H) ∈ interior (effectiveDomain h) := by
    -- Openness upgrades the chosen domain point to an interior point.
    exact mem_interior_iff_mem_nhds.mpr (IsOpen.mem_nhds hopen y.2)
  have hline_int :
      AffineMap.lineMap (y : H) x (1 - α) ∈ interior (effectiveDomain h) := by
    -- Proposition 3.44 keeps the punctured segment inside the interior.
    exact
      lineMap_mem_interior_of_mem_Ico_of_mem_interior_of_mem_closure hconv hy_int hx
        ⟨sub_nonneg.mpr hα.2.le, sub_lt_self 1 hα.1⟩
  -- Reorient the segment back to the `x`-to-`y` parameterization used in the theorem.
  have hline_int' : AffineMap.lineMap x y α ∈ interior (effectiveDomain h) := by
    simpa [AffineMap.lineMap_apply_one_sub] using hline_int
  exact interior_subset hline_int'

omit [CompleteSpace H] in
/-- Helper for Proposition 17 9: a `Γ₀(H)` function agrees with the right-sided segment trace at
every closure point of its effective domain. -/
lemma tendsto_lineMap_to_closure_point_of_mem_gammaZero
    {g : H → Set.Ioi (⊥ : EReal)} {x : H} (hg : g ∈ Γ₀(H))
    (_hx : x ∈ closure (effectiveDomain g)) (y : effectiveDomain g) :
    Filter.Tendsto
      (fun α : ℝ ↦ (g (AffineMap.lineMap x y α) : EReal))
      (𝓝[>] (0 : ℝ))
      (𝓝 (g x : EReal)) := by
  rcases (mem_gammaZero_iff.mp hg) with ⟨hg_lsc, _hg_conv⟩
  by_cases hx_dom : x ∈ effectiveDomain g
  · -- On the finite branch, Proposition 9.14 applies directly to the two effective-domain points.
    exact
      tendsto_apply_lineMap_right_zero_of_lowerSemicontinuous_epigraph_convex
        hg_lsc
        (convex_epigraph_asEReal_of_mem_gammaZero hg)
        (mem_effectiveDomain_iff.mp hx_dom)
        (mem_effectiveDomain_iff.mp y.2)
  · have hx_top : (g x : EReal) = ⊤ := by
      -- Outside the effective domain, a proper `]-∞,+∞]`-valued function can only take `+∞`.
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx_dom))
    rw [hx_top, EReal.tendsto_nhds_top_iff_real]
    intro ξ
    have hline_tendsto :
        Filter.Tendsto (fun α : ℝ ↦ AffineMap.lineMap x y α)
          (𝓝[>] (0 : ℝ))
          (𝓝 x) := by
      -- The affine segment map is continuous and evaluates to `x` at `0`.
      simpa using
        ((AffineMap.lineMap_continuous (p := x) (q := (y : H))).tendsto (0 : ℝ)).mono_left
          nhdsWithin_le_nhds
    have hlevel_closed : IsClosed (lowerLevelSet g.asEReal ξ) := by
      -- Lower semicontinuity of a `Γ₀(H)` function makes every lower level set closed.
      exact (lowerSemicontinuous_iff_isClosed_lowerLevelSet g.asEReal).1 hg_lsc ξ
    have hx_not_level : x ∉ lowerLevelSet g.asEReal ξ := by
      intro hx_level
      rw [mem_lowerLevelSet_iff] at hx_level
      have htop_le : (⊤ : EReal) ≤ (ξ : EReal) := by
        simp [hx_top] at hx_level
      exact (not_le_of_gt (EReal.coe_lt_top ξ)) htop_le
    have havoid :
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), AffineMap.lineMap x y α ∉ lowerLevelSet g.asEReal ξ := by
      -- A path converging to a point outside a closed set eventually stays outside that set.
      exact hline_tendsto.eventually (hlevel_closed.isOpen_compl.mem_nhds hx_not_level)
    -- Leaving the lower level set is exactly the eventual lower bound needed for convergence to
    -- `+∞`.
    exact havoid.mono fun α hα ↦ by
      rw [mem_lowerLevelSet_iff] at hα
      exact lt_of_not_ge hα

include hopen hconv hdiff hcriterion

-- Proof sketch: apply the Chapter 9 segment-limit theorem to the canonical boundary-liminf
-- extension, use that this extension lies in `Γ₀(H)`, and compare its segment trace with the
-- original function `h` on `effectiveDomain h`.
/-- Under the hypotheses of Proposition 17.9, the canonical boundary-liminf extension recovers
the textbook boundary-segment limit formula along every segment from
`x ∈ closure (effectiveDomain h)` to a chosen point `y : effectiveDomain h`. -/
theorem tendsto_lineMap_to_boundaryLiminfExtension
    {x : H} (y : effectiveDomain h) (hx : x ∈ closure (effectiveDomain h)) :
    Filter.Tendsto
      (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal))
      (𝓝[>] (0 : ℝ))
      (𝓝 (boundaryLiminfExtensionEReal h x)) := by
  let hdom_nonempty : (effectiveDomain h).Nonempty := ⟨y, y.2⟩
  let hconvh : ConvexOn h (effectiveDomain h) :=
    convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
      h hdom_nonempty hopen hconv hdiff hcriterion
  let fext : H → Set.Ioi (⊥ : EReal) :=
    boundaryLiminfExtension h hconvh hopen hdiff.continuousOn
  have hfext_gamma : fext ∈ Γ₀(H) :=
    boundaryLiminfExtension_mem_gammaZero h hconvh hopen hdiff.continuousOn
  have hdom_subset : effectiveDomain h ⊆ effectiveDomain fext := by
    intro z hz
    -- On the original effective domain, the extension uses the finite interior branch.
    rw [mem_effectiveDomain_iff, boundaryLiminfExtension_coe]
    simpa [boundaryLiminfExtensionEReal_of_mem_effectiveDomain h hz] using
      (mem_effectiveDomain_iff.mp hz)
  have hy_ext : (y : H) ∈ effectiveDomain fext := hdom_subset y.2
  have hx_ext_closure : x ∈ closure (effectiveDomain fext) := closure_mono hdom_subset hx
  have htrace_ext :
      Filter.Tendsto
        (fun α : ℝ ↦ (fext (AffineMap.lineMap x y α) : EReal))
        (𝓝[>] (0 : ℝ))
        (𝓝 (fext x : EReal)) := by
    -- Route correction: apply the closure-point `Γ₀(H)` segment theorem to the canonical
    -- boundary-liminf extension itself.
    exact
      tendsto_lineMap_to_closure_point_of_mem_gammaZero hfext_gamma hx_ext_closure ⟨(y : H), hy_ext⟩
  have hα_pos : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
    simpa using (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
  have hα_lt_one : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), α < 1 := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hEq :
      (fun α : ℝ ↦ (fext (AffineMap.lineMap x y α) : EReal)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal)) := by
    filter_upwards [hα_pos, hα_lt_one] with α hα_pos hα_lt_one
    have hline_dom : AffineMap.lineMap x y α ∈ effectiveDomain h :=
      lineMap_mem_effectiveDomain_of_mem_Ioo_of_mem_closure
        (h := h) hopen hconv y hx ⟨hα_pos, hα_lt_one⟩
    -- On the punctured segment, the boundary extension agrees with `h` because the trace stays
    -- inside the original effective domain.
    calc
      (fext (AffineMap.lineMap x y α) : EReal)
          = boundaryLiminfExtensionEReal h (AffineMap.lineMap x y α) := by
            rw [boundaryLiminfExtension_coe]
      _ = h (AffineMap.lineMap x y α) :=
        boundaryLiminfExtensionEReal_of_mem_effectiveDomain h hline_dom
  have htrace :
      Filter.Tendsto
        (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal))
        (𝓝[>] (0 : ℝ))
        (𝓝 (fext x : EReal)) :=
    Filter.Tendsto.congr' hEq htrace_ext
  -- The target limit is the explicit `EReal` branch of the same canonical extension.
  simpa [fext, boundaryLiminfExtension_coe] using htrace

-- Proof sketch: on `effectiveDomain h`, the canonical owner uses its interior branch and agrees
-- with `h`; on `closure (effectiveDomain h) \ effectiveDomain h`, the preceding segment-limit
-- theorem identifies the value with the segment liminf; and outside
-- `closure (effectiveDomain h)` the canonical extension is `+∞`.
/-- Under the hypotheses of Proposition 17.9, the canonical boundary-liminf extension is given by
the textbook segment formula determined by a chosen point `y : effectiveDomain h`. -/
theorem boundaryLiminfExtensionEReal_eq_segmentFormula
    (y : effectiveDomain h) :
    boundaryLiminfExtensionEReal h =
      fun x ↦
        if x ∈ effectiveDomain h then
          (h x : EReal)
        else if x ∈ closure (effectiveDomain h) then
          Filter.liminf
            (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        else
          ⊤ := by
  funext x
  by_cases hx_dom : x ∈ effectiveDomain h
  · -- On the effective domain, the explicit boundary extension uses its interior branch.
    simp [hx_dom, boundaryLiminfExtensionEReal_of_mem_effectiveDomain]
  · by_cases hx_closure : x ∈ closure (effectiveDomain h)
    · -- The segment-limit theorem identifies the closure branch with the right-sided liminf.
      have hliminf :
          Filter.liminf
              (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal))
              (nhdsWithin (0 : ℝ) (Set.Ioi 0)) =
            boundaryLiminfExtensionEReal h x := by
        simpa using
          (tendsto_lineMap_to_boundaryLiminfExtension
            (h := h) hopen hconv hdiff hcriterion (x := x) y hx_closure).liminf_eq
      simp [hx_dom, hx_closure, hliminf]
    · -- Outside the closure, the explicit definition is already on the exterior `⊤` branch.
      simp [hx_dom, hx_closure, boundaryLiminfExtensionEReal_eq_top_of_not_mem_closure]

-- Proof sketch: the convexity criterion above and differentiability-implies-continuity reduce the
-- statement to Proposition 9.33 for the boundary-liminf extension.
/-- Under the hypotheses of Proposition 17.9, the canonical boundary-liminf extension belongs to
`Γ₀(H)`. -/
theorem boundaryLiminfExtension_mem_gammaZero_of_criterion
    (hdom_nonempty : (effectiveDomain h).Nonempty) :
    boundaryLiminfExtension h
        (convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
          h hdom_nonempty hopen hconv hdiff hcriterion)
        hopen
        hdiff.continuousOn ∈
      Γ₀(H) := by
  -- Proposition 9.33 applies once the Chapter 17 criterion supplies convexity on the domain.
  exact
    boundaryLiminfExtension_mem_gammaZero h
      (convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
        h hdom_nonempty hopen hconv hdiff hcriterion)
      hopen
      hdiff.continuousOn

-- Proof sketch: on `effectiveDomain h`, the boundary-liminf extension uses its interior branch,
-- so it agrees with `h` and is therefore finite.
/-- Every point of `effectiveDomain h` lies in the effective domain of the canonical
boundary-liminf extension from Proposition 17.9. -/
theorem domain_subset_effectiveDomain_boundaryLiminfExtension
    (hdom_nonempty : (effectiveDomain h).Nonempty) :
    effectiveDomain h ⊆
      effectiveDomain
        (boundaryLiminfExtension h
          (convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
            h hdom_nonempty hopen hconv hdiff hcriterion)
          hopen
          hdiff.continuousOn) := by
  intro x hx
  -- The extension uses the interior branch on `effectiveDomain h`, so the same finite value
  -- witnesses membership in the new effective domain.
  rw [mem_effectiveDomain_iff, boundaryLiminfExtension_coe]
  simpa [boundaryLiminfExtensionEReal_of_mem_effectiveDomain h hx] using
    (mem_effectiveDomain_iff.mp hx)

-- Proof sketch: outside `closure (effectiveDomain h)`, the boundary-liminf extension is on its
-- `+∞` branch, so no such point lies in its effective domain.
/-- The effective domain of the canonical boundary-liminf extension from Proposition 17.9 is
contained in `closure (effectiveDomain h)`. -/
theorem effectiveDomain_boundaryLiminfExtension_subset_closure
    (hdom_nonempty : (effectiveDomain h).Nonempty) :
    effectiveDomain
        (boundaryLiminfExtension h
          (convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
            h hdom_nonempty hopen hconv hdiff hcriterion)
          hopen
          hdiff.continuousOn) ⊆
      closure (effectiveDomain h) := by
  intro x hx
  by_contra hx_not_closure
  have hx_top :
      (boundaryLiminfExtension h
        (convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
          h hdom_nonempty hopen hconv hdiff hcriterion)
        hopen
        hdiff.continuousOn x : EReal) = ⊤ := by
    rw [boundaryLiminfExtension_coe]
    exact boundaryLiminfExtensionEReal_eq_top_of_not_mem_closure (h := h) hx_not_closure
  have hx_finite :
      (boundaryLiminfExtension h
        (convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
          h hdom_nonempty hopen hconv hdiff hcriterion)
        hopen
        hdiff.continuousOn x : EReal) < ⊤ :=
    mem_effectiveDomain_iff.mp hx
  exact (not_lt_of_ge le_top) (hx_top ▸ hx_finite)

-- Proof sketch: on `effectiveDomain h`, the extension is given by the interior branch of the
-- boundary-liminf construction, which is exactly `h`.
/-- On `effectiveDomain h`, the canonical boundary-liminf extension from Proposition 17.9 agrees
with the original function `h`. -/
theorem boundaryLiminfExtension_eqOn_domain
    (hdom_nonempty : (effectiveDomain h).Nonempty) :
    EqOn
      (boundaryLiminfExtension h
        (convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
          h hdom_nonempty hopen hconv hdiff hcriterion)
        hopen
        hdiff.continuousOn)
      h
      (effectiveDomain h) := by
  intro x hx
  apply Subtype.ext
  -- On the effective domain, the extension coincides with the original function by construction.
  rw [boundaryLiminfExtension_coe, boundaryLiminfExtensionEReal_of_mem_effectiveDomain h hx]

end Proposition_17_9

end ERealFunction
