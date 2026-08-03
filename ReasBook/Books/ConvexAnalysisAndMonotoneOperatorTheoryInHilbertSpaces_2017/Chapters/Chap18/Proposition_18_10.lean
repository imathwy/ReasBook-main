import Mathlib
import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap01.Text_1_0_10
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Corollary_16_30
import BauschkeLean.Chap17.Proposition_17_6
import BauschkeLean.Chap17.Proposition_17_39.Index

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityAndStrictConvexity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (gradf : H → H)

/-- Helper for Proposition 18 10: a Gâteaux derivative within a set already determines the
whole-space Gâteaux derivative, because only the radial-segment witness changes. -/
lemma hasGateauxDerivativeAt_of_hasGateauxDerivativeWithinAt
    {T : H → ℝ} {A : H →L[ℝ] ℝ} {C : Set H} {x : H}
    (hA : HasGateauxDerivativeWithinAt T A C x) :
    HasGateauxDerivativeAt T A x := by
  exact ⟨hasRadialSegmentsAt_univ x, hA.2⟩

/-- Helper for Proposition 18 10: at finite values, the affine `EReal` subgradient inequality is
equivalent to the corresponding real inequality on `toReal`. -/
lemma ereal_affine_ineq_iff_inner_le_toReal_sub
    {x y u : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    (((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal)) ↔
      (⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal)) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hsub :
      (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) =
        (f y : EReal) - (f x : EReal) := by
    -- Rewriting both finite values through `toReal` turns the subtraction into a real one.
    calc
      (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) =
          (((f y : EReal).toReal : EReal) - (((f x : EReal).toReal : EReal))) := by
            rw [EReal.coe_sub]
      _ = (f y : EReal) - (f x : EReal) := by
        rw [EReal.coe_toReal hy_top hy_bot, EReal.coe_toReal hx_top hx_bot]
  constructor
  · intro hineq
    -- Move `f x` to the right and read the resulting finite inequality in `ℝ`.
    have hsubineq : (⟪y - x, u⟫_ℝ : EReal) ≤ (f y : EReal) - (f x : EReal) := by
      exact (EReal.le_sub_iff_add_le (.inl hx_bot) (.inl hx_top)).2 hineq
    have hcast :
        (⟪y - x, u⟫_ℝ : EReal) ≤
          (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) := by
      simpa [hsub] using hsubineq
    exact_mod_cast hcast
  · intro hineq
    -- Cast the real inequality back to `EReal`, then undo the subtraction transport.
    have hcast :
        (⟪y - x, u⟫_ℝ : EReal) ≤
          (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) := by
      exact_mod_cast hineq
    have hsubineq : (⟪y - x, u⟫_ℝ : EReal) ≤ (f y : EReal) - (f x : EReal) := by
      simpa [hsub] using hcast
    exact (EReal.le_sub_iff_add_le (.inl hx_bot) (.inl hx_top)).1 hsubineq

/-- Helper for Proposition 18 10: along any fixed direction, an interior effective-domain point
stays in the effective domain for all sufficiently small positive steps. -/
lemma eventually_mem_effectiveDomain_along_ray_of_mem_interior
    {x d : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • d ∈ effectiveDomain f := by
  -- Openness of the interior turns a short ray from `x` into an effective-domain certificate.
  have hinterior : interior (effectiveDomain f) ∈ nhds x := isOpen_interior.mem_nhds hx
  rcases Metric.mem_nhds_iff.mp hinterior with ⟨r, hr, hrball⟩
  have hcont : ContinuousAt (fun α : ℝ ↦ x + α • d) 0 := by
    simpa using (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hball_nhds : Metric.ball x r ∈ nhds x := Metric.ball_mem_nhds x hr
  have hball_nhds0 : Metric.ball x r ∈ nhds ((fun α : ℝ ↦ x + α • d) 0) := by
    simpa using hball_nhds
  have hevent_ball : ∀ᶠ α : ℝ in nhds 0, x + α • d ∈ Metric.ball x r := by
    exact hcont hball_nhds0
  have hevent_ball_within :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • d ∈ Metric.ball x r :=
    nhdsWithin_le_nhds hevent_ball
  filter_upwards [hevent_ball_within] with α hα
  exact interior_subset (hrball hα)

/-- Helper for Proposition 18 10: every subgradient at an interior effective-domain point is
dominated by the Gâteaux gradient on each direction. -/
lemma subgradient_inner_le_gateauxGradient_of_mem_interior_effectiveDomain
    {x u g y : H} (hx : x ∈ interior (effectiveDomain f)) (hu : u ∈ (∂ f) x)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H g) x) :
    ⟪y, u⟫_ℝ ≤ ⟪y, g⟫_ℝ := by
  have hx_eff : x ∈ effectiveDomain f := interior_subset hx
  have hquot_tendsto :
      Filter.Tendsto
        (fun α : ℝ ↦
          (((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪y, g⟫_ℝ) := by
    -- The Gâteaux derivative identifies the one-sided secant-slope limit in direction `y`.
    simpa [one_div, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm, real_inner_comm,
      toDual_apply_eq_toDualMap_apply, toDualMap_apply_apply] using
      hgrad.tendsto_directionalDifferenceQuotient y
  have hquot_ge :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ⟪y, u⟫_ℝ ≤
          (((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) := by
    have hevent :
        ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • y ∈ effectiveDomain f :=
      eventually_mem_effectiveDomain_along_ray_of_mem_interior (f := f) (x := x) (d := y) hx
    filter_upwards [hevent, self_mem_nhdsWithin] with α hαdom hα
    have hineq :
        ⟪(x + α • y) - x, u⟫_ℝ ≤
          (f (x + α • y) : EReal).toReal - (f x : EReal).toReal := by
      exact
        (ereal_affine_ineq_iff_inner_le_toReal_sub
          (f := f) (x := x) (y := x + α • y) (u := u) hx_eff hαdom).1
          ((mem_subdifferential_iff (f := f) (x := x) (u := u)).1 hu (x + α • y))
    have hscaled :
        α * ⟪y, u⟫_ℝ ≤ (f (x + α • y) : EReal).toReal - (f x : EReal).toReal := by
      -- Expand the secant step so the positive scalar `α` can be divided out.
      simpa [sub_eq_add_neg, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
        inner_add_left, inner_smul_left, inner_sub_left] using hineq
    exact (le_div_iff₀ hα).2 (by simpa [mul_comm] using hscaled)
  -- Passing the subgradient inequalities to the limit compares `u` with the Gâteaux gradient.
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hquot_tendsto hquot_ge

/-- Helper for Proposition 18 10: at an interior effective-domain point, a Gâteaux gradient makes
the subdifferential a singleton with that value. -/
lemma subdifferential_eq_singleton_at_interior_of_hasGateauxDerivativeAt
    (hf0 : f ∈ Γ₀(H))
    {x g : H}
    (hx : x ∈ interior (effectiveDomain f))
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H g) x) :
    (∂ f) x = ({g} : Set H) := by
  have hgrad_mem : g ∈ (∂ f) x := by
    -- Proposition 17.6 gives the gradient as a distinguished subgradient.
    exact gateauxGradient_mem_subdifferential f hf0.2 (interior_subset hx) g hgrad
  refine Set.Subset.antisymm ?_ ?_
  · intro u hu
    have hu_eq : u = g := by
      -- Compare `u` and `g` against every direction and use inner-product extensionality.
      apply ext_inner_left ℝ
      intro y
      have hy_le :
          ⟪y, u⟫_ℝ ≤ ⟪y, g⟫_ℝ := by
        exact
          subgradient_inner_le_gateauxGradient_of_mem_interior_effectiveDomain
            (f := f) hx hu hgrad
      have hneg_le :
          ⟪-y, u⟫_ℝ ≤ ⟪-y, g⟫_ℝ := by
        exact
          subgradient_inner_le_gateauxGradient_of_mem_interior_effectiveDomain
            (f := f) hx hu hgrad
      have hy_ge :
          ⟪y, g⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
        simpa using hneg_le
      exact le_antisymm hy_le hy_ge
    simp [hu_eq]
  · intro u hu
    rw [Set.mem_singleton_iff] at hu
    simpa [hu] using hgrad_mem

/-- Helper for Proposition 18 10: at an interior effective-domain point, the prescribed
Gâteaux derivative field makes the subdifferential a singleton with value `gradf x`. -/
lemma subdifferential_eq_singleton_of_hasGateauxDerivativeOn_mem_interior_effectiveDomain
    (hf0 : f ∈ Γ₀(H))
    {x : H}
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradf x))
        (interior (effectiveDomain f)))
    (hx : x ∈ interior (effectiveDomain f)) :
    (∂ f) x = ({gradf x} : Set H) := by
  have hgradAt :
      HasGateauxDerivativeAt
        (fun y ↦ (f y : EReal).toReal) (toDualMap ℝ H (gradf x)) x := by
    -- Upgrade the within-domain derivative to a whole-space derivative at the interior point.
    exact hasGateauxDerivativeAt_of_hasGateauxDerivativeWithinAt (hgrad x hx)
  simpa using
    subdifferential_eq_singleton_at_interior_of_hasGateauxDerivativeAt
      (f := f) hf0 (x := x) (g := gradf x) hx hgradAt

/-- Helper for Proposition 18 10: a subgradient point for `f` lies in the effective domain of the
Fenchel conjugate `f*`, represented by `f∗[hf]`. -/
lemma gammaZeroConjugate_mem_effectiveDomain_of_mem_subgradient
    {x u : H} (hu : u ∈ (∂ f) x) :
    u ∈ effectiveDomain (f∗[hf]) := by
  have hx_dom : x ∈ effectiveDomain f := by
    have hx_subdom : x ∈ SetValuedOperator.dom (∂ f) := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨u, hu⟩
    exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf hx_subdom
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hfy :
      (f x : EReal) + (f∗[hf] u : EReal) =
        ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
    simpa [gammaZeroConjugate_apply] using
      (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty x u).1 hu
  have hfu_top : (f∗[hf] u : EReal) ≠ ⊤ := by
    intro hfu_top
    have hsum_top : (f x : EReal) + (f∗[hf] u : EReal) = ⊤ := by
      rw [hfu_top]
      exact EReal.add_top_of_ne_bot hfx_bot
    exact EReal.coe_ne_top _ <| by
      calc
        (((⟪x, u⟫_ℝ : ℝ) : EReal)) = (f x : EReal) + (f∗[hf] u : EReal) := by
          simpa using hfy.symm
        _ = ⊤ := hsum_top
  -- Effective-domain membership is exactly finiteness for `]-∞,+∞]`-valued functions.
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_ne le_top hfu_top

/-- Helper for Proposition 18 10: Fenchel--Young equality along `∂ f(x)` becomes a real-valued
formula for the conjugate trace. -/
lemma gammaZeroConjugate_toReal_eq_inner_sub_of_mem_subgradient
    {x u : H} (hu : u ∈ (∂ f) x) :
    (f∗[hf] u : EReal).toReal = ⟪x, u⟫_ℝ - (f x : EReal).toReal := by
  have hx_dom : x ∈ effectiveDomain f := by
    have hx_subdom : x ∈ SetValuedOperator.dom (∂ f) := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨u, hu⟩
    exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf hx_subdom
  have hu_dom : u ∈ effectiveDomain (f∗[hf]) :=
    gammaZeroConjugate_mem_effectiveDomain_of_mem_subgradient (f := f) hf hu
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_dom)
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hfu_top : (f∗[hf] u : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hu_dom)
  have hfu_bot : (f∗[hf] u : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f∗[hf] u : EReal) from (f∗[hf] u).2)
  have hfy :
      (f x : EReal) + (f∗[hf] u : EReal) =
        ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
    simpa [gammaZeroConjugate_apply] using
      (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty x u).1 hu
  have hfy' := hfy
  rw [← EReal.coe_toReal hfx_top hfx_bot, ← EReal.coe_toReal hfu_top hfu_bot,
    ← EReal.coe_add] at hfy'
  have hfy_toReal :
      (f x : EReal).toReal + (f∗[hf] u : EReal).toReal = ⟪x, u⟫_ℝ := by
    exact EReal.coe_eq_coe_iff.mp hfy'
  linarith

/-- Helper for Proposition 18 10: the gradient image over `interior (effectiveDomain f)` lies in
the effective domain of the Fenchel conjugate `f*`, represented by `f∗[hf]`. -/
lemma gradientImage_subset_effectiveDomain_gammaZeroConjugate_of_hasGateauxDerivativeOn
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradf x))
        (interior (effectiveDomain f))) :
    gradf '' interior (effectiveDomain f) ⊆ effectiveDomain (f∗[hf]) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hsub :
      (∂ f) x = ({gradf x} : Set H) :=
    subdifferential_eq_singleton_of_hasGateauxDerivativeOn_mem_interior_effectiveDomain
      (f := f) (hf0 := hf) (gradf := gradf) hgrad hx
  have hmem : gradf x ∈ (∂ f) x := by
    simp [hsub]
  exact gammaZeroConjugate_mem_effectiveDomain_of_mem_subgradient hf hmem

/-- Helper for Proposition 18 10: if a convex real-valued trace on `[0,1]` meets its endpoint
chord at one interior point, then the trace agrees with that chord on all of `[0,1]`. -/
lemma eq_lineMap_on_Icc_of_convex_eq_at_interior
    {φ : ℝ → ℝ}
    (hφ : _root_.ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (hEq : φ γ = AffineMap.lineMap (φ 0) (φ 1) γ) :
    Set.EqOn φ (AffineMap.lineMap (φ 0) (φ 1)) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  let ℓ : ℝ → ℝ := fun s ↦ AffineMap.lineMap (φ 0) (φ 1) s
  let ψ : ℝ → ℝ := fun s ↦ ℓ s - φ s
  have hline_convex : _root_.ConvexOn ℝ (Set.Icc (0 : ℝ) 1) ℓ := by
    rw [convexOn_iff_forall_pos]
    constructor
    · exact convex_Icc (0 : ℝ) 1
    · intro x hx y hy a b ha hb hab
      have hab' : b = 1 - a := by
        linarith
      have hEqLine : ℓ (a * x + b * y) = a * ℓ x + b * ℓ y := by
        simp [ℓ, AffineMap.lineMap_apply_module, hab', sub_eq_add_neg, mul_add, add_mul]
        ring
      simpa [smul_eq_mul] using le_of_eq hEqLine
  have hline_concave : _root_.ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) ℓ := by
    rw [concaveOn_iff_forall_pos]
    constructor
    · exact convex_Icc (0 : ℝ) 1
    · intro x hx y hy a b ha hb hab
      have hab' : b = 1 - a := by
        linarith
      have hEqLine : ℓ (a * x + b * y) = a * ℓ x + b * ℓ y := by
        simp [ℓ, AffineMap.lineMap_apply_module, hab', sub_eq_add_neg, mul_add, add_mul]
        ring
      simpa [smul_eq_mul] using ge_of_eq hEqLine
  have hdefect : _root_.ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) ψ := by
    exact hline_concave.sub hφ
  have hzero_nonneg :
      ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ ψ s := by
    intro s hs
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      simp
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      simp
    have hle :
        φ ((1 - s) • (0 : ℝ) + s • (1 : ℝ)) ≤
          (1 - s) • φ 0 + s • φ 1 := by
      exact hφ.2 h0 h1 (sub_nonneg.mpr hs.2) hs.1 (by ring)
    simpa [ψ, ℓ, AffineMap.lineMap_apply_module, smul_eq_mul, sub_eq_add_neg] using hle
  have hψ_zero : ψ 0 = 0 := by
    simp [ψ, ℓ]
  have hψ_one : ψ 1 = 0 := by
    simp [ψ, ℓ]
  have hψ_gamma : ψ γ = 0 := by
    simp [ψ, ℓ, hEq]
  by_cases htγ : t ≤ γ
  · have ht_le : ψ t ≤ ψ γ := by
      exact
        hdefect.left_le_of_le_right'' (y := γ) ht (by simp) htγ hγ.2
          (by simp [hψ_one, hψ_gamma])
    have ht_nonneg : 0 ≤ ψ t := hzero_nonneg ht
    have ht_zero : ψ t = 0 := by
      linarith
    have ht_eq : φ t = ℓ t := by
      linarith
    simpa [ℓ] using ht_eq
  · have hγt : γ ≤ t := by
      linarith
    have ht_le : ψ t ≤ ψ γ := by
      exact
        hdefect.right_le_of_le_left'' (y := γ) (by simp) ht hγ.1 hγt
          (by simp [hψ_zero, hψ_gamma])
    have ht_nonneg : 0 ≤ ψ t := hzero_nonneg ht
    have ht_zero : ψ t = 0 := by
      linarith
    have ht_eq : φ t = ℓ t := by
      linarith
    simpa [ℓ] using ht_eq

/- Source/core/bridge triage:
- `source-facing`: Proposition 18.10 is the strict-convexity statement on the gradient image
  `gradf '' interior (effectiveDomain f)`.
- `core/canonical`: the owner object on the `f` side is the subdifferential `∂ f` together with
  its canonical range `SetValuedOperator.range (∂ f)`.
- `bridge/view`: the gradient image identifies with that range under
  `SetValuedOperator.dom (∂ f) = interior (effectiveDomain f)`, and Corollary 16.30 plus
  `SetValuedOperator.dom_inverse` transport this owner-level statement to
  `SetValuedOperator.dom (∂ (f∗[hf]))` when needed downstream.

This file therefore stays source-facing: it keeps the gradient-image strict-convexity statement as
the main public result and records only the owner-level range bridges needed by the later
conjugate-domain reformulation. -/

-- Proof sketch: if `y = gradf x` with `x ∈ interior (effectiveDomain f)`, then Proposition 17.31
-- identifies `(∂ f) x` with `{gradf x}`, hence `y ∈ SetValuedOperator.range (∂ f)`. Conversely,
-- if `y ∈ SetValuedOperator.range (∂ f)`, choose `x` with `y ∈ (∂ f) x`. Then
-- `x ∈ SetValuedOperator.dom (∂ f) = interior (effectiveDomain f)`, and Proposition 17.31 (1)
-- identifies the subdifferential at `x` with `{gradf x}`, so `y = gradf x`.
/-- If `f ∈ Γ₀(H)` has `dom (∂ f) = interior (effectiveDomain f)` and an explicit Gâteaux
gradient field `gradf` on `interior (effectiveDomain f)`, then the range of the
subdifferential of `f` is exactly the gradient image `gradf '' interior (effectiveDomain f)`. -/
theorem range_subdifferential_eq_gradientImage_of_hasGateauxDerivativeOn
    (hf0 : f ∈ Γ₀(H))
    (hdom : SetValuedOperator.dom (∂ f) = interior (effectiveDomain f))
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradf x))
        (interior (effectiveDomain f))) :
    SetValuedOperator.range (∂ f) = gradf '' interior (effectiveDomain f) := by
  ext y
  constructor
  · intro hy
    rcases (SetValuedOperator.mem_range_iff (∂ f) y).1 hy with ⟨x, hyx⟩
    have hxdom : x ∈ SetValuedOperator.dom (∂ f) :=
      (SetValuedOperator.mem_dom_iff (∂ f) x).2 ⟨y, hyx⟩
    have hx :
        x ∈ interior (effectiveDomain f) := by
      simpa [hdom] using hxdom
    have hsub :
        (∂ f) x = ({gradf x} : Set H) :=
      subdifferential_eq_singleton_of_hasGateauxDerivativeOn_mem_interior_effectiveDomain
        (f := f) (hf0 := hf0) (gradf := gradf) hgrad hx
    have hy_eq : y = gradf x := by
      simpa [hsub] using hyx
    exact ⟨x, hx, hy_eq.symm⟩
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    have hsub :
        (∂ f) x = ({gradf x} : Set H) :=
      subdifferential_eq_singleton_of_hasGateauxDerivativeOn_mem_interior_effectiveDomain
        (f := f) (hf0 := hf0) (gradf := gradf) hgrad hx
    have hmem : gradf x ∈ (∂ f) x := by
      simp [hsub]
    exact (SetValuedOperator.mem_range_iff (∂ f) (gradf x)).2 ⟨x, hmem⟩

/-- Helper for Proposition 18 10: one interior point of `∂ f*` together with affine trace data on
`[u₀,u₁]` forces both endpoints into `∂ f(x)`. -/
lemma endpoint_mem_subgradient_of_affine_conjugate_trace
    {x u0 u1 : H} {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hfin : segment ℝ u0 u1 ⊆ effectiveDomain (f∗[hf]))
    (haff :
      Set.EqOn
        (fun β : ℝ ↦ (f∗[hf] (AffineMap.lineMap u0 u1 β) : EReal).toReal)
        (AffineMap.lineMap
          ((f∗[hf] u0 : EReal).toReal)
          ((f∗[hf] u1 : EReal).toReal))
        (Set.Icc (0 : ℝ) 1))
    (hxconj : x ∈ (∂ (f∗[hf])) (AffineMap.lineMap u0 u1 α)) :
    u0 ∈ (∂ f) x ∧ u1 ∈ (∂ f) x := by
  let m : H := AffineMap.lineMap u0 u1 α
  -- Route correction: first transport the interior `∂ f*` datum back to `∂ f`, then compare the
  -- affine trace with the endpoint Fenchel--Young inequalities in real form.
  have hm_sub : m ∈ (∂ f) x := by
    rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate (f := f) hf] at hxconj
    simpa [m, SetValuedOperator.mem_inverse_iff] using hxconj
  have hα_Icc : α ∈ Set.Icc (0 : ℝ) 1 := ⟨hα.1.le, hα.2.le⟩
  have hx_dom : x ∈ effectiveDomain f := by
    have hx_subdom : x ∈ SetValuedOperator.dom (∂ f) := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨m, hm_sub⟩
    exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf hx_subdom
  have hu0_dom : u0 ∈ effectiveDomain (f∗[hf]) := hfin <| by
    simpa using left_mem_segment (𝕜 := ℝ) u0 u1
  have hu1_dom : u1 ∈ effectiveDomain (f∗[hf]) := hfin <| by
    simpa using right_mem_segment (𝕜 := ℝ) u0 u1
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_dom)
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hu0_top : (f∗[hf] u0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hu0_dom)
  have hu1_top : (f∗[hf] u1 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hu1_dom)
  have hu0_bot : (f∗[hf] u0 : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f∗[hf] u0 : EReal) from (f∗[hf] u0).2)
  have hu1_bot : (f∗[hf] u1 : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f∗[hf] u1 : EReal) from (f∗[hf] u1).2)
  have hmid_trace :
      (f∗[hf] m : EReal).toReal =
        AffineMap.lineMap
          ((f∗[hf] u0 : EReal).toReal)
          ((f∗[hf] u1 : EReal).toReal) α := by
    simpa [m] using haff hα_Icc
  have hmid_affine :
      (f∗[hf] m : EReal).toReal =
        (1 - α) * ((f∗[hf] u0 : EReal).toReal) + α * ((f∗[hf] u1 : EReal).toReal) := by
    calc
      (f∗[hf] m : EReal).toReal =
          AffineMap.lineMap
            ((f∗[hf] u0 : EReal).toReal)
            ((f∗[hf] u1 : EReal).toReal) α := hmid_trace
      _ = (1 - α) * ((f∗[hf] u0 : EReal).toReal) + α * ((f∗[hf] u1 : EReal).toReal) := by
        simp [AffineMap.lineMap_apply_module, smul_eq_mul, sub_eq_add_neg, add_comm]
  have hmid_formula :
      (f∗[hf] m : EReal).toReal = ⟪x, m⟫_ℝ - (f x : EReal).toReal :=
    gammaZeroConjugate_toReal_eq_inner_sub_of_mem_subgradient (f := f) hf hm_sub
  have hmid_linear :
      ⟪x, m⟫_ℝ - (f x : EReal).toReal =
        (1 - α) * (⟪x, u0⟫_ℝ - (f x : EReal).toReal) +
          α * (⟪x, u1⟫_ℝ - (f x : EReal).toReal) := by
    calc
      ⟪x, m⟫_ℝ - (f x : EReal).toReal =
          (1 - α) * ⟪x, u0⟫_ℝ + α * ⟪x, u1⟫_ℝ - (f x : EReal).toReal := by
            simp [m, AffineMap.lineMap_apply_module, inner_add_right, inner_smul_right,
              sub_eq_add_neg, add_mul, add_comm]
      _ = (1 - α) * (⟪x, u0⟫_ℝ - (f x : EReal).toReal) +
            α * (⟪x, u1⟫_ℝ - (f x : EReal).toReal) := by
            ring
  -- Fenchel--Young gives the endpoint inequalities, and finiteness converts them to real bounds.
  have hfy0 :
      ((⟪x, u0⟫_ℝ : ℝ) : EReal) ≤ (f x : EReal) + (f∗[hf] u0 : EReal) := by
    simpa [gammaZeroConjugate_apply] using
      (fenchel_young_inequality (isProper_of_mem_gammaZero hf) x u0)
  have hfy1 :
      ((⟪x, u1⟫_ℝ : ℝ) : EReal) ≤ (f x : EReal) + (f∗[hf] u1 : EReal) := by
    simpa [gammaZeroConjugate_apply] using
      (fenchel_young_inequality (isProper_of_mem_gammaZero hf) x u1)
  have hfy0_toReal :
      ⟪x, u0⟫_ℝ ≤ (f x : EReal).toReal + (f∗[hf] u0 : EReal).toReal := by
    have hfy0' := hfy0
    rw [← EReal.coe_toReal hfx_top hfx_bot, ← EReal.coe_toReal hu0_top hu0_bot,
      ← EReal.coe_add] at hfy0'
    exact_mod_cast hfy0'
  have hfy1_toReal :
      ⟪x, u1⟫_ℝ ≤ (f x : EReal).toReal + (f∗[hf] u1 : EReal).toReal := by
    have hfy1' := hfy1
    rw [← EReal.coe_toReal hfx_top hfx_bot, ← EReal.coe_toReal hu1_top hu1_bot,
      ← EReal.coe_add] at hfy1'
    exact_mod_cast hfy1'
  have hweighted :
      (1 - α) *
          (((f∗[hf] u0 : EReal).toReal) - (⟪x, u0⟫_ℝ - (f x : EReal).toReal)) +
        α * (((f∗[hf] u1 : EReal).toReal) - (⟪x, u1⟫_ℝ - (f x : EReal).toReal)) = 0 := by
    linarith [hmid_affine, hmid_formula, hmid_linear]
  have hδ0_nonneg :
      0 ≤ ((f∗[hf] u0 : EReal).toReal) - (⟪x, u0⟫_ℝ - (f x : EReal).toReal) := by
    linarith
  have hδ1_nonneg :
      0 ≤ ((f∗[hf] u1 : EReal).toReal) - (⟪x, u1⟫_ℝ - (f x : EReal).toReal) := by
    linarith
  have hδ0_zero :
      ((f∗[hf] u0 : EReal).toReal) - (⟪x, u0⟫_ℝ - (f x : EReal).toReal) = 0 := by
    have hα_pos : 0 < α := hα.1
    have h_one_sub_pos : 0 < 1 - α := by
      linarith [hα.2]
    have hα_nonneg : 0 ≤ α := hα_pos.le
    have hδ1_scaled_nonneg :
        0 ≤ α * (((f∗[hf] u1 : EReal).toReal) - (⟪x, u1⟫_ℝ - (f x : EReal).toReal)) := by
      exact mul_nonneg hα_nonneg hδ1_nonneg
    by_contra hδ0_ne
    have hδ0_pos :
        0 < ((f∗[hf] u0 : EReal).toReal) - (⟪x, u0⟫_ℝ - (f x : EReal).toReal) := by
      exact lt_of_le_of_ne hδ0_nonneg (by simpa [eq_comm] using hδ0_ne)
    have hδ0_scaled_pos :
        0 <
          (1 - α) * (((f∗[hf] u0 : EReal).toReal) - (⟪x, u0⟫_ℝ - (f x : EReal).toReal)) := by
      exact mul_pos h_one_sub_pos hδ0_pos
    linarith [hweighted, hδ1_scaled_nonneg, hδ0_scaled_pos]
  have hδ1_zero :
      ((f∗[hf] u1 : EReal).toReal) - (⟪x, u1⟫_ℝ - (f x : EReal).toReal) = 0 := by
    have hα_pos : 0 < α := hα.1
    have h_one_sub_pos : 0 < 1 - α := by
      linarith [hα.2]
    have h_one_sub_nonneg : 0 ≤ 1 - α := h_one_sub_pos.le
    have hδ0_scaled_nonneg :
        0 ≤
          (1 - α) * (((f∗[hf] u0 : EReal).toReal) - (⟪x, u0⟫_ℝ - (f x : EReal).toReal)) := by
      exact mul_nonneg h_one_sub_nonneg hδ0_nonneg
    by_contra hδ1_ne
    have hδ1_pos :
        0 < ((f∗[hf] u1 : EReal).toReal) - (⟪x, u1⟫_ℝ - (f x : EReal).toReal) := by
      exact lt_of_le_of_ne hδ1_nonneg (by simpa [eq_comm] using hδ1_ne)
    have hδ1_scaled_pos :
        0 <
          α * (((f∗[hf] u1 : EReal).toReal) - (⟪x, u1⟫_ℝ - (f x : EReal).toReal)) := by
      exact mul_pos hα.1 hδ1_pos
    linarith [hweighted, hδ0_scaled_nonneg, hδ1_scaled_pos]
  have hsum0_real :
      (f x : EReal).toReal + (f∗[hf] u0 : EReal).toReal = ⟪x, u0⟫_ℝ := by
    linarith
  have hsum1_real :
      (f x : EReal).toReal + (f∗[hf] u1 : EReal).toReal = ⟪x, u1⟫_ℝ := by
    linarith
  have hfy0_eq :
      (f x : EReal) + (f∗[hf] u0 : EReal) = ((⟪x, u0⟫_ℝ : ℝ) : EReal) := by
    have hsum0_coe :
        (((f x : EReal).toReal + (f∗[hf] u0 : EReal).toReal : ℝ) : EReal) =
          (f x : EReal) + (f∗[hf] u0 : EReal) := by
      calc
        (((f x : EReal).toReal + (f∗[hf] u0 : EReal).toReal : ℝ) : EReal) =
            (((f x : EReal).toReal : EReal) + ((f∗[hf] u0 : EReal).toReal : EReal)) := by
              rw [EReal.coe_add]
        _ = (f x : EReal) + (f∗[hf] u0 : EReal) := by
              rw [EReal.coe_toReal hfx_top hfx_bot, EReal.coe_toReal hu0_top hu0_bot]
    calc
      (f x : EReal) + (f∗[hf] u0 : EReal) =
          (((f x : EReal).toReal + (f∗[hf] u0 : EReal).toReal : ℝ) : EReal) := by
            simpa using hsum0_coe.symm
      _ = ((⟪x, u0⟫_ℝ : ℝ) : EReal) := by
        exact_mod_cast hsum0_real
  have hfy1_eq :
      (f x : EReal) + (f∗[hf] u1 : EReal) = ((⟪x, u1⟫_ℝ : ℝ) : EReal) := by
    have hsum1_coe :
        (((f x : EReal).toReal + (f∗[hf] u1 : EReal).toReal : ℝ) : EReal) =
          (f x : EReal) + (f∗[hf] u1 : EReal) := by
      calc
        (((f x : EReal).toReal + (f∗[hf] u1 : EReal).toReal : ℝ) : EReal) =
            (((f x : EReal).toReal : EReal) + ((f∗[hf] u1 : EReal).toReal : EReal)) := by
              rw [EReal.coe_add]
        _ = (f x : EReal) + (f∗[hf] u1 : EReal) := by
              rw [EReal.coe_toReal hfx_top hfx_bot, EReal.coe_toReal hu1_top hu1_bot]
    calc
      (f x : EReal) + (f∗[hf] u1 : EReal) =
          (((f x : EReal).toReal + (f∗[hf] u1 : EReal).toReal : ℝ) : EReal) := by
            simpa using hsum1_coe.symm
      _ = ((⟪x, u1⟫_ℝ : ℝ) : EReal) := by
        exact_mod_cast hsum1_real
  constructor
  · exact (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty x u0).2 <| by
      simpa [gammaZeroConjugate_apply] using hfy0_eq
  · exact (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty x u1).2 <| by
      simpa [gammaZeroConjugate_apply] using hfy1_eq

/-- Helper for Proposition 18 10: affine trace data for `f*` on a closed segment and one interior
image point of `∂ f*` force the whole segment into `∂ f(x)`. -/
lemma segment_subset_subgradient_of_affine_conjugate_trace_of_mem_image_openSegment
    (x u0 u1 : H)
    (hfin : segment ℝ u0 u1 ⊆ effectiveDomain (f∗[hf]))
    (haff :
      Set.EqOn
        (fun α : ℝ ↦ (f∗[hf] (AffineMap.lineMap u0 u1 α) : EReal).toReal)
        (AffineMap.lineMap
          ((f∗[hf] u0 : EReal).toReal)
          ((f∗[hf] u1 : EReal).toReal))
        (Set.Icc (0 : ℝ) 1))
    (hint : x ∈ SetValuedOperator.image (∂ (f∗[hf])) (openSegment ℝ u0 u1)) :
    segment ℝ u0 u1 ⊆ (∂ f) x := by
  rcases (SetValuedOperator.mem_image (∂ (f∗[hf])) (openSegment ℝ u0 u1) x).1 hint with
    ⟨m, hm_open, hxconj⟩
  rw [openSegment_eq_image_lineMap] at hm_open
  rcases hm_open with ⟨α, hα, rfl⟩
  rcases endpoint_mem_subgradient_of_affine_conjugate_trace
      (f := f) hf hα hfin haff hxconj with ⟨hu0, hu1⟩
  -- Convexity of the subdifferential fiber upgrades endpoint membership to the whole segment.
  exact (convex_subdifferential f x).segment_subset hu0 hu1

/-- Helper for Proposition 18 10: a set containing a closed segment contains both endpoints. -/
lemma endpoints_mem_of_segment_subset
    {s : Set H} {u v : H} (hseg : segment ℝ v u ⊆ s) :
    v ∈ s ∧ u ∈ s := by
  constructor
  · -- The left endpoint belongs to every closed segment.
    exact hseg <| by simpa using left_mem_segment (𝕜 := ℝ) v u
  · -- The right endpoint belongs to every closed segment.
    exact hseg <| by simpa using right_mem_segment (𝕜 := ℝ) v u

-- Proof sketch: if `f*` were affine on a nontrivial segment inside a convex set `C`, then every
-- interior point of that segment would still belong to `C` and hence to the gradient image
-- `gradf '' interior (effectiveDomain f)`. Choose `x` in the interior effective domain with
-- `gradf x` on the open segment. Proposition 17.31 identifies `gradf x` with the unique
-- subgradient of `f` at `x`, so Corollary 16.30 puts `x` in the subdifferential of `f*` at
-- `gradf x`. Proposition 16.37 (2) then forces the whole segment into `(∂ f) x`, contradicting
-- the singleton subdifferential furnished by Gâteaux differentiability at `x`.
/-- Proposition 18 10: if `f ∈ Γ₀(H)` and `gradf` is a Gâteaux gradient field of the finite-valued
representative of `f` on `interior (effectiveDomain f)`, then the Fenchel conjugate `f*`,
represented by `f∗[hf]`, is strictly convex on every nonempty convex subset of the
gradient image `gradf '' interior (effectiveDomain f)`. -/
theorem gammaZeroConjugate_strictlyConvexOn_of_hasGateauxDerivativeOn
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradf x))
        (interior (effectiveDomain f)))
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C)
    (hC_subset : C ⊆ gradf '' interior (effectiveDomain f)) :
    StrictlyConvexOn (f∗[hf]) C := by
  refine ⟨hC_nonempty, ?_, ?_⟩
  · exact
      Set.Subset.trans hC_subset
        (gradientImage_subset_effectiveDomain_gammaZeroConjugate_of_hasGateauxDerivativeOn
          hf gradf hgrad)
  · intro u hu v hv huv α hα0 hα1
    let m : H := AffineMap.lineMap v u α
    have hm_eq :
        m = α • u + (1 - α) • v := by
      simp [m, AffineMap.lineMap_apply_module, add_comm]
    have hu_eff : u ∈ effectiveDomain (f∗[hf]) :=
      (gradientImage_subset_effectiveDomain_gammaZeroConjugate_of_hasGateauxDerivativeOn
        hf gradf hgrad) (hC_subset hu)
    have hv_eff : v ∈ effectiveDomain (f∗[hf]) :=
      (gradientImage_subset_effectiveDomain_gammaZeroConjugate_of_hasGateauxDerivativeOn
        hf gradf hgrad) (hC_subset hv)
    have hmC : m ∈ C := by
      rw [hm_eq]
      exact hC_convex hu hv hα0.le (sub_nonneg.mpr hα1.le) (by ring)
    have hm_eff : m ∈ effectiveDomain (f∗[hf]) :=
      (gradientImage_subset_effectiveDomain_gammaZeroConjugate_of_hasGateauxDerivativeOn
        hf gradf hgrad) (hC_subset hmC)
    have hconv_raw : IsConvex f.asEReal∗ := by
      exact (mem_gamma_iff _).mp (conjugate_mem_gamma f.asEReal) |>.1
    have hconv_conj :
        ConvexOn (f∗[hf]) (effectiveDomain (f∗[hf])) := by
      refine ⟨⟨u, hu_eff⟩, subset_rfl, ?_⟩
      intro x hx y hy a ha0 ha1
      simpa [gammaZeroConjugate_apply] using hconv_raw (x := x) (y := y) ha0.le ha1.le
    have hineq :
        (f∗[hf] m : EReal) ≤
          (α : EReal) * (f∗[hf] u : EReal) +
            (1 - α : EReal) * (f∗[hf] v : EReal) := by
      simpa [gammaZeroConjugate_apply, hm_eq] using hconv_raw (x := u) (y := v) hα0.le hα1.le
    by_contra hlt
    have hlt_m :
        ¬(f∗[hf] m : EReal) <
          (α : EReal) * (f∗[hf] u : EReal) +
            (1 - α : EReal) * (f∗[hf] v : EReal) := by
      simpa [hm_eq] using hlt
    have hEq :
        (f∗[hf] m : EReal) =
          (α : EReal) * (f∗[hf] u : EReal) +
            (1 - α : EReal) * (f∗[hf] v : EReal) :=
      le_antisymm hineq (le_of_not_gt hlt_m)
    let φ : ℝ → ℝ := fun t ↦ (f∗[hf] (AffineMap.lineMap v u t) : EReal).toReal
    have hu_top : (f∗[hf] u : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hu_eff)
    have hu_bot : (f∗[hf] u : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f∗[hf] u : EReal) from (f∗[hf] u).2)
    have hv_top : (f∗[hf] v : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hv_eff)
    have hv_bot : (f∗[hf] v : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f∗[hf] v : EReal) from (f∗[hf] v).2)
    have hm_top : (f∗[hf] m : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hm_eff)
    have hm_bot : (f∗[hf] m : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f∗[hf] m : EReal) from (f∗[hf] m).2)
    have hsub_cast :
        (1 - (α : EReal)) = ((1 - α : ℝ) : EReal) := by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
    have hEq_real :
        φ α = AffineMap.lineMap (φ 0) (φ 1) α := by
      have hEq_cast :
          ((φ α : ℝ) : EReal) =
            ((AffineMap.lineMap (φ 0) (φ 1) α : ℝ) : EReal) := by
        calc
          ((φ α : ℝ) : EReal) = (f∗[hf] m : EReal) := by
            simpa [φ, m] using (EReal.coe_toReal hm_top hm_bot)
          _ = (α : EReal) * (f∗[hf] u : EReal) +
                (1 - α : EReal) * (f∗[hf] v : EReal) := hEq
          _ = ((AffineMap.lineMap (φ 0) (φ 1) α : ℝ) : EReal) := by
            rw [show (α : EReal) = ((α : ℝ) : EReal) by rfl, hsub_cast,
              ← EReal.coe_toReal hu_top hu_bot, ← EReal.coe_toReal hv_top hv_bot,
              ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
            simp [φ, AffineMap.lineMap_apply_module, add_comm]
      exact_mod_cast hEq_cast
    have htrace_convex :
        _root_.ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ := by
      have htoRealConvex :
          _root_.ConvexOn ℝ (effectiveDomain (f∗[hf])) (fun z ↦ (f∗[hf] z : EReal).toReal) :=
        hconv_conj.toReal_convexOn_effectiveDomain
      have hcomp :
          _root_.ConvexOn ℝ
            ((AffineMap.lineMap v u) ⁻¹' effectiveDomain (f∗[hf])) φ :=
        htoRealConvex.comp_affineMap (AffineMap.lineMap v u)
      refine hcomp.subset ?_ (convex_Icc (0 : ℝ) 1)
      intro t ht
      exact
        (show AffineMap.lineMap v u t ∈ effectiveDomain (f∗[hf]) from
          by
            have hsegC : segment ℝ v u ⊆ C := by
              intro z hz
              rw [segment_eq_image_lineMap] at hz
              rcases hz with ⟨β, hβ, rfl⟩
              have hzC :
                  β • u + (1 - β) • v ∈ C :=
                hC_convex hu hv hβ.1 (sub_nonneg.mpr hβ.2) (by ring)
              simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using hzC
            exact
              (gradientImage_subset_effectiveDomain_gammaZeroConjugate_of_hasGateauxDerivativeOn
                hf gradf hgrad) <|
                hC_subset <|
                hsegC <| by
                  rw [segment_eq_image_lineMap]
                  exact ⟨t, ht, rfl⟩)
    have haff :
        Set.EqOn
          (fun t : ℝ ↦ (f∗[hf] (AffineMap.lineMap v u t) : EReal).toReal)
          (AffineMap.lineMap
            ((f∗[hf] v : EReal).toReal)
            ((f∗[hf] u : EReal).toReal))
          (Set.Icc (0 : ℝ) 1) := by
      simpa [φ] using
        eq_lineMap_on_Icc_of_convex_eq_at_interior htrace_convex ⟨hα0, hα1⟩ hEq_real
    have hfin :
        segment ℝ v u ⊆ effectiveDomain (f∗[hf]) := by
      intro z hz
      have hsegC : segment ℝ v u ⊆ C := by
        intro w hw
        rw [segment_eq_image_lineMap] at hw
        rcases hw with ⟨β, hβ, rfl⟩
        have hwC :
            β • u + (1 - β) • v ∈ C :=
          hC_convex hu hv hβ.1 (sub_nonneg.mpr hβ.2) (by ring)
        simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using hwC
      exact
        (gradientImage_subset_effectiveDomain_gammaZeroConjugate_of_hasGateauxDerivativeOn
          hf gradf hgrad) <|
          hC_subset (hsegC hz)
    have hm_open : m ∈ openSegment ℝ v u := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨α, ⟨hα0, hα1⟩, rfl⟩
    rcases hC_subset hmC with ⟨x, hx, hmgrad⟩
    have hsub :
        (∂ f) x = ({gradf x} : Set H) :=
      subdifferential_eq_singleton_of_hasGateauxDerivativeOn_mem_interior_effectiveDomain
        (f := f) (hf0 := hf) (gradf := gradf) hgrad hx
    have hxconj : x ∈ (∂ (f∗[hf])) m := by
      rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate f hf]
      have hmem : m ∈ (∂ f) x := by
        simp [hmgrad, hsub]
      simpa [SetValuedOperator.mem_inverse_iff] using hmem
    have hint :
        x ∈ SetValuedOperator.image (∂ (f∗[hf])) (openSegment ℝ v u) :=
      (SetValuedOperator.mem_image (∂ (f∗[hf])) (openSegment ℝ v u) x).2
        ⟨m, hm_open, hxconj⟩
    have hseg_sub :
        segment ℝ v u ⊆ (∂ f) x :=
      segment_subset_subgradient_of_affine_conjugate_trace_of_mem_image_openSegment
        (f := f) hf x v u hfin haff hint
    have hendpoints :
        v ∈ (∂ f) x ∧ u ∈ (∂ f) x :=
      -- The subgradient segment contradiction is read off at the two endpoints.
      endpoints_mem_of_segment_subset (s := (∂ f) x) hseg_sub
    have hv_sub : v ∈ (∂ f) x := hendpoints.1
    have hu_sub : u ∈ (∂ f) x := hendpoints.2
    have hv_eq : v = gradf x := by
      simpa [hsub] using hv_sub
    have hu_eq : u = gradf x := by
      simpa [hsub] using hu_sub
    exact huv (hu_eq.trans hv_eq.symm)

end DifferentiabilityAndStrictConvexity

end ERealFunction
