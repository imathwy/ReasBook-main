import BauschkeLean.Chap01.Text_1_0_14
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap17.Definition_17_1
import BauschkeLean.Chap18.Proposition_18_10
import Mathlib.Analysis.Convex.Function

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open SetValuedOperator

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- This file keeps the source-facing continuous-convex subgradient projector local, while reusing
-- the canonical Chapter 16 subdifferential owner `∂`, the Chapter 1 lower-level-set owner
-- `lowerLevelSet`, and the Chapter 1 selection owner `Selection`.

section

variable [CompleteSpace H]

/-- Under the continuity and convexity assumptions of Definition 29.40, every point of `H` lies in
`dom (∂ f.toEReal)`. -/
theorem subgradientProjector_mem_dom
    (f : H → ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f) (x : H) :
    x ∈ SetValuedOperator.dom (∂ f.toEReal) := by
  have hconvE : ConvexOn f.toEReal (effectiveDomain f.toEReal) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [Function.effectiveDomain_toEReal]
    · simp [Function.effectiveDomain_toEReal]
    · intro y hy z hz a ha0 ha1
      have hreal :
          f (a • y + (1 - a) • z) ≤ a * f y + (1 - a) * f z := by
        simpa [smul_eq_mul] using
          hconv.2 (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le) (by linarith)
      change ((f (a • y + (1 - a) • z) : ℝ) : EReal) ≤
        ((a * f y + (1 - a) * f z : ℝ) : EReal)
      exact_mod_cast hreal
  let hxcont : ContinuousPoint f.toEReal x :=
    ⟨1, zero_lt_one, by simp [Function.effectiveDomain_toEReal], by
      simpa [Function.toEReal_apply] using hcont.continuousAt⟩
  rw [SetValuedOperator.mem_dom_iff]
  exact
    (subdifferential_nonempty_and_weaklyCompact_of_continuousPoint
      f.toEReal hconvE hxcont).1

/-- The globally defined selected subgradient of a continuous convex real-valued function, obtained
by evaluating the source selection of `∂ f.toEReal` at the canonical global domain witness. -/
noncomputable def continuousConvexSelectedSubgradient
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (s : Selection (∂ f.toEReal)) (x : H) : H :=
  s ⟨x, subgradientProjector_mem_dom f hcont hconv x⟩

/-- The globally selected subgradient belongs to the corresponding subdifferential fiber. -/
theorem continuousConvexSelectedSubgradient_mem_subdifferential
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (s : Selection (∂ f.toEReal)) (x : H) :
    continuousConvexSelectedSubgradient f hcont hconv s x ∈ (∂ f.toEReal) x := by
  exact selection_apply_mem s ⟨x, subgradientProjector_mem_dom f hcont hconv x⟩

/-- If the lower level set `C = lev_{≤ ξ} f` is nonempty, then every active-branch selected
subgradient in Definition 29.40 is nonzero. This is the source-faithful hypothesis that rules out
the spurious empty-set case where the displayed denominator `‖u‖ ^ 2` would otherwise be
mathematically undefined. -/
theorem selectedSubgradient_ne_zero_of_lt_of_nonempty_lowerLevelSet
    (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hC : (lowerLevelSet f.toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ f.toEReal)) {x : H} (hx : ξ < f x) :
    continuousConvexSelectedSubgradient f hcont hconv s x ≠ 0 := by
  rcases hC with ⟨y, hy⟩
  intro hu
  let u : H := continuousConvexSelectedSubgradient f hcont hconv s x
  have hu0 : u = 0 := by
    simpa [u] using hu
  have hu_mem : u ∈ (∂ f.toEReal) x := by
    simpa [u] using
      continuousConvexSelectedSubgradient_mem_subdifferential f hcont hconv s x
  have hxy : f x ≤ f y := by
    have hsub :
        (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) :=
      (mem_subdifferential_iff f.toEReal x u).1 hu_mem y
    have hsub0 : (0 : EReal) + (f x : EReal) ≤ (f y : EReal) := by
      simpa [hu0, inner_zero_right] using hsub
    have hsub' : (f x : EReal) ≤ (f y : EReal) := by
      simpa using hsub0
    exact_mod_cast hsub'
  have hy_le : f y ≤ ξ := by
    simpa [Function.toEReal_apply] using
      (mem_lowerLevelSet_iff f.toEReal.asEReal ξ y).1 hy
  linarith

/-- The source-facing projector of Definition 29.40 (1): if `f` is continuous and convex, if the
lower level set `lev_{≤ ξ} f` is nonempty, and if `s` is a selection of `∂ f`, then the associated
subgradient
projector is the source-facing operator obtained by the textbook piecewise formula. The
lower-level-set nonemptiness hypothesis is part of the owner because it is exactly what rules out
the mathematically invalid active branch with zero selected subgradient. -/
noncomputable def continuousConvexSubgradientProjector
    (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hC : (lowerLevelSet f.toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ f.toEReal)) :
    H → H :=
  fun x ↦
    if hx : ξ < f x then
      let u := continuousConvexSelectedSubgradient f hcont hconv s x
      let hu :
          u ≠ 0 :=
        selectedSubgradient_ne_zero_of_lt_of_nonempty_lowerLevelSet
          f ξ hcont hconv hC s hx
      let denom : ℝˣ := Units.mk0 (‖u‖ ^ 2) (pow_ne_zero 2 (norm_ne_zero_iff.2 hu))
      x + (((ξ - f x) / (denom : ℝ)) • u)
    else
      x

/-- Evaluating `continuousConvexSubgradientProjector` at `x` recovers the selected-subgradient
formula from Definition 29.40. -/
theorem continuousConvexSubgradientProjector_apply
    (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hC : (lowerLevelSet f.toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ f.toEReal)) (x : H) :
    continuousConvexSubgradientProjector f ξ hcont hconv hC s x =
      if ξ < f x then
        let u : H := continuousConvexSelectedSubgradient f hcont hconv s x
        x + (((ξ - f x) / (‖u‖ ^ 2)) • u)
      else
        x := by
  by_cases hξx : ξ < f x
  · simp [continuousConvexSubgradientProjector, hξx]
  · simp [continuousConvexSubgradientProjector, hξx]

/-- On the lower-level-set branch `f x ≤ ξ`, the continuous-convex subgradient projector fixes
`x`. -/
theorem continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
    (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hC : (lowerLevelSet f.toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ f.toEReal))
    {x : H} (hx : x ∈ lowerLevelSet f.toEReal.asEReal ξ) :
    continuousConvexSubgradientProjector f ξ hcont hconv hC s x = x := by
  have hfx : f x ≤ ξ := by
    simpa [Function.toEReal_apply] using
      (mem_lowerLevelSet_iff f.toEReal.asEReal ξ x).1 hx
  simp [continuousConvexSubgradientProjector, not_lt.mpr hfx]

/-- On the active branch `ξ < f x`, the continuous-convex subgradient projector is given by the
selected-subgradient formula from Definition 29.40. -/
theorem continuousConvexSubgradientProjector_apply_of_lt
    (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hC : (lowerLevelSet f.toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ f.toEReal))
    {x : H} (hx : ξ < f x) :
    continuousConvexSubgradientProjector f ξ hcont hconv hC s x =
      let u : H := continuousConvexSelectedSubgradient f hcont hconv s x
      x + (((ξ - f x) / (‖u‖ ^ 2)) • u) := by
  simp [continuousConvexSubgradientProjector, hx]

/-- Expanding the source-facing continuous-convex subgradient projector of Definition 29.40 (1)
recovers the displayed piecewise formula. -/
theorem continuousConvexSubgradientProjector_def
    (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hC : (lowerLevelSet f.toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ f.toEReal)) :
    continuousConvexSubgradientProjector f ξ hcont hconv hC s =
      fun x ↦
        if ξ < f x then
          let u : H := continuousConvexSelectedSubgradient f hcont hconv s x
          x + (((ξ - f x) / (‖u‖ ^ 2)) • u)
        else
          x := by
  funext x
  simpa using continuousConvexSubgradientProjector_apply f ξ hcont hconv hC s x

end

/-
Source/core/bridge triage for Definition 29.40 (2):
- `source-facing`: the main mathematical content is that the differentiable case is a
  specialization of the general Chapter 29 subgradient-projector construction.
- `core/canonical`: the Chapter 29 owner remains
  `continuousConvexSubgradientProjector`.
- `bridge/view`: the differentiable case is only the equality between that owner and the explicit
  gradient formula obtained when the selected subgradient is forced to be the Gâteaux gradient on
  the active branch. -/

section

variable [CompleteSpace H]

/-- Helper for Definition 29.40: on the active branch `ξ < f x`, continuity, convexity, and the
prescribed Gâteaux gradient identify the subdifferential of `f.toEReal` at `x` with the singleton
`{grad x}`. -/
lemma activeSubdifferential_eq_singleton_gradient
    (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (grad : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun z ↦ (f z : EReal).toReal)
        (fun z ↦ InnerProductSpace.toDualMap ℝ H (grad z))
        {x | ξ < f x})
    {x : H} (hx : ξ < f x) :
    (∂ f.toEReal) x = ({grad x} : Set H) := by
  have hfΓ : f.toEReal ∈ Γ₀(H) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ f hcont hconv
  have hgradAt :
      HasGateauxDerivativeAt
        (fun z ↦ (f z : EReal).toReal)
        (InnerProductSpace.toDualMap ℝ H (grad x)) x := by
    -- Upgrade the active-set derivative to a whole-space derivative at `x`.
    exact hasGateauxDerivativeAt_of_hasGateauxDerivativeWithinAt (hgrad x hx)
  have hxInterior : x ∈ interior (effectiveDomain f.toEReal) := by
    -- Real-valued functions have full effective domain after `toEReal`.
    simp [Function.effectiveDomain_toEReal]
  -- The interior-point singleton theorem turns differentiability into a singleton fiber.
  simpa using
    subdifferential_eq_singleton_at_interior_of_hasGateauxDerivativeAt
      (f := f.toEReal) hfΓ (x := x) (g := grad x) hxInterior hgradAt

/-- Helper for Definition 29.40: on the active branch `ξ < f x`, the globally selected
subgradient equals the prescribed Gâteaux gradient. -/
lemma selectedSubgradient_eq_gradientOnActive
    (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (s : Selection (∂ f.toEReal)) (grad : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun z ↦ (f z : EReal).toReal)
        (fun z ↦ InnerProductSpace.toDualMap ℝ H (grad z))
        {x | ξ < f x})
    {x : H} (hx : ξ < f x) :
    continuousConvexSelectedSubgradient f hcont hconv s x = grad x := by
  have hselected :
      continuousConvexSelectedSubgradient f hcont hconv s x ∈ (∂ f.toEReal) x :=
    continuousConvexSelectedSubgradient_mem_subdifferential f hcont hconv s x
  -- Rewrite the selected-subgradient membership through the singleton active fiber.
  rw [activeSubdifferential_eq_singleton_gradient f ξ hcont hconv grad hgrad hx] at hselected
  simpa using hselected

/-- Definition 29.40 (2): if `f` is continuous and convex and `grad` realizes the Gâteaux
gradient field of `(fun z ↦ (f z : EReal).toReal)` on the active branch `{x | ξ < f x}`, then
every selected-subgradient projector from Definition 29.40 (1) agrees with the explicit gradient
formula. -/
theorem continuousConvexSubgradientProjector_eq_gradientFormula
    (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hC : (lowerLevelSet f.toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ f.toEReal)) (grad : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun z ↦ (f z : EReal).toReal)
        (fun z ↦ InnerProductSpace.toDualMap ℝ H (grad z))
        {x | ξ < f x}) :
    continuousConvexSubgradientProjector f ξ hcont hconv hC s =
      fun x ↦
        if ξ < f x then
          x + (((ξ - f x) / (‖grad x‖ ^ 2)) • grad x)
        else
          x := by
  funext x
  by_cases hx : ξ < f x
  · have hactive :
        continuousConvexSubgradientProjector f ξ hcont hconv hC s x =
          x + (((ξ - f x) / (‖grad x‖ ^ 2)) • grad x) := by
      -- Rewrite the active selected-subgradient branch through the singleton gradient fiber.
      simpa [selectedSubgradient_eq_gradientOnActive f ξ hcont hconv s grad hgrad hx] using
        (continuousConvexSubgradientProjector_apply_of_lt f ξ hcont hconv hC s hx)
    -- The active branch now matches the displayed gradient formula exactly.
    simpa [hx] using hactive
  · -- On the inactive branch, the projector fixes `x`, matching the displayed formula.
    simp [continuousConvexSubgradientProjector, hx]

/-- Evaluating the differentiable bridge from Definition 29.40 (2) recovers the explicit
gradient branch formula. -/
theorem continuousConvexSubgradientProjector_apply_of_hasGateauxDerivativeOn
    (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hC : (lowerLevelSet f.toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ f.toEReal)) (grad : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun z ↦ (f z : EReal).toReal)
        (fun z ↦ InnerProductSpace.toDualMap ℝ H (grad z))
        {x | ξ < f x})
    (x : H) :
    continuousConvexSubgradientProjector f ξ hcont hconv hC s x =
      if ξ < f x then
        x + (((ξ - f x) / (‖grad x‖ ^ 2)) • grad x)
      else
        x := by
  simpa using congrArg (fun G : H → H ↦ G x)
    (continuousConvexSubgradientProjector_eq_gradientFormula
      f ξ hcont hconv hC s grad hgrad)

/-- On the active branch `ξ < f x`, the differentiable specialization of Definition 29.40 is
given by the explicit gradient formula. -/
theorem continuousConvexSubgradientProjector_apply_of_lt_of_hasGateauxDerivativeOn
    (f : H → ℝ) (ξ : ℝ) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hC : (lowerLevelSet f.toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ f.toEReal)) (grad : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun z ↦ (f z : EReal).toReal)
        (fun z ↦ InnerProductSpace.toDualMap ℝ H (grad z))
        {x | ξ < f x})
    {x : H} (hx : ξ < f x) :
    continuousConvexSubgradientProjector f ξ hcont hconv hC s x =
      x + (((ξ - f x) / (‖grad x‖ ^ 2)) • grad x) := by
  simpa [hx] using
    (continuousConvexSubgradientProjector_apply_of_hasGateauxDerivativeOn
      f ξ hcont hconv hC s grad hgrad x)

end

end

end ERealFunction
