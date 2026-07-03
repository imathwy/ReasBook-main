import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_2 (from Chap09) -/
universe u

namespace Function

section

variable {E : Type u}

/-- The canonical extended-real-valued lift of a real-valued potential. -/
abbrev toEReal (ω : E → ℝ) : E → EReal :=
  Real.toEReal ∘ ω

/-- Evaluating the canonical extended-real-valued lift of a real-valued potential. -/
@[simp] theorem toEReal_apply (ω : E → ℝ) (x : E) :
    ω.toEReal x = ω x :=
  rfl

end

section

variable {E : Type u} [Nonempty E]

/-- A real-valued function, viewed in `EReal`, is proper. -/
theorem toEReal_isProper (ω : E → ℝ) :
    IsProperExtendedRealFunction ω.toEReal := by
  refine ⟨?_, ?_⟩
  · intro x
    simp [Function.toEReal]
  · let x : E := Classical.choice inferInstance
    exact ⟨x, by simp [effective_domain, Function.toEReal]⟩

end

section

variable {E : Type u} [TopologicalSpace E]

/-- Continuity of a real-valued function implies lower semicontinuity of its canonical
`EReal` coercion. -/
theorem toEReal_lowerSemicontinuous_of_continuous
    {ω : E → ℝ} (hω : Continuous ω) :
    LowerSemicontinuous ω.toEReal := by
  simpa [Function.toEReal] using
    (continuous_coe_real_ereal.comp hω).lowerSemicontinuous

end

section

variable {E : Type u} [PseudoMetricSpace E]

/-- A Lipschitz real-valued function remains lower semicontinuous after coercion to `EReal`. -/
theorem toEReal_lowerSemicontinuous_of_lipschitz
    {ω : E → ℝ} {L : NNReal} (hω : LipschitzWith L ω) :
    LowerSemicontinuous ω.toEReal :=
  toEReal_lowerSemicontinuous_of_continuous hω.continuous

end

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-- A convex real-valued function remains convex after coercion to `EReal`. -/
theorem toEReal_isConvexFunction
    {ω : E → ℝ} (hω : ConvexOn ℝ Set.univ ω) :
    is_convex_function ω.toEReal := by
  have hne_bot :
      ∀ x ∈ effective_domain ω.toEReal, ω.toEReal x ≠ ⊥ := by
    intro x hx
    simp [Function.toEReal]
  refine (is_convex_function_iff_convexOn_toReal hne_bot).2 ?_
  simpa [effective_domain, Function.toEReal] using hω

end

end Function

noncomputable section

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 9.2 has two layers in the local API.
- `bregmanDistance` is a `bridge/view` owner in the Hilbert-space gradient setting, since its
  formula uses both `∇` and `inner`.
- The standing assumptions on `ω` over `C` are a `source-facing` Chapter 9 owner recorded below as
  `IsBregmanPotentialOn`; that owner itself lives in the weaker normed-space convex-analysis
  setting and the constrained-potential statement for `ω + δ_C` is derived from it. -/

/-- Definition 9.2: the Bregman distance associated with a proper closed convex potential `ω`,
viewed as a totalized real-valued function with intended source domain
`dom(ω) × dom(∂ ω)`, is
`B_ω(x, y) = ω(x) - ω(y) - ⟪∇ω(y), x - y⟫` on finite points. -/
def bregmanDistance (ω : E → EReal) (x y : E) : ℝ :=
  (ω x).toReal - (ω y).toReal - inner ℝ (∇ (fun z ↦ (ω z).toReal) y) (x - y)

notation "B[" ω "]" => bregmanDistance ω
notation "B[" ω "]" => bregmanDistance (Function.toEReal ω)

-- Proof sketch: unfold `bregmanDistance`; evaluating the definition at `(x, y)` gives the
-- displayed totalized real-valued expression.
/-- The defining formula for `bregmanDistance` at `(x, y)` is
`ω(x) - ω(y) - ⟪∇ω(y), x - y⟫` on finite points. -/
@[simp] theorem bregmanDistance_def (ω : E → EReal) (x y : E) :
    B[ω] x y =
      (ω x).toReal - (ω y).toReal - inner ℝ (∇ (fun z ↦ (ω z).toReal) y) (x - y) := sorry

-- Proof sketch: unfold `bregmanDistance` at `(x, x)`; the two function values cancel and the
-- remaining inner product is against `x - x = 0`.
/-- The Bregman distance of a point from itself is zero. -/
@[simp] theorem bregmanDistance_self_eq_zero (ω : E → EReal) (x : E) :
    B[ω] x x = 0 := sorry

-- Proof sketch: substitute `y = x` and reduce to `bregmanDistance_self_eq_zero`.
/-- If the two arguments coincide, then the Bregman distance vanishes. -/
theorem bregmanDistance_eq_zero_of_eq (ω : E → EReal) {x y : E} (hxy : x = y) :
    B[ω] x y = 0 := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Bregman potential on `C` with modulus `σ` is proper, closed, convex, differentiable on
`dom(∂ ω)`, contains `C` in `dom(ω)`, and has `ω.toReal` `σ`-strongly convex on `C`. The
equivalent constrained-potential formulation for `ω + δ_C` is derived below. -/
class IsBregmanPotentialOn (ω : E → EReal) (C : Set E) (σ : ℝ) : Prop
    extends IsProperExtendedRealFunction ω where
  closed : LowerSemicontinuous ω
  convex : is_convex_function ω
  differentiableOn_subdifferential_domain :
    DifferentiableOn ℝ (fun x ↦ (ω x).toReal) (subdifferential_domain ω)
  subset_effective_domain : C ⊆ effective_domain ω
  sigma_pos : 0 < σ
  strongConvexOn : StrongConvexOn C σ (fun x ↦ (ω x).toReal)

-- Proof sketch: because `hω.subset_effective_domain` forces `ω` to be finite on `C`, the
-- constrained potential `ω + δ_C` has effective domain exactly `C`, and on that set its
-- real-valued restriction agrees with `x ↦ (ω x).toReal`; the claim is therefore just the stored
-- `hω.strongConvexOn` rewritten through the canonical constrained-potential view.
/-- A Bregman potential on `C` also yields the constrained-potential strong-convexity statement
for `ω + δ_C` on its effective domain. -/
theorem IsBregmanPotentialOn.strongConvexOn_add_indicator
    {ω : E → EReal} {C : Set E} {σ : ℝ} (hω : IsBregmanPotentialOn ω C σ) :
    StrongConvexOn (effective_domain (fun x ↦ ω x + extendedIndicator C x)) σ
      (fun x ↦ ((ω x + extendedIndicator C x)).toReal) := sorry

end

/-! ### Text_9_2 (from Chap09) -/
open scoped Gradient

noncomputable section

/- Text 9.2 is a `bridge/view` item. The chapter's Bregman-distance owner already lives in
`Definition_9_2`, and `Text_9_1` already provides the real-valued gradient specialization.
This file only adds the one-dimensional `deriv` bridge and the asymmetry example. -/

-- Proof sketch: rewrite the real-valued bridge theorem from `Text_9_1` and use the canonical
-- `gradient_eq_deriv'` bridge on `ℝ`, together with the standard formula for the real inner
-- product.
/-- For a real-valued potential on `ℝ`, the Chapter 9 Bregman distance specializes to the
one-variable derivative formula `ω(x) - ω(y) - ω'(y) (x - y)`. -/
@[simp] theorem bregmanDistance_apply_real_deriv (ω : ℝ → ℝ) (x y : ℝ) :
    B[ω] x y = ω x - ω y - deriv ω y * (x - y) := by
  rw [bregmanDistance_apply_real]
  rw [gradient_eq_deriv']
  rw [show inner ℝ (deriv ω y) (x - y) = deriv ω y * (x - y) by
    simpa using (RCLike.inner_apply' (deriv ω y) (x - y) :
      inner ℝ (deriv ω y) (x - y) = (starRingEnd ℝ) (deriv ω y) * (x - y))]

-- Proof sketch: take `ω = exp`, `x = 0`, and `y = 1`. The function `exp` is strictly convex on
-- `Set.univ`, and the two Bregman values reduce to unequal real numbers.
/-- Text 9.2: there exists a strictly convex function and two points for which the Bregman
distance is asymmetric. -/
theorem exists_strictly_convex_bregman_asymmetric_pair :
    ∃ (ω : ℝ → ℝ) (x y : ℝ),
      StrictConvexOn ℝ Set.univ ω ∧
        B[ω] x y ≠ B[ω] y x := by
  refine ⟨Real.exp, 0, 2, ?_, ?_⟩
  · simpa using strictConvexOn_exp
  · have h02 : B[Real.exp] 0 2 = 1 + Real.exp 2 := by
      rw [bregmanDistance_apply_real_deriv]
      rw [Real.deriv_exp]
      ring_nf
      norm_num [Real.exp_zero]
    have h20 : B[Real.exp] 2 0 = Real.exp 2 - 3 := by
      rw [bregmanDistance_apply_real_deriv]
      rw [Real.deriv_exp]
      ring_nf
      norm_num [Real.exp_zero]
      ring
    intro hEq
    rw [h02, h20] at hEq
    linarith
