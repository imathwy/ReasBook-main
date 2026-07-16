import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_6

-- Declarations for this item will be appended below by the statement pipeline.

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
