import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped GaugePolar Rockafellar

universe u v w

section

variable {𝕜 : Type w}
variable {X : Type u} {Y : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [HasPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.6 gives an equivalent supremum formula for the polar of a gauge that
  is finite and strictly positive away from the origin.
- `core/canonical`: the owner abstractions are the chapter declarations `IsGauge` from
  `Text_15_0_1` and `gauge_polar` from `Text_15_0_5`, with the unit-sublevel owner
  `gaugeUnitSublevel` from `Text_15_0_2` as the canonical set-side view of the same gauge.
- `bridge/view`: the displayed quotient formula is the source-facing specialization of the support
  function of the unit sublevel, written directly as a `WithBotTop 𝕜` supremum over the canonical
  indexing set `{x : X | x ≠ 0}`.

Domain-style sampling used here:
- `IsGauge` from `Text_15_0_1`;
- `gaugeUnitSublevel` from `Text_15_0_2`;
- `gauge_polar` from `Text_15_0_5`.
- `supportFunction_def` from `Text_13_0_1`.

Primitive data vs derived API:
- primitive inputs: a gauge `k : X → WithBotTop 𝕜`, a dual point `xStar : Y`, and the finiteness
  and strict-positivity hypotheses from the source, both only away from the origin because
  `IsGauge.map_zero` already fixes the zero case;
- derived formula: the supremum of the nonzero quotients `⟪x, xStar⟫ₚ / k(x)`.

Layer target: `bridge/view`; the theorem keeps `gauge_polar` as the owner and adds the textbook's
equivalent supremum expression.
- Ambient refinement: the quotient formula uses only dual evaluation and the sampled owner
  declarations, so it is stated at the canonical pairing layer rather than the concrete
  self-inner-product model. The statement is kept at the intrinsic `WithBotTop 𝕜` owner layer,
  avoiding a real-`sSup` bridge.
-/

-- Proof sketch: unfold `gauge_polar`. Because `k x` is finite and strictly positive for `x ≠ 0`,
-- the inequalities `⟪x, x⋆⟫ₚ ≤ μ⋆ k x` are equivalent on nonzero vectors to the intrinsic
-- quotient bound `((⟪x, x⋆⟫ₚ : WithBotTop 𝕜) / k x) ≤ μ⋆` in `WithBotTop 𝕜`. Equivalently, after
-- normalizing a nonzero vector by the positive scalar `k x`, the admissible-majorant condition is
-- the support-function inequality on the canonical unit sublevel `gaugeUnitSublevel k`, so the
-- polar value is the supremum of that quotient family.
/-- Text 15.0.6: if a gauge `k` is finite and positive away from the origin, then its
polar admits the equivalent formula
`kᵒ(x⋆) = sup_{x ≠ 0} ⟪x, x⋆⟫ₚ / k(x)` at the intrinsic codomain layer `WithBotTop 𝕜`.
The source hypotheses are kept as primitive finiteness and strict-positivity away from the origin;
no `EReal.toReal` bridge is exposed on the theorem surface. -/
theorem gauge_polar_eq_sSup_inner_div_off_zero
    (k : X → WithBotTop 𝕜) [IsGauge k] (xStar : Y)
    (hfinite : ∀ ⦃x : X⦄, x ≠ 0 → k x < ⊤)
    (hpos : ∀ ⦃x : X⦄, x ≠ 0 → 0 < k x) :
    kᵒ xStar =
      sSup ((fun x : X ↦ (⟪x, xStar⟫ₚ : WithBotTop 𝕜) / k x) '' {x : X | x ≠ 0}) := sorry

end
