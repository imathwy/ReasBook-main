import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_9
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_14_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped GaugePolar PolarCone Rockafellar

universe u v w

section

variable {𝕜 : Type w} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type v} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.7 states that for the indicator `k = δ(· | K)` of a convex cone
  `K ⊆ R^n`, the polar `kᵒ` agrees with the Fenchel conjugate `k*`, and both are the indicator
  of the polar cone `Kᵒ`.
- `core/canonical`: the existing owner declarations are the generic indicator owner
  `indicatorFunction`, the gauge polar `gauge_polar`, the set polar `polarCone`, and the Chapter
  14 owner theorem `convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone`.
- `bridge/view`: the indicator-polar identity remains the source-facing Chapter 15 bridge from the
  gauge-polar owner to the Chapter 14 indicator-of-polar theorem surface. The conjugacy clause is
  then the source-facing set-level cone statement, rewriting through the existing Chapter 14
  indicator/conjugate owner theorem rather than rebuilding the support-function proof locally.

Domain-style sampling used here:
- `indicatorFunction`;
- `gauge_polar`;
- `polarCone`;
- `convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone`.

Primitive data vs derived API:
- primitive datum for the main identity: a set `K : Set X`;
- primitive data for the conjugacy clause: a set `K : Set X` together with the intrinsic
  hypotheses `K.Nonempty` and `Set.IsCone 𝕜 K`;
- derived cone-specific view: a bundled cone `ConvexCone 𝕜 X`, if needed later, is only a thin
  bridge to this set-level owner data;
- source-facing functions: the canonical indicator bridge `δ[𝕜](· | K)` for the polar identity,
  and in the Chapter 14 conjugacy clause the same `WithBotTop 𝕜`-valued indicator surface;
- derived content: the indicator-of-polar-cone formula and, under the necessary nonemptiness
  hypothesis for conjugacy, the equality with the Fenchel conjugate via the existing Chapter 14
  indicator/conjugate theorem.

Layer target: the main indicator-of-polar identity is `bridge/view` from Chapter 15 gauge polarity
to the Chapter 14 indicator-of-polar owner surface, while the conjugacy equality is the
`source-facing` set-level cone clause and reuses the existing chapter owner theorem directly.
-/

-- Proof sketch: for `k = indicatorFunction (K : Set X)`, the defining admissible-majorant
-- inequality for `gauge_polar k xStar` is equivalent to `⟪x, xStar⟫ ≤ 0` for every `x ∈ K`.
-- Hence the polar value is `0` exactly on `polarCone K` and `⊤` outside it, which is precisely
-- `indicatorFunction (polarCone K)`.
/-- Text 15.0.7 (2): for any set `K`, the polar of its indicator function is the indicator
of the polar cone. The source's cone hypothesis is redundant for this identity and is therefore
omitted from the main declaration. -/
theorem gauge_polar_indicatorFunction_eq_indicatorFunction_polarCone
    (K : Set X) :
    (δ[𝕜](· | K))ᵒ =
      ((δ[𝕜](· | (Kᵒ[𝕜] : PointedCone 𝕜 Y)) : Y → WithBotTop 𝕜)) := by
  sorry

variable [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]

-- Proof sketch: rewrite the gauge polar of the indicator by the preceding Chapter 15
-- indicator-polar bridge, then invoke the Chapter 14 owner theorem identifying the Fenchel
-- conjugate of the indicator of a nonempty cone with the indicator of its polar cone. The
-- nonemptiness hypothesis is mathematically necessary: for the empty cone, the polar gauge is
-- identically `0` while the conjugate of the indicator is identically `⊥`.
/-- Text 15.0.7 (1): for a nonempty cone `K`, the polar of its indicator function agrees with its
Fenchel conjugate at the pairing layer. The bundled convex-cone packaging is redundant for this
equality, so the theorem is stated on the primitive set-level cone data. -/
theorem gauge_polar_indicatorFunction_eq_convexConjugate_indicatorFunction
    (K : Set X) (hK_nonempty : K.Nonempty) (hK_cone : Set.IsCone 𝕜 K) :
    (δ[𝕜](· | K))ᵒ = (δ[𝕜](· | K))⋆ := by
  sorry

end
