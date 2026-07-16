import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

open scoped GaugePolar Rockafellar

variable {𝕜 : Type w} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [DecidableLT 𝕜]
variable {X : Type u} {Y : Type v} [AddCommMonoid X] [Module 𝕜 X] [HasPairing X Y 𝕜]
variable {k : X → WithBotTop 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.9 states the generalized Cauchy inequality for a gauge and its polar.
- `core/canonical`: the owner objects already present in the chapter are the source-facing gauge
  predicate `IsGauge` from `Text_15_0_1`, the polar gauge owner `gauge_polar`/`kᵒ` from
  `Text_15_0_5`, and the effective-domain owner `dom(·)` from `Definition_4_4`.
- `bridge/view`: the inequality is stated at the pairing layer `HasPairing X Y 𝕜`, matching the
  owner layer of `gauge_polar`.

Domain-style sampling used here:
- `IsGauge` from `Text_15_0_1`;
- `gauge_polar` and `gauge_polar_le_of_majorant` from `Text_15_0_5`;
- `dom(·)` / `mem_effectiveDomain` from `Definition_4_4`;
- `HasPairing` and `HasPairingNegLeft` from `Chap01.HasPairing`.

Primitive data vs derived API:
- primitive inputs: a gauge `k : X → WithBotTop 𝕜`, a primal vector `x`, and a dual vector
  `xStar`;
- owner-side domain conditions: membership of `x` and `xStar` in the canonical effective domains
  `dom(k)` and `dom(kᵒ)`;
- derived strengthening: the real absolute-value version under the norm-gauge hypothesis.
-/

-- Proof sketch: by the definition of `kᵒ xStar` as the infimum of admissible real
-- majorants `μStar`, every `ε > 0` yields some `μStar ≤ kᵒ xStar + ε` with
-- `⟪x, xStar⟫ ≤ μStar * k x` for all `x`. Evaluating at the chosen `x`, then letting `ε ↓ 0`,
-- gives the required bound because both domain hypotheses ensure the right-hand side is finite.
/-- Text 15.0.9 (1): for a gauge `k` and its polar `kᵒ`, the pairing `⟪x, x⋆⟫` is bounded by
`k(x) kᵒ(x⋆)` on `dom(k) × dom(kᵒ)`. -/
theorem inner_le_mul_gauge_polar
    [IsGauge k] {x : X} {xStar : Y}
    (hx : x ∈ dom(k)) (hxStar : xStar ∈ dom(kᵒ)) :
    ((⟪x, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ k x * kᵒ xStar := sorry

end

section

open scoped GaugePolar Rockafellar

variable {𝕜 : Type w} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsOrderedRing 𝕜] [DecidableLT 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module 𝕜 X]
variable [HasPairing X Y 𝕜] [HasPairingNegLeft X Y 𝕜]
variable {k : X → WithBotTop 𝕜}

-- Proof sketch: apply the first inequality to `x` and to `-x`. The norm-gauge hypothesis gives
-- `k (-x) = k x` via the owner-side absolute homogeneity theorem
-- `IsGaugeNorm.map_smul_eq_abs`, while left-negation compatibility of the pairing gives
-- `⟪-x, xStar⟫ₚ = -⟪x, xStar⟫ₚ`; combining the two one-sided bounds yields the estimate for
-- `|⟪x, xStar⟫ₚ|`.
/-- Text 15.0.9 (2): if `k` is a norm-gauge, then the generalized Cauchy inequality holds with an
absolute value for every `x` and `x⋆`. -/
theorem abs_inner_le_mul_gauge_polar
    [IsGaugeNorm k] (x : X) (xStar : Y) :
    ((|⟪x, xStar⟫ₚ| : 𝕜) : WithBotTop 𝕜) ≤ k x * kᵒ xStar := sorry

end
