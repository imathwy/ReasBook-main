import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ENNReal NNReal Rockafellar

universe u v

section GaugeUnitSublevel

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.2 says that every gauge on `R^n` is the gauge of some nonempty convex
  set. The reusable owner-level unit-sublevel API is scalar-generic at the `IsGauge` layer, while
  the bridge to `egauge ℝ≥0` stays on real modules; specializing to `R^n` recovers the source
  statement.
- `core/canonical`: the existing source-facing owner for the function-side notion is the imported
  declaration `IsGauge` from Text 15.0.1,
  while the canonical set-side gauge owner is mathlib's extended Minkowski functional
  `egauge ℝ≥0`, rendered in the chapter notation as `γ(· | ·)`.
- `bridge/view`: the textbook proof chooses the unit sublevel set `gaugeUnitSublevel k`, so the
  representation is most naturally stated by identifying a gauge with the extended gauge of the
  canonical preimage `k ⁻¹' Set.Iic 1`, kept under the short chapter name
  `gaugeUnitSublevel k`.

Domain-style sampling used here:
- `IsGauge`;
- `egauge`;
- `egauge_eq_sInf_nonneg_dilates`;
- the chapter/project sublevel-set style `f ⁻¹' Set.Iic a`, as in `Set.polar` and
  `supportFunction C ⁻¹' Set.Iic 1`.

Primitive data vs derived API:
- primitive datum: a gauge `k : E → WithBotTop 𝕜`;
- derived object: its canonical unit sublevel set `gaugeUnitSublevel k`, implemented as the
  high-reuse abbreviation of the owner expression `k ⁻¹' Set.Iic 1`;
- derived fact: in the real specialization, `k` is recovered from this set through `egauge ℝ≥0`.

Layer target: `bridge/view`, stated directly in terms of the canonical owner `egauge ℝ≥0` rather
than introducing a parallel local gauge wrapper.
-/

/-- The canonical unit sublevel set attached to a gauge `k`. -/
abbrev gaugeUnitSublevel (k : E → WithBotTop 𝕜) : Set E :=
  k ⁻¹' Set.Iic (1 : WithBotTop 𝕜)

namespace IsGauge

-- Proof sketch: a gauge vanishes at the origin, and `0 ≤ 1` in the ordered scalar.
/-- The canonical unit sublevel set of a gauge contains the origin. -/
theorem zero_mem_unitSublevel (k : E → WithBotTop 𝕜) [hk : IsGauge k] :
    (0 : E) ∈ gaugeUnitSublevel k := by
  change k 0 ≤ (1 : WithBotTop 𝕜)
  rw [hk.map_zero]
  exact WithBotTop.coe_le_coe.mpr (zero_le_one : (0 : 𝕜) ≤ 1)

/-- The canonical unit sublevel set of a gauge is nonempty. -/
theorem unitSublevel_nonempty (k : E → WithBotTop 𝕜) [IsGauge k] :
    (gaugeUnitSublevel k).Nonempty :=
  ⟨0, zero_mem_unitSublevel k⟩

section OrderedCodomain

variable [NoBotOrder 𝕜]

-- Proof sketch: `gaugeUnitSublevel k` is the closed sublevel set `{x | k x ≤ 1}` of the convex
-- owner `k`, so convexity is exactly the owner theorem `Function.IsConvex.convex_le`.
/-- The canonical unit sublevel set of a gauge is convex. -/
theorem convex_unitSublevel (k : E → WithBotTop 𝕜) [hk : IsGauge k] :
    Convex 𝕜 (gaugeUnitSublevel k) := by
  simpa [gaugeUnitSublevel] using hk.convex.convex_le (1 : WithBotTop 𝕜)

end OrderedCodomain

end IsGauge

end GaugeUnitSublevel

section RealEgaugeBridge

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

local notation "γ" C => fun x : E ↦ (γ(x | C) : EReal)

namespace IsGauge

-- Proof sketch: let `C = gaugeUnitSublevel k`. Positive homogeneity gives
-- `x ∈ μ • C ↔ k x ≤ μ` for `μ ≥ 0`, so the defining infimum formula for `egauge ℝ≥0 C x`
-- collapses to the infimum of the upper ray `{μ | k x ≤ μ}`, which is exactly `k x`.
/-- Text 15.0.2: every gauge is the gauge of its unit sublevel set `gaugeUnitSublevel k`.
Since `gaugeUnitSublevel k` is the canonical unit sublevel set `{x | k x ≤ 1}`, this realizes
every gauge as the gauge of a nonempty convex set. Specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the source statement. -/
theorem eq_egauge_unitSublevel (k : E → EReal) [IsGauge k] :
    k = γ (gaugeUnitSublevel k) := sorry

end IsGauge

end RealEgaugeBridge
