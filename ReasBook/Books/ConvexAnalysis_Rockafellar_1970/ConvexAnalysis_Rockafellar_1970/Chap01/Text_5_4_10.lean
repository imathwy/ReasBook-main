import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 5.4.10 writes the gauge as the infimum of nonnegative scalars `λ`
  such that `x ∈ λ • C`, with chapter notation
  `γ(x | C)`.
- `core/canonical`: the matching owner already introduced in Definition 4.8.2 is mathlib's
  extended Minkowski functional `egauge 𝕜 : Set E → E → ℝ≥0∞` at the primitive scalar-action layer
  `[NNNorm 𝕜] [SMul 𝕜 E]`; the chapter surface `γ(x | C)` is the specialization `𝕜 = ℝ≥0`.
- `bridge/view`: the infimum formula is available upstream both at the generic owner layer
  `egauge_eq_sInf_dilates` and at the chapter-default nonnegative specialization
  `egauge_eq_sInf_nonneg_dilates`; this item reuses those owner bridges directly.
- Primitive data vs derived API: the set `C` and point `x` are primitive. Convexity and
  nonemptiness are redundant for the canonical owner and therefore do not belong in the public API.
- Domain-style sampling used here:
  `γ[𝕜](x | C)`,
  `γ(x | C)`,
  `egauge_eq_sInf_dilates`,
  `egauge_eq_sInf_nonneg_dilates`,
  `IsGauge.eq_egauge_unitSublevel`,
  `egauge_le_of_mem_smul`,
  `le_egauge_iff`.
-/

open scoped Pointwise NNReal Rockafellar

section Gauge

variable {𝕜 : Type*} [NNNorm 𝕜]
variable {E : Type*} [SMul 𝕜 E]

/- Owner-level infimum bridge for arbitrary scalar types with `NNNorm`. -/
recall egauge_eq_sInf_dilates (C : Set E) (x : E) :
  γ[𝕜](x | C) = sInf (enorm '' {c : 𝕜 | x ∈ c • C})

end Gauge

section GaugeNNReal

variable {E : Type*} [SMul ℝ≥0 E]

/- Text 5.4.10 reuses the chapter-default nonnegative-scalar specialization from
Definition 4.8.2. -/
recall egauge_eq_sInf_nonneg_dilates (C : Set E) (x : E) :
  γ(x | C) = sInf (enorm '' {c : ℝ≥0 | x ∈ c • C})

end GaugeNNReal
