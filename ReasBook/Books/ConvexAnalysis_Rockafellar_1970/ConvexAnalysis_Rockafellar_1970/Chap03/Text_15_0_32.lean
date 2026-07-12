import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_31

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar Pointwise ENNReal NNReal

universe u

section

variable {E : Type u} [Zero E] [SMul ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.32 identifies the obverse construction on indicator and gauge
  functions.
- `core/canonical`: the existing owner APIs are the Chapter 15 declarations
  `Function.rightScalarMul` and `obverse` from `Text_15_0_31`, together with the chapter
  indicator owner `δ(· | C)` and the chapter gauge notation `γ(· | C)` for mathlib's owner
  `egauge ℝ≥0 C`.
- `bridge/view`: the theorem-level content is exactly the comparison between the source-facing
  obverse construction and those canonical owners.

Domain-style sampling used here:
- `rightScalarMul`;
- `obverse`;
- `indicatorFunction`;
- `egauge`;
- `egauge_le_iff_mem_smul`.
- `supportFunction_isClosedGauge_of_zero_mem`;
- `gauge_polar_supportFunction_eq_egauge_of_isClosedConvexZero`.

Primitive data vs derived API:
- primitive data: the chapter owner declarations `Function.rightScalarMul` and `obverse f`;
- derived API: the two identifications exchanging indicator and gauge, with the support-function
  closed-gauge package and its polar relation reused from Corollary 15.1.2 rather than rebuilt
  locally. The only codomain bridge needed here is the canonical coercion from
  `γ(· | C) : E → ℝ≥0∞` to `E → WithBotTop ℝ`, so no local gauge wrapper is kept.

Layer target: `bridge/view`, reusing the upstream Chapter 15 owner declarations and keeping only
the indicator/gauge comparison theorems in this file. The first bridge theorem uses only the real
action layer needed for `obverse` and `γ(· | C)`, while the converse bridge theorem below
inherits the stronger topological ambient from the imported owner API
`egauge_le_iff_mem_smul` and Corollary 15.1.2. Both therefore stay coordinate-free and only
specialize to `R^n` when desired.
-/

-- Proof sketch: for `f = indicatorFunction C`, the positive right scalar multiple condition
-- corresponding to `f_λ x ≤ 1` is equivalent to `x ∈ (λ : ℝ) • C`, because the indicator is `0`
-- on `C` and `⊤` off `C`. Taking the infimum over positive `λ` then gives the canonical extended
-- gauge of `C`; the hypothesis `0 ∈ C` ensures the positive-scalar and nonnegative-scalar
-- formulations agree at the origin.
/-- Text 15.0.32: for a set `C` containing the origin, the obverse of its indicator function
`δ(· | C)` is the extended gauge `γ(· | C)`, viewed in `WithBotTop ℝ`. Specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the source ambient `R^n`. -/
theorem obverse_indicatorFunction_eq_egauge
    {C : Set E} (h0C : (0 : E) ∈ C) :
    obverse (δ(· | C)) = (γ(· | C) : E → WithBotTop ℝ) := sorry

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

-- Proof sketch: positive homogeneity makes the positive right scalar multiple of
-- `fun x ↦ (egauge ℝ≥0 C x : WithBotTop ℝ)` independent of `λ`, so the obverse condition reduces
-- to
-- `egauge ℝ≥0 C x ≤ 1`. For a closed convex set containing `0`, Corollary 9.7.1 identifies this
-- sublevel set with `C`, hence the infimum is `0` on `C` and `⊤` outside `C`, which is exactly
-- `indicatorFunction C`.
/-- For a closed convex set containing the origin, the obverse of the extended gauge `egauge ℝ≥0
C`, written on the theorem surface as `γ(· | C)` and viewed in `WithBotTop ℝ`, is the indicator
`δ(· | C)`. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the source ambient `R^n`. -/
theorem obverse_egauge_eq_indicatorFunction
    {C : Set E} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (h0C : (0 : E) ∈ C) :
    obverse ((γ(· | C) : E → WithBotTop ℝ)) = (δ(· | C) : E → WithBotTop ℝ) := sorry

end
