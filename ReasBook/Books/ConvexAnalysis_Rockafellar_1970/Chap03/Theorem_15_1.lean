import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ENNReal GaugePolar NNReal RealInnerProductSpace Rockafellar

section

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 15.1 specializes Chapter 15 polarity to gauges: `kᵒ` is a closed
  gauge, `kᵒᵒ = cl(k)`, and for a set gauge `γ(· | C)` the polar is `γ(· | Cᵒ)`.
- `core/canonical`: on the function side, the owner abstraction is
  `convex_function_polar` together with the Chapter 15 owner theorem
  `convex_function_polar_convex_function_polar_eq_lowerSemicontinuousHull_of_nonnegative_convex_zero`;
  on the set side, the owners are `Set.polar`, `egauge ℝ≥0`, and the chapter closure surface
  `cl(·)`.
- `bridge/view`: `gauge_polar` is the positively homogeneous specialization of
  `convex_function_polar` via `convex_function_polar_eq_gauge_polar`, and the set-side gauge is
  rendered through the chapter gauge notation `γ(· | C)` together with only the canonical codomain
  coercion to `EReal`.

Domain-style sampling used here:
- `convex_function_polar_eq_gauge_polar`;
- `isNonnegativeClosedConvexZero_convex_function_polar_of_nonnegative_convex_zero`;
- `convex_function_polar_convex_function_polar_eq_lowerSemicontinuousHull_of_nonnegative_convex_zero`;
- `IsClosedGauge`;
- `Set.polar` and the canonical extended gauge `egauge ℝ≥0`, used through the chapter notation
  `γ(· | C)` and file-local `EReal` coercion bridges `γX`/`γY`;
- the chapter closure notation `cl(·)` from `Text_7_0_4`.

Primitive data vs derived API:
- primitive datum: a gauge `k : E → EReal`, and for the set-side clause a primal set
  `C : Set X` in a paired ambient `(X, Y)`;
- derived function-side API: the closedness package for `gauge_polar k` and the bipolar identity,
  both read through the owner `convex_function_polar`;
- derived set-side API: the identification of `gauge_polar` with the gauge of `Set.polar C`.

Layer target:
- clause (1) stays `source-facing` at the weak inner-product ambient used by the Chapter 15
  function-polar owners;
- clause (3) is raised from a self-dual inner-product model to the pairing layer
  `(X, Y, HasPairingSwap X Y ℝ)`, matching the canonical owner `Set.polar`;
- clause (2) stays `source-facing` in the stronger finite-dimensional normed ambient required by
  the Chapter 15 bipolar owner
  `convex_function_polar_convex_function_polar_eq_lowerSemicontinuousHull_of_nonnegative_convex_zero`;
- all three are refined through the core owner `convex_function_polar` rather than treated as an
  independent second polarity theory.

The source sentence is split into atomic declarations.
-/

-- Proof sketch: first pass to the owner `convex_function_polar k` using positive homogeneity of
-- `k`. The Chapter 15 owner theorem gives the nonnegative/closed/convex/zero package for this
-- polar. Transport those fields back along `convex_function_polar_eq_gauge_polar`; only the
-- positive-homogeneity field remains the genuinely gauge-specific part.
/-- Theorem 15.1 (1): if `k` is a gauge, then its polar `kᵒ` is a closed gauge in the source
terminology. -/
theorem gauge_polar_isClosedGauge
    (k : E → EReal) [IsGauge k] :
    IsClosedGauge kᵒ := by
  sorry

end

section

variable {X : Type*} {Y : Type*}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Y] [Module ℝ Y]
variable [HasPairing X Y ℝ] [HasPairing Y X ℝ] [HasPairingSwap X Y ℝ]

local notation "γX" C => fun x : X ↦ (γ(x | C) : EReal)
local notation "γY" D => fun y : Y ↦ (γ(y | D) : EReal)

-- Proof sketch: specialize the defining majorant inequality for `gauge_polar` to
-- `k = γ C`. For `μ⋆ > 0`, the condition
-- `⟪x, x⋆⟫ ≤ μ⋆ γ(x | C)` for all `x` is equivalent, by positive homogeneity of the gauge, to the
-- condition `μ⋆⁻¹ x⋆ ∈ Cᵒ[ℝ]`. Thus the admissible scalars are exactly the dilates placing
-- `x⋆` in `Cᵒ[ℝ]`, which is the defining infimum formula for `egauge ℝ≥0 (Cᵒ[ℝ])`.
--
-- The convexity hypothesis from the source prose is redundant for this owner-level identity: the
-- comparison uses only the defining majorant inequalities for `gauge_polar`, `egauge ℝ≥0`, and
-- `Set.polar`.
/-- Theorem 15.1 (3): for a set `C` in a paired real ambient `(X, Y)`, the polar of the canonical
extended gauge of `C` is the canonical extended gauge of `Cᵒ[ℝ]`, both viewed in `EReal`. The
source's nonemptiness assumption is redundant for this owner-level identity and is therefore
omitted; specializing to the self-dual inner-product case recovers the textbook `R^n` statement.
-/
theorem gauge_polar_egauge_eq_egauge_polar
    (C : Set X) :
    (γX C)ᵒ = γY (Cᵒ[ℝ]) := sorry

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: use clause (1) to recover that `gauge_polar k` is still a gauge, so
-- `gauge_polar` remains the positively homogeneous specialization of `convex_function_polar` on
-- both the first and second application. The Chapter 15 owner theorem for
-- `convex_function_polar` then gives the bipolar identity directly, specialized to the gauge
-- hypotheses `k ≥ 0`, convexity, and `k 0 = 0`.
/-- Theorem 15.1 (2): in a finite-dimensional real inner-product space, hence in particular on
`R^n`, the bipolar `kᵒᵒ` of a gauge `k` equals the chapter closure `cl(k)`. -/
theorem gauge_polar_polar_eq_lowerSemicontinuousHull
    (k : E → EReal) [IsGauge k] :
    kᵒᵒ = cl(k) := by
  sorry

end
