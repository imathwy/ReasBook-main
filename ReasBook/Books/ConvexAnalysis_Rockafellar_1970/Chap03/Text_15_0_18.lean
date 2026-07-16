import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_17
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_15_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage:
- `source-facing`: Text 15.0.18 says that a symmetric closed bounded convex set `C` with
  `0 ∈ interior C` determines a unique Minkowski metric whose radius-`ε` balls are the translates
  `x + ε C`; specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` display.
- `core/canonical`: the owner abstractions are the upstream Chapter 15 convex-body owner
  `ConvexBody E`, the canonical set-symmetry predicate `Balanced ℝ (K : Set E)` from mathlib,
  the interior predicate `interior`, and the ambient metric owner `MetricSpace E`, refined by
  `MetricSpace.IsMinkowskiMetric`, from `Text_15_0_17`.
- `bridge/view`: the ball formula is stated with the canonical metric owner `closedBall` and the
  canonical pointwise-set expression `({x} : Set E) + ε • C`, after fixing the ambient owner
  `ρ : MetricSpace E`.

Domain-style sampling used here:
- the Chapter 15 owner abstraction `MetricSpace.IsMinkowskiMetric`;
- `Balanced ℝ` on convex sets as the canonical symmetry predicate;
- `Metric.closedBall` and pointwise set operations on subsets of `E`;
- the ambient mathlib owners `MetricSpace`, `IsClosed`, `Convex`, `Bornology.IsBounded`, and
  `interior`.

Primitive data vs derived API:
- primitive input: a convex body `K : ConvexBody E` together with
  `Balanced ℝ (K : Set E)` and `(0 : E) ∈ interior (K : Set E)`;
- derived output: the unique ambient metric owner `ρ : MetricSpace E` whose closed balls are
  exactly the translates and dilates of `(K : Set E)`.

Layer target: `bridge/view`, because the source identifies the geometric body from Theorem 15.2
with the metric owner abstraction from Text 15.0.17.
-/

-- Proof sketch: Theorem 15.2 gives the unique norm whose unit ball is `C`. Transport that norm
-- across the equivalence `minkowskiMetricNormEquiv` from Text 15.0.17 to obtain a Minkowski
-- metric. The distance formula `ρ(x, y) = k (x - y)` identifies the canonical closed ball
-- `Metric.closedBall x ε` with the `ε`-sublevel set of `k` translated by `x`, and the unit-ball
-- description of `C` rewrites that set as `({x} : Set E) + ε • C`. Uniqueness follows from the
-- inverse laws of the norm-metric correspondence.
/-- Text 15.0.18: if `C` is a symmetric closed bounded convex set in a finite-dimensional real
normed space and `0 ∈ interior C`, then there exists a unique Minkowski metric whose radius-`ε`
closed ball about `x` is the translate-dilate `({x} : Set E) + ε • C` for every `ε > 0`.
Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement. -/
theorem existsUnique_minkowskiMetric_of_balanced_zero_mem_interior
    (K : ConvexBody E)
    (hK_bal : Balanced ℝ (K : Set E))
    (hK_int : (0 : E) ∈ interior (K : Set E)) :
    ∃! ρ : MetricSpace E,
      ρ.IsMinkowskiMetric ∧
        (letI := ρ
         ∀ x : E, ∀ ε > 0,
           Metric.closedBall x ε = ({x} : Set E) + ε • (K : Set E)) :=
      sorry

end
