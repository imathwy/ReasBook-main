import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_8
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Mul
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {E : Type*}

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 8.5 states the structural properties of the recession function `f0⁺` of
  a proper convex function and gives its global and closed-case quotient formulas.
- `core/canonical`: the owner abstractions already introduced earlier in the chapter are
  `Function.recessionFunction`, `Function.IsConvex 𝕜`, `Function.IsProper`, the primitive
  non-`⊥` codomain condition `∀ x, f x ≠ ⊥`, and the
  generic positive-homogeneity predicate `Function.PositivelyHomogeneous`.
- `bridge/view`: the displayed supremum formula is already the exact owner theorem
  `Function.recessionFunction_apply` from Corollary 8.5.1, while the closed-case clauses
  below remain source-facing quotient and limit formulations.

Domain-style sampling used here:
- `Function.recessionFunction`;
- `Function.recessionFunction_apply`;
- `Function.IsConvex 𝕜`;
- `Function.IsProper`;
- `isClosed_recessionCone`;
- `LowerSemicontinuous`.

Primitive data vs derived API:
- primitive input: a function `f : E → WithTopBot α`;
- owner hypotheses: clause (2) stays at the additive-zero properness owner layer, while
  clauses (1), (3), and (5) use the primitive codomain side condition
  `∀ z, f z ≠ ⊥` together with convexity/closedness; the fixed-basepoint closed-case formulas
  (6) and (7) stay on the same primitive non-`⊥` codomain layer rather than taking
  `f.IsProper` directly;
- minimality note for remaining concrete clauses: parts (6) and (7) are stated with scalar
  difference quotients `((f (x + t • y) - f x) / (t : WithTopBot 𝕜))` and `t : 𝕜`, so the
  ordered scalar-module layer there is statement-level data, not proof-local
  artifacts;
- derived API: positive homogeneity, properness, and convexity of `f0⁺`, the
  already-established global supremum formula, and the closed-case quotient formulas at a fixed
  base point.

Layer target: this file stays `source-facing`, with theorem surfaces attached directly to the
canonical owner namespace `Function` (for `recessionFunction`) instead of compatibility wrappers.
-/

namespace Function

section

variable {α : Type*}
variable [AddCommGroup α] [ConditionallyCompleteLattice α]
variable [Add E]
variable (f : E → WithTopBot α)

/-- Theorem 8.5 (2): the recession function `f0⁺` of a proper convex function is proper. -/
-- Proof sketch: `(f0⁺) 0 = 0` gives a point of the epigraph, while the recession-cone
-- description of the epigraph shows that no value of `f0⁺` can be `⊥`.
theorem recessionFunction_isProper (hf_proper : f.IsProper) : (f₀⁺).IsProper := sorry

end

section

variable {α : Type*}
variable [AddCommGroup α] [ConditionallyCompleteLattice α]
variable [Add E]
variable (f : E → WithTopBot α)

/- Theorem 8.5 (4): for every vector `y`, the recession function satisfies the global formula
`f0⁺(y) = sup {f (x + y) - f x | x ∈ dom f}`. This is exactly the owner theorem from
Corollary 8.5.1. -/
recall recessionFunction_apply

end

section

variable {𝕜 : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable (f : E → WithTopBot 𝕜)

/-- Primitive owner form of Theorem 8.5 (1): under convexity and the primitive non-`⊥`
codomain condition, the recession function `f0⁺` is positively homogeneous. -/
-- Proof sketch: view the epigraph of `f0⁺` as the recession cone of the epigraph of
-- `f`. Recession cones are closed under positive scaling, so the resulting vertical infimum is
-- positively homogeneous.
theorem recessionFunction_positivelyHomogeneous_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot 𝕜)) :
    ((f)₀⁺).PositivelyHomogeneous 𝕜 := sorry

/-- Theorem 8.5 (1), proper specialization. -/
theorem recessionFunction_positivelyHomogeneous
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper) :
    ((f)₀⁺).PositivelyHomogeneous 𝕜 :=
  recessionFunction_positivelyHomogeneous_of_ne_bot (f := f) hf_convex
    (fun z => hf_proper.ne_bot z)

end

section

variable {𝕜 : Type*} {α : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α]
variable (f : E → WithTopBot α)

/-- Primitive owner form of Theorem 8.5 (3): under convexity and the primitive non-`⊥`
codomain condition, the recession function `f0⁺` is convex. -/
-- Proof sketch: identify the epigraph of `f0⁺` with the recession cone of the
-- epigraph of `f`. Convexity of `epi f` implies convexity of its recession cone.
theorem recessionFunction_isConvex_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot α)) :
    ((f)₀⁺).IsConvex 𝕜 := sorry

/-- Theorem 8.5 (3), proper specialization. -/
theorem recessionFunction_isConvex
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper) :
    ((f)₀⁺).IsConvex 𝕜 :=
  recessionFunction_isConvex_of_ne_bot (f := f) hf_convex
    (fun z => hf_proper.ne_bot z)

end

section

variable {𝕜 : Type*} {α : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [TopologicalSpace α] [OrderTopology α]
variable [Module 𝕜 α]
variable [TopologicalSpace (WithTopBot α)] [OrderTopology (WithTopBot α)]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable (f : E → WithTopBot α)

open Filter
open scoped Topology

/-- Primitive owner form of Theorem 8.5 (5): if `f` is closed, convex, and nowhere `⊥`, then its
recession function `f0⁺` is closed as well, here expressed by lower semicontinuity in a scalar
topological vector space, with codomain neighborhoods taken in the order topology on
`WithTopBot α`. -/
-- Proof sketch: the epigraph of `f0⁺` is the recession cone of the epigraph of `f`.
-- Lower semicontinuity makes `epi f` closed, and the recession cone of a closed convex set is
-- closed, so `f0⁺` is lower semicontinuous.
theorem recessionFunction_lowerSemicontinuous_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot α))
    (hf_closed : LowerSemicontinuous f) :
    LowerSemicontinuous ((f)₀⁺) := sorry

/-- Theorem 8.5 (5), proper specialization. -/
theorem recessionFunction_lowerSemicontinuous
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f) :
    LowerSemicontinuous ((f)₀⁺) :=
  recessionFunction_lowerSemicontinuous_of_ne_bot (f := f) hf_convex
    (fun z => hf_proper.ne_bot z) hf_closed

end

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable (f : E → WithTopBot 𝕜)

open Filter
open scoped Topology

/-- Theorem 8.5 (6): if `f` is closed, nowhere `⊥`, and `x ∈ dom f`, then `f0⁺(y)` is the
supremum of the positive difference quotients `[(f (x + λ y) - f x) / λ]` based at `x`. -/
-- Proof sketch: apply Theorem 8.3 to the closed convex epigraph of `f`. For a fixed base point
-- `(x, f x)` in `epi f`, the smallest slope `v` for which the ray in direction `(y, v)` stays in
-- `epi f` is independent of `x`, and this slope is exactly the supremum of the positive
-- difference quotients at that base point.
theorem recessionFunction_eq_sSup_differenceQuotients_at_point
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot 𝕜))
    (hf_closed : LowerSemicontinuous f)
    {x : E} (hx : x ∈ dom f) (y : E) :
    ((f)₀⁺) y =
      sSup {r : WithTopBot 𝕜 |
        ∃ t : 𝕜, 0 < t ∧ r = (f (x + t • y) - f x) / (t : WithTopBot 𝕜)} := sorry

/-- Theorem 8.5 (7): if `f` is closed, nowhere `⊥`, and `x ∈ dom f`, then the positive
difference quotient `[(f (x + λ y) - f x) / λ]` tends to `f0⁺(y)` as `λ → +∞`. -/
-- Proof sketch: Theorem 23.1 shows that for a convex function the difference quotient in `λ` is
-- monotone nondecreasing. The preceding supremum formula identifies its least upper bound with
-- `(f0⁺) y`, so monotone convergence yields the limit at `+∞`.
theorem tendsto_differenceQuotient_atTop_recessionFunction
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z, f z ≠ (⊥ : WithTopBot 𝕜))
    (hf_closed : LowerSemicontinuous f)
    {x : E} (hx : x ∈ dom f) (y : E) :
    Tendsto (fun t : 𝕜 ↦ (f (x + t • y) - f x) / (t : WithTopBot 𝕜)) atTop
      (𝓝 (((f)₀⁺) y)) := sorry

end

end Function

end
