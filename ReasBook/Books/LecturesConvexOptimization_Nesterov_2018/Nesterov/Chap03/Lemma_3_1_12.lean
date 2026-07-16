import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_1_1_5
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise Topology WithTopConvexAnalysis

universe u

/- Lemma 3.1.12 lies in the chapter's weighted-sum / subdifferential calculus for closed convex
`WithTop ℝ`-valued functions on the intrinsic ambient spaces already used by the chapter owners.

Sampled owner declarations:
- `dom` and `withTopRealPart` from `Definition_3_3`
- `ClosedConvexOn` and `ClosedConvexFunction` from `Definition_3_1_1_5`
- `subdifferential` and the notation `∂ f(x)` from `Definition_3_1_5`
- `ClosedConvexOn.nonneg_smul` and `ClosedConvexOn.add_inter` from `Theorem_3_1_5`

Best owner abstraction:
- the canonical pointwise weighted sum
  `((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂)`

Primitive data:
- the scalars `α₁`, `α₂`
- the functions `f₁`, `f₂`

Derived API:
- `withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos`
- `ClosedConvexFunction.nonneg_weighted_add`
- `interior_effectiveDomain_nonneg_weighted_add_eq_of_pos`
- `subdifferential_nonneg_weighted_add_eq_of_pos`

Source/core/bridge triage:
- source-facing: the numbered weighted-sum conclusions of Lemma 3.1.12
- core/canonical:
  `dom`, `ClosedConvexOn`, `ClosedConvexFunction`, `subdifferential`,
  pointwise scalar multiplication, and pointwise addition
- bridge/view: the positive-weight effective-domain identity for the canonical weighted sum

The previous local wrapper changed the mathematics at zero weights by forcing finiteness on
`dom f₁ ∩ dom f₂`. This refinement removes that duplicate wheel and states the lemma directly for
the canonical pointwise weighted sum. Strict positivity now appears exactly on the domain,
interior-domain, and subdifferential formulas where the common-domain identity is valid; the
closed-convex statement itself remains at the correct nonnegative-weight level. -/

section WeightedAdd

variable {X : Type u}

section ClosedConvex

variable [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
variable {f₁ f₂ : X → WithTop ℝ} {α₁ α₂ : ℝ}

/-- The nonnegative weighted pointwise sum of two closed convex functions is again a closed convex
function. -/
-- Proof sketch: apply the canonical owner rules `ClosedConvexOn.nonneg_smul` and
-- `ClosedConvexOn.add_inter` to the positive-weight case, and split the zero-weight cases to the
-- corresponding single-summand scalar-multiple statements.
theorem ClosedConvexFunction.nonneg_weighted_add
    (hf₁ : ClosedConvexFunction f₁)
    (hf₂ : ClosedConvexFunction f₂)
    (hα₁ : 0 ≤ α₁)
    (hα₂ : 0 ≤ α₂) :
    ClosedConvexFunction ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂) := sorry

end ClosedConvex

section EffectiveDomainInterior

variable [TopologicalSpace X]
variable {f₁ f₂ : X → WithTop ℝ} {α₁ α₂ : ℝ}

/-- Under strictly positive weights, the effective domain of the canonical weighted pointwise sum
is exactly the common effective domain of the two summands. -/
-- Proof sketch: positivity forces every occurrence of `⊤` in either summand to remain `⊤` after
-- scalar multiplication, so finiteness of the pointwise sum is equivalent to simultaneous
-- finiteness of both summands.
theorem withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂) =
      dom f₁ ∩ dom f₂ := sorry

/-- Lemma 3.1.12 (1): under strictly positive weights, the interior of the effective domain of the
canonical weighted pointwise sum equals the intersection of the interiors of the summand domains.
-/
-- Proof sketch: rewrite the effective domain using
-- `withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos`, then apply the canonical
-- topological identity `interior (A ∩ B) = interior A ∩ interior B`.
theorem interior_effectiveDomain_nonneg_weighted_add_eq_of_pos
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    interior (dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂)) =
      interior (dom f₁) ∩ interior (dom f₂) := sorry

end EffectiveDomainInterior

section Subdifferential

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {f₁ f₂ : V → WithTop ℝ} {α₁ α₂ : ℝ}

/-- Lemma 3.1.12 (2): if `f₁` and `f₂` are closed convex and `α₁, α₂ > 0`, then at every interior
point of the effective domain of the canonical weighted pointwise sum, its subdifferential equals
the Minkowski sum of the scaled pointwise subdifferentials. -/
-- Proof sketch: use `interior_effectiveDomain_nonneg_weighted_add_eq_of_pos` to place `x` in the
-- common interior effective domain of the summands. There the ordinary weighted sum is finite, so
-- the directional-derivative sum rule and the support-function description of subdifferentials
-- identify the subdifferential of the weighted sum with the weighted Minkowski sum.
theorem subdifferential_nonneg_weighted_add_eq_of_pos
    (hf₁ : ClosedConvexFunction f₁)
    (hf₂ : ClosedConvexFunction f₂)
    (hα₁ : 0 < α₁)
    (hα₂ : 0 < α₂)
    {x : V}
    (hx : x ∈ interior (dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂))) :
    ∂ (((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂))(x) =
      α₁ • ∂ f₁(x) + α₂ • ∂ f₂(x) := sorry

end Subdifferential

end WeightedAdd

end
