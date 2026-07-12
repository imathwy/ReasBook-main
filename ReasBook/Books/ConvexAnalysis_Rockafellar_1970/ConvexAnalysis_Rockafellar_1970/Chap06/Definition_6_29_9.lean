import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v r

namespace Bifunction

section

variable {𝕜 : Type r} {U : Type u} {X : Type v}
variable [Zero 𝕜]
variable (𝕜)

attribute [local instance] Classical.propDecidable

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.9 attaches to a linear transformation `A` the bifunction whose
  `u`-slice is the indicator of the singleton `{A u}`.
- `core/canonical`: this is the singleton specialization of the Chapter 6 set-valued-map indicator
  owner `δᵇ[𝕜](S)` from Definition 6.29.3, itself built from the Chapter 1 indicator
  `δ[𝕜](x | C)`.
- `bridge/view`: the textbook linear-map case is the specialization `graphIndicator 𝕜 A`, together
  with its pointwise `0`/`+∞` singleton formula.

Domain-style sampling used here:
- `indicator` and the notation `δ[𝕜](x | C)`;
- set-valued-map indicator notation `δᵇ[𝕜](S)`;
- `indicator_def`;
- `indicator_of_mem`;
- `indicator_of_notMem`.

Layer target: `core/canonical`, with `graphIndicator` exposed as the singleton-fiber view of the
existing set-valued-map indicator owner.
-/

/-- Definition 6.29.9, owner form: the singleton-graph indicator attached to a map `T`; its
`u`-slice is the Chapter 1 indicator of the singleton `{T u}`. The source-facing linear-map case
is `graphIndicator 𝕜 A`. -/
def graphIndicator (T : U → X) : U → X → WithBotTop 𝕜 :=
  δᵇ[𝕜](fun u ↦ ({T u} : Set X))

/-- `graphIndicator` is exactly the set-valued-map indicator owner specialized to singleton
fibers. -/
@[simp] theorem graphIndicator_eq_indicatorBifunction_singleton (T : U → X) :
    graphIndicator 𝕜 T = δᵇ[𝕜](fun u ↦ ({T u} : Set X)) :=
  rfl

/-- Sign-dual singleton-graph indicator attached to a map `T`; its `u`-slice is the negative of
the Chapter 1 indicator of the singleton `{T u}`. This is the canonical owner used for the
concave graph-indicator branch in later adjoint formulas. -/
def graphConcaveIndicator [Neg 𝕜] (T : U → X) : U → X → WithBotTop 𝕜 :=
  -graphIndicator 𝕜 T

/-- The concave singleton-graph owner is the pointwise negation of the convex owner. -/
@[simp] theorem graphConcaveIndicator_eq_neg_graphIndicator [Neg 𝕜]
    (T : U → X) :
    graphConcaveIndicator 𝕜 T = -graphIndicator 𝕜 T :=
  rfl

/-- Each slice of the singleton-graph indicator is the Chapter 1 indicator of the singleton image
`{T u}`. -/
theorem graphIndicator_slice
    (T : U → X) (u : U) :
    graphIndicator 𝕜 T u = (δ[𝕜](· | ({T u} : Set X))) := by
  funext x
  simp [graphIndicator]

/-- The singleton-graph indicator takes the value `0` at `T u` and `+∞` away from `T u`. In
particular, for a linear map `A`, this is the pointwise formula for `graphIndicator 𝕜 A`. -/
@[simp] theorem graphIndicator_cases
    (T : U → X) (u : U) (x : X) :
    graphIndicator 𝕜 T u x =
      if x = T u then (0 : WithBotTop 𝕜) else ⊤ := by
  simp [graphIndicator, indicator_def]

/-- Each slice of the singleton-graph concave indicator is the negative of the Chapter 1
indicator of the singleton image `{T u}`. -/
theorem graphConcaveIndicator_slice [Neg 𝕜]
    (T : U → X) (u : U) :
    graphConcaveIndicator 𝕜 T u = (-(δ[𝕜](· | ({T u} : Set X)))) := by
  rfl

/-- Pointwise branch formula for the singleton-graph concave indicator: it is `-0` at `T u` and
`-⊤ = ⊥` away from `T u`. -/
@[simp] theorem graphConcaveIndicator_cases [Neg 𝕜]
    (T : U → X) (u : U) (x : X) :
    graphConcaveIndicator 𝕜 T u x =
      if x = T u then (-(0 : WithBotTop 𝕜)) else ⊥ := by
  by_cases hx : x = T u
  · simp [graphConcaveIndicator, hx]
  · simp [graphConcaveIndicator, hx]

/-- At the singleton image point `T u`, the concave graph indicator equals `-0`. -/
@[simp] theorem graphConcaveIndicator_eq_neg_zero [Neg 𝕜]
    (T : U → X) (u : U) :
    graphConcaveIndicator 𝕜 T u (T u) = (-(0 : WithBotTop 𝕜)) := by
  simp [graphConcaveIndicator_cases]

/-- Away from `T u`, the concave graph indicator equals `⊥`. -/
@[simp] theorem graphConcaveIndicator_eq_bot_of_ne [Neg 𝕜]
    (T : U → X) (u : U) {x : X} (hx : x ≠ T u) :
    graphConcaveIndicator 𝕜 T u x = (⊥ : WithBotTop 𝕜) := by
  simp [graphConcaveIndicator_cases, hx]

end

end Bifunction
