import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise Rockafellar

section IntrinsicInterior

variable
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 6.6.2 states the relative-interior and closure formulas for the
  Minkowski sum `C₁ + C₂` of two convex subsets of a finite-dimensional normed space over `𝕜`,
  with a specialization to the textbook `ℝ^n` model.
- `core/canonical`: the owner abstractions are `Convex.intrinsicInterior_linear_image` for
  relative interior under linear images, `ri_prod_eq` for products,
  `add_image_prod` for the addition-map image of a product, and `vadd_set_closure_subset` for
  the closure inclusion under continuous additive actions.
- `bridge/view`: Rockafellar's `ri` and `cl` are represented by `intrinsicInterior 𝕜` and
  `closure`, while the proof route factors the Minkowski sum through the linear addition map
  applied to the product set `C₁ ×ˢ C₂`; clause (2) is then rewritten from `+ᵥ` to the textbook
  pointwise-addition notation `+`.
- Domain-style sampling used here: `Convex.intrinsicInterior_linear_image`,
  `ri_prod_eq`, `add_image_prod`, and `vadd_set_closure_subset`.
- Best owner abstraction: there is no exact upstream additive theorem with the target interface, so
  the canonical owner remains `Convex.intrinsicInterior_linear_image`; clause (1) is therefore the
  minimal source-facing additive bridge obtained from that owner plus `ri_prod_eq`,
  while clause (2) is the minimal source-facing additive specialization of
  `vadd_set_closure_subset`, not a parallel replacement owner.
- Primitive data vs derived API: in clause (1), the primitive data are the two convexity proofs,
  so the Minkowski-sum relative-interior identity is derived API on the `Convex` owner; clause (2)
  adds no new primitive data and is the derived additive surface form of the canonical action
  theorem.
- Layer target: both clauses stay `source-facing`; clause (1) is a thin bridge on the chapter
  owner theorem, and clause (2) is a thin additive bridge on the canonical action theorem.
- Semantic note: the closure inclusion is valid without convexity assumptions, so those source
  adjectives are removed from clause (2) as mathematically redundant.
-/

namespace Convex

/-- Corollary 6.6.2 (1): for convex sets `C₁` and `C₂` in a finite-dimensional normed space over
`𝕜`, the relative interior of their Minkowski sum is the Minkowski sum of their relative
interiors.
Specializing to `EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` statement. This is the
source-facing additive bridge built from `Convex.intrinsicInterior_linear_image`. -/
-- Proof sketch: apply the linear-image theorem from Theorem 6.6 to the addition map
-- `(x₁, x₂) ↦ x₁ + x₂` on `E × E`, then simplify the source and target images with the product
-- formula from Text 6.18 and `Set.add_image_prod`.
@[simp] theorem intrinsicInterior_add {C₁ C₂ : Set E} (hC₁ : Convex 𝕜 C₁) (hC₂ : Convex 𝕜 C₂) :
    ri[𝕜](C₁ + C₂) = ri[𝕜](C₁) + ri[𝕜](C₂) := by
  simpa [ri_prod_eq, Set.add_image_prod] using
    (hC₁.prod hC₂).intrinsicInterior_linear_image
      (LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E)

end Convex

end IntrinsicInterior

section Closure

variable {E : Type*} [TopologicalSpace E] [Add E] [ContinuousAdd E]

namespace Set

/- Corollary 6.6.2 (2): for subsets `C₁` and `C₂` of a topological additive space, the sum of
their closures is contained in the closure of their Minkowski sum. Equivalently,
`closure C₁ + closure C₂ ⊆ closure (C₁ + C₂)`. This is the additive specialization of the
canonical theorem `vadd_set_closure_subset`; specializing further to
`EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` statement. -/
theorem closure_add_subset (C₁ C₂ : Set E) :
    closure C₁ + closure C₂ ⊆ closure (C₁ + C₂) := by
  simpa [vadd_eq_add] using (vadd_set_closure_subset C₁ C₂)

end Set

end Closure
