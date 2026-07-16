import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_6_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Theorem 5.4.6.2 stays on the compatibility owner `IsBetaCompatibleWith`.

Sampled declarations in the same domain:
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the source-facing compatibility owner;
* mathlib `ConvexCone.smul_mem` and `ConvexCone.add_mem`, the ambient cone-owner closure API;
* `IsPositivelyHomogeneousOn.smul_mem` from `Chap03/Definition_3_1_7`, the chapter's bundled
  nonnegative-scalar owner surface;
* `IsThreeTimesContDiffConcaveOnWith` from `Definition_5_4_6_1`, the neighboring subsection owner
  on the same cone-ordered map space.

Source/core/bridge triage:
* source-facing: Theorem 5.4.6.2 on positive linear combinations of `β`-compatible maps;
* core/canonical: closure of `IsBetaCompatibleWith Q₁ K F β` under nonnegative scaling and
  addition, matching the cone-owner surface already used elsewhere in the chapter;
* bridge/view: the source-faithful positive-combination theorem built directly from that
  nonnegative closure API.

Primitive data:
* `Q₁`, `K`, `F`, `β`, and the map `ξ`.

Derived API:
* the owner-level closure theorems `IsBetaCompatibleWith.smul` and `IsBetaCompatibleWith.add`;
* the source-facing specialization `IsBetaCompatibleWith.pos_combination`.

The previous carrier-level cone wrapper duplicated the owner predicate with no extra mathematics, so
this refinement keeps only the closure statements on `IsBetaCompatibleWith` itself and aligns the
scalar-closure surface with the chapter's canonical nonnegative-scalar cone API. -/

namespace IsBetaCompatibleWith

variable {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {β : NNReal}

-- Proof sketch: scaling a `β`-compatible map by a bundled nonnegative scalar preserves convexity
-- and differentiability data, and multiplies both derivative terms in the compatibility
-- inequality by the same nonnegative factor. For `α > 0` this is the cone-owner closure
-- `K.smul_mem`; for `α = 0` the rescaled map is the zero map, whose compatibility expression is
-- the zero vector.
/-- `NNReal`-scalar multiples of a `β`-compatible map are again `β`-compatible with the same
barrier. -/
theorem smul
    {ξ : E₁ → E₂} (hξ : IsBetaCompatibleWith Q₁ K F β ξ)
    (α : NNReal) :
    IsBetaCompatibleWith Q₁ K F β (α • ξ) := sorry

-- Proof sketch: the sum of two `β`-compatible maps preserves the shared convexity, interior,
-- parameter, and barrier data, while linearity of iterated derivatives turns the compatibility
-- expression for `ξ₁ + ξ₂` into the sum of the two corresponding expressions. Closure of `K`
-- under addition then gives the result.
/-- The sum of two `β`-compatible maps is again `β`-compatible with the same barrier. -/
theorem add
    {ξ₁ ξ₂ : E₁ → E₂}
    (hξ₁ : IsBetaCompatibleWith Q₁ K F β ξ₁)
    (hξ₂ : IsBetaCompatibleWith Q₁ K F β ξ₂) :
    IsBetaCompatibleWith Q₁ K F β (ξ₁ + ξ₂) := sorry

-- Proof sketch: apply the owner-level closure lemmas `IsBetaCompatibleWith.smul` to the two
-- positive coefficients viewed as `NNReal`, then combine the two resulting hypotheses with
-- `IsBetaCompatibleWith.add`.
/-- Theorem 5.4.6.2: positive linear combinations of `β`-compatible functions are again
`β`-compatible with the same self-concordant barrier. -/
theorem pos_combination
    {ξ₁ ξ₂ : E₁ → E₂} {α₁ α₂ : ℝ}
    (hξ₁ : IsBetaCompatibleWith Q₁ K F β ξ₁)
    (hξ₂ : IsBetaCompatibleWith Q₁ K F β ξ₂)
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    IsBetaCompatibleWith Q₁ K F β (α₁ • ξ₁ + α₂ • ξ₂) :=
  by
    simpa using
      IsBetaCompatibleWith.add
        (IsBetaCompatibleWith.smul hξ₁ ⟨α₁, hα₁.le⟩)
        (IsBetaCompatibleWith.smul hξ₂ ⟨α₂, hα₂.le⟩)

end IsBetaCompatibleWith

end
