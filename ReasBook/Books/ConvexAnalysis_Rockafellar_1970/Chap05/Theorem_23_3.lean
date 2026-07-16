import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [NormedField 𝕜] [Preorder 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 23.3 has three clauses. At a point `x` where a convex function `f` is
  finite-valued, nonemptiness of the subdifferential implies properness of `f`; emptiness of the
  subdifferential forces an infinite bilateral directional derivative in some direction; and the
  same infinite bilateral derivative occurs in every direction `z - x` with
  `z ∈ riDom[𝕜](f)`.
- `core/canonical`: the owner abstractions already present in the project are `Function.IsProper`,
  `_root_.subdifferentialAt`, `Function.HasBilateralDirectionalDerivativeAt`,
  `Function.directionalDerivativeAt`, `dom(·)`, and `riDom[𝕜](·)`.
- `bridge/view`: the source wording “subdifferentiable at `x`” is represented directly by
  `(_root_.subdifferentialAt f x).Nonempty`, while the source phrase “infinite bilateral
  directional derivative” is stated on the canonical owner
  `Function.HasBilateralDirectionalDerivativeAt ... ⊥`; the one-sided equality view is already a
  derived consequence of
  `Function.hasBilateralDirectionalDerivativeAt_iff_hasDirectionalDerivativeAt_and_neg`, so this
  file keeps only the owner-facing clauses as public API.

Domain-style sampling used here:
- `Function.IsProper` from `Chap01/Definition_4_6`;
- `Function.IsConvex.eq_bot_of_mem_riDom` from `Chap02/Theorem_7_2`;
- `Function.neg_directionalDerivativeAt_neg_le_of_finite_point` from `Chap05/Theorem_23_1`;
- `_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt` from `Chap05/Theorem_23_2`.

Primitive data vs derived API:
- primitive inputs: the convex function `f`, the base point `x`, the domain-side finiteness
  hypothesis `x ∈ dom(f)`, the lower-side finiteness hypothesis `f x ≠ ⊥` needed only in clause
  (1), and the owner-side status of `_root_.subdifferentialAt f x`;
- derived conclusions: properness of `f`, existence of an infinite bilateral directional
  derivative on the owner `Function.HasBilateralDirectionalDerivativeAt`, including the
  relative-interior specialization to directions `z - x`.

For clauses (2) and (3), the hypothesis `f x ≠ ⊥` is derived rather than primitive: if
`f x = ⊥`, then the defining inequality for `_root_.subdifferentialAt f x` is automatic for every
`xStar : Y`, so the subdifferential is the whole dual-side pairing space and in particular is not
empty.

Layer target: `source-facing`, stated directly on the canonical chapter owners.
-/

variable {f : E → WithBotTop 𝕜} {x : E}
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

-- Proof sketch: choose a subgradient `xStar ∈ _root_.subdifferentialAt f x`. The supporting
-- inequality `f z ≥ f x + xStar (z - x)` and the finiteness of `f x` rule out `f z = ⊥` for any
-- `z`, while `x ∈ dom(f)` and `f x ≠ ⊥` already give a finite point. Convexity is not needed for
-- this clause once a subgradient at `x` is given, so the theorem is stated in that stronger
-- owner-level form.
/-- Theorem 23.3 (1): if a function is finite-valued at `x` and is subdifferentiable at `x`, then
it is proper. -/
theorem isProper_of_subdifferentialAt_nonempty
    (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) (hsub : (∂[Y]f(x)).Nonempty) :
    f.IsProper := sorry

end Function

end

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Function

variable {f : E → WithBotTop 𝕜} {x : E}
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]
variable (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f))
variable (hsub : (∂[Y]f(x)) = ∅)

-- Proof sketch: if `f x = ⊥`, then every `xStar : Y` satisfies the defining
-- inequality for `_root_.subdifferentialAt f x`, contradicting `hsub`; hence `x ∈ dom(f)` and
-- emptiness already force `f x ≠ ⊥`. Then Theorem 23.2 identifies emptiness of the
-- subdifferential with failure of the directional-derivative lower-bound characterization.
-- Equivalently, the support function of `_root_.subdifferentialAt f x` collapses to `⊥`, so some
-- directional derivative is `⊥`; then Lemma 23.0.3 packages the reflected-direction equality as
-- the canonical owner
-- `HasBilateralDirectionalDerivativeAt ... ⊥`.
/-- Theorem 23.3 (2), owner form: if a convex function has empty subdifferential at `x` with
`x ∈ dom(f)`, then some direction has bilateral directional derivative `-∞`. -/
theorem exists_hasBilateralDirectionalDerivativeAt_eq_bot_of_subdifferentialAt_eq_empty :
    ∃ y : E, HasBilateralDirectionalDerivativeAt f x y ⊥ := sorry

end Function

end

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Function

variable {f : E → WithBotTop 𝕜} {x z : E}
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]
variable (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f))
variable (hsub : (∂[Y]f(x)) = ∅)

-- Proof sketch: by clause (2), emptiness of `_root_.subdifferentialAt f x` together with
-- `x ∈ dom(f)` already yields one direction with bilateral derivative `⊥`; the same emptiness
-- assumption also rules out `f x = ⊥`. Combine that owner clause with the convexity and
-- direction-side regularity of `y ↦ directionalDerivativeAt f x y`. Theorem 7.2 applies to that
-- convex directional-derivative function and propagates the value `⊥` from one direction to
-- every point of the relative interior of its effective domain. The standard cone-domain
-- description for directional derivatives at `x` then shows that every `z - x` with
-- `z ∈ riDom[𝕜](f)` lies in that relative interior, and Lemma 23.0.3 repackages the conclusion as a
-- bilateral owner statement.
/-- Theorem 23.3 (3), owner form: if a convex function has empty subdifferential at `x` with
`x ∈ dom(f)`, then for every `z ∈ riDom[𝕜](f)` the direction `z - x` has bilateral directional
derivative `-∞`. -/
theorem hasBilateralDirectionalDerivativeAt_sub_eq_bot_of_mem_riDom_of_subdifferentialAt_eq_empty
    (hz : z ∈ riDom[𝕜](f)) :
    HasBilateralDirectionalDerivativeAt f x (z - x) ⊥ := sorry

end Function

end
