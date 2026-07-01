import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped Rockafellar

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.6.1 specializes the family convex-hull theorem to functions supported at
  single points, with prescribed finite values `α i` at `a i` and `+∞` elsewhere.
- `core/canonical`: the chapter owners already available are the singleton indicator
  `δ(· | {a i})`, the family convex hull `conv(⨅ i, f i)`, the finite-simplex owner
  `StdSimplex 𝕜 s`, and the maximal minorant theorem `Function.isGreatest_conv_iInf_minorant`.
- `bridge/view`: the source family surface is used directly as
  `fun i x ↦ δ(x | ({a i} : Set E)) + α i`. The value formula is exposed directly as a
  finite-simplex set-builder specialization of
  `Function.convexHull_eq_sInf_convexCombination_values`, and the maximality claim is stated on
  the canonical hull `conv(⨅ i, fun x ↦ δ(x | ({a i} : Set E)) + α i)`.

Domain-style sampling used here:
- `indicator`;
- `StdSimplex`;
- `Function.convexHull_iInf_apply_eq_sInf_convexCombination_values`;
- `Function.isGreatest_conv_iInf_minorant`.

Layer target:
- no new owner is introduced, because the textbook surface already matches the canonical indicator
  notation;
- the theorems are `bridge/view` specializations of the existing canonical family convex-hull
  owners stated directly on that surface.
-/

section Formula

variable {E : Type u} {𝕜 : Type w} {I : Type v}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Function

-- Proof sketch: specialize `Function.convexHull_iInf_apply_eq_sInf_convexCombination_values` to
-- the family `fun i x ↦ δ(x | ({a i} : Set E)) + α i`. The singleton-support branch behavior of
-- `δ(x | ({a i} : Set E))` reduces admissible finite combinations to convex combinations of the
-- prescribed points `a i`, and the weighted value sum becomes `∑ λ_i α_i`.
/-- The convex hull of the singleton-indicator family
`f_i(x) = δ(x | ({a i} : Set E)) + α i` is the infimum of the weighted sums
`∑ λ_i α_i` over all finite convex-combination representations of `x` by the points `a i`. -/
theorem convexHull_iInf_indicator_singleton_add_eq_sInf_convexCombination_values
    (a : I → E) (α : I → 𝕜) (x : E) :
    conv(⨅ i, (fun x : E ↦ δ[𝕜](x | ({a i} : Set E)) + (α i : WithBotTop 𝕜))) x =
      sInf
        {r : WithBotTop 𝕜 |
          ∃ (s : Finset I) (w : StdSimplex 𝕜 s),
            x = w.sum (fun i c ↦ c • a i) ∧
              r = (by
                classical
                exact w.sum (fun i c ↦ (c : WithBotTop 𝕜) * (α i : WithBotTop 𝕜))
                  : WithBotTop 𝕜)} := sorry

end Function

end Formula

section GreatestMinorant

variable {E : Type u} {𝕜 : Type w} {I : Sort v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Function

-- Proof sketch: apply `Function.isGreatest_conv_iInf_minorant` to the family
-- `fun i x ↦ δ(x | ({a i} : Set E)) + α i`. For these singleton-support functions, the pointwise
-- minorant condition is equivalent to the single value constraint `h (a i) ≤ α i`, because the
-- right-hand side is `⊤` away from `a i`.
/-- Text 5.6.1: the convex hull of the singleton-support family is the greatest convex function
satisfying the pointwise constraints `f(a_i) ≤ α_i`. -/
theorem isGreatest_convexHull_iInf_indicator_singleton_add_minorant
    (a : I → E) (α : I → 𝕜) :
    IsGreatest
      {h : E → WithBotTop 𝕜 | h.IsConvex 𝕜 ∧ ∀ i : I, h (a i) ≤ α i}
      (conv(⨅ i, (fun x : E ↦ δ[𝕜](x | ({a i} : Set E)) + (α i : WithBotTop 𝕜)))) := sorry

end Function

end GreatestMinorant
