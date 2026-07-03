import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_20
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_23
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient HessianDualLocalNorm

noncomputable section

universe u

/-
Corollary 5.3.4 lies in the Chapter 5 self-concordant-barrier / analytic-center / dual-local-norm
domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `IsMinOn` in `Definition_5_3_3`, the canonical analytic-center owner;
* `IsSelfConcordantBarrierOnWith.subset_dikinEllipsoid_barrierParameter_add_two_sqrt_of_isMinOn`
  in `Theorem_5_3_9`, the owner-level analytic-center inclusion theorem upstream in the same
  chapter;
* `HasPositiveDefiniteHessianOn` in `Definition_5_0_23`, the chapter owner for domain-level
  Hessian nondegeneracy;
* `HessianDualLocalNorm.ofPosDefMem` in `Definition_5_0_20`, the canonical bridge from
  `HasPositiveDefiniteHessianOn` to the Chapter 5 Hessian-metric dual local norm.

Best owner abstraction:
* source-facing: the analytic-center Hessian and dual-local-norm comparison bounds;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: `HessianDualLocalNorm.ofPosDefMem`, which derives the local Hessian data needed to
  evaluate the dual norm from the positive-definite-Hessian owner.

Primitive data:
* the barrier owner `hF : IsSelfConcordantBarrierOnWith dom ν F`;
* the analytic-center witness `hcenter : IsMinOn F dom (xStar : E)`;
* for the dual-norm comparison only, the domain-level positive-definite-Hessian owner
  `HasPositiveDefiniteHessianOn dom F`.

Derived API:
* the Loewner lower bound comparing `hessian F x` to the Hessian at the analytic center;
* the corresponding comparison of Hessian dual local norms, stated through the canonical
  domain-level bridge `HessianDualLocalNorm.ofPosDefMem`.

Source/core/bridge triage:
* source-facing: the textbook analytic-center comparison corollaries;
* core/canonical: the barrier owner `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: `HessianDualLocalNorm.ofPosDefMem`.

These corollaries carry genuine source-facing content, so they should remain theorem-shaped rather
than a pure recall. Their public surface is nevertheless barrier-owner based: the surrounding
Chapter 5 API already organizes barrier consequences under `IsSelfConcordantBarrierOnWith`, and
the dual-norm comparison should use the domain-level dual-norm bridge instead of exposing raw
determinant witnesses in the public statement. -/

namespace IsSelfConcordantBarrierOnWith

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: for a chosen analytic center `xStar`, Theorem 5.3.9 bounds the
-- `xStar`-local distance of every `x ∈ dom`, and Theorem 5.1.5 then turns the inclusion of the
-- unit Dikin ball at `x` into the larger Dikin ball at `xStar` of radius `ν + 2 √ν`. Rewriting
-- that ellipsoid inclusion in Loewner order gives the displayed Hessian comparison.
/-- Corollary 5.3.4: if `xStar` is an analytic center of a `ν`-self-concordant barrier on `dom`,
then for every `x ∈ dom` the Hessian at `x` dominates the Hessian at `xStar` in Loewner order by
the factor `(ν + 2 √ν)⁻²`. -/
theorem hessian_loewner_lower_bound_of_isMinOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E))
    (x : dom) :
    (1 / (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) ^ (2 : ℕ))) •
        hessian F (xStar : E) ≤
      hessian F x := by
  letI : IsSelfConcordantBarrierOnWith dom ν F := hF
  sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: use the support-function representation of the dual local norm as the supremum
-- of the pairing over the corresponding Dikin ellipsoid. The Loewner comparison from
-- `IsSelfConcordantBarrierOnWith.hessian_loewner_lower_bound_of_isMinOn` is equivalent to
-- inclusion of these ellipsoids,
-- which yields the stated comparison of inverse-Hessian dual norms after identifying vectors with
-- covectors through the Riesz map.
/-- The dual local norm of the covector corresponding to `v` at any point of a self-concordant
barrier domain is controlled by the corresponding dual local norm at an analytic center with
factor `ν + 2 √ν`. -/
theorem dualLocalNorm_le_barrierParameter_add_two_sqrt_mul_of_isMinOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [HasPositiveDefiniteHessianOn dom F]
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E))
    (x : dom)
    (v : E) :
    HessianDualLocalNorm.ofPosDefMem F x.2 (toDual ℝ E v) ≤
      ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) *
        HessianDualLocalNorm.ofPosDefMem F xStar.2 (toDual ℝ E v) := by
  letI : IsSelfConcordantBarrierOnWith dom ν F := hF
  sorry

end

end IsSelfConcordantBarrierOnWith

end
