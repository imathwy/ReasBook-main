import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable (H : Dᵒᵖ ⥤ A) [H.rightOp.IsHomological] [H.rightOp.ShiftSequence ℤ]

/-
Domain-style sampling:
- primary domain: long exact cohomology sequences attached to contravariant cohomological functors
  on pretriangulated categories;
- sampled owner declarations:
  `Functor.IsHomological`,
  `Functor.homologySequenceComposableArrows₅`,
  `Functor.homologySequenceComposableArrows₅_exact`,
  `ComposableArrows.Exact.δlast`,
  `Functor.homologySequenceδ`;
- best owner abstraction: the source-facing owner is a contravariant functor `H : Dᵒᵖ ⥤ A` with
  canonical cohomological predicate `H.rightOp.IsHomological`; the core exact-sequence API is the
  homological six-term sequence of `H.rightOp`;
- primitive data: a contravariant cohomological functor `H`, its shift sequence on `H.rightOp`,
  a distinguished triangle `T`, and a cohomological degree `n`;
- derived API: the centered five-term cohomology segment in `A`, obtained by truncating the
  canonical six-term owner for `H.rightOp` and reading its maps in the source-facing
  cohomological order;
- source/core/bridge triage:
  `source-facing`: the exact five-term cohomology segment for a contravariant cohomological
    functor `H : Dᵒᵖ ⥤ A`;
  `core/canonical`: `H.rightOp.IsHomological` together with
    `Functor.homologySequenceComposableArrows₅_exact` on `H.rightOp`;
  `bridge/view`: `ComposableArrows.Exact.δlast`, specialized through the source-facing maps
    `((H.rightOp.shift (n + 1)).map T.mor₁).unop`,
    `(H.rightOp.homologySequenceδ T n (n + 1) _).unop`,
    `((H.rightOp.shift n).map T.mor₂).unop`, and
    `((H.rightOp.shift n).map T.mor₁).unop`.
-/

/-- 13.3.5.1: for a distinguished triangle and a contravariant cohomological functor
`H : Dᵒᵖ ⥤ A`, the centered five-term cohomology segment
`H^{n + 1}(Y) ⟶ H^{n + 1}(X) ⟶ H^n(Z) ⟶ H^n(Y) ⟶ H^n(X)` is exact, where
`H^m(W)` is represented by `((H.rightOp.shift m).obj W).unop`. -/
@[stacks 0148]
theorem cohomologySequenceCenteredFiveTerm_exact
    (T : Triangle D) (hT : T ∈ distTriang D) (n : ℤ) :
    (mk₄ (((H.rightOp.shift (n + 1)).map T.mor₁).unop)
      ((H.rightOp.homologySequenceδ T n (n + 1) rfl).unop)
      (((H.rightOp.shift n).map T.mor₂).unop)
      (((H.rightOp.shift n).map T.mor₁).unop)).Exact := by
  have hδ := (H.rightOp.homologySequenceComposableArrows₅_exact T hT n (n + 1) rfl).δlast
  refine exact_of_δ₀ ?_ (exact_of_δ₀ ?_ ?_)
  · simpa [ShortComplex.unop] using
      (hδ.exact 2).unop.exact_toComposableArrows
  · simpa [ShortComplex.unop] using
      (hδ.exact 1).unop.exact_toComposableArrows
  · simpa [ShortComplex.unop] using
      (hδ.exact 0).unop.exact_toComposableArrows

end Functor
end CategoryTheory
