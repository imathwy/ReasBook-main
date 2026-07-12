import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12

universe u v w z

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {Y : Type w} [Zero U]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.13 specializes the generalized-program objective to the case of
  a convex bifunction and records that this zero-slice function is convex.
- `core/canonical`: the source-facing owner for the zero slice is already `Bifunction.objective`
  from Definition 6.29.12, while convexity of a bifunction is already owned by
  `Function.IsConvex 𝕜 (uncurry F)` from Definition 6.29.4.
- `bridge/view`: convexity of the objective is obtained by restricting the convex epigraph of
  `uncurry F` to first-coordinate value `u = 0`.

Domain-style sampling used here:
- `Bifunction.objective` from `Definition_6_29_12`;
- `objective_apply` from the same file;
- `Function.isConvex_iff_convex_epigraph` from `Chap01.Theorem_4_2`;
- `Function.IsConvex` from `Chap01.Theorem_4_2`.

Primitive data vs derived API:
- primitive source-facing owner: `(F)₀`;
- primitive convexity hypothesis: `(uncurry F).IsConvex 𝕜`;
- derived API: convexity of the zero slice `(F)₀.IsConvex 𝕜`.

Layer target:
- clause `(1)` is `core/canonical recall/use` for the objective-function owner;
- clause `(2)` first records the intrinsic fixed-slice owner theorem
  `Function.IsConvex.slice_fixed` at the primitive epigraph layer, then specializes it to the
  zero-slice theorem `Function.IsConvex.slice_zero` and finally to the source-facing objective
  theorem `Function.IsConvex.objective`.
-/

/- Definition 6.29.13 (1): for the generalized convex program associated with a convex bifunction
`F`, the objective function `F₀` is the zero slice already owned by `Bifunction.objective`. -/
recall objective

end

end Bifunction

namespace Function.IsConvex

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMulZeroClass 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid α] [SMul 𝕜 α] [LE α]

/-- A slice at a fixed first-coordinate value is convex whenever that value is fixed by all convex
combinations `(a, b)` with `a + b = 1`. -/
theorem slice_fixed
    {f : U × X → WithBotTop α} (hf : f.IsConvex 𝕜) {u : U}
    (hfixed : ∀ a b : 𝕜, 0 ≤ a → 0 ≤ b → a + b = 1 → a • u + b • u = u) :
    (fun x : X ↦ f (u, x)).IsConvex 𝕜 := by
  rw [Function.isConvex_iff_convex_epigraph] at hf ⊢
  let S : Set ((U × X) × α) := {r | f r.1 ≤ r.2}
  have hS : Convex 𝕜 S := by
    simpa [S] using hf
  intro p hp q hq a b ha hb hab
  have hp' : (((u, p.1), p.2) : (U × X) × α) ∈ S := by
    simpa [S] using hp
  have hq' : (((u, q.1), q.2) : (U × X) × α) ∈ S := by
    simpa [S] using hq
  simpa [S, Prod.smul_mk, Prod.mk_add_mk, hfixed a b ha hb hab] using
    hS hp' hq' ha hb hab

/-- Definition 6.29.13 (2): the zero-slice objective function of a convex
bifunction is convex. -/
theorem slice_zero
    {f : U × X → WithBotTop α} (hf : f.IsConvex 𝕜) :
    (fun x : X ↦ f (0, x)).IsConvex 𝕜 := by
  refine hf.slice_fixed ?_
  intro a b ha hb hab
  simp

-- Proof sketch: this is the source-facing `Bifunction.objective` specialization of the intrinsic
-- owner theorem `Function.IsConvex.slice_zero`.
theorem objective
    {F : U → X → WithBotTop α} (hF : (uncurry F).IsConvex 𝕜) :
    (F)₀.IsConvex 𝕜 := by
  simpa [Bifunction.objective, Function.uncurry] using
    (hF.slice_zero : (fun x : X ↦ uncurry F (0, x)).IsConvex 𝕜)

end

end Function.IsConvex
