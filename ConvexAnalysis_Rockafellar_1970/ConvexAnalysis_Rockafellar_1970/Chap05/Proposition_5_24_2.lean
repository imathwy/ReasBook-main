import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open Filter
open scoped Topology

section

variable {𝕜 : Type v}
variable [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace Function

/- Local bridge so theorem surfaces stay on `WithTopBot` while reusing chapter scalar action. -/
local instance instSMulWithTopBot_iterated : SMul 𝕜 (WithTopBot 𝕜) :=
  (show SMul 𝕜 (WithBotTop 𝕜) from inferInstance)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 5.24.2 studies the directional derivatives of the convex
  direction-function `y ↦ directionalDerivativeAt f x y` at a direction `y` where that value is
  finite, and compares every such iterated directional derivative with the first-order directional
  derivative in the same direction.
- `core/canonical`: the owner abstraction is already the Chapter 23 directional-derivative owner
  `Function.directionalDerivativeAt`; the proposition should therefore remain on
  `directionalDerivativeAt (directionalDerivativeAt f x) y z` rather than introducing a second
  local wrapper such as `secondDirectionalDerivativeAt`.
- `bridge/view`: the first displayed formula in the source is exactly the canonical owner
  definition of `Function.directionalDerivativeAt`, specialized to the function
  `directionalDerivativeAt f x : E → WithTopBot 𝕜`; the only new theorem-level content here is the
  inequality against `directionalDerivativeAt f x z`.

Domain-style sampling used here:
- `Function.directionalDerivativeAt` from
  `Items/Chap05/Lemma_23_0_1.lean`;
- the chapter effective-domain owner `dom(·)` and its membership bridge
  `mem_effectiveDomain` from `Items/Chap01/Definition_4_4.lean`;
- `Function.directionalDerivativeAt_eq_sInf_directionalDifferenceQuotientAt` from
  `Items/Chap05/Theorem_23_1.lean`, which gives the canonical finite-point owner formula reused
  here for the iterated derivative after the proposition's own finiteness hypotheses are first
  used to recover the missing lower finiteness `f x ≠ ⊥`;
- `Function.isConvex_directionalDerivativeAt_of_finite_point`,
  `Function.positivelyHomogeneous_directionalDerivativeAt_of_finite_point`, and
  `Function.directionalDerivativeAt_zero_of_finite_point` from
  `Items/Chap05/Theorem_23_1.lean`,
  which are the nearest owner-level regularity package for the direction-function
  `y ↦ directionalDerivativeAt f x y` once that lower finiteness has been recovered.

Primitive data vs derived API:
- primitive data: the convex function `f`, the finite base point `x ∈ dom(f)`, the direction `y`
  where `directionalDerivativeAt f x y` is finite, and the comparison direction `z`;
- primitive owner reused from upstream: `Function.directionalDerivativeAt`;
- owner-side abstraction governing the proof shape: the proposition first derives the missing
  lower finiteness `f x ≠ ⊥` from the finiteness of `directionalDerivativeAt f x y`, then applies
  the finite-point Chapter 23 owner package to the direction-function
  `g := directionalDerivativeAt f x`; Proposition 5.24.2 is therefore a thin owner-level
  inequality for the existing directional-derivative owner rather than a new
  “second directional derivative” API;
- the finite-value hypothesis at the iterated base point is surfaced with the canonical
  primitive owner pair `y ∈ dom(directionalDerivativeAt f x)` and
  `directionalDerivativeAt f x y ≠ ⊥`.
- derived API: the iterated-owner inequality below. The notation-level source identity
  `f'(x; y; z) = lim ...` is not a second owner and is handled by direct recall of the owner
  definition `Function.directionalDerivativeAt`.

Layer target: `bridge/view`. The proposition does not define a new mathematical owner; it gives a
source-facing inequality for the existing Chapter 23 owner.

Ambient-assumption minimization:
- the statement uses only convexity on a scalar-action space and the existing
  `WithTopBot 𝕜`-input directional-derivative owner, so it stays at
  `[AddCommMonoid E] [SMul 𝕜 E]` with the scalar/order/topology assumptions already required by
  the owner package from `Theorem_23_1`;
- no additional norm/topology/inner-product/finite-dimensional structure on `E` is needed on the
  public theorem surface.
-/

/- Proposition 5.24.2 first reuses the canonical Chapter 23 owner definition for directional
derivatives, specialized to the convex direction-function `directionalDerivativeAt f x`. -/
recall Function.directionalDerivativeAt
    {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
    [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
    (f : E → WithTopBot 𝕜) (x d : E) : WithTopBot 𝕜 :=
  limUnder (𝓝[>] (0 : 𝕜)) (directionalDifferenceQuotientAt f x d)

-- Proof sketch: first use the proposition's own finiteness hypotheses on
-- `g := directionalDerivativeAt f x` to recover the missing lower finiteness `f x ≠ ⊥`. The
-- finite-point owner package from Theorem 23.1 then applies to `g`, making it convex,
-- positively homogeneous, and normalized by `g 0 = 0`. Apply the owner formula for
-- `directionalDerivativeAt g y z` at the finite point `y`, and bound each positive difference
-- quotient of `g` by the subadditivity estimate `g (y + t • z) ≤ g y + t • g z`.
/-- Owner-level comparison at the primitive directional-function layer: if `g` is convex,
positively homogeneous, normalized by `g 0 = 0`, and finite at `y`, then every directional
derivative of `g` at `y` is bounded above by the first-order value `g z` in the comparison
direction. -/
theorem directionalDerivativeAt_le_of_isConvex_of_positivelyHomogeneous_of_zero
    {g : E → WithTopBot 𝕜}
    (hg_convex : g.IsConvex 𝕜) (hg_hom : g.PositivelyHomogeneous 𝕜) (hg_zero : g 0 = 0)
    {y : E} (hy : y ∈ dom(g)) (hy_bot : g y ≠ ⊥) (z : E) :
    directionalDerivativeAt g y z ≤ g z := by
  sorry

end Function

end

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace Function

/- Local bridge so theorem surfaces stay on `WithTopBot` while reusing chapter scalar action. -/
local instance instSMulWithTopBot_second : SMul 𝕜 (WithTopBot 𝕜) :=
  (show SMul 𝕜 (WithBotTop 𝕜) from inferInstance)

/-- Proposition 5.24.2, owner form: if `f` is convex, `x ∈ dom(f)`, and the directional
derivative `directionalDerivativeAt f x y` is finite, then the directional derivatives of the
convex direction-function `directionalDerivativeAt f x` at `y` are bounded above by the
first-order directional derivative in the same comparison direction. The source notation
`f'(x; y; z)` is represented canonically by
`directionalDerivativeAt (directionalDerivativeAt f x) y z`. -/
theorem iterated_directionalDerivativeAt_le
    {f : E → WithTopBot 𝕜} (hf_convex : f.IsConvex 𝕜) {x : E} (hx : x ∈ dom(f))
    {y : E} (hy : y ∈ dom(directionalDerivativeAt f x))
    (hy_bot : directionalDerivativeAt f x y ≠ ⊥) (z : E) :
    directionalDerivativeAt (directionalDerivativeAt f x) y z ≤ directionalDerivativeAt f x z := by
  have hx_bot : f x ≠ ⊥ := by
    sorry
  let g : E → WithTopBot 𝕜 := directionalDerivativeAt f x
  have hg_convex : g.IsConvex 𝕜 := by
    simpa [g] using
      (Function.isConvex_directionalDerivativeAt_of_finite_point
        (f := f) (x := x) hf_convex hx hx_bot)
  have hg_hom : g.PositivelyHomogeneous 𝕜 := by
    simpa [g] using
      (Function.positivelyHomogeneous_directionalDerivativeAt_of_finite_point
        (f := f) (x := x) hf_convex hx hx_bot)
  have hg_zero : g 0 = 0 := by
    simpa [g] using
      (Function.directionalDerivativeAt_zero_of_finite_point
        (f := f) (x := x) hf_convex hx hx_bot)
  have hy' : y ∈ dom(g) := by
    simpa [g] using hy
  have hy_bot' : g y ≠ ⊥ := by
    simpa [g] using hy_bot
  simpa [g] using
    (directionalDerivativeAt_le_of_isConvex_of_positivelyHomogeneous_of_zero
      (g := g) hg_convex hg_hom hg_zero hy' hy_bot' z)

end Function

end
