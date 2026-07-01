import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_31_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_5_2

open Bornology

noncomputable section

open scoped RealInnerProductSpace Rockafellar

universe u

namespace Function

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g : E → EReal}

local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ
local notation "IsClosedProperConcave[ℝ]" => @Function.IsClosedProperConcave ℝ

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.5.3 gives three sufficient conditions for existence of the
  Chapter 38 function inner product.
- `core/canonical`: the owner abstractions already present are `Function.HasInnerProduct`,
  `convexConjugate` with notation `f⋆`, `concaveConjugate`, and the domain-relative-interior
  notation `riDom(·)`.
- `bridge/view`: the source phrases `dom g` and `dom g^*` for a concave function are rendered in
  the chapter orientation by `dom(-g)` and `dom(-concaveConjugate g)`, since the project's
  effective-domain owner is phrased on the convex side of the sign-duality.

Primary mathematical domain:
- Fenchel duality and existence of the Chapter 38 inner product.

Domain-style sampling used here:
- `Function.HasInnerProduct` from `Definition_38_5_2`;
- `riDom(·)` from `Chap01.Definition_4_4`;
- `convexConjugate` / `concaveConjugate` from Chapters 3 and 6.

Primitive data vs derived API:
- primitive inputs: a convex function `f` and a concave function `g` on a finite-dimensional real
  inner-product space;
- primitive owner layer already upstream: `HasInnerProduct f g`;
- derived API here: three source-facing sufficient conditions for that owner.

Layer target: `source-facing`, stated directly on `HasInnerProduct f g` rather than through a
parallel strong-duality package.
-/

-- Proof sketch: interpret `HasInnerProduct f g` as the zero-duality-gap statement
-- `sup_x (g* x - f x) = inf_y (f* y - g y)`. Apply the identity-map Fenchel theorem in the
-- orientation where the primal side is `f` and the dual side is `g*`; the closed proper concave
-- owner on `g` identifies `g**` with `g`, and the source condition
-- `ri(dom f) ∩ ri(dom g^*) ≠ ∅` is rendered by `riDom(f) ∩ riDom(-g∗)`.
/-- Proposition 38.5.3 (1): if `f` is convex proper, `g` is closed proper concave, and
`ri (dom f)` meets `ri (dom g^*)`, rendered by `riDom(f)` meeting `riDom(-g∗)`, then the
Chapter 38 inner product of `f` and `g` exists. -/
theorem hasInnerProduct_of_g_closed_and_nonempty_inter_riDom_f_concaveConjugate
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    (hg : IsClosedProperConcave[ℝ] g)
    (hri : (riDom(f) ∩ riDom(-(g∗ : E → EReal))).Nonempty) :
    HasInnerProduct f g := sorry

-- Proof sketch: apply the same identity-map Fenchel theorem to the primal objective
-- `y ↦ f⋆ y - g y`. Closedness of `f` identifies `(f⋆)⋆` with `f`, and the source condition
-- `ri(dom g) ∩ ri(dom f^*) ≠ ∅` is represented by the chapter owners
-- `riDom(-g) ∩ riDom(f⋆)`.
/-- Proposition 38.5.3 (2): if `g` is concave proper, `f` is closed proper convex, and
`ri (dom g)` meets `ri (dom f^*)`, rendered by `riDom(-g)` meeting `riDom(f⋆)`, then the
Chapter 38 inner product of `f` and `g` exists. -/
theorem hasInnerProduct_of_f_closed_and_nonempty_inter_riDom_g_convexConjugate
    (hf : IsClosedProperConvex[ℝ] f)
    (hg_concave : g.IsConcave ℝ) (hg_proper : (-g).IsProper)
    (hri : (riDom(-g) ∩ riDom(f⋆)).Nonempty) :
    HasInnerProduct f g := sorry

-- Proof sketch: if `dom(f)` is bounded, Chapter 13 makes `f⋆` finite everywhere, so
-- `riDom(f⋆) = Set.univ`; similarly, boundedness of the concave-side effective domain `dom(-g)`
-- makes `-concaveConjugate g` finite everywhere. Hence one of the two previous relative-interior
-- qualifications becomes automatic, and `HasInnerProduct f g` follows.
/-- Proposition 38.5.3 (3): a simple sufficient condition is that `f` be closed proper convex,
`g` be closed proper concave, and that either `dom(f)` or the concave-side effective domain
`dom(-g)` corresponding to the source `dom g` be bounded. -/
theorem hasInnerProduct_of_closed_and_bounded_effectiveDomain
    (hf : IsClosedProperConvex[ℝ] f)
    (hg : IsClosedProperConcave[ℝ] g)
    (hdom_bounded : IsBounded dom(f) ∨ IsBounded dom(-g)) :
    HasInnerProduct f g := sorry

end

end Function
