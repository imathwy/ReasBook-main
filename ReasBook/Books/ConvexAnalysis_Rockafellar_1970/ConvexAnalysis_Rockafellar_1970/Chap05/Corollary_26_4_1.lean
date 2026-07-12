import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_1_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Remark_5_24_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_26_3

noncomputable section

open scoped Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 26.4.1 identifies the Legendre-side domain
  `D = dom∂[E](fStar)` for `fStar = (f⋆ : StrongDual ℝ E → WithBotTop ℝ)`, records the
  almost-convex sandwich
  `riDom(fStar) ⊆ D ⊆ dom(fStar)`, and packages the strict-convexity clause on convex subsets of `D`
  through the canonical owner `Function.IsEssentiallyStrictlyConvex (Y := E) fStar`.
- `core/canonical`: the chapter owners already present are `dom∂(·)`, `riDom(·)`, `dom(·)`, and
  `Function.IsEssentiallyStrictlyConvex`.
- `bridge/view`: the textbook set `{xStar | ∂f⋆(xStar) ≠ ∅}` is already the canonical owner
  `dom∂[E](fStar)`; the Euclidean graph-domain view `(Function.subdifferentialGraph f⋆).dom` is
  only a companion reformulation.

Domain-style sampling used here:
- `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- `Function.IsEssentiallyStrictlyConvex` from `Definition_26_2_1`;
- `domSubdifferential_between_riDom_and_dom_of_convex_proper` from `Remark_5_24_1`;
- `Function.IsClosedProperConvex
    .isEssentiallyStrictlyConvex_iff_convexConjugate_isEssentiallySmooth` from `Theorem_26_3`.

Primitive data vs derived API:
- primitive inputs: the genuinely extra closedness hypothesis `LowerSemicontinuous f` and the
  source hypothesis `f.IsEssentiallySmooth`, whose owner already carries convexity and properness;
- primitive source-facing owner set: the Legendre-side domain `D = dom∂[E](fStar)`;
- derived API: the conjugate-side owner `Function.IsEssentiallyStrictlyConvex (Y := E) fStar` and
  domain sandwich.

Layer target: `source-facing`, stated directly through the chapter owner set `dom∂[E](fStar)` and the
canonical Chapter 26 owner `Function.IsEssentiallyStrictlyConvex (Y := E) fStar`, rather than
through the Euclidean graph-domain view or an unpacked strict-convexity clause.
-/

namespace Function.IsClosedProperConvex

variable {f : E → WithBotTop ℝ}
local notation "fStar" => (f⋆ : StrongDual ℝ E → WithBotTop ℝ)

local notation "D" => dom∂[E](fStar)

-- Proof sketch: combine `hclosed` with the convexity and properness fields already carried by
-- `hess` to build the closed-proper-convex owner for `f`. Apply Theorem 26.3 on the conjugate
-- side to obtain `Function.IsEssentiallyStrictlyConvex (Y := E) fStar`. Then apply Remark 5.24.1 to
-- the closed proper convex conjugate `f⋆` to obtain the sandwich
-- `riDom(fStar) ⊆ dom∂[E](fStar) ⊆ dom(fStar)`.
/-- Corollary 26.4.1: if `f` is essentially smooth and closed proper convex, then on the canonical
Legendre-side domain `D = dom∂[E](fStar)` for `fStar = (f⋆ : StrongDual ℝ E → WithBotTop ℝ)`,
equivalently `D = {xStar | (∂[E]fStar(xStar)).Nonempty}`, the conjugate-side Chapter 26 owner
`Function.IsEssentiallyStrictlyConvex (Y := E) fStar` holds, and one has the almost-convex
sandwich `ri(dom fStar) ⊆ D ⊆ dom(fStar)`. -/
theorem convexConjugate_isEssentiallyStrictlyConvex_and_subgradientDom_between
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth) :
    Function.IsEssentiallyStrictlyConvex (Y := E) fStar ∧
      riDom(fStar) ⊆ D ∧
      D ⊆ dom(fStar) := by
  sorry

end Function.IsClosedProperConvex

end
