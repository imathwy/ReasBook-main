import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜] [DecidableLT 𝕜] [AddCommGroup 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.28.3 states that for each fixed primal point `x`, the
  Lagrangian slice in the multiplier variable `u⋆` is concave.
- `core/canonical`: the Lagrangian owner is `OrdinaryConvexProgram.saddleLagrangian` from
  `Definition_6_28_3`, with the multiplier-set and branch lemmas supplied by
  `Definition_6_28_6`.
- `bridge/view`: the chapter's canonical owner for global extended-valued concavity is
  `Function.IsConcave`, while `Function.IsConcave.convex_neg` remains the internal sign-dual
  bridge to convexity of the negated slice.

Domain-style sampling used here:
- `OrdinaryConvexProgram.saddleLagrangian` from `Definition_6_28_3`;
- `OrdinaryConvexProgram.multiplierSet` and its branch lemmas from `Definition_6_28_6`;
- `Function.IsConcave` from `Definition_6_30_2`;
- `Function.IsConcave.convex_neg` from `Definition_6_30_2`.

Primitive data vs derived API:
- primitive source data: the program `P` and the fixed primal point `x`;
- core owner statement: the dual slice `P.saddleLagrangian · x`;
- derived curvature API: `(P.saddleLagrangian · x).IsConcave`.

Layer target: `bridge/view`. The proposition adds a curvature property of the existing
Lagrangian owner; it should not introduce a second Lagrangian wrapper or a surrogate multiplier
owner.
-/

variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

-- Proof sketch: split on whether the fixed primal point lies in `P.constraintSet`. Off the
-- constraint set the dual slice is constantly `⊤`, hence concave. On the constraint set,
-- Definition 6.28.6 makes the slice equal to an affine function on `multiplierSet` and equal
-- to `⊥` off that convex set, so the negated slice is the pointwise supremum of convex affine
-- minorants and is therefore globally convex.
/-- Proposition 6.28.3: for each fixed primal point `x`, the Lagrangian slice in the multiplier
variable is concave on the whole multiplier space. The chapter's canonical owner for that
conclusion is `Function.IsConcave`. -/
theorem lagrangianDualSlice_isConcave
    (x : E) :
    (P.saddleLagrangian · x).IsConcave 𝕜 := sorry

end OrdinaryConvexProgram

end
