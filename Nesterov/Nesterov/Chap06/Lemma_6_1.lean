import Nesterov.Chap03.Definition_3_1_1_5
import Nesterov.Chap03.Theorem_3_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u

/- Lemma 6.1 lies in the chapter's Fenchel-biconjugacy domain.

Primary domain:
- Fenchel duality for `ℝ ∪ {+∞}`-valued functions on real inner-product spaces.

Sampled owner-style declarations:
- `dom` and `withTopToEReal` from `Chap03/Definition_3_3`, the chapter owners for the
  finite-value domain and the canonical codomain bridge to `EReal`;
- `ClosedConvexFunction` from `Chap03/Definition_3_1_1_5`, the chapter owner for proper
  closed-convex `WithTop`-valued functions;
- `fenchelDual` with the notation `f⋆` from `Chap03/Definition_3_1_2_1`, the source-facing
  Fenchel-conjugate owner;
- `fenchelBidual` with the notation `f⋆⋆` from `Chap03/Theorem_3_1_5_2`, the canonical
  source-facing biconjugate owner.

Best owner abstraction:
- source-facing theorem: the Fenchel-Moreau equality for a proper closed convex function;
- core/canonical owner: `fenchelBidual`;
- bridge/view: the explicit supremum formula obtained from `fenchelBidual` by the
  `dom (f⋆)`-restriction bridge under `hproper`;
- Euclidean `ℝⁿ` is only a specialization layer, already handled separately by chapter recall
  files such as `Theorem_3_20`.

Primitive data:
- `f : E → WithTop ℝ`;
- properness as `(dom f).Nonempty`;
- closed convexity as `ClosedConvexFunction f`.

Derived API:
- the owner-level equality `(f⋆⋆) x = withTopToEReal (f x)`;
- the explicit source-facing supremum formula obtained by restricting the owner-level supremum to
  `dom (f⋆)` under `hproper`.

Source/core/bridge triage:
- source-facing: Lemma 6.1's equality between `f` and its Fenchel biconjugate;
- core/canonical: `fenchelBidual`;
- bridge/view: the theorem `fenchelMoreau_eq_sSup_inner_sub_fenchelDual` below, which uses the
  `dom (f⋆)`-restriction bridge from `Theorem_3_1_5_2`.

The previous file rebuilt local owners for the effective domain, closed-convexity, conjugate, and
biconjugate integrand. Those notions already live upstream on the canonical chapter surfaces
`dom`, `ClosedConvexFunction`, `f⋆`, and `f⋆⋆`, so this file keeps only the source-facing theorem
layer and derives the displayed supremum formula from the canonical owner `fenchelBidual` through
the domain-restriction bridge justified by `hproper`.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace ClosedConvexFunction

/-- Lemma 6.1, owner form: a proper closed convex function agrees with its Fenchel bidual. -/
-- Proof sketch: this is the Fenchel-Moreau theorem on the chapter owner surface `f⋆⋆`; the
-- nonempty-domain hypothesis is the source-facing properness assumption under which the bidual
-- recovers the original function.
theorem fenchelBidual_eq_of_dom_nonempty
    {f : E → WithTop ℝ} (hf : ClosedConvexFunction f) (hdom : (dom f).Nonempty) (x : E) :
    (f⋆⋆) x = withTopToEReal (f x) := by
  sorry

end ClosedConvexFunction

/-- Lemma 6.1, source-facing form: a proper closed convex function equals the supremum of the
affine terms `⟪s, x⟫ - f_*(s)` over `dom f_*`. -/
theorem fenchelMoreau_eq_sSup_inner_sub_fenchelDual
    {f : E → WithTop ℝ} (hf : ClosedConvexFunction f) (hdom : (dom f).Nonempty) (x : E) :
    withTopToEReal (f x) =
      sSup ((fun s : E ↦ (inner ℝ s x : EReal) - (f⋆) s) '' dom (f⋆)) := by
  calc
    withTopToEReal (f x) = (f⋆⋆) x := (hf.fenchelBidual_eq_of_dom_nonempty hdom x).symm
    _ = sSup ((fun s : E ↦ (inner ℝ s x : EReal) - (f⋆) s) '' dom (f⋆)) :=
      fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty hdom x

end
