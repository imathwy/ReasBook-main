import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_9
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_81

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SupportFunction

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 7.17 lies in the chapter's support-function / subdifferential positivity domain.

Mandatory domain-style sampling before refinement:
- `supportFunction` with notation `ξ[Q]` in `Chap03/Definition_3_9`, the chapter owner for support
  functions of sets;
- `supportFunction_dom_eq_univ_of_nonempty_bounded` in `Chap03/Proposition_3_11`, the bounded-set
  finiteness theorem for that owner;
- `ConvexBody.supportFunctionReal` in `Chap07/Definition_7_24`, the convex-body `toReal` bridge
  showing that Chapter 7 treats real-valued support functions through the Chapter 3 owner;
- `StrictlyPositiveOn` in `Chap07/Definition_7_81`, the source-facing positivity predicate for
  real-valued functions.

Best owner abstraction:
- source-facing: Lemma 7.17 as a `StrictlyPositiveOn` statement for a centrally symmetric support
  function;
- core/canonical: the chapter support-function owner `ξ[S]`;
- bridge/view: the real-valued support-function surface `fun x ↦ (ξ[S] x).toReal`.

Primitive data:
- a set `S : Set E`;
- nonemptiness, boundedness, and central symmetry of `S`.

Derived API:
- the real-valued support function `fun x ↦ (ξ[S] x).toReal`, justified by
  `supportFunction_dom_eq_univ_of_nonempty_bounded`;
- the `StrictlyPositiveOn` conclusion on `Set.univ`.

The previous version stated the support function through a raw `sSup ((fun s ↦ ⟪s, x⟫) '' S)`
formula even though the chapter already owns this notion as `ξ[S]` and Chapter 7 already uses the
`toReal` bridge for real-valued support functions. This refinement keeps the source-facing
positivity theorem but moves it to the canonical owner surface, drops the redundant closedness
hypothesis from the public API, and replaces the over-concrete `EuclideanSpace ℝ (Fin n)` ambient
model by the standard real inner-product-space layer. The `.toReal` bridge is kept only under the
finite-value hypothesis supplied by nonemptiness together with boundedness.
-/

-- Proof sketch: let `f x = (ξ[S] x).toReal`. For `g ∈ ∂ f(x)`, use the subgradient inequality at
-- `y` together with the support-function subgradient characterization to identify `g` with a
-- support point of `S` at `x`. Central symmetry gives `-g ∈ S`, hence
-- `f y = (ξ[S] y).toReal ≥ ⟪-g, y⟫`. Rearranging yields
-- `0 ≤ f y + f x + ⟪g, y - x⟫`.
/-- Lemma 7.17: the real-valued support-function surface `x ↦ (ξ[S] x).toReal` of a nonempty
bounded centrally symmetric set is strictly positive on the whole space in the sense of
Definition 7.81. At this owner level, closedness is redundant because the support function depends
only on the closed convex hull of `S`, while nonemptiness is essential to keep the `.toReal`
bridge faithful. -/
theorem supportFunction_strictlyPositiveOn_univ_of_nonempty_bounded_centrallySymmetric
    (S : Set E) (hS_nonempty : S.Nonempty) (hS_bounded : Bornology.IsBounded S)
    (hS_centrallySymmetric : ∀ ⦃s : E⦄, s ∈ S → -s ∈ S) :
    StrictlyPositiveOn Set.univ (fun x ↦ (ξ[S] x).toReal) := sorry

end
