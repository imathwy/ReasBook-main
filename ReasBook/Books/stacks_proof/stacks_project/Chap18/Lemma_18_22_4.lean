import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap07.Lemma_7_31_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

/- Lemma 18.22.4: let
`(f, f^\sharp) : (\mathit{Sh}(\mathcal C), \mathcal O) \to (\mathit{Sh}(\mathcal D), \mathcal O')`,
let `s : \mathcal F \to f^{-1}\mathcal G` be as in Lemma 18.22.3, and assume `f` is presented by
a continuous functor `u : \mathcal D \to \mathcal C` with `\mathcal G = h_V^\#`,
`\mathcal F = h_U^\#`, and `s` induced by a morphism `c : U \to u(V)`. Then the commutative
diagrams of Lemma 18.20.2 and Lemma 18.22.3 agree via the identifications of Lemma 18.21.3.
In Lean, the underlying comparison is exactly the representable-localization theorem
`CategoryTheory.representable_localization_comparison_agrees_with_localized_pullback`; the ringed
structure-map identifications are supplied separately by Lemma 18.21.5 and Lemma 18.22.2. -/
recall CategoryTheory.representable_localization_comparison_agrees_with_localized_pullback
