import Mathlib.Tactic.Recall
import StacksProject_2024.Chap14.Lemma_14_13_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for 14.13.0.1:
- primary domain: simplicial copowers and their degreewise compatibility condition for simplicial
  morphisms
- source-facing statement: the displayed simplicial equation relating a degreewise family
  `F Δ u : V.obj Δ ⟶ W.obj Δ` across a morphism `f : Δ ⟶ Δ'`
- core/canonical owner in the chapter: `simplicialCopower`
- bridge/view owners for the compatibility condition:
  `SimplicialCopowerHomFamily`,
  `SimplicialCopowerHomFamily.IsCompatible`
- same-kind upstream declarations inspected:
  `simplicialCopower` in `Definition_14_13_1`,
  `SimplicialCopowerHomFamily`,
  `SimplicialCopowerHomFamily.IsCompatible`,
  `SimplicialCopowerHomFamily.isCompatible_iff`,
  `simplicialCopowerCompatibleFamilyCorepresentableBy` in `Lemma_14_13_2`
- primitive data: a simplex-indexed objectwise family of morphisms together with the ambient
  simplicial objects `U`, `V`, and `W`
- derived API: the subtype of compatible families, its compatibility characterization, and the
  universal-property equivalence with morphisms `U × V ⟶ W`
- source/core/bridge triage: this item is a bridge/view statement recording the defining
  compatibility equation for the chapter's copower owner abstraction, so the correct refinement is
  direct recall of the bridge owner and its canonical compatibility theorem rather than any local
  restatement.
-/

/- 14.13.0.1 packages the displayed compatibility equation as the chapter's owner abstraction on
simplex-indexed degreewise morphism families. -/
recall SimplicialCopowerHomFamily.IsCompatible

/- The displayed equation in 14.13.0.1 is exactly the canonical characterization of that
compatibility predicate. -/
recall SimplicialCopowerHomFamily.isCompatible_iff
