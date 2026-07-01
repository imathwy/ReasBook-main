import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage for Lemma 12.14.10:
- primary domain: degreewise split short exact sequences of cochain complexes and their canonical
  connecting morphisms in the homotopy-category package.
- inspected owner declarations:
  `CochainComplex.cocycleOfDegreewiseSplit`,
  `CochainComplex.homOfDegreewiseSplit`,
  `CochainComplex.homOfDegreewiseSplit_f`,
  `CochainComplex.triangleOfDegreewiseSplit`.
- best owner abstraction: the canonical owner morphism
  `CochainComplex.homOfDegreewiseSplit`.
- layer: `core/canonical`; this numbered item is a direct recall of the owner morphism and its
  degreewise component formula, not a source-facing new construction.
- primitive data: a short complex `S` of cochain complexes together with a degreewise splitting
  family `σ`.
- derived API: the cocycle description, the component formula, and the associated triangle remain
  upstream and are reused directly here.
-/

/- Lemma 12.14.10: for a degreewise split short complex
`0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` of cochain complexes in an additive category, the family of
components `s^n ≫ d_B^n ≫ π^{n + 1} : C^n ⟶ A^{n + 1}` assembles into the canonical morphism
`C^• ⟶ A^•[1]`. -/
recall CochainComplex.homOfDegreewiseSplit

/- Companion recall: the degree-`n` component of
`CochainComplex.homOfDegreewiseSplit` is `s^n ≫ d_B^n ≫ π^{n + 1}`. -/
recall CochainComplex.homOfDegreewiseSplit_f
