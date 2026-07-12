import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open Module
open scoped IntermediateField

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Lemma 9.9.2:
- primary domain: minimal polynomials and simple field extensions;
- sampled owner declarations:
  `minpoly`,
  `IntermediateField.adjoin.powerBasis`,
  `PowerBasis.finrank`,
  `IntermediateField.adjoin.finrank`;
- best owner abstraction: the simple extension `k⟮α⟯` is canonically controlled by
  `IntermediateField.adjoin.powerBasis`, and the degree comparison itself is already owned by
  `IntermediateField.adjoin.finrank`.

Source/core/bridge triage:
- `source-facing`: the textbook equality between the degree of the minimal polynomial of an
  algebraic element `α` and the degree `[k(α) : k]` of the corresponding simple extension;
- `core/canonical`: `minpoly k α` together with the simple intermediate field `k⟮α⟯`;
- `bridge/view`: `IntermediateField.adjoin.finrank`, whose proof runs through the canonical power
  basis of `k⟮α⟯`.

Primitive data is still just the algebraic element `α`, its minimal polynomial `minpoly k α`, and
the canonical simple extension `k⟮α⟯`. The degree equality is derived API from
`IntermediateField.adjoin.finrank`, but the source-facing lemma is naturally phrased with an
algebraicity hypothesis rather than the owner theorem's integral hypothesis, so the refined file
keeps a thin bridge theorem instead of a bare recall.
-/

/-- Lemma 9.9.2: if `α` is algebraic over `k`, then the degree of its minimal polynomial over `k`
is the extension degree `[k(α) : k]`. -/
theorem minpoly_natDegree_eq_finrank_adjoin (α : K) (hα : IsAlgebraic k α) :
    (minpoly k α).natDegree = finrank k k⟮α⟯ := by
  simpa [eq_comm] using IntermediateField.adjoin.finrank hα.isIntegral

end
