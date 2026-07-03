import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_9_1 (from Chap09) -/
/- Domain-style sampling for minimal polynomials in field extensions:
- primary domain: the minimal polynomial of an element in a field extension;
- sampled owner declaration:
  `minpoly`;
- sampled derived/specification API:
  `minpoly.monic`,
  `minpoly.aeval`,
  `minpoly.irreducible`;
- best owner abstraction: the canonical owner `minpoly`, with monicity, the root property,
  and irreducibility all derived from that owner instead of stored as primitive local data;
- primitive data: only the polynomial `minpoly k α`;
- derived API: algebraicity/integrality consequences and degree-theoretic consequences such as
  `IntermediateField.adjoin.finrank`.

Source/core/bridge triage:
- `source-facing`: the textbook minimal polynomial of an algebraic element `α` over `k`;
- `core/canonical`: `minpoly`;
- `bridge/view`: downstream field-theoretic comparisons such as
  `IntermediateField.adjoin.finrank`.

This file should therefore remain a pure recall surface: Definition 9.9.1 does not introduce new
primitive data beyond the canonical owner already present in mathlib, so any local wrapper would
only duplicate the chapter API.
-/

/- Definition 9.9.1: for an algebraic element `α` of a field extension `K/k`, the polynomial
called the minimal polynomial of `α` over `k` is the canonical mathlib polynomial `minpoly k α`. -/
recall minpoly

/-! ### Lemma_9_9_2 (from Chap09) -/
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
