import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap20.Lemma_20_37_1

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for 20.37.3.1:
- primary domain: Milnor short exact sequences for derived sections over an open subset of a
  ringed space;
- sampled owner declarations:
  `moduleDerivedSectionsAtOpenToAb`,
  `derivedSectionsOverOpen_cohomology_shortExact`;
- best owner abstraction: the canonical Chapter 20 owner for this item is
  `derivedSectionsOverOpen_cohomology_shortExact`, built from
  `moduleDerivedSectionsAtOpen X U` and its exact codomain-change bridge
  `moduleDerivedSectionsAtOpenToAb X U`;
- primitive data: a sequential inverse system `Ksys`, a chosen derived limit `K`, and the degree
  `m`;
- derived API: the tower `n ↦ H^m(U, K_n)`, the Milnor difference map, and the resulting short
  exact sequence.

Layer triage:
- `source-facing`: the Milnor short exact sequence for `H^m(U, K)` over a fixed open subset;
- `core/canonical`: `derivedSectionsOverOpen_cohomology_shortExact`;
- `bridge/view`: none. This item is an exact-interface recall of the canonical theorem, so the
  refined file should reuse it directly instead of keeping local copies of the cohomology tower and
  `R^1 lim` model.
-/

/- 20.37.3.1: for a ringed space `X`, an open subset `U ⊆ X`, a sequential inverse system
`(K_n)` in `D(𝒪_X)`, a chosen derived limit `K = R lim K_n`, and `m : ℤ`, the groups
`H^m(U, K)` fit into the Milnor short exact sequence
`0 ⟶ R¹ lim H^(m - 1)(U, K_n) ⟶ H^m(U, K) ⟶ lim H^m(U, K_n) ⟶ 0`.
This is exactly the canonical Chapter 20 theorem
`derivedSectionsOverOpen_cohomology_shortExact`, built from the owner
`moduleDerivedSectionsAtOpenToAb X U`. -/
recall derivedSectionsOverOpen_cohomology_shortExact

end AlgebraicGeometry.RingedSpace
