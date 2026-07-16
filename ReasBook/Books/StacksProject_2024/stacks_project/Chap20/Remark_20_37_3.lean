import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap20.Lemma_20_37_1

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Remark 20.37.3:
- primary domain: Milnor short exact sequences for derived sections over an open subset of a
  ringed space, read in the source as the short exact sequence for the presheaf values
  of `objectwiseCohomologyPresheaf X K m` at `U`, namely `H^m(U, K)`;
- sampled owner declarations:
  `derivedSectionsOverOpen_cohomology_shortExact`,
  `moduleDerivedSectionsAtOpenToAb`,
  `objectwiseCohomologyPresheaf`;
- best owner abstraction: the Chapter 20 owner
  `derivedSectionsOverOpen_cohomology_shortExact`, built from
  `moduleDerivedSectionsAtOpen X U` together with its exact `toAb` bridge
  `moduleDerivedSectionsAtOpenToAb X U`; the presheaf
  `objectwiseCohomologyPresheaf X K m` is the source-facing view of its middle term;
- primitive data: a ringed space `X`, an open subset `U ⊆ X`, a sequential inverse system
  `(K_n)`, a chosen derived limit `K = R lim K_n`, and a degree `m : ℤ`;
- derived API: none beyond the canonical Chapter 20 Milnor theorem itself.

Source/core/bridge triage:
- `source-facing`: the presheaf-value reading
  `H^m(U, K)` as the value at `U` of `objectwiseCohomologyPresheaf X K m`
  from Lemma `20.32.3`;
- `core/canonical`: `derivedSectionsOverOpen_cohomology_shortExact`;
- `bridge/view`: none. This remark adds no new mathematics beyond that owner theorem, so the
  refined file should not keep a separate local bridge theorem or parallel short-exact-sequence
  wrapper.
-/

/- Remark 20.37.3: for a ringed space `(X, 𝒪_X)`, an open subset `U ⊆ X`, a sequential inverse
system `(K_n)` in `D(𝒪_X)`, a chosen derived limit `K = R lim K_n`, and `m : ℤ`, the source
writes the Milnor short exact sequence using the value at `U` of the objectwise cohomology
presheaf, namely `H^m(U, K)`.
This is exactly the canonical Chapter 20 theorem
`derivedSectionsOverOpen_cohomology_shortExact`, whose middle term is read source-facingly as the
value at `U` of the objectwise cohomology presheaf from Lemma `20.32.3`. -/
recall derivedSectionsOverOpen_cohomology_shortExact

end AlgebraicGeometry.RingedSpace
