import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_23_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Remark 21.23.4:
- primary domain: Milnor short exact sequences for objectwise derived sections on a ringed site;
- sampled owner declarations:
  `RingedSite.Hom.moduleSectionsAsAbelianDerived`,
  `CategoryTheory.SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `ringedSiteDerivedSectionsOverObject_cohomology_shortExact`;
- best owner abstraction: the Chapter 21 owner is
  `ringedSiteDerivedSectionsOverObject_cohomology_shortExact`, built from the canonical derived
  sections functor `RingedSite.Hom.moduleSectionsAsAbelianDerived X U`;
- primitive-vs-derived split:
  primitive data are a ringed site `X`, an object `U : X`, a tower `Ksys : ℕᵒᵖ ⥤ ModuleDerived X`,
  a chosen derived limit `K`, and a degree `m`;
  the Milnor `R¹ lim` term is derived API, canonically owned by
  `SequentialInverseSystem.firstDerivedLimit` on the cohomology tower.

Source/core/bridge triage:
- `source-facing`: the Milnor short exact sequence for `H^m(U, K)`;
- `core/canonical`: `RingedSite.Hom.moduleSectionsAsAbelianDerived`,
  `SequentialInverseSystem.firstDerivedLimit`, and
  `ringedSiteDerivedSectionsOverObject_cohomology_shortExact`;
- `bridge/view`: this remark is recall-only, so the file should reuse the chapter owner directly
  instead of keeping a parallel local sections-functor wrapper. -/

/- Remark 21.23.4: for a ringed site `X`, an object `U : X`, a sequential inverse system
`(K_n)` in `D(𝒪_X)`, a chosen derived limit `K = R limₙ K_n`, and `m : ℤ`, the groups `H^m(U, K)`
fit into the Milnor short exact sequence
`0 ⟶ R¹ limₙ H^(m - 1)(U, K_n) ⟶ H^m(U, K) ⟶ limₙ H^m(U, K_n) ⟶ 0`.
This is exactly the canonical Chapter 21 theorem
`ringedSiteDerivedSectionsOverObject_cohomology_shortExact`. -/
recall ringedSiteDerivedSectionsOverObject_cohomology_shortExact
