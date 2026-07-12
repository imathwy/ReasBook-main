import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.Remark_20_54_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Remark 21.50.2:
- primary domain: projection-formula morphisms and derived base-change maps in monoidal derived
  categories;
- sampled owner declarations:
  `CategoryTheory.projectionFormulaMorphism`,
  `CategoryTheory.IsDerivedBaseChangeMap`,
  `CategoryTheory.projectionFormulaMorphism_baseChange_commSq`,
  `CategoryTheory.CommSq`;
- best owner abstraction:
  `source-facing`: the ringed-site compatibility square for the projection-formula morphism;
  `core/canonical`: `CategoryTheory.projectionFormulaMorphism_baseChange_commSq` together with the
    owner declarations `projectionFormulaMorphism` and `IsDerivedBaseChangeMap`;
  `bridge/view`: the ringed-site specialization surface, which is recall-only here.
- primitive data: the commutativity isomorphism `Lg ⋙ Lf' ≅ Lf ⋙ Lg'`, the two adjunctions, the
  pullback-tensor comparison isomorphisms, and the chosen base-change maps;
- derived API: direct reuse of the generic categorical compatibility square.

Source/core/bridge triage:
- `source-facing`: the projection-formula/base-change compatibility statement for ringed sites;
- `core/canonical`: `CategoryTheory.projectionFormulaMorphism_baseChange_commSq`;
- `bridge/view`: this file, reduced to canonical recall.

The previous local specialization surface duplicated the owner theorem’s interface without adding
new mathematics. This remark is therefore best expressed as a direct recall of the categorical
owner already established in Chapter 20. -/

/- Remark 21.50.2 is exactly the categorical compatibility square
`CategoryTheory.projectionFormulaMorphism_baseChange_commSq`, applied in the ringed-site derived
setting. -/
recall CategoryTheory.projectionFormulaMorphism_baseChange_commSq
