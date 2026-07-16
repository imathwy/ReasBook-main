import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Remark_21_35_11

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Remark 20.42.13:
- primary domain: pullback comparison for derived internal Hom in the braided monoidal closed
  derived categories of module sheaves on ringed spaces, via the project’s ringed-site owner;
- sampled owner declarations:
  `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`,
  `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison_spec`,
  `MonoidalClosed.braidedHomEquiv`,
  `ihom.ev`;
- best owner abstraction: the project owner
  `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`, with this file providing only
  the ringed-space specialization of that owner;
- primitive data: the functor `leftDerivedPullback`, the chosen pullback-tensor comparison
  isomorphism, and the objects `K`, `L`;
- derived API: the ringed-space view of the canonical comparison morphism
  `Lh^* Rℋom(K, L) ⟶ Rℋom(Lh^* K, Lh^* L)`,
  together with its evaluation-side specification theorem.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization of the canonical pullback/internal-Hom
  comparison;
- `core/canonical`: `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`;
- `bridge/view`: this file is recall-only and should not keep a second ringed-space wrapper for
  the specialization to `D(𝒪_Y)` and `D(𝒪_X)`. -/

/- Remark 20.42.13: after choosing a derived pullback functor
`Lh^* : D(𝒪_Y) ⥤ D(𝒪_X)` and the pullback-tensor comparison isomorphism of
Lemma `20.27.3`, the canonical morphism
`Lh^* Rℋom(K, L) ⟶ Rℋom(Lh^* K, Lh^* L)`
is exactly the ringed-space specialization of the Chapter 21 owner
`SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`. -/
recall SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison

/- The evaluation-side description of Remark 20.42.13 is already owned by the Chapter 21
companion theorem `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison_spec`. -/
recall SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison_spec

end AlgebraicGeometry.RingedSpace
