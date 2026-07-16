import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_34_7

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.7:
- primary domain: quasi-isomorphism invariance of internal-Hom complexes of `𝒪_X`-module
  cochain complexes on a ringed space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.quasiIso_ringedSiteModuleComplexInternalHomMap_of_quasiIso_of_isKInjective`,
  `(ihom L).map`,
  `MonoidalClosed.pre`;
- best owner abstraction: the Chapter 21 ringed-site owner theorem
  `SheafOfModules.RingedSite.quasiIso_ringedSiteModuleComplexInternalHomMap_of_quasiIso_of_isKInjective`,
  stated directly for the canonical closed-monoidal internal-Hom comparison composite;
- primitive data: the ambient ringed space together with the quasi-isomorphisms
  `(𝓛')^• ⟶ 𝓛^•` and `(𝓘')^• ⟶ 𝓘^•`;
- derived API: the ringed-space specialization of that owner theorem, with no parallel local
  wrapper for the internal-Hom comparison morphism or its quasi-isomorphism statement.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.7 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`:
  `SheafOfModules.RingedSite.quasiIso_ringedSiteModuleComplexInternalHomMap_of_quasiIso_of_isKInjective`,
  `(ihom L).map`, and `MonoidalClosed.pre`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly recall the owner theorem
instead of keeping a second theorem with the same mathematical content under a local name. -/

/- Lemma 20.41.7: for a ringed space `(X, 𝒪_X)`, if
`(𝓘')^• ⟶ 𝓘^•` is a quasi-isomorphism of K-injective complexes of `𝒪_X`-modules and
`(𝓛')^• ⟶ 𝓛^•` is a quasi-isomorphism of complexes of `𝒪_X`-modules, then the induced canonical
morphism `ℋom^•(𝓛^•, (𝓘')^•) ⟶ ℋom^•((𝓛')^•, 𝓘^•)`
is a quasi-isomorphism. In the project API this is exactly the Chapter 21 ringed-site owner
theorem specialized to the canonical site of opens of `X`. -/
recall SheafOfModules.RingedSite.quasiIso_ringedSiteModuleComplexInternalHomMap_of_quasiIso_of_isKInjective

end AlgebraicGeometry.RingedSpace
