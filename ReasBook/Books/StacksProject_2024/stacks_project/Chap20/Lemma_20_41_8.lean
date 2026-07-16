import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_34_8

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.8:
- primary domain: K-injectivity of internal-Hom complexes for complexes of `𝒪_X`-modules on a
  ringed space;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsKInjective`,
  `(ihom L).obj I`,
  `ringedSiteModuleComplexInternalHom_isKInjective`;
- best owner abstraction: the canonical internal-Hom owner `(ihom L).obj I`, together with the
  owner instance
  `ringedSiteModuleComplexInternalHom_isKInjective`;
- primitive data: the ambient ringed space, the K-flat source complex, and the K-injective target
  complex;
- derived API: the K-injectivity statement for the canonical internal-Hom complex.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.8 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: `(ihom L).obj I` and
  `ringedSiteModuleComplexInternalHom_isKInjective`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly recall the ringed-site
owner instance instead of rebuilding a parallel ringed-space internal-Hom complex and its
differential term-by-term. -/

/- Lemma 20.41.8: if `𝓘^•` is a K-injective complex of `𝒪_X`-modules on a ringed space
`(X, 𝒪_X)` and `𝓛^•` is K-flat, then the canonical internal-Hom complex from `𝓛^•` to `𝓘^•`
is K-injective. In the project API this is exactly the ringed-site owner instance specialized to
the canonical site of opens of `X`. -/
recall SheafOfModules.RingedSite.ringedSiteModuleComplexInternalHom_isKInjective

end AlgebraicGeometry.RingedSpace
