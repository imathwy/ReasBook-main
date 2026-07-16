import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_44_9_KFlat

-- Declarations for this item will be appended below by the statement pipeline.

open SheafOfModules.RingedSite

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.46.10:
- primary domain: K-flatness of internal-Hom complexes of `𝒪_X`-modules;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsStrictlyPerfect`,
  `(ihom E).obj F`,
  `ringedSiteModuleComplexInternalHom_isKFlat_of_isStrictlyPerfect`;
- best owner abstraction: the canonical internal-Hom owner `(ihom E).obj F`, together with the
  owner theorem
  `ringedSiteModuleComplexInternalHom_isKFlat_of_isStrictlyPerfect`;
- primitive data: the two complexes `E` and `F`, the strict-perfectness hypothesis on `E`, and
  the K-flatness hypothesis on `F`;
- derived API: the K-flatness conclusion for the canonical internal-Hom complex.

Source/core/bridge triage:
- `source-facing`: Lemma 20.46.10 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: `(ihom E).obj F` together with
  `ringedSiteModuleComplexInternalHom_isKFlat_of_isStrictlyPerfect`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file is therefore a pure `bridge/view` recall: the ringed-site owner theorem already carries
the faithful statement, so the ringed-space chapter should reuse it directly instead of keeping a
parallel theorem on a local internal-Hom bridge. -/

/- Lemma 20.46.10: if `F` is K-flat and `E` is strictly perfect, then the canonical internal-Hom
complex from `E` to `F` of `𝒪_X`-modules on a ringed space is K-flat. In the project API this is
exactly the ringed-site owner theorem specialized to the canonical site of opens of `X`. -/
recall ringedSiteModuleComplexInternalHom_isKFlat_of_isStrictlyPerfect

end AlgebraicGeometry.RingedSpace
