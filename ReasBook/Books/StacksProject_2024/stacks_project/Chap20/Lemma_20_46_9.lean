import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_44_9

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

open SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 20.46.9:
- primary domain: derived internal Hom for cochain complexes of `𝒪_X`-modules on a ringed space,
  computed by the canonical internal-Hom complex when the source complex is strictly perfect;
- inspected owner declarations:
  `(ihom E).obj F`,
  `CochainComplex.IsStrictlyPerfect`,
  `ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_isStrictlyPerfect`;
- best owner abstraction: the Chapter 21 ringed-site theorem
  `ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_isStrictlyPerfect`; this
  Chapter 20 file is only the opens-site `bridge/view` of that canonical owner theorem;
- primitive data: the two complexes `E` and `F` and the strict-perfect hypothesis on `E`;
- derived API: the representing-isomorphism theorem itself.

Source/core/bridge triage:
- `source-facing`: Lemma 20.46.9 for complexes of `𝒪_X`-modules on a ringed space,
  asserting that the derived internal Hom is represented by the explicit internal-Hom complex;
- `core/canonical`: `ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_isStrictlyPerfect`
  together with its internal-Hom owner `(ihom E).obj F`;
- `bridge/view`: the ringed-space specialization theorem of the Chapter 21 owner theorem on the
  opens site of `X`.
-/

/- Lemma 20.46.9 is a pure `bridge/view` item: on a ringed space, the statement is exactly the
Chapter 21 owner theorem on the canonical site of opens. The chapter therefore reuses that owner
directly instead of keeping a parallel ringed-space theorem with the same mathematical content. -/

/- Lemma 20.46.9: if `E` is strictly perfect, then for complexes `E` and `F` of `𝒪_X`-modules on
a ringed space, the derived internal Hom from `E` to `F` is represented by the canonical
internal-Hom complex `(ihom E).obj F`. In the project API this is exactly the Chapter 21
ringed-site theorem specialized to the canonical site of opens of `X`. -/
recall ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_isStrictlyPerfect

end AlgebraicGeometry.RingedSpace
