import Mathlib.Tactic.Recall
import stacks_project.Chap21.Lemma_21_7_4

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 20.7.3:
- primary domain: higher direct images of `\mathcal O_X`-modules and the underlying abelian
  sheaves obtained by forgetting module structure;
- sampled declarations in this domain:
  `SheafOfModules.toSheaf`,
  `ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf`,
  `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`,
  `RingedSpace.higherDirectImageModule_underlyingSheaf_isomorphic_higherDirectImageAbelianSheaf`;
- best owner abstraction: the canonical owner for the present statement is the ringed-site theorem
  `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`;
- primitive-vs-derived split:
  the primitive data are the continuous functor between sites, the structure-sheaf map, the module
  sheaf, and the cohomological degree appearing in that owner theorem;
  the ringed-space language of opens, inverse-image opens, and `R^i f_*` is derived bridge API
  obtained by specializing the owner to the opens site of a ringed space.

Source/core/bridge triage:
- `source-facing`: the ringed-space statement that the underlying abelian sheaf of
  `R^i f_* \mathcal F` is the sheafification of `V ↦ H^i(f^{-1}(V), \mathcal F)`;
- `core/canonical`: `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`;
- `bridge/view`: later ringed-space declarations such as
  `RingedSpace.higherDirectImageModule_underlyingSheaf_isomorphic_higherDirectImageAbelianSheaf`,
  which compare the module-valued higher direct image with the abelian-sheaf one after this owner
  theorem has already identified the abelian-sheaf target.

This item introduces no new owner-level data, so the correct refinement is to recall the canonical
owner theorem directly instead of keeping a parallel ringed-space wrapper.
-/

open RingedSite.Hom

/- Lemma 20.7.3: for a morphism of ringed spaces `f : X ⟶ Y` and an `\mathcal O_X`-module
`\mathcal F`, the higher direct image sheaf `R^i f_* \mathcal F` is the sheaf associated to the
presheaf `V ↦ H^i(f^{-1}(V), \mathcal F)` on `Y`, with restriction maps induced by the standard
cohomology restriction morphisms. In the project API this is the ringed-space specialization of
the canonical ringed-site owner theorem below. -/
recall higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology

end AlgebraicGeometry
