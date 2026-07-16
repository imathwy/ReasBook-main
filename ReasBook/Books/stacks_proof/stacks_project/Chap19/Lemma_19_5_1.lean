import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap19.Theorem_19_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace)

/- Domain-style sampling for Lemma 19.5.1:
- primary domain: injective resolutions in categories of sheaves of modules on ringed spaces;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `EnoughInjectives`,
  `modulesOnRingedSite_hasEnoughInjectives`,
  `siteAbelianSheaf_hasEnoughInjectives`;
- best owner abstraction: the nonredundant source-facing specialization in this file is
  `EnoughInjectives (RingedSpace.Modules X)`;
- primitive data: the ringed-site enough-injectives theorem specialized along the owner
  `(RingedSpace.Modules X)`;
- derived API: downstream resolution-functor existence consequences.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization of enough injectives for sheaves of modules;
- `core/canonical`: `EnoughInjectives`;
- `bridge/view`: the abbreviation `RingedSpace.Modules` and the specialization of the
  ringed-site theorem.

This item is a `bridge/view` recall: the owner already exists upstream as
`modulesOnRingedSite_hasEnoughInjectives`, so this file should expose only the ringed-space
specialization rather than a parallel local instance name. -/

/- This file keeps only the faithful ringed-space specialization of the enough-injectives owner.
Any stronger owner-level structure would require separate justification. -/

/- Lemma 19.5.1: the category of `\mathcal O_X`-module sheaves on a ringed space has enough
injectives. This is exactly the ringed-site owner theorem specialized to
`X.ringCatSheaf`. -/
#check
  (modulesOnRingedSite_hasEnoughInjectives X.ringCatSheaf :
    EnoughInjectives X.Modules)

end AlgebraicGeometry.RingedSpace
