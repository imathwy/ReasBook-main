import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_19_5_1 (from Chap19) -/
open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 19.5.1:
- primary domain: injective resolutions in categories of sheaves of modules on ringed spaces;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `EnoughInjectives`,
  `modulesOnRingedSite_hasEnoughInjectives`,
  `CategoryTheory.exists_resolutionFunctorOne`;
- best owner abstraction: the nonredundant source-facing specialization in this file is
  `EnoughInjectives (RingedSpace.Modules X)`;
- primitive data: the ringed-site enough-injectives theorem specialized along the owner
  `(RingedSpace.Modules X)`;
- derived API: the Chapter 13 resolution-functor existence consequences.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization of enough injectives for sheaves of modules;
- `core/canonical`: `EnoughInjectives`;
- `bridge/view`: the abbreviation `RingedSpace.Modules` and the specialization of the
  ringed-site theorem. -/

/- This file keeps only the faithful ringed-space specialization of the enough-injectives owner.
Any stronger owner-level structure would require separate justification. -/

/-- The category of `\mathcal O_X`-module sheaves on a ringed space has enough injectives. -/
instance sheafModules_enoughInjectives (X : RingedSpace) :
    EnoughInjectives (RingedSpace.Modules X) := by
  simpa [RingedSpace.Modules] using
    modulesOnRingedSite_hasEnoughInjectives ((RingedSpace.ringCatSheaf X))

end AlgebraicGeometry.RingedSpace
