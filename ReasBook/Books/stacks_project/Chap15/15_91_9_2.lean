import Mathlib.Tactic.Recall
import stacks_project.Chap15.«15_91_9_1»

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Domain-style sampling:
- primary domain: Beauville-Laszlo glueability for modules over an `R`-algebra;
- sampled owner declarations:
  `beauvilleLaszloModuleCechSequence`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `tensorBaseChangeUnitPrimaryComponent`,
  `isBeauvilleLaszloGlueableAlong_iff_injective_fPowerTorsionToTensor_of_glueingPair`;
- best owner abstraction: the source-facing glueability condition is owned directly by
  `(beauvilleLaszloModuleCechSequence R' M f).ShortExact`; the torsion criteria are later
  bridge/view reformulations and should not be repackaged here.
- primitive data vs derived API: the primitive data are the `R`-algebra `R'`, the `R`-module `M`,
  the element `f`, and the canonical short complex `beauvilleLaszloModuleCechSequence R' M f`;
  torsion reformulations and completion specializations are derived API.
- source/core/bridge triage:
  `source-facing`: the textbook glueability condition for modules along `(R → R', f)`;
  `core/canonical`: `(beauvilleLaszloModuleCechSequence R' M f).ShortExact`;
  `bridge/view`: the torsion criteria from Lemma `15.91.10` and the completion specialization in
    Remark `15.91.11`.
-/

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {f : R}

/- 15.91.9.2: Beauville-Laszlo glueability of an `R`-module `M` for `(R → R', f)` is expressed in
Lean by the owner predicate `(beauvilleLaszloModuleCechSequence R' M f).ShortExact`. This file
keeps that canonical owner directly, with no parallel alias. -/
#check (beauvilleLaszloModuleCechSequence R' M f).ShortExact

end
