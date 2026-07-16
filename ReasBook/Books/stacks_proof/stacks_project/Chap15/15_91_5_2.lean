import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap15.Lemma_15_91_6

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {R : Type*} [CommRing R]
variable (f : R)

/- Domain-style sampling:
- primary domain: the completion-specialized Beauville-Laszlo Cech complex for a ring `R` and
  element `f : R`.
- sampled owner declarations:
  `beauvilleLaszloCechLeftMap`,
  `beauvilleLaszloCechRightMap`,
  `beauvilleLaszloCech_comp_eq_zero`,
  `principalAdicCompletion`.
- best owner abstraction: the generic zero-composite owner theorem
  `beauvilleLaszloCech_comp_eq_zero`, specialized directly to the completion map
  `algebraMap R (principalAdicCompletion f)`.
- primitive data: the ring `R`, the element `f : R`, and the completion algebra
  `R → AdicCompletion (principalIdeal f) R`.
- derived API: the completion specialization of the zero-composite relation, inherited directly
  from the owner theorem by specialization along the canonical completion map.
- source/core/bridge triage:
  `source-facing`: the completion specialization
    `R → AdicCompletion (principalIdeal f) R × Localization.Away f →
      Localization.Away (algebraMap R (AdicCompletion (principalIdeal f) R) f)`;
  `core/canonical`: `beauvilleLaszloCech_comp_eq_zero`;
  `bridge/view`: the specialization
    `beauvilleLaszloCech_comp_eq_zero (algebraMap R (principalAdicCompletion f)) f`.
-/

/- 15.91.5.2: for the completion map `R → AdicCompletion (principalIdeal f) R`, the
Beauville-Laszlo Cech composite
`R → AdicCompletion (principalIdeal f) R × R_f →
  Localization.Away (algebraMap R (AdicCompletion (principalIdeal f) R) f)` vanishes. This file
checks the canonical owner theorem specialized to the completion map, with no parallel local
wrapper or duplicate completion-specific alias. -/
#check beauvilleLaszloCech_comp_eq_zero (algebraMap R (principalAdicCompletion f)) f

end
