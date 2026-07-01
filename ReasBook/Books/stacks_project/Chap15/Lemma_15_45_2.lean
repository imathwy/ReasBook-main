import Mathlib.Tactic.Recall
import stacks_project.Chap10.Lemma_10_155_1
import stacks_project.Chap10.Lemma_10_155_2
import stacks_project.Chap10.Lemma_10_150_4
import stacks_project.Chap15.Lemma_15_37_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingHom

universe u

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations and strict henselizations, together
  with the owner predicates `FormallyEtale` and `RingHom.formally_smooth_for_adic`;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `Ring.DirectLimit.formallyEtale`,
  `RingHom.formallyEtale_of_isFilteredColimitOfEtale`,
  `RingHom.IsFilteredColimitOfEtale`,
  `RingHom.formally_smooth_for_adic`,
  `RingHom.formally_smooth_for_adic_maximalIdeal_of_formallyEtale`;
- best owner abstraction: the primitive source data are the henselization/strict-henselization
  owners, while formal étaleness and maximal-ideal-adic formal smoothness are derived API of the
  structural maps;
- primitive data: local-ring structure and the filtered-colimit-of-étale presentations stored in
  `IsHenselizationOf` / `IsStrictHenselizationOf`;
- derived API: the six source-facing formal-étale and maximal-ideal-adic formal-smoothness
  statements below.

Layer triage:
- `source-facing`: the six numbered parts of Lemma 15.45.2;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`,
  `RingHom.IsFilteredColimitOfEtale`, `FormallyEtale`, and `RingHom.formally_smooth_for_adic`;
- `bridge/view`: passage from the henselization owners to the formal-étale owner theorem
  `Ring.DirectLimit.formallyEtale`, and then to the maximal-ideal-adic formal-smoothness
  statements.
-/

section

variable {R : Type u}
variable [CommRing R] [IsLocalRing R]

section Henselization

variable {Rh : Type u}
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

/-- Lemma 15.45.2 (1): the canonical map from a local ring to its henselization is formally
étale. -/
theorem henselizationMap_formallyEtale :
    (algebraMap R Rh).FormallyEtale :=
  formallyEtale_of_isFilteredColimitOfEtale
    IsHenselizationOf.isFilteredColimitOfEtale

/-- Lemma 15.45.2 (4): the canonical map from a local ring to its henselization is formally
smooth for the `maximalIdeal Rh`-adic topology. -/
theorem henselizationMap_formallySmooth_for_maximalIdeal_adic :
    (algebraMap R Rh).formally_smooth_for_adic (maximalIdeal Rh) :=
  formally_smooth_for_adic_maximalIdeal_of_formallyEtale
    henselizationMap_formallyEtale

end Henselization

section StrictHenselization

variable {Rsh : Type u}
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Lemma 15.45.2 (3): the canonical map from a local ring to its strict henselization is
formally étale. -/
theorem strictHenselizationMap_formallyEtale :
    (algebraMap R Rsh).FormallyEtale :=
  formallyEtale_of_isFilteredColimitOfEtale
    IsStrictHenselizationOf.isFilteredColimitOfEtale

/-- Lemma 15.45.2 (6): the canonical map from a local ring to its strict henselization is
formally smooth for the `maximalIdeal Rsh`-adic topology. -/
theorem strictHenselizationMap_formallySmooth_for_maximalIdeal_adic :
    (algebraMap R Rsh).formally_smooth_for_adic (maximalIdeal Rsh) :=
  formally_smooth_for_adic_maximalIdeal_of_formallyEtale
    strictHenselizationMap_formallyEtale

end StrictHenselization

section StrictOverHenselization

variable {Rh Rsh : Type u}
variable [CommRing Rh] [IsLocalRing Rh]
variable [CommRing Rsh] [Algebra Rh Rsh] [IsStrictHenselizationOf Rh Rsh]

/-- Lemma 15.45.2 (2): the canonical comparison map from a henselization to a strict
henselization is formally étale. -/
theorem strictHenselizationOverHenselizationMap_formallyEtale :
    (algebraMap Rh Rsh).FormallyEtale :=
  formallyEtale_of_isFilteredColimitOfEtale
    IsStrictHenselizationOf.isFilteredColimitOfEtale

/- Lemma 15.45.2 (5): the canonical comparison map from a henselization to a strict
henselization is formally smooth for the `maximalIdeal Rsh`-adic topology. -/
recall strictHenselizationMap_formallySmooth_for_maximalIdeal_adic

end StrictOverHenselization

end
