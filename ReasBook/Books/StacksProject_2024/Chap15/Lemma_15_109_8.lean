import Mathlib
import stacks_project.Chap15.Definition_15_107_6
import stacks_project.Chap15.Lemma_15_43_2
import stacks_project.Chap15.Lemma_15_51_4
import stacks_project.Chap15.Lemma_15_51_10
import stacks_project.Chap15.Lemma_15_52_4
import stacks_project.Chap15.Lemma_15_109_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/- Domain-style sampling:
- primary domain: Noetherian local commutative algebra of formal fibers, Nagata rings,
  henselizations, and strict henselizations;
- sampled owner declarations:
  `LocalFormalFibersHaveProperty`,
  `NagataRing`,
  `branchNumber`,
  `geometricBranchNumber`,
  `branchNumber_le_completion_minimalPrimes`,
  `geometricBranchNumber_le_completion`;
- best owner abstraction: the source-facing hypothesis should stay in the Chapter 15 owner
  `LocalFormalFibersHaveProperty`, specialized to the canonical bridge
  `Algebra.IsGeometricallyNormalProperty`. The branch counts should be expressed through the
  existing owners `branchNumber` and `geometricBranchNumber`, while the completion side uses the
  canonical object `ACompletion`;
- primitive data: the Noetherian local ring `A`, a chosen henselization or strict henselization,
  and the chosen strict henselization of `ACompletion`;
- derived API: the Nagata conclusion for `A`, the minimal-prime count of `ACompletion`, and the
  equality of branch counts.

Source/core/bridge triage:
- `source-facing`: the three clauses of Lemma `15.109.8`;
- `core/canonical`: `LocalFormalFibersHaveProperty`, `NagataRing`, `branchNumber`,
  `geometricBranchNumber`, `minimalPrimes`, and `ACompletion`;
- `bridge/view`: the completion comparison theorems from Lemma `15.109.1` and the compatible
  residue-field comparison used internally to build the strict-henselization comparison in part
  `(3)`.
-/

-- Proof sketch: geometrically normal rings are geometrically reduced, so Lemma `15.52.4` upgrades
-- the hypothesis on the formal fibers of `A` to the Nagata property.
/-- Lemma 15.109.8 (1): if the formal fibers of the Noetherian local ring `A` are geometrically
normal, then `A` is a Nagata ring. This applies in particular when `A` is excellent or
quasi-excellent. -/
theorem nagataRing_of_geometricallyNormal_formalFibers
    (hgeom :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    NagataRing A := sorry

variable {Ah : Type u}
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

-- Proof sketch: first use part `(1)` to see that `A` is Nagata. Then compare the minimal primes
-- of a chosen henselization `Ah` with those of the completion `ACompletion`: Lemma `15.109.1`
-- gives one inequality, and the Stacks argument reduces the reverse inequality to the domain case,
-- passes to the normalization, and uses normality of the completed local factors.
/-- Lemma 15.109.8 (2): if the formal fibers of the Noetherian local ring `A` are geometrically
normal, then the number of branches of `A`, computed from a chosen henselization `Ah`, equals the
number of minimal primes of its completion `ACompletion`. -/
theorem branchNumber_eq_completion_minimalPrimes_of_geometricallyNormal_formalFibers
    (hgeom :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    branchNumber A Ah = (minimalPrimes ACompletion).encard := sorry

variable {Ash Ahatsh : Type u}
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
variable [CommRing Ahatsh] [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
variable [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]

-- Proof sketch: apply the branch-count equality to the strict henselization `Ash`, using that
-- strict henselizations preserve geometrically normal formal fibers and the canonical
-- strict-henselization completion comparison from Lemma `15.109.1`; the compatible
-- residue-field comparison needed to build that bridge is internal to the proof.
/-- Lemma 15.109.8 (3): if the formal fibers of the Noetherian local ring `A` are geometrically
normal, then the number of geometric branches of `A` equals the number of geometric branches of
its completion `ACompletion`. -/
theorem geometricBranchNumber_eq_completion_of_geometricallyNormal_formalFibers
    (hgeom :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    geometricBranchNumber A Ash = geometricBranchNumber ACompletion Ahatsh := sorry

end
