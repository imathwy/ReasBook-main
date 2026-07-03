import Mathlib
import stacks_project.Chap10.Definition_10_137_10
import stacks_project.Chap15.Definition_15_107_6

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations, strict henselizations, minimal
  primes, and smoothness at the closed point;
- sampled owner declarations of the same kind:
  `branchNumber`,
  `geometricBranchNumber`,
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`;
- best owner abstraction: the source-facing branch-count equalities should stay expressed in terms
  of the chapter owners `branchNumber` / `geometricBranchNumber` with the source-facing smoothness
  hypothesis `Algebra.SmoothAtPrime A B (closedPoint B)`, while henselization and strict
  henselization remain primitive ambient data through `IsHenselizationOf` and
  `IsStrictHenselizationOf`;
- primitive data: a local homomorphism `A → B` of local rings, a chosen henselization or strict
  henselization on each side, the source-facing closed-point smoothness hypothesis, and in clause
  `(2)` the purely inseparable residue-field extension;
- derived API: the equalities comparing the branch and geometric-branch counts.

Source/core/bridge triage:
- `source-facing`: the two branch-count invariance statements below;
- `core/canonical`: `branchNumber`, `geometricBranchNumber`, `IsHenselizationOf`,
  `IsStrictHenselizationOf`, and the canonical local smoothness owner `IsSmoothAt`;
- `bridge/view`: `Algebra.smoothAtPrime_iff_isSmoothAt`, which justifies keeping
  `Algebra.SmoothAtPrime` as the source-facing hypothesis rather than introducing a parallel local
  reformulation.
-/

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsLocalRing A]
variable [CommRing B] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]

section StrictHenselization

variable {Ash : Type u} {Bsh : Type v}
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
variable [CommRing Bsh] [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]

-- Proof sketch: pass to chosen strict henselizations of `A` and `B`, use that the smooth local
-- map remains flat after strict henselization, and compare minimal primes by going down and the
-- domain criterion after quotienting by a minimal prime of `A`.
/-- Lemma 15.107.8 (1): if `A → B` is a local homomorphism of local rings whose closed point is
smooth over `A`, then the number of geometric branches of `A`, computed from a chosen strict
henselization `Ash`, equals the number of geometric branches of `B`, computed from a chosen strict
henselization `Bsh`. -/
theorem geometricBranchNumber_eq_of_smoothAtPrime_closedPoint
    (hsmooth : Algebra.SmoothAtPrime A B (closedPoint B)) :
    geometricBranchNumber A Ash = geometricBranchNumber B Bsh := sorry

end StrictHenselization

section Henselization

variable {Ah : Type u} {Bh : Type v}
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
variable [CommRing Bh] [Algebra B Bh] [IsHenselizationOf B Bh]

-- Proof sketch: repeat the strict-henselization argument with ordinary henselizations. The purely
-- inseparable residue-field extension is used after normalizing the reduced domain quotient of `A`
-- to force the relevant tensor product with the henselization of `B` to stay local.
/-- Lemma 15.107.8 (2): if `A → B` is a local homomorphism of local rings whose closed point is
smooth over `A` and whose induced residue-field extension is purely inseparable, then the number
of branches of `A`, computed from a chosen henselization `Ah`, equals the number of branches of
`B`, computed from a chosen henselization `Bh`. -/
theorem branchNumber_eq_of_smoothAtPrime_closedPoint_of_purelyInseparable
    (hsmooth : Algebra.SmoothAtPrime A B (closedPoint B))
    (hκ : IsPurelyInseparable (ResidueField A) (ResidueField B)) :
    branchNumber A Ah = branchNumber B Bh := sorry

end Henselization

end
