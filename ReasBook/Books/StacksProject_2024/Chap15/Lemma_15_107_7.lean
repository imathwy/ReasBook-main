import Mathlib
import StacksProject_2024.Chap15.Definition_15_107_6
import StacksProject_2024.Chap15.Definition_15_107_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Unibranch
open IsLocalRing

universe u

noncomputable section

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations, strict henselizations, minimal
  primes, and the unibranch normalization;
- sampled owner declarations of the same kind:
  `branchNumber`,
  `geometricBranchNumber`,
  `IsUnibranch`,
  `MaximalSpectrum`;
- best owner abstraction: `branchNumber` and `geometricBranchNumber` remain the source-facing
  owners, while the maximal-ideal side of the finite formulas should be expressed through the
  canonical owner `MaximalSpectrum A′` instead of a parallel subtype of maximal ideals;
- primitive data: the local ring `A` together with a chosen henselization or strict
  henselization;
- derived API: cardinality comparisons for minimal primes and for the maximal spectrum of the
  unibranch normalization.

Source/core/bridge triage:
- `source-facing`: the six clauses of Lemma 15.107.7;
- `core/canonical`: `branchNumber`, `geometricBranchNumber`, `IsUnibranch`,
  `IsGeometricallyUnibranch`, `minimalPrimes`, and `MaximalSpectrum`;
- `bridge/view`: the finite-count formulas over `MaximalSpectrum A′`.
-/

section Henselization

variable (A Ah : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

-- Proof sketch: use the comparison of minimal primes from the henselization count with the reduced
-- integral closure and the fact that an infinite set of minimal primes forces the counted set in
-- the definition of `branchNumber` to have infinite cardinality.
/-- Lemma 15.107.7 (1): if a local ring `A` has infinitely many minimal prime ideals, then the
number of branches of `A`, computed from a chosen henselization `Ah`, is `∞`. -/
theorem branchNumber_eq_top_of_infinite_minimalPrimes
    (hinf : (minimalPrimes A).Infinite) :
    branchNumber A Ah = ⊤ := sorry

-- Proof sketch: unfold `branchNumber` and combine Lemma `15.107.3`, turning the statement
-- `branchNumber A Ah = 1` into the existence of a unique minimal prime of `Ah`.
/-- Lemma 15.107.7 (2): the number of branches of `A`, computed from a chosen henselization `Ah`,
is `1` if and only if `A` is unibranch. -/
theorem branchNumber_eq_one_iff_isUnibranch :
    branchNumber A Ah = 1 ↔ IsUnibranch A := sorry

-- Proof sketch: apply Lemma `15.107.2` to identify minimal primes of the henselization-side
-- normalization base change with minimal primes of `Ah`, then use Lemma `15.107.2 (4)` to replace
-- those minimal primes by points of the maximal spectrum of the reduced integral closure `A'`.
/-- Lemma 15.107.7 (3): if `A` has finitely many minimal primes, then the number of branches of
`A`, computed from a chosen henselization `Ah`, is the number of points of the maximal spectrum of
the unibranch normalization `A'` of `A`. -/
theorem branchNumber_eq_encard_maximalIdeals_unibranchNormalization
    (hfinite : (minimalPrimes A).Finite) :
    branchNumber A Ah = (Set.univ : Set (MaximalSpectrum A′)).encard := sorry

end Henselization

section StrictHenselization

variable (A Ash : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

local notation "κ" => ResidueField A

-- Proof sketch: use the strict henselization analogue of the branch count and compare minimal
-- primes through Lemma `15.107.4`; an infinite set of minimal primes forces the strict
-- henselization count to be infinite as well.
/-- Lemma 15.107.7 (4): if a local ring `A` has infinitely many minimal prime ideals, then the
number of geometric branches of `A`, computed from a chosen strict henselization `Ash`, is `∞`. -/
theorem geometricBranchNumber_eq_top_of_infinite_minimalPrimes
    (hinf : (minimalPrimes A).Infinite) :
    geometricBranchNumber A Ash = ⊤ := sorry

-- Proof sketch: unfold `geometricBranchNumber` and combine Lemma `15.107.5`, turning the
-- statement
-- `geometricBranchNumber A Ash = 1` into the existence of a unique minimal prime of `Ash`.
/-- Lemma 15.107.7 (5): the number of geometric branches of `A`, computed from a chosen strict
henselization `Ash`, is `1` if and only if `A` is geometrically unibranch. -/
theorem geometricBranchNumber_eq_one_iff_isGeometricallyUnibranch :
    geometricBranchNumber A Ash = 1 ↔ IsGeometricallyUnibranch A := sorry

-- Proof sketch: use Lemma `15.107.4 (3)` to replace minimal primes of `Ash` by minimal primes of
-- `A' ⊗[A] A^sh`, use Lemma `15.107.4 (5)` to group them by maximal ideals of `A'`, and then
-- identify each fiber with the separable-degree multiplicity from the residue field extension over
-- `κ` by the actual embedding type `Field.Emb κ m.ResidueField`, equivalently `[κ(m') : κ]_s`,
-- using Lemma `15.107.4 (2)` together with Fields, Lemma `9.14.8`.
/-- Lemma 15.107.7 (6): if `A` has finitely many minimal primes, then the number of geometric
branches of `A`, computed from a chosen strict henselization `Ash`, is obtained by counting each
point `m'` of the maximal spectrum of the unibranch normalization `A'` of `A` with multiplicity
`[κ(m') : κ]_s`. -/
theorem geometricBranchNumber_eq_encard_weighted_maximalSpectrum_unibranchNormalization
    (hfinite : (minimalPrimes A).Finite) :
    geometricBranchNumber A Ash =
      (Set.univ :
        Set (Σ m : MaximalSpectrum A′, Field.Emb κ m.ResidueField)).encard :=
    sorry

end StrictHenselization
