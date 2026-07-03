import Mathlib
import StacksProject_2024.Chap10.Lemma_10_155_6
import StacksProject_2024.Chap10.Lemma_10_155_10
import StacksProject_2024.Chap15.Lemma_15_12_3
import StacksProject_2024.Chap15.Lemma_15_12_4
import StacksProject_2024.Chap15.Lemma_15_43_1
import StacksProject_2024.Chap15.Definition_15_107_6

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingPairCat

universe u

noncomputable section

section

variable {A Ah Ash Ahatsh : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/- Domain-style sampling:
- primary domain: local commutative algebra of henselizations, strict henselizations, and
  maximal-ideal completions of Noetherian local rings;
- sampled owner declarations:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `RingPairCat.henselizationToAdicCompletion`,
  `henselizationMapRingHom`,
  `existsUnique_algHom_between_strictHenselizations_of_residueFieldMap`,
  `strictHenselizationComparison`,
  `minimalPrimes`,
  `RingHom.FaithfullyFlat.injective`;
- best owner abstraction: the completion comparison should come from the pair-henselization owner
  map `RingPairCat.henselizationToAdicCompletion`, specialized to `(A, maximalIdeal A)` and
  composed with the Chapter 10 comparison `henselizationMapRingHom` from an arbitrary chosen
  henselization `Ah` into that owner. For strict henselizations, the source-facing statement is
  the branch-number inequality itself; any compatible residue-field map belongs only to the
  auxiliary bridge that derives the comparison `Ash → Ahatsh` from
  `existsUnique_algHom_between_strictHenselizations_of_residueFieldMap`, as in Chapter 10's
  `strictHenselizationComparison`, rather than to the main theorem surface;
- primitive data: the local Noetherian ring `A`, a chosen henselization `Ah`, and for part `(3)`
  the chosen strict henselizations of `A` and `ACompletion`;
- derived API: the owner-derived henselization-completion comparison and the induced contraction
  map on minimal primes, together with the owner-derived strict-henselization completion
  comparison and its locality / flatness properties.

Source/core/bridge triage:
- `source-facing`: the three branch-count comparisons in Lemma 15.109.1;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`, `minimalPrimes`,
  `RingHom.FaithfullyFlat`, the pair-henselization completion owner, and
  `existsUnique_algHom_between_strictHenselizations_of_residueFieldMap`;
- `bridge/view`: the owner-derived comparison `Ah → ACompletion` and the residue-field
  compatibility data used only to derive the strict-henselization completion comparison.
-/
local notation "A_pair" => pairOfIdeal (maximalIdeal A)
local notation "A_h" => henselizationRing A_pair

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

private noncomputable abbrev selfHenselizationMapRingHom
    (R : Type u) [CommRing R] [IsLocalRing R]
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    (R_h : Type u) [CommRing R_h] [Algebra R R_h] [IsHenselizationOf R R_h] :
    Rh →+* R_h :=
  @henselizationMapRingHom R Rh R_h _ _ _ _ _ _ R _ _ _ _ _ _

/-- The canonical comparison map from a chosen henselization `Ah` of a Noetherian local ring `A`
to the maximal-ideal completion `AdicCompletion (maximalIdeal A) A`. -/
noncomputable abbrev henselizationCompletionComparison
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh] :
    Rh →+* AdicCompletion (maximalIdeal R) R :=
  let R_pair := pairOfIdeal (maximalIdeal R)
  let R_h := henselizationRing R_pair
  R_pair.henselizationToAdicCompletion.comp (selfHenselizationMapRingHom R Rh R_h)

-- Proof sketch: combine injectivity of `Ah → Ahat` with the minimal-prime existence result for
-- injective maps and the going-down property for flat maps to show every minimal prime of `Ah` is
-- the contraction of some minimal prime of `Ahat`.
/-- Lemma 15.109.1 (1): for a Noetherian local ring `A`, the canonical compatible map from a
chosen henselization `Ah` to the maximal-ideal completion `AdicCompletion (maximalIdeal A) A`
induces a surjection from the minimal primes of the completion onto the minimal primes of `Ah`. -/
theorem henselizationCompletion_surjOn_minimalPrimes :
    Set.SurjOn
      (Ideal.comap (henselizationCompletionComparison A Ah))
      (minimalPrimes ACompletion)
      (minimalPrimes Ah) := sorry

-- Proof sketch: apply the previous surjectivity statement to the contraction map on minimal
-- primes and compare cardinalities of the minimal-prime sets.
/-- Lemma 15.109.1 (2): the number of branches of `A`, computed from a chosen henselization `Ah`,
is at most the number of minimal primes of the completion
`AdicCompletion (maximalIdeal A) A`. Since the completion is henselian, this is the number of
branches of the completion. -/
theorem branchNumber_le_completion_minimalPrimes :
    branchNumber A Ah ≤ (minimalPrimes ACompletion).encard := sorry

variable [CommRing Ahatsh] [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
variable [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]

-- Proof sketch: compare `Ash` with a strict henselization `Ahatsh` of the completion through the
-- flat injective owner comparison `Ash → Ahatsh`, obtained internally from the canonical
-- strict-henselization comparison bridge; the auxiliary composed `A`-algebra structure on
-- `Ahatsh` and the tower through `ACompletion` are derived internally from
-- `A → ACompletion → Ahatsh`. Repeat the minimal-prime argument from part `(1)`, and then
-- translate the resulting surjectivity into the inequality of geometric branch numbers.
/-- Lemma 15.109.1 (3): for a chosen strict henselization `Ash` of `A` and a chosen strict
henselization `Ahatsh` of the completion `ACompletion = AdicCompletion (maximalIdeal A) A`, the
canonical comparison between these strict henselizations induces the branch-count inequality from
`A` to its completion. -/
theorem geometricBranchNumber_le_completion :
    geometricBranchNumber A Ash ≤ geometricBranchNumber ACompletion Ahatsh := sorry

end
