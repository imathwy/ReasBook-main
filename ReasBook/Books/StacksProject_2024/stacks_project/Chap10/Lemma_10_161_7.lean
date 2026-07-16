import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_161_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain triage: this file is in the commutative algebra of `N-1`/`N-2` descent along
module-finite extensions of domains.

Owner abstractions sampled for this item:
- `IsN1Ring`, the source-facing `N-1` owner from `Definition_10_161_1`;
- `IsN2Ring`, the source-facing `N-2` owner from `Definition_10_161_1`;
- `IsN1Ring.integralClosure_finite`, the derived finite-normalization field of the `N-1` owner;
- `IsN2Ring.integralClosure_finite`, the derived finite-normalization-in-finite-extensions field
  of the `N-2` owner.

This file is `source-facing`: the textbook item states descent of the `N-1` and `N-2` properties
themselves along a finite extension `R ⊂ S`. The primitive data are the rings and the finite
extension `R → S`; the finiteness statements for integral closures are derived API coming from the
owner classes and should remain internal to the eventual proofs rather than becoming new public
wrapper declarations here.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]

-- Proof sketch: let `R'` be the integral closure of `R` in `FractionRing R`. The fraction field of
-- `S` is a finite extension of `FractionRing R`, so `R'` maps into the integral closure of `S` in
-- `FractionRing S`. Since `S` is finite over `R` and `R` is Noetherian, the finiteness of that
-- larger integral closure over `S` descends to finiteness of `R'` over `R`.
/-- Lemma 10.161.7 (1): if `R` is a Noetherian domain, `R ⊂ S` is a finite extension of domains,
and `S` is `N-1`, then `R` is `N-1`. -/
theorem isN1Ring_of_finite_extension
    (hRS : Function.Injective (algebraMap R S)) [IsN1Ring S] :
    IsN1Ring R := by
  sorry

-- Proof sketch: fix a finite extension `L` of `FractionRing R`. Using the finite domain extension
-- `R ⊂ S`, view `L` as a finite extension of `FractionRing S`. The integral closure of `R` in `L`
-- is contained in the integral closure of `S` in `L`; the latter is finite over `S` by the `N-2`
-- hypothesis on `S`, hence finite over `R` because `S` is finite over `R`.
/-- Lemma 10.161.7 (2): if `R` is a Noetherian domain, `R ⊂ S` is a finite extension of domains,
and `S` is `N-2`, then `R` is `N-2`. -/
theorem isN2Ring_of_finite_extension
    (hRS : Function.Injective (algebraMap R S)) [IsN2Ring S] :
    IsN2Ring R := by
  sorry

end
