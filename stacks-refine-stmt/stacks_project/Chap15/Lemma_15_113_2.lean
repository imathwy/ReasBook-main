import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open scoped Pointwise

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
  [FiniteDimensional (FractionRing A) L] [IsGalois (FractionRing A) L]

local notation "K" => FractionRing A
local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A

/- Domain-style sampling for Lemma 15.113.2:
- primary domain: ramification and inertia for primes of the integral closure of a discrete
  valuation ring in a finite Galois extension;
- inspected owner declarations:
  `integralClosure.isFractionRing_of_finite_extension`,
  `IsIntegralClosure.finite`,
  `integralClosure.isDedekindDomain`,
  `Ideal.ramificationIdxIn_eq_ramificationIdx`,
  `Ideal.inertiaDegIn_eq_inertiaDeg`,
  `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`;
- best owner abstraction: the integral-closure owner `B = integralClosure A L`, its canonical
  owner set `p.primesOver B`, and the Galois ramification owners `p.ramificationIdxIn B` and
  `p.inertiaDegIn B`;
- primitive data: the owner ring `B`, the maximal ideal `p = maximalIdeal A`, and a chosen branch
  `P : p.primesOver B`;
- derived API: the fraction-field, finiteness, Dedekind-domain, induced Galois-action, and
  `IsGaloisGroup` instances on `B`, plus the equal-ramification / equal-inertia / fundamental
  identity theorems specialized to this owner. -/

/- Source/core/bridge triage:
- source-facing: the three specialized statements for the maximal ideal of a discrete valuation
  ring;
- core/canonical: the integral-closure owners above and the mathlib Galois ramification theorems;
- bridge/view: specialization from the general Galois-Dedekind owner API to the DVR setting
  `p = maximalIdeal A`, `B = integralClosure A L`. -/

local instance : IsFractionRing B L :=
  integralClosure.isFractionRing_of_finite_extension K L

local instance : Module.Finite A B :=
  IsIntegralClosure.finite A K L B

local instance : IsDedekindDomain B :=
  integralClosure.isDedekindDomain A K L

local instance : Module.IsTorsionFree A L :=
  .trans_faithfulSMul A K L

local instance : Module.IsTorsionFree A B :=
  IsIntegralClosure.isTorsionFree A L

local instance : IsGaloisGroup Gal(L/K) A B :=
  IsGaloisGroup.of_isFractionRing Gal(L/K) A B K L

-- Proof sketch: apply `Ideal.ramificationIdxIn_eq_ramificationIdx` to a branch
-- `P : p.primesOver B`, using the owner instance that such a branch is maximal, then reverse the
-- resulting equality.
/- Lemma 15.113.2 (1): every prime of the integral closure above the maximal ideal of the base
discrete valuation ring is automatically maximal, so its ramification index is the common value
`Ideal.ramificationIdxIn p B`. -/
theorem ramificationIdx_eq_ramificationIdxIn_of_mem_primesOver
    (P : (p).primesOver B) :
    ramificationIdx p P.1 = (p).ramificationIdxIn B := by
  let _ : P.1.IsMaximal := inferInstance
  simpa [eq_comm] using Ideal.ramificationIdxIn_eq_ramificationIdx p P.1 Gal(L/K)

-- Proof sketch: apply `Ideal.inertiaDegIn_eq_inertiaDeg` to a branch `P : p.primesOver B`, using
-- the owner instance that such a branch is maximal, then reverse the resulting equality.
/- Lemma 15.113.2 (2): every prime of the integral closure above the maximal ideal of the base
discrete valuation ring is automatically maximal, so its inertia degree is the common value
`Ideal.inertiaDegIn p B`. -/
theorem inertiaDeg_eq_inertiaDegIn_of_mem_primesOver
    (P : (p).primesOver B) :
    inertiaDeg p P.1 = (p).inertiaDegIn B := by
  let _ : P.1.IsMaximal := inferInstance
  simpa [eq_comm] using Ideal.inertiaDegIn_eq_inertiaDeg p P.1 Gal(L/K)

/-- The common ramification index in Lemma 15.113.2 satisfies `e ≥ 1`. -/
theorem one_le_ramificationIdxIn :
    1 ≤ (p).ramificationIdxIn B := by
  exact Nat.succ_le_of_lt <| Nat.pos_of_ne_zero <|
    Ideal.ramificationIdxIn_ne_zero Gal(L/K) (IsDiscreteValuationRing.not_a_field A)

/-- The common inertia degree in Lemma 15.113.2 satisfies `f ≥ 1`. -/
theorem one_le_inertiaDegIn :
    1 ≤ (p).inertiaDegIn B := by
  exact Nat.succ_le_of_lt <| Nat.pos_of_ne_zero <|
    Ideal.inertiaDegIn_ne_zero Gal(L/K)

-- Proof sketch: use
-- `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` and identify `Nat.card
-- (Gal(L/K))` with `Module.finrank K L`.
/-- Lemma 15.113.2 (3): the degree of the finite Galois extension is the number of primes of the
integral closure above the maximal ideal times the common ramification index and inertia degree. -/
theorem finrank_eq_ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn :
    Module.finrank K L =
      ((p).primesOver B).ncard * ((p).ramificationIdxIn B * (p).inertiaDegIn B) := by
  calc
    Module.finrank K L = Nat.card Gal(L/K) := by
      simpa using (IsGaloisGroup.card_eq_finrank Gal(L/K) K L).symm
    _ = ((p).primesOver B).ncard * ((p).ramificationIdxIn B * (p).inertiaDegIn B) := by
      symm
      exact
        Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
          (IsDiscreteValuationRing.not_a_field A) B Gal(L/K)

end
