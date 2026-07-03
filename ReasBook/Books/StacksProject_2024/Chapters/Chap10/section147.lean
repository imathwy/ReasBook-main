import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_147_1 (from Chap10) -/
open Polynomial

universe u

section

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/- Domain-style sampling:
- primary domain: commutative algebra of polynomial quotients and integrality over a base ring;
- inspected owner declarations:
  * `exists_derivative_mul_eq_and_isIntegral_coeff`
  * `Ideal.Quotient.mkₐ`
  * `Ideal.Quotient.mkₐ_surjective`
  * `Ideal.Quotient.mkₐ_ker`
- best owner abstraction: the canonical quotient algebra map `Ideal.Quotient.mkₐ R I` into
  `B[X] ⧸ I`, with the representative statement derived from the upstream mathlib theorem
  `exists_derivative_mul_eq_and_isIntegral_coeff`;
- primitive data: the mapped polynomial `f.map (algebraMap R B)`, its principal ideal quotient,
  and the integrality hypothesis on the quotient element `h`;
- derived API: the source-facing existence of a representative for
  `(f.map (algebraMap R B)).derivative * h` with `R`-integral coefficients.
-/

-- Proof sketch: after a syntomic finite free faithfully flat extension of `B`, Lemma `10.136.14`
-- splits `f.map (algebraMap R B)` into linear factors. Evaluating an integral equation for `h` at
-- those roots shows each value `h(αᵢ)` is integral over `R`. The interpolation formula for
-- `derivative (f.map (algebraMap R B)) * h` in the quotient then gives a polynomial
-- representative whose coefficients are integral over `R`, and comparing coordinates in the split
-- extension shows those coefficients already lie in `B`.
/-- Lemma 10.147.1: if `f : R[X]` is monic and `h` is integral over `R` in
`B[X] ⧸ Ideal.span {f.map (algebraMap R B)}`, then
`derivative (f.map (algebraMap R B)) * h` is represented by a polynomial over `B` whose
coefficients are integral over `R`. -/
theorem exists_representative_derivative_mul_with_integral_coeffs
    (f : R[X]) (hf : f.Monic)
    (h : B[X] ⧸ Ideal.span {f.map (algebraMap R B)})
    (hint : IsIntegral R h) :
    ∃ g : B[X],
      (∀ i : ℕ, IsIntegral R (g.coeff i)) ∧
        Ideal.Quotient.mk (Ideal.span {f.map (algebraMap R B)})
            (derivative (f.map (algebraMap R B))) *
          h =
            Ideal.Quotient.mk (Ideal.span {f.map (algebraMap R B)}) g := by
  let fB : B[X] := f.map (algebraMap R B)
  let I : Ideal B[X] := Ideal.span {fB}
  have hfB : fB.Monic := hf.map (algebraMap R B)
  have hfB_coeff : ∀ i, IsIntegral R (fB.coeff i) := fun i ↦ by
    simpa [fB] using (show IsIntegral R (algebraMap R B (f.coeff i)) from isIntegral_algebraMap)
  obtain ⟨g, hg, hgint⟩ :=
    exists_derivative_mul_eq_and_isIntegral_coeff
      (Ideal.Quotient.mkₐ_surjective R I) hfB hfB_coeff
      (Ideal.Quotient.mkₐ_ker R I) hint
  exact ⟨g, hgint, by simpa [fB, I] using hg⟩

end

/-! ### Lemma_10_147_2 (from Chap10) -/
universe u v w

namespace TensorProduct

section

variable {R : Type u} {S : Type v} {B : Type w}
variable [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra R B] [Algebra.Etale R S]

-- Proof sketch: `[Algebra.Etale R S]` provides `[Algebra.Smooth R S]`, so this is the direct
-- source-facing specialization of the canonical owner theorem
-- `TensorProduct.toIntegralClosure_bijective_of_smooth`.
/-- Lemma 10.147.2: if `R → S` is étale and `A = integralClosure R B`, then the canonical map
`S ⊗[R] A → integralClosure S (S ⊗[R] B)` is bijective, hence an isomorphism. -/
theorem toIntegralClosure_bijective_of_etale :
    Function.Bijective (toIntegralClosure R S B) :=
  TensorProduct.toIntegralClosure_bijective_of_smooth

end

end TensorProduct

/-! ### Example_10_147_3 (from Chap10) -/
noncomputable section

open scoped BigOperators
open Polynomial

section

variable (p d : ℕ)

local notation "K" => Localization.Away (p : ℤ)
local notation "P" => cyclotomic p K
local notation "A" => AdjoinRoot P
local notation "ζ" => (AdjoinRoot.root P : A)

/-- Helper for Example 10.147.3: the distinguished adjoined root satisfies `ζ ^ p = 1`. -/
lemma zeta_pow_prime_eq_one [Fact p.Prime] : ζ ^ p = (1 : A) := by
  -- Evaluate the cyclotomic factorization at the distinguished root.
  have h :=
    congrArg (fun Q : K[X] => aeval ζ Q) (Polynomial.cyclotomic_prime_mul_X_sub_one K p)
  have hzero : 0 = ζ ^ p - 1 := by
    simpa [aeval_def] using h
  exact sub_eq_zero.mp hzero.symm

/-- Helper for Example 10.147.3: the distinguished root is a unit because its `p`-th power is `1`.
-/
lemma zeta_isUnit [Fact p.Prime] : IsUnit ζ := by
  -- A `p`-th root of unity is invertible, with inverse `ζ ^ (p - 1)`.
  have hp : p.Prime := Fact.out
  refine IsUnit.of_mul_eq_one (ζ ^ (p - 1)) ?_
  rw [← pow_succ', Nat.sub_one_add_one hp.ne_zero]
  exact zeta_pow_prime_eq_one (p := p)

/-- Helper for Example 10.147.3: the basic cyclotomic unit `ζ - 1` is invertible. -/
lemma zeta_sub_one_isUnit [Fact p.Prime] : IsUnit (ζ - 1) := by
  -- Differentiate `(Φ_p) * (X - 1) = X ^ p - 1`, then evaluate at `ζ`.
  have h :=
    congrArg
      (fun Q : K[X] => aeval ζ Q)
      (congrArg (@Polynomial.derivative K _) (Polynomial.cyclotomic_prime_mul_X_sub_one K p))
  have hderiv_eval :
      aeval ζ (derivative P) * (ζ - 1) = aeval ζ (derivative (X ^ p : K[X])) := by
    simpa [aeval_def, derivative_mul] using h
  have hderiv_rhs : aeval ζ (derivative (X ^ p : K[X])) = (p : A) * ζ ^ (p - 1) := by
    rw [Polynomial.derivative_X_pow]
    simp [aeval_def]
  have hderiv : aeval ζ (derivative P) * (ζ - 1) = (p : A) * ζ ^ (p - 1) :=
    hderiv_eval.trans hderiv_rhs
  have hp_unit : IsUnit (p : A) := by
    simpa using
      (IsLocalization.Away.algebraMap_isUnit (S := K) (x := (p : ℤ))).map (algebraMap K A)
  have hrhs_unit : IsUnit ((p : A) * ζ ^ (p - 1)) := by
    exact hp_unit.mul ((zeta_isUnit (p := p)).pow (p - 1))
  -- The derivative identity shows `ζ - 1` divides a unit.
  exact
    isUnit_of_dvd_unit
      ⟨aeval ζ (derivative P), by simpa [mul_comm] using hderiv.symm⟩
      hrhs_unit

/-- Helper for Example 10.147.3: every nontrivial smaller power difference `ζ ^ m - 1` is a unit.
-/
lemma zeta_pow_sub_one_isUnit [Fact p.Prime] {m : ℕ} (hm0 : 0 < m) (hmp : m < p) :
    IsUnit (ζ ^ m - 1) := by
  -- Use a modular inverse of `m` modulo `p` to compare `ζ ^ m - 1` with `ζ - 1`.
  have hp : p.Prime := Fact.out
  have hm_coprime : m.Coprime p := (Nat.coprime_of_lt_prime hm0.ne' hmp hp).symm
  obtain ⟨n, _, hmod_mod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm_coprime hp.one_lt
  have hmod : m * n ≡ 1 [MOD p] := by
    simpa [Nat.ModEq, Nat.one_mod_eq_one.mpr hp.one_lt.ne'] using hmod_mod
  have hn0 : 0 < n := by
    by_contra hn0
    have hn : n = 0 := Nat.eq_zero_of_not_pos hn0
    have hbad : 0 ≡ 1 [MOD p] := by simpa [hn] using hmod
    have hp1 : 1 < p := hp.one_lt
    simpa [Nat.ModEq, hp1.ne', Nat.one_mod_eq_one.mpr hp1.ne'] using hbad
  have hle : 1 ≤ m * n := by
    simpa using Nat.mul_le_mul (Nat.succ_le_of_lt hm0) (Nat.succ_le_of_lt hn0)
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm
  have hpow : (ζ ^ m) ^ n = ζ := by
    calc
      (ζ ^ m) ^ n = ζ ^ (m * n) := by rw [pow_mul]
      _ = ζ ^ (1 + p * k) := by rw [hk]
      _ = ζ ^ 1 * (ζ ^ p) ^ k := by rw [pow_add, pow_mul]
      _ = ζ * (ζ ^ p) ^ k := by rw [pow_one]
      _ = ζ := by rw [zeta_pow_prime_eq_one (p := p), one_pow, mul_one]
  have hdiv : ζ ^ m - 1 ∣ ζ - 1 := by
    refine ⟨∑ i ∈ Finset.range n, (ζ ^ m) ^ i, ?_⟩
    calc
      ζ - 1 = (ζ ^ m) ^ n - 1 := by simpa [hpow]
      _ = (ζ ^ m - 1) * ∑ i ∈ Finset.range n, (ζ ^ m) ^ i := by
        symm
        exact mul_geom_sum _ _
  -- A divisor of the unit `ζ - 1` is again a unit.
  exact isUnit_of_dvd_unit hdiv (zeta_sub_one_isUnit (p := p))

/-- Helper for Example 10.147.3: each ordered pairwise difference among the first `d` powers of `ζ`
is a unit when `d < p`. -/
lemma pairwise_power_difference_isUnit [Fact p.Prime] {i j : Fin d} (hij : i < j) (hd : d < p) :
    IsUnit (ζ ^ (i : ℕ) - ζ ^ (j : ℕ)) := by
  -- Rewrite the difference as a unit multiple of `ζ ^ (j - i) - 1`.
  have hm0 : 0 < (j : ℕ) - i := Nat.sub_pos_of_lt hij
  have hmp : (j : ℕ) - i < p := by
    exact lt_trans (lt_of_le_of_lt (Nat.sub_le _ _) j.2) hd
  have hz_pow_unit : IsUnit (ζ ^ (i : ℕ)) := (zeta_isUnit (p := p)).pow (i : ℕ)
  have hfactor :
      ζ ^ (i : ℕ) - ζ ^ (j : ℕ) = -(ζ ^ (i : ℕ)) * (ζ ^ ((j : ℕ) - i) - 1) := by
    calc
      ζ ^ (i : ℕ) - ζ ^ (j : ℕ)
          = ζ ^ (i : ℕ) - ζ ^ (i : ℕ) * ζ ^ ((j : ℕ) - i) := by
              rw [show (j : ℕ) = (i : ℕ) + ((j : ℕ) - i) from
                    (Nat.add_sub_of_le (Nat.le_of_lt hij)).symm, pow_add, Nat.add_sub_cancel_left]
      _ = ζ ^ (i : ℕ) * (1 - ζ ^ ((j : ℕ) - i)) := by ring
      _ = -(ζ ^ (i : ℕ)) * (ζ ^ ((j : ℕ) - i) - 1) := by ring
  -- The remaining factor is a unit by the modular-inverse argument.
  rw [hfactor]
  exact (hz_pow_unit.neg).mul (zeta_pow_sub_one_isUnit (p := p) hm0 hmp)

/-- Example 10.147.3: for `d < p`, the first `d` powers of the distinguished root in
`ℤ[1/p][X] / (1 + X + ··· + X^(p - 1))` have unit pairwise-difference product. -/
-- Proof sketch: `Polynomial.cyclotomic_prime` identifies the defining polynomial with
-- `1 + X + ··· + X^(p - 1)`, so the example ring is the canonical adjoin-root quotient
-- `AdjoinRoot (cyclotomic p (Localization.Away (p : ℤ)))`. Take `α_i = ζ^i`, where `ζ` is the
-- distinguished root of this owner polynomial. In the fraction field these are distinct
-- `p`-th roots of unity, so `T^p - 1` factors as `∏ (T - α_i)`. Differentiating and evaluating at
-- each `α_i` identifies the omitted-difference product with `p * α_i^(p - 1)`, which is a unit
-- because `p` is inverted in the base ring and each `α_i` is itself a unit.
theorem cyclotomic_prime_example_unit_pairwise_difference_product
    [Fact p.Prime] (hd : d < p) :
    IsUnit
      (∏ ij ∈ (Finset.univ : Finset (Fin d)).offDiag with ij.1 < ij.2,
        (ζ ^ (ij.1 : ℕ) - ζ ^ (ij.2 : ℕ))) := by
  -- Each factor in the filtered off-diagonal product is already a unit.
  refine (IsUnit.prod_iff).2 ?_
  intro ij hij
  exact pairwise_power_difference_isUnit (p := p) (d := d) ((Finset.mem_filter.mp hij).2) hd

end

/-! ### Lemma_10_147_4 (from Chap10) -/
/- Lemma 10.147.4: if `R → S` is smooth, `A = integralClosure R B`, and
`A' = integralClosure S (S ⊗[R] B)`, then the canonical map
`S ⊗[R] A → A'` is bijective, hence an isomorphism. This is exactly the canonical theorem
`TensorProduct.toIntegralClosure_bijective_of_smooth`. -/
recall TensorProduct.toIntegralClosure_bijective_of_smooth

/-! ### Lemma_10_147_5 (from Chap10) -/
open CategoryTheory Limits MorphismProperty

universe u v

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/- Domain-style sampling for Lemma 10.147.5:
* primary domain: filtered colimits of smooth commutative ring maps;
* sampled owner declarations:
  - `RingHom.Smooth`, the mathlib owner for smooth ring homomorphisms;
  - `RingHom.toMorphismProperty`, the canonical bridge from a ring-hom property to
    `CommRingCat`;
  - `CategoryTheory.MorphismProperty.ind`, the canonical filtered-colimit owner;
  - `RingHom.IsFilteredColimitOfEtale`, the project's source-facing wrapper for the analogous
    filtered-colimit-of-etale property.
* best owner abstraction: `RingHom.IsFilteredColimitOfSmooth` as the source-facing owner, with
  core/canonical content given by `ind (toMorphismProperty RingHom.Smooth)`;
* primitive data: only the ring map `f : R →+* A`;
* derived API: any chosen filtered diagram, cocone, and comparison isomorphism presenting `f` as
  a filtered colimit of smooth algebras.

Source/core/bridge triage:
* `source-facing`: `RingHom.IsFilteredColimitOfSmooth`;
* `core/canonical`: `ind (toMorphismProperty RingHom.Smooth)`;
* `bridge/view`: the hidden same-universe `ULift` presentation of `f` used to speak to
  `CategoryTheory.MorphismProperty.ind`.

The old local `CommRingCat.smooth` abbreviation duplicated the canonical owner
`RingHom.Smooth` and its bridge `RingHom.toMorphismProperty`, so this file now exposes the
filtered-colimit hypothesis through the ring-hom owner instead.
-/

/-- An `R`-algebra map `f : R →+* A` is a filtered colimit of smooth `R`-algebras. This thin
source-facing wrapper hides the same-universe `ULift` bookkeeping needed to express the canonical
owner `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.Smooth)`. -/
abbrev IsFilteredColimitOfSmooth (f : R →+* A) : Prop :=
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra R (ULift A) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift A) := ULift.algebra' R (ULift A)
  ind.{max u v, max u v, max u v + 1} (toMorphismProperty Smooth)
    (CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift A)))

end

end RingHom

namespace TensorProduct

section

variable {R S : Type u} {B : Type v}
variable [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra R B]

-- Proof sketch: write `S` as a filtered colimit of smooth `R`-algebras. By Lemma `10.147.4`,
-- the canonical comparison map is bijective after base change to each smooth stage. Tensor
-- products commute with filtered colimits, and the integral closure on the target is obtained as
-- the filtered colimit of the stagewise integral closures, so the colimit comparison map is
-- exactly `TensorProduct.toIntegralClosure R S B`.
/-- Lemma 10.147.5: if `R → S` is a filtered colimit of smooth `R`-algebras and
`A = integralClosure R B`, then the canonical map
`S ⊗[R] A → integralClosure S (S ⊗[R] B)` is bijective, hence an isomorphism. -/
theorem toIntegralClosure_bijective_of_isFilteredColimitOfSmooth
    (hS : (algebraMap R S).IsFilteredColimitOfSmooth) :
    Function.Bijective (toIntegralClosure R S B) := sorry

end

end TensorProduct
