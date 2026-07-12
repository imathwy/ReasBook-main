import Mathlib
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularIndicator
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerBasisAPI

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section ProjectiveCharacterCriterion

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
-- Serre's Chapter 18 modular system uses a *complete* DVR `A`; the projective scalar-extension
-- owner `projectiveCharacterScalarExtension` requires adic completeness of the maximal ideal.
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [CharZero K]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

/-
Domain-style sampling for Exercise `18-18.3-2`:
* primary domain: modular representation theory of finite groups, combining the projective
  scalar-extension owner `projectiveGrothendieckScalarExtensionHom A K`, the Chapter `16`
  Grothendieck-character owner `finiteRepGrothendieckCharacter`, the Chapter `12`
  scalar-extension owner `A ⊗R[K](G)`, and the Cartan owners `cartanCokernel` and
  `cartanMatrix`;
* relevant owner declarations inspected in this domain:
  `projectiveGrothendieckScalarExtensionHom`,
  `finiteRepGrothendieckCharacter`,
  `characterRingOverFieldAlgebraScalarExtension`,
  `cartanCokernel`,
  `cartanMatrix`.

Layer triage:
* source-facing: the projective-character span inside `A ⊗R[K](G)` and the invariant-factor
  formulas indexed by `p`-regular conjugacy-class representatives;
* core/canonical: the owner declarations
  `projectiveGrothendieckScalarExtensionHom A K`, `finiteRepGrothendieckCharacter K G`,
  `A ⊗R[K](G)`, `cartanCokernel`, and `cartanMatrix`;
* bridge/view: the codomain restriction from `R₀[K](G)` to `A ⊗R[K](G)` obtained from
  `finiteRepGrothendieckCharacter K G` and the canonical inclusion `R[K](G) ⊆ A ⊗R[K](G)`.

Ordinary-character regime check:
* the source-facing span in part `(1)` lives in the characteristic-zero ordinary-character setting
  used nearby in Chapter `18`;
* its primitive definition inside `A ⊗R[K](G)` needs only `[CharZero K]`, but the membership
  criterion below must stay in the standard large-field regime
  `[HasEnoughRootsOfUnity K (Monoid.exponent G)]`, matching the Chapter `16` image criterion and
  neighboring Theorem `18-18.3-1`.
-/
local notation "k" => IsLocalRing.ResidueField A
local notation "e" => (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G))
local instance instFintypeGPrimeToPRootLift : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 18-18.3-2: choose residue-field representatives in `A` for the
prime-to-`p` roots appearing in the coefficient-ring Brauer basis. -/
noncomputable def primeToPRoot_residue_section :
    PrimeToPRoot p k → A :=
  fun ζ ↦ Classical.choose (IsLocalRing.residue_surjective (R := A) (ζ : k))

/-- Helper for Exercise 18-18.3-2: the chosen residue-field representatives really lift the
underlying prime-to-`p` roots of unity. -/
@[simp] theorem residue_primeToPRoot_residue_section
    (ζ : PrimeToPRoot p k) :
    IsLocalRing.residue A
        (primeToPRoot_residue_section (p := p) (A := A) ζ) =
      (ζ : k) := by
  exact Classical.choose_spec (IsLocalRing.residue_surjective (R := A) (ζ : k))

/-- Helper for Exercise 18-18.3-2: the chosen residue-field section on prime-to-`p` roots is
injective, so it can serve as the coefficient-ring lift required by Exercise `18-18.2-9`. -/
theorem primeToPRoot_residue_section_injective :
    Function.Injective (primeToPRoot_residue_section (p := p) (A := A)) := by
  intro ζ ξ hζξ
  apply Subtype.ext
  apply Units.ext
  have hres := congrArg (IsLocalRing.residue A) hζξ
  simpa using hres

/-- Helper for Exercise 18-18.3-2: every prime-to-`p` root of unity in the residue field lifts to
an actual root of the same order in the Henselian coefficient ring `A`. This is the fixed-order
Hensel step needed before packaging a source-faithful multiplicative lift. -/
theorem exists_primeToPRoot_pow_lift
    (ζ : PrimeToPRoot p k) :
    ∃ a : A,
      a ^ orderOf (ζ : kˣ) = 1 ∧
        IsLocalRing.residue A a = (ζ : k) := by
  have hcop : Nat.Coprime p (orderOf (ζ : kˣ)) := by
    exact ζ.2
  have hn_ne : orderOf (ζ : kˣ) ≠ 0 := by
    -- A `p`-regular root of unity has finite order prime to `p`, hence nonzero order.
    intro hn0
    have hp_one : p = 1 := by
      simpa [hn0] using hcop
    exact (Fact.out : Nat.Prime p).ne_one hp_one
  have hpow : (ζ : k) ^ orderOf (ζ : kˣ) = 1 := by
    -- The residue-field root already satisfies its defining cyclotomic equation.
    simpa using congrArg ((↑) : kˣ → k) (pow_orderOf_eq_one (ζ : kˣ))
  let f : Polynomial A := Polynomial.X ^ orderOf (ζ : kˣ) - 1
  have hf_monic : f.Monic := by
    simpa [f] using (Polynomial.monic_X_pow_sub_C (a := (1 : A)) hn_ne)
  have hTFAE := HenselianLocalRing.TFAE A
  have hresidue_lift :
      ∀ f : Polynomial A, f.Monic → ∀ a₀ : k,
        Polynomial.aeval a₀ f = 0 → Polynomial.aeval a₀ (Polynomial.derivative f) ≠ 0 →
          ∃ a : A, f.IsRoot a ∧ IsLocalRing.residue A a = a₀ := by
    -- Use the residue-field formulation of Hensel's lemma bundled in mathlib's TFAE.
    exact (List.TFAE.out hTFAE 0 1).mp (show HenselianLocalRing A from inferInstance)
  have hroot0 : Polynomial.aeval (ζ : k) f = 0 := by
    -- The target residue root is a simple root of `X^n - 1` in the residue field.
    simpa [Polynomial.aeval_def, f, sub_eq_zero] using hpow
  have hderiv_ne : Polynomial.aeval (ζ : k) (Polynomial.derivative f) ≠ 0 := by
    have hn_not_dvd : ¬ p ∣ orderOf (ζ : kˣ) :=
      (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcop
    have hn_cast_ne : ((orderOf (ζ : kˣ) : ℕ) : k) ≠ 0 :=
      (NeZero.of_not_dvd (R := k) hn_not_dvd).out
    have hzeta_ne : (ζ : k) ≠ 0 := Units.ne_zero _
    -- The derivative is `n * X^(n-1)`, and both factors stay nonzero at a root of unity.
    rw [show Polynomial.aeval (ζ : k) (Polynomial.derivative f) =
        ((orderOf (ζ : kˣ) : k) * (ζ : k) ^ (orderOf (ζ : kˣ) - 1)) by
          rw [show Polynomial.derivative f =
              Polynomial.derivative (Polynomial.X ^ orderOf (ζ : kˣ)) by
                simp [f]]
          rw [Polynomial.derivative_X_pow]
          simp]
    exact mul_ne_zero hn_cast_ne (pow_ne_zero _ hzeta_ne)
  obtain ⟨a, ha_root, ha_res⟩ := hresidue_lift f hf_monic (ζ : k) hroot0 hderiv_ne
  refine ⟨a, ?_, ha_res⟩
  -- Unfold the polynomial root condition back to the concrete order equation.
  have hroot_eq : a ^ orderOf (ζ : kˣ) - 1 = 0 := by
    simpa [f, Polynomial.IsRoot.def] using Polynomial.IsRoot.def.mp ha_root
  exact sub_eq_zero.mp hroot_eq

/-- Helper for Exercise 18-18.3-2: if `a^m = 1`, then `a^n = 1` for every multiple `n` of `m`.
This isolates the fixed-order bookkeeping used when comparing different chosen lifts at a common
exponent. -/
theorem pow_eq_one_of_pow_eq_one_of_dvd
    {a : A} {m n : ℕ} (ha : a ^ m = 1) (hmn : m ∣ n) :
    a ^ n = 1 := by
  rcases hmn with ⟨r, rfl⟩
  rw [pow_mul, ha, one_pow]

/-- Helper for Exercise 18-18.3-2: the order of a prime-to-`p` root of unity is nonzero. This is
the input needed to turn its fixed-order lift into a unit. -/
theorem primeToPRoot_order_ne_zero
    (ζ : PrimeToPRoot p k) :
    orderOf (ζ : kˣ) ≠ 0 := by
  intro hzero
  have hcop : Nat.Coprime p 0 := hzero ▸ ζ.2
  have hp_one : p = 1 := (Nat.coprime_zero_right p).mp hcop
  exact (Fact.out : Nat.Prime p).ne_one hp_one

/-- Helper for Exercise 18-18.3-2: choose the fixed-order Hensel lift attached to a prime-to-`p`
root of unity in the residue field. -/
noncomputable def primeToPRoot_powLift :
    PrimeToPRoot p k → A :=
  fun ζ ↦ Classical.choose (exists_primeToPRoot_pow_lift (p := p) (A := A) ζ)

/-- Helper for Exercise 18-18.3-2: the chosen fixed-order lift satisfies the expected order
equation in `A`. -/
@[simp] theorem primeToPRoot_powLift_pow_orderOf
    (ζ : PrimeToPRoot p k) :
    primeToPRoot_powLift (p := p) (A := A) ζ ^ orderOf (ζ : kˣ) = 1 := by
  exact (Classical.choose_spec (exists_primeToPRoot_pow_lift (p := p) (A := A) ζ)).1

/-- Helper for Exercise 18-18.3-2: the chosen fixed-order lift reduces to the original residue
root of unity. -/
@[simp] theorem residue_primeToPRoot_powLift
    (ζ : PrimeToPRoot p k) :
    IsLocalRing.residue A (primeToPRoot_powLift (p := p) (A := A) ζ) = (ζ : k) := by
  exact (Classical.choose_spec (exists_primeToPRoot_pow_lift (p := p) (A := A) ζ)).2

/-- Helper for Exercise 18-18.3-2: the fixed-order lift is automatically a unit because a
nontrivial power of it equals `1`. -/
noncomputable def primeToPRoot_unitLift
    (ζ : PrimeToPRoot p k) : Aˣ :=
  (IsUnit.of_pow_eq_one
    (primeToPRoot_powLift_pow_orderOf (p := p) (A := A) ζ)
    (primeToPRoot_order_ne_zero (p := p) (A := A) ζ)).unit

/-- Helper for Exercise 18-18.3-2: coercing the chosen unit lift back to `A` recovers the fixed
order lift chosen above. -/
@[simp] theorem primeToPRoot_unitLift_val
    (ζ : PrimeToPRoot p k) :
    ((primeToPRoot_unitLift (p := p) (A := A) ζ : Aˣ) : A) =
      primeToPRoot_powLift (p := p) (A := A) ζ := by
  exact IsUnit.unit_spec
    (IsUnit.of_pow_eq_one
      (primeToPRoot_powLift_pow_orderOf (p := p) (A := A) ζ)
      (primeToPRoot_order_ne_zero (p := p) (A := A) ζ))

/-- Helper for Exercise 18-18.3-2: the chosen unit lift still reduces to the original prime-to-`p`
root of unity. -/
@[simp] theorem residue_primeToPRoot_unitLift
    (ζ : PrimeToPRoot p k) :
    IsLocalRing.residue A ((primeToPRoot_unitLift (p := p) (A := A) ζ : Aˣ) : A) = (ζ : k) := by
  simpa using residue_primeToPRoot_powLift (p := p) (A := A) ζ

/-- Helper for Exercise 18-18.3-2: an `n`-th root of unity in the coefficient ring that reduces
to `1` is already `1` when `n` is prime to `p`. This is the uniqueness input behind the canonical
prime-to-`p` lift. -/
private theorem unit_eq_one_of_pow_eq_one_of_residue_eq_one
    {u : Aˣ} {n : ℕ} (hn : Nat.Coprime p n)
    (hu : ((u : A) ^ n) = 1)
    (hres : IsLocalRing.residue A (u : A) = 1) :
    u = 1 := by
  let s : A := ∑ i ∈ Finset.range n, (u : A) ^ i
  have hn_not_dvd : ¬ p ∣ n :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hn
  have hn_cast_ne : ((n : ℕ) : k) ≠ 0 :=
    (NeZero.of_not_dvd (R := k) hn_not_dvd).out
  have hs_res :
      IsLocalRing.residue A s = (n : k) := by
    -- The geometric sum reduces to the constant sum `1 + ... + 1 = n`.
    calc
      IsLocalRing.residue A s
          = ∑ i ∈ Finset.range n,
              IsLocalRing.residue A ((u : A) ^ i) := by
                simp [s]
      _ = ∑ i ∈ Finset.range n, (1 : k) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [map_pow]
            simpa [hres]
      _ = (n : k) := by simp
  have hs_unit : IsUnit s := by
    have hs_res_ne : IsLocalRing.residue A s ≠ 0 := by
      simpa [hs_res] using hn_cast_ne
    have hs_not_mem : s ∉ IsLocalRing.maximalIdeal A := by
      intro hs_mem
      exact hs_res_ne ((IsLocalRing.residue_eq_zero_iff s).2 hs_mem)
    exact (IsLocalRing.notMem_maximalIdeal).1 hs_not_mem
  have hgeom : s * ((u : A) - 1) = 0 := by
    -- Rewrite the standard geometric-series identity using `u^n = 1`.
    simpa [s, hu] using (geom_sum_mul (u : A) n)
  have hsub : (u : A) - 1 = 0 := by
    exact (IsUnit.mul_right_eq_zero hs_unit).1 hgeom
  apply Units.ext
  exact sub_eq_zero.mp hsub

/-- Helper for Exercise 18-18.3-2: the fixed-order lift of a prime-to-`p` root of unity is unique
once its residue and a common prime-to-`p` exponent are prescribed. -/
theorem primeToPRoot_powLift_unique
    {a b : A} {n : ℕ} (hn : Nat.Coprime p n)
    (ha : a ^ n = 1) (hb : b ^ n = 1)
    (hres : IsLocalRing.residue A a = IsLocalRing.residue A b) :
    a = b := by
  have hn_ne : n ≠ 0 := by
    intro hzero
    have hcop : Nat.Coprime p 0 := hzero ▸ hn
    have hp_one : p = 1 := (Nat.coprime_zero_right p).mp hcop
    exact (Fact.out : Nat.Prime p).ne_one hp_one
  rcases IsUnit.of_pow_eq_one ha hn_ne with ⟨ua, rfl⟩
  rcases IsUnit.of_pow_eq_one hb hn_ne with ⟨ub, rfl⟩
  have hub_res_ne : IsLocalRing.residue A (ub : A) ≠ 0 := by
    simpa using (Units.ne_zero (Units.map (IsLocalRing.residue A).toMonoidHom ub))
  have hua_pow : ua ^ n = 1 := by
    apply Units.ext
    simpa using ha
  have hub_pow : ub ^ n = 1 := by
    apply Units.ext
    simpa using hb
  have hu_pow :
      ((((ua * ub⁻¹ : Aˣ) : A)) ^ n) = 1 := by
    have hu_pow_units : (ua * ub⁻¹ : Aˣ) ^ n = 1 := by
      rw [mul_pow, hua_pow, inv_pow, hub_pow]
      simp
    simpa using congrArg (fun z : Aˣ ↦ (z : A)) hu_pow_units
  have hu_res :
      IsLocalRing.residue A (((ua * ub⁻¹ : Aˣ) : A)) = 1 := by
    calc
      IsLocalRing.residue A (((ua * ub⁻¹ : Aˣ) : A))
          = IsLocalRing.residue A (ua : A) *
              (IsLocalRing.residue A (ub : A))⁻¹ := by
                simp
      _ = IsLocalRing.residue A (ub : A) *
            (IsLocalRing.residue A (ub : A))⁻¹ := by
              rw [hres]
      _ = 1 := by
            rw [mul_inv_cancel₀ hub_res_ne]
  have hu_eq_one : (ua * ub⁻¹ : Aˣ) = 1 :=
    unit_eq_one_of_pow_eq_one_of_residue_eq_one
      (p := p) (A := A) hn hu_pow hu_res
  -- Multiply back by `ub` to recover the equality of the two chosen lifts.
  have hua_eq_ub : ua = ub := by
    simpa [mul_assoc] using congrArg (fun z : Aˣ ↦ z * ub) hu_eq_one
  simpa using congrArg (fun z : Aˣ ↦ (z : A)) hua_eq_ub

/-- Helper for Exercise 18-18.3-2: the canonical fixed-order lift packages into a multiplicative
map on prime-to-`p` roots of unity. This is the source-faithful replacement for the earlier
arbitrary residue section. -/
noncomputable def primeToPRoot_unitsLift :
    PrimeToPRoot p k →* Aˣ where
  toFun := primeToPRoot_unitLift (p := p) (A := A)
  map_one' := by
    apply Units.ext
    rw [primeToPRoot_unitLift_val]
    exact
      primeToPRoot_powLift_unique (p := p) (A := A)
        (n := 1) (Nat.coprime_one_right p)
        (by simpa using primeToPRoot_powLift_pow_orderOf (p := p) (A := A) (1 : PrimeToPRoot p k))
        (by simp)
        (by simpa using residue_primeToPRoot_powLift (p := p) (A := A) (1 : PrimeToPRoot p k))
  map_mul' ζ ξ := by
    apply Units.ext
    let n : ℕ := orderOf (ζ : kˣ) * orderOf (ξ : kˣ)
    have hn : Nat.Coprime p n := by
      dsimp [n]
      rw [Nat.coprime_mul_iff_right]
      exact ⟨ζ.2, ξ.2⟩
    have hζ_pow :
        (primeToPRoot_unitLift (p := p) (A := A) ζ : A) ^ n = 1 := by
      dsimp [n]
      exact
        pow_eq_one_of_pow_eq_one_of_dvd
          (primeToPRoot_powLift_pow_orderOf (p := p) (A := A) ζ)
          (dvd_mul_right (orderOf (ζ : kˣ)) (orderOf (ξ : kˣ)))
    have hξ_pow :
        (primeToPRoot_unitLift (p := p) (A := A) ξ : A) ^ n = 1 := by
      dsimp [n]
      exact
        pow_eq_one_of_pow_eq_one_of_dvd
          (primeToPRoot_powLift_pow_orderOf (p := p) (A := A) ξ)
          (by
            simpa [Nat.mul_comm] using
              (dvd_mul_left (orderOf (ξ : kˣ)) (orderOf (ζ : kˣ))))
    have hmul_pow :
        (((primeToPRoot_unitLift (p := p) (A := A) ζ : A) *
              (primeToPRoot_unitLift (p := p) (A := A) ξ : A)) ^ n) = 1 := by
      calc
        (((primeToPRoot_unitLift (p := p) (A := A) ζ : A) *
              (primeToPRoot_unitLift (p := p) (A := A) ξ : A)) ^ n)
            =
              (primeToPRoot_unitLift (p := p) (A := A) ζ : A) ^ n *
                (primeToPRoot_unitLift (p := p) (A := A) ξ : A) ^ n := by
                  rw [mul_pow]
        _ = 1 * 1 := by rw [hζ_pow, hξ_pow]
        _ = 1 := by simp
    have hprod_pow :
        primeToPRoot_powLift (p := p) (A := A) (ζ * ξ) ^ n = 1 := by
      dsimp [n]
      exact
        pow_eq_one_of_pow_eq_one_of_dvd
          (primeToPRoot_powLift_pow_orderOf (p := p) (A := A) (ζ * ξ))
          (Commute.orderOf_mul_dvd_mul_orderOf (Commute.all (ζ : kˣ) (ξ : kˣ)))
    rw [primeToPRoot_unitLift_val]
    exact
      primeToPRoot_powLift_unique (p := p) (A := A) hn hprod_pow hmul_pow <| by
        simpa [map_mul, primeToPRoot_unitLift_val]

/-- Helper for Exercise 18-18.3-2: forgetting the unit structure on the canonical lift is still
injective because reduction to the residue field recovers the original root of unity. -/
theorem primeToPRoot_unitsLift_injective :
    Function.Injective fun ζ : PrimeToPRoot p k ↦
      ((primeToPRoot_unitsLift (p := p) (A := A) ζ : Aˣ) : A) := by
  intro ζ ξ hζξ
  apply Subtype.ext
  apply Units.ext
  calc
    ((ζ : kˣ) : k)
        = IsLocalRing.residue A ((primeToPRoot_unitsLift (p := p) (A := A) ζ : Aˣ) : A) := by
            symm
            exact residue_primeToPRoot_unitLift (p := p) (A := A) ζ
    _ =
        IsLocalRing.residue A ((primeToPRoot_unitsLift (p := p) (A := A) ξ : Aˣ) : A) := by
          exact congrArg (IsLocalRing.residue A) hζξ
    _ = ((ξ : kˣ) : k) := residue_primeToPRoot_unitLift (p := p) (A := A) ξ

/-- Helper for Exercise 18-18.3-2: the Hensel lift of a prime-to-`p` root remains primitive after
mapping to the fraction field. -/
theorem algebraMap_primeToPRoot_unitsLift_isPrimitiveRoot
    (ζ : PrimeToPRoot p k) :
    IsPrimitiveRoot
      (algebraMap A K ((primeToPRoot_unitsLift (p := p) (A := A) ζ : Aˣ) : A))
      (orderOf (ζ : kˣ)) := by
  classical
  let u : Aˣ := primeToPRoot_unitsLift (p := p) (A := A) ζ
  have hpowA : ((u : A) ^ orderOf (ζ : kˣ)) = 1 := by
    simpa [u, primeToPRoot_unitLift_val] using
      primeToPRoot_powLift_pow_orderOf (p := p) (A := A) ζ
  refine ⟨?_, ?_⟩
  · rw [← map_pow, hpowA, map_one]
  · intro l hl
    have hlA : ((u : A) ^ l) = 1 := by
      apply IsFractionRing.injective A K
      simpa [u, map_pow] using hl
    have hlres :
        ((ζ : kˣ) ^ l : kˣ) = 1 := by
      apply Units.ext
      have hres := congrArg (IsLocalRing.residue A) hlA
      have hu_res :
          IsLocalRing.residue A (u : A) = ((ζ : kˣ) : k) := by
        change
          IsLocalRing.residue A
              ((primeToPRoot_unitsLift (p := p) (A := A) ζ : Aˣ) : A) =
            ((ζ : kˣ) : k)
        exact residue_primeToPRoot_unitLift (p := p) (A := A) ζ
      simpa [map_pow, hu_res] using hres
    exact orderOf_dvd_of_pow_eq_one hlres

/-- Helper for Exercise 18-18.3-2: every order coprime to `p` occurs as the order of a primitive
root in the fraction field of the Henselian DVR. -/
theorem exists_fractionField_primitiveRoot_of_coprime
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
    [CharP (IsLocalRing.ResidueField A) p]
    (m : ℕ) (hm_ne : m ≠ 0) (hm_coprime : Nat.Coprime p m) :
    ∃ ω : K, IsPrimitiveRoot ω m := by
  classical
  letI : NeZero m := ⟨hm_ne⟩
  have hm_not_dvd : ¬ p ∣ m :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hm_coprime
  letI : NeZero (m : IsLocalRing.ResidueField A) :=
    NeZero.of_not_dvd (R := IsLocalRing.ResidueField A) hm_not_dvd
  letI : IsSepClosed (IsLocalRing.ResidueField A) :=
    IsSepClosed.of_isAlgClosed (IsLocalRing.ResidueField A)
  letI : HasEnoughRootsOfUnity (IsLocalRing.ResidueField A) m := inferInstance
  obtain ⟨ζ, hζ⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (IsLocalRing.ResidueField A) m
  let ζu : (IsLocalRing.ResidueField A)ˣ := (hζ.isUnit hm_ne).unit
  have hζu : IsPrimitiveRoot ζu m := hζ.isUnit_unit hm_ne
  have hζu_order : orderOf ζu = m := hζu.eq_orderOf.symm
  have hζ_regular : IsPRegular p ζu := by
    change Nat.Coprime p (orderOf ζu)
    rw [hζu_order]
    exact hm_coprime
  let ξ : PrimeToPRoot p (IsLocalRing.ResidueField A) := ⟨ζu, hζ_regular⟩
  refine
    ⟨algebraMap A K ((primeToPRoot_unitsLift (p := p) (A := A) ξ : Aˣ) : A), ?_⟩
  simpa [ξ, hζu_order] using
    algebraMap_primeToPRoot_unitsLift_isPrimitiveRoot
      (p := p) (A := A) (K := K) ξ

/-- Helper for Exercise 18-18.3-2: the fraction field of the Henselian DVR contains primitive
roots of the orders of all `p`-regular group elements. -/
theorem exists_fractionField_primitiveRoot_of_isPRegular
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [Algebra A K] [IsFractionRing A K] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    (s : G) (hs : IsPRegular p s) :
    ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
  classical
  let m : ℕ := orderOf s
  have hm_ne : m ≠ 0 := by
    exact (orderOf_pos s).ne'
  exact
    exists_fractionField_primitiveRoot_of_coprime
      (p := p) (A := A) (K := K) m hm_ne (by simpa [m] using hs)

/-- Helper for Exercise 18-18.3-2: the canonical source-faithful coefficient-ring lift used in the
Brauer basis is obtained by forgetting the unit structure on `primeToPRoot_unitsLift`. -/
noncomputable def primeToPRoot_canonicalLift :
    PrimeToPRoot p k → A :=
  fun ζ ↦ ((primeToPRoot_unitsLift (p := p) (A := A) ζ : Aˣ) : A)

/-- Helper for Exercise 18-18.3-2: the canonical coefficient-ring lift reduces to the original
prime-to-`p` residue-field root. -/
@[simp] theorem residue_primeToPRoot_canonicalLift
    (ζ : PrimeToPRoot p k) :
    IsLocalRing.residue A (primeToPRoot_canonicalLift (p := p) (A := A) ζ) = (ζ : k) := by
  exact residue_primeToPRoot_unitLift (p := p) (A := A) ζ

/-- Helper for Exercise 18-18.3-2: once the full regular indicator is known to lie in the mapped
projective-character span, dividing by the prime-to-`p` unit recovers the scaled indicator. -/
theorem scaled_regular_indicator_mem_of_full_regular_indicator_mem
    (c : PRegularConjClass G p)
    (hfull :
      full_regular_indicator (p := p) (A := A) (K := K) (G := G) c ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G))) :
    scaled_regular_indicator (p := p) (A := A) (K := K) c ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
  rcases ordCompl_centralizerCard_isUnit (p := p) (A := A) (G := G) c with ⟨u, hu⟩
  have hscaled :
      ((↑u⁻¹ : A) •
          full_regular_indicator (p := p) (A := A) (K := K) (G := G) c) ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) :=
    Submodule.smul_mem _ _ hfull
  have hfull_eq :
      full_regular_indicator (p := p) (A := A) (K := K) (G := G) c =
        ((↑u : A) • scaled_regular_indicator (p := p) (A := A) (K := K) c) := by
    simpa [full_regular_indicator, hu] using
      (full_regular_indicator_eq_ordCompl_smul_scaled_regular_indicator
        (p := p) (A := A) (K := K) (G := G) c)
  have hrewrite :
      ((↑u⁻¹ : A) •
          full_regular_indicator (p := p) (A := A) (K := K) (G := G) c) =
        scaled_regular_indicator (p := p) (A := A) (K := K) c := by
    rw [hfull_eq]
    simp [smul_smul]
  -- Route correction: isolate the unit-rescaling step so the remaining blocker is exactly the
  -- source-faithful projective-envelope expansion of `full_regular_indicator`.
  exact hrewrite ▸ hscaled

/-- Helper for Exercise 18-18.3-2: the centralizer `p`-part of a regular class has nonzero image
in the characteristic-zero coefficient field. This is the denominator that gets inverted in the
source orthogonality computation. -/
theorem algebraMap_centralizerPPart_ne_zero
    (c : PRegularConjClass G p) :
    algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) ≠ 0 := by
  let g : G := Classical.choose (ConjClasses.mk_surjective c.1)
  have hg : ConjClasses.mk g = c.1 := Classical.choose_spec (ConjClasses.mk_surjective c.1)
  have hpos : 0 < ConjClasses.centralizerPPart p c.1 := by
    rw [← hg, ConjClasses.centralizerPPart_mk, Representation.centralizerPPart]
    exact pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _
  have hneK : ((ConjClasses.centralizerPPart p c.1 : ℕ) : K) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  simpa using hneK

/-- Helper for Exercise 18-18.3-2: in the coefficient field, the centralizer order of a regular
class splits as its `p`-part times its prime-to-`p` complement. -/
theorem centralizerCard_cast_eq_centralizerPPart_mul_ordCompl_cast
    (c : PRegularConjClass G p) :
    algebraMap A K (ConjClasses.centralizerCard c.1 : A) =
      algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) := by
  -- Rewrite Serre's class-level factorization and then map it into the characteristic-zero
  -- coefficient field.
  have hcard :
      ConjClasses.centralizerCard c.1 =
        ConjClasses.centralizerPPart p c.1 *
          ordCompl[p] (ConjClasses.centralizerCard c.1) :=
    ConjClasses.centralizerCard_eq_centralizerPPart_mul_ordCompl
      (p := p) (G := G) c.1
  simpa [map_mul] using congrArg (fun n : ℕ => algebraMap A K (n : A)) hcard

/-- Helper for Exercise 18-18.3-2: after casting to the coefficient field, the orbit-stabilizer
identity for a regular conjugacy class becomes `|c| * |C_G(s)| = |G|`. -/
theorem card_carrier_mul_centralizerCard_cast_eq_groupCard
    (c : PRegularConjClass G p) :
    (Nat.card c.1.carrier : K) *
        algebraMap A K (ConjClasses.centralizerCard c.1 : A) =
      (Fintype.card G : K) := by
  let g : G := Classical.choose (ConjClasses.mk_surjective c.1)
  have hg : ConjClasses.mk g = c.1 := Classical.choose_spec (ConjClasses.mk_surjective c.1)
  letI : Fintype (ConjClasses.mk g).carrier := Fintype.ofFinite (ConjClasses.mk g).carrier
  letI : Fintype (MulAction.stabilizer (ConjAct G) g) :=
    Fintype.ofFinite (MulAction.stabilizer (ConjAct G) g)
  have hcard_mul_nat :
      Nat.card c.1.carrier * ConjClasses.centralizerCard c.1 = Fintype.card G := by
    calc
      Nat.card c.1.carrier * ConjClasses.centralizerCard c.1 =
          Fintype.card (ConjClasses.mk g).carrier *
            Nat.card (Subgroup.centralizer ({g} : Set G)) := by
              simp [hg, ConjClasses.centralizerCard, g]
      _ =
          Fintype.card (ConjClasses.mk g).carrier *
            Nat.card (MulAction.stabilizer (ConjAct G) g) := by
              rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
      _ = Fintype.card G := by
            simpa [ConjAct.orbit_eq_carrier_conjClasses] using
              (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g)
  -- Move the natural-number identity directly into `K`, keeping the centralizer-card cast explicit.
  calc
    (Nat.card c.1.carrier : K) *
        algebraMap A K (ConjClasses.centralizerCard c.1 : A) =
      (Nat.card c.1.carrier : K) * (ConjClasses.centralizerCard c.1 : K) := by
        simp
    _ = (Fintype.card G : K) := by
        exact_mod_cast hcard_mul_nat

/-- Helper for Exercise 18-18.3-2: the class-size factor and the prime-to-`p` part of the
centralizer order combine to the inverse of the centralizer `p`-part. This is the scalar identity
used after collapsing Serre's orthogonality sum to one conjugacy class. -/
theorem class_card_mul_ordCompl_eq_card_mul_centralizerPPart_inv
    (c : PRegularConjClass G p) :
    (Nat.card c.1.carrier : K) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) =
      (Fintype.card G : K) *
        (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ := by
  let x : K := algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)
  let y : K := algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)
  have hmul :
      (Nat.card c.1.carrier : K) * (x * y) =
        (Fintype.card G : K) := by
    -- First rewrite the centralizer factorization in `K`, then insert the orbit-stabilizer cast.
    calc
      (Nat.card c.1.carrier : K) * (x * y) =
        (Nat.card c.1.carrier : K) *
          algebraMap A K (ConjClasses.centralizerCard c.1 : A) := by
            simp [x, y,
              centralizerCard_cast_eq_centralizerPPart_mul_ordCompl_cast
                (p := p) (A := A) (K := K) (G := G) c]
      _ = (Fintype.card G : K) := by
            exact
              card_carrier_mul_centralizerCard_cast_eq_groupCard
                (p := p) (A := A) (K := K) (G := G) c
  have hx_ne : x ≠ 0 := by
    -- The `p`-part is a positive power of `p`, so its image stays nonzero in the fraction field.
    exact algebraMap_centralizerPPart_ne_zero (p := p) (A := A) (K := K) (G := G) c
  calc
    (Nat.card c.1.carrier : K) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) =
      (Nat.card c.1.carrier : K) * y := by
        simp [y]
    _ =
      ((Nat.card c.1.carrier : K) * y) * (x * x⁻¹) := by
        rw [mul_inv_cancel₀ hx_ne, mul_one]
    _ = ((Nat.card c.1.carrier : K) * (x * y)) * x⁻¹ := by
        ring
    _ = (Fintype.card G : K) * x⁻¹ := by
          rw [hmul]
    _ = (Fintype.card G : K) *
        (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ := by
          simp [x]

/-- Helper for Exercise 18-18.3-2: Serre's pairing with the prime-to-`p` indicator at `c`
collapses to the inverse-class regular value scaled by the inverse centralizer `p`-part. This is
the class-sum half of the orthogonality argument for part `(a)`. -/
theorem projectiveEnvelope_pairing_primeToP_indicator_eq_inverse_regularRestriction
    (i : FiniteProjectiveGroupAlgebraModule k G)
    (c : PRegularConjClass G p) :
    (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            (if hs : IsPRegular p s then
              algebraMap A K
                ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                  (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
            else 0) =
      (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
        regularRestriction (p := p)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [i]ₚ₀)
          (inversePRegularConjClass (p := p) c) := by
  classical
  let Φ :=
    regularRestriction (p := p)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [i]ₚ₀)
  let a : ConjClasses G → K := fun d ↦
    if h : d = c.1 then
      Φ (inversePRegularConjClass (p := p) c) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)
    else 0
  have hsum :
      ∑ s : G,
        (if hs : IsPRegular p (s⁻¹) then
          Φ (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
        else 0) *
          (if hs : IsPRegular p s then
            algebraMap A K
              ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
          else 0) =
        ∑ s : G, a (ConjClasses.mk s) := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    by_cases hmk : ConjClasses.mk s = c.1
    · have hs_reg : IsPRegular p s := by
        exact c.2 s (by simpa [ConjClasses.mem_carrier_iff_mk_eq] using hmk)
      have hs_inv : IsPRegular p (s⁻¹) := by
        simpa [IsPRegular, orderOf_inv] using hs_reg
      have hInvClass :
          PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs_inv⟩ =
            inversePRegularConjClass (p := p) c := by
        apply Subtype.ext
        simpa [ConjClasses.inv_mk] using congrArg Inv.inv hmk
      -- The source sum only receives a contribution from the supporting regular class.
      rw [dif_pos hs_inv, dif_pos hs_reg,
        primeToP_regular_indicator_ofSubtype_eq_ordCompl
          (p := p) (A := A) (G := G) c hs_reg hmk]
      simp [a, hmk, hInvClass]
    · by_cases hs_reg : IsPRegular p s
      · -- Outside the supporting class, the point mass kills the second factor.
        rw [dif_pos hs_reg,
          primeToP_regular_indicator_ofSubtype_eq_zero_of_mk_ne
            (p := p) (A := A) (G := G) c hs_reg hmk]
        simp [a, hmk]
      · simp [a, hmk, hs_reg]
  rw [hsum, sum_over_group_eq_sum_over_conjClasses (G := G) (K := K) a]
  rw [Finset.sum_eq_single c.1]
  · rw [show a c.1 = Φ (inversePRegularConjClass (p := p) c) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) from dif_pos rfl]
    calc
      (Fintype.card G : K)⁻¹ *
          ((Nat.card c.1.carrier : K) *
            (Φ (inversePRegularConjClass (p := p) c) *
              algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)))
          =
        (Fintype.card G : K)⁻¹ *
          (((Nat.card c.1.carrier : K) *
              algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)) *
            Φ (inversePRegularConjClass (p := p) c)) := by
              ring
      _ =
        (Fintype.card G : K)⁻¹ *
          (((Fintype.card G : K) *
              (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹) *
            Φ (inversePRegularConjClass (p := p) c)) := by
              rw [class_card_mul_ordCompl_eq_card_mul_centralizerPPart_inv
                (p := p) (A := A) (K := K) (G := G) c]
      _ =
        (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
          Φ (inversePRegularConjClass (p := p) c) := by
            have hcardG_ne : (Fintype.card G : K) ≠ 0 :=
              Nat.cast_ne_zero.mpr Fintype.card_ne_zero
            calc
              (Fintype.card G : K)⁻¹ *
                  (((Fintype.card G : K) *
                      (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹) *
                    Φ (inversePRegularConjClass (p := p) c))
                  =
                (((Fintype.card G : K)⁻¹ * (Fintype.card G : K)) *
                    (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹) *
                  Φ (inversePRegularConjClass (p := p) c) := by
                    ring
              _ =
                (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
                  Φ (inversePRegularConjClass (p := p) c) := by
                    simp [hcardG_ne]
  · intro d hd hdc
    simp [a, hdc]
  · intro hc
    simp at hc

/-- Helper for Exercise 18-18.3-2: evaluating the Brauer-basis expansion of Serre's prime-to-`p`
indicator at a regular class reads the point mass as the sum of its basis coefficients times the
corresponding basis values. -/
theorem primeToP_regular_indicator_apply_eq_sum_basis_repr
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (c c' : PRegularConjClass G p) :
    let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
    let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
    let bA :=
      exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
        (p := p) (A := A) liftA hliftA
        (residue_primeToPRoot_canonicalLift (p := p) (A := A))
        π hπ_pairwise hπ_complete
    (primeToP_regular_indicator (p := p) (A := A) (G := G) c) c' =
      ∑ j, ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) * bA j c' := by
  classical
  dsimp
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  have hsum_repr :=
    congrFun
      (bA.sum_repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c))
      c'
  -- Evaluate the basis expansion at `c'` and rewrite the scalar action pointwise as
  -- multiplication in `A`.
  simpa [bA, Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc] using hsum_repr.symm
end ProjectiveCharacterCriterion

end Representation
