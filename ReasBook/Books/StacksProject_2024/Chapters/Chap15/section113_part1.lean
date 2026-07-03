import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_113_1 (from Chap15) -/
open Ideal IsLocalRing
open scoped Pointwise

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [IsGalois K L]

local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A

private local instance integralClosureMulSemiringAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

/-- Any maximal ideal of the integral closure of the local ring `A` lies over `maximalIdeal A`. -/
private instance liesOver_maximalIdeal_of_isMaximal
    (m : Ideal B) [m.IsMaximal] : m.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

/- Domain-style sampling for Lemma 15.113.1:
- primary domain: Galois conjugacy of prime and maximal ideals in the integral closure of a local
  integrally closed domain;
- sampled owner declarations:
  `exists_gal_smul_eq_of_liesOver`,
  `MulAction.stabilizer`,
  `Ideal.LiesOver`,
  `residueField_normal_of_liesOver`;
- best owner abstraction: the chapter owner theorem `exists_gal_smul_eq_of_liesOver`, whose
  maximal-ideal specialization is exactly the source-facing local-ring statement here;
- primitive data: the integral closure `B = integralClosure A L`, two maximal ideals `m, m' : Ideal B`,
  and the canonical `LiesOver (maximalIdeal A)` facts supplied by locality;
- derived API: conjugacy of maximal ideals and the downstream residue-field transport statements in
  later files.

Source/core/bridge triage:
- `source-facing`: the local-ring maximal-ideal transitivity statement in Lemma 15.113.1;
- `core/canonical`: `exists_gal_smul_eq_of_liesOver`;
- `bridge/view`: the canonical specialization from maximal ideals of `B` to primes lying over
  `maximalIdeal A`. -/

-- Proof sketch: maximal ideals of `B` lie over `maximalIdeal A`, so this is the
-- `p = maximalIdeal A` specialization of Lemma `15.111.10 (1)`.
/-- Lemma 15.113.1: for `B = integralClosure A L`, the canonical action of `Gal(L/K)` on `B`
is transitive on the maximal ideals of `B`. -/
theorem exists_gal_smul_eq_of_isMaximal
    (m m' : Ideal B) (hm : m.IsMaximal) (hm' : m'.IsMaximal) :
    ∃ σ : Gal(L/K), σ • m = m' := by
  letI : m.IsMaximal := hm
  letI : m'.IsMaximal := hm'
  exact exists_gal_smul_eq_of_liesOver p m m'

end

/-! ### Lemma_15_113_2 (from Chap15) -/
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

/-! ### Definition_15_113_3 (from Chap15) -/
open scoped Pointwise

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [Algebra.IsAlgebraic K L]

local notation "B" => integralClosure A L

/- Domain-style sampling for Definition 15.113.3:
- primary domain: ramification theory of finite Galois extensions, specifically the subgroup
  owners attached to an ideal of the integral closure;
- sampled owner declarations:
  `MulAction.stabilizer`,
  `Ideal.inertia`,
  `Ideal.inertia_le_stabilizer`,
  `IsIntegralClosure.MulSemiringAction`;
- best owner abstraction: the subgroup-valued owners `MulAction.stabilizer` and `Ideal.inertia`;
- primitive data: an ideal `m : Ideal B`, together with the induced `Gal(L/K)`-action on `B`;
- derived API: the maximal-ideal specialization used later in the chapter, plus the decomposition
  and inertia fields and the residue-field actions built from it.

Layer triage:
- `source-facing`: naming the decomposition group and inertia group attached to a maximal ideal;
- `core/canonical`: `MulAction.stabilizer Gal(L/K) m` and `m.inertia Gal(L/K)`;
- `bridge/view`: the specialization from an arbitrary ideal to the maximal-ideal situation in the
  textbook.

This file should therefore recall those subgroup owners directly, with no parallel local wrapper
API. -/

local instance integralClosureMulSemiringAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

variable (m : Ideal B)

/- Definition 15.113.3 (1): for an ideal `m` of `B = integralClosure A L`, the canonical
decomposition-group owner is the stabilizer of `m` in `Gal(L / K)`. For a maximal ideal, this is
the textbook decomposition group. -/
set_option linter.hashCommand false in
#check (MulAction.stabilizer Gal(L/K) m)

/- Definition 15.113.3 (2): for an ideal `m` of `B`, the canonical inertia-group owner is the
ideal-theoretic inertia subgroup of `Gal(L / K)` attached to `m`. For a maximal ideal, this is the
textbook inertia group. -/
set_option linter.hashCommand false in
#check (m.inertia Gal(L/K))

end

/-! ### Lemma_15_113_4 (from Chap15) -/
open Ideal IsLocalRing
open scoped Pointwise

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [IsGalois K L]

local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A
local notation "κA" => Ideal.ResidueField p

/-- The Galois group acts on the integral closure through the induced automorphisms of the ambient
field. -/
private local instance integralClosureMulSemiringAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

private theorem integralClosure_smulCommClass :
    SMulCommClass Gal(L/K) A B := sorry

attribute [local instance] integralClosure_smulCommClass

private theorem integralClosure_isInvariant :
    Algebra.IsInvariant A B Gal(L/K) := sorry

attribute [local instance] integralClosure_isInvariant

/- Domain-style sampling for Lemma 15.113.4:
- primary domain: residue-field extensions and decomposition groups for maximal ideals of the
  integral closure in a Galois extension of fraction fields;
- sampled owner declarations:
  `Ideal.LiesOver`,
  `Ideal.ResidueField.map`,
  `residueField_normal_of_liesOver`,
  `stabilizerHom_surjective_of_liesOver`,
  `IsFractionRing.stabilizerHom`;
- best owner abstraction: the canonical owner map `IsFractionRing.stabilizerHom`, with the
  source-facing prime-ideal surjectivity theorem `stabilizerHom_surjective_of_liesOver`
  supplying its maximal-ideal specialization once the local integral-closure residue-field bridge
  is in place at the weaker local integrally closed-domain layer;
- primitive data: a maximal ideal `m : Ideal B`;
- derived API: the induced residue-field extension `κ(m) / κA`, its normality, and the canonical
  decomposition-group action on the residue field. -/

/- Source/core/bridge triage:
- `source-facing`: the five clauses of Lemma 15.113.4 for maximal ideals of `B`;
- `core/canonical`: `Ideal.LiesOver`, `residueField_normal_of_liesOver`, and
  `IsFractionRing.stabilizerHom` together with the prime-ideal surjectivity theorem from
  Lemma `15.111.10` and its maximal-ideal specialization;
- `bridge/view`: the maximal-ideal specialization of the residue-field bridge instances and
  source-facing theorems from Lemma `15.111.10`. -/

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {L : Type v} [Field L] [Algebra A L]

/- Any maximal ideal of the integral closure of the local ring `A` lies over `maximalIdeal A`. -/
private instance liesOver_maximalIdeal_of_isMaximal
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    m.LiesOver (maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

end

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

local notation "D" => MulAction.stabilizer Gal(L/K) m
local notation "ρ" => IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField

-- Proof sketch: this is the `p = maximalIdeal A`, `q = m` specialization of the prime-ideal
-- normality theorem from Lemma `15.111.10`.
/- Lemma 15.113.4 (1): for a maximal ideal `m` of `integralClosure A L`, the residue field
extension `κ(m) / κA` is normal. This is exactly the `p = maximalIdeal A`, `q = m`
specialization of `residueField_normal_of_liesOver`. -/
#check (residueField_normal_of_liesOver p m : Normal κA m.ResidueField)

/- Lemma 15.113.4 (2): the decomposition group `D = stabilizer Gal(L / K) m` surjects onto
`Aut(κ(m) / κA)`. This is exactly the `p = maximalIdeal A`, `q = m` specialization of the
source-facing prime-ideal surjectivity theorem from Lemma `15.111.10`. -/
#check (IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField :
  D →* (m.ResidueField ≃ₐ[κA] m.ResidueField))
#check (stabilizerHom_surjective_of_liesOver p m : Function.Surjective ρ)

-- Proof sketch: maximal ideals of `B` are conjugate by Lemma `15.113.1`; transport the residue
-- field extension along the induced algebra equivalence and use invariance of separability under
-- base-field algebra equivalence.
/-- Lemma 15.113.4 (3): for any two maximal ideals `m` and `m'` of `integralClosure A L`, the
residue field extensions over `κA` are simultaneously separable. This is the formalized
`some (equivalently all)` clause. -/
theorem residueField_separable_iff_of_isMaximal
    (m' : Ideal (integralClosure A L)) [m'.IsMaximal] :
    Algebra.IsSeparable κA m.ResidueField ↔ Algebra.IsSeparable κA m'.ResidueField := sorry

-- Proof sketch: combine `residueField_normal_of_liesOver p m` with the assumed separability of
-- `κ(m) / κA`; the canonical field-theoretic owner `isGalois_iff` packages exactly this
-- conjunction.
/-- Lemma 15.113.4 (4): if `κ(m) / κA` is separable, then it is Galois. -/
theorem residueField_isGalois_of_separable
    (hsep : Algebra.IsSeparable κA m.ResidueField) :
    IsGalois κA m.ResidueField := by
  exact isGalois_iff.mpr ⟨hsep, residueField_normal_of_liesOver p m⟩

/- Lemma 15.113.4 (5): after clause `(4)`, the target group may be read as
`Gal(κ(m) / κA)`, but the canonical map and its surjectivity statement are exactly those of
clause `(2)`. -/
#check (IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField :
  D →* Gal(m.ResidueField/κA))
#check (stabilizerHom_surjective_of_liesOver p m : Function.Surjective ρ)

end

/-! ### Lemma_15_113_5 (from Chap15) -/
open Ideal IsLocalRing
open scoped Pointwise

universe u v

noncomputable section

section

/- Domain-style sampling for Lemma 15.113.5:
- primary domain: wild and tame inertia for maximal ideals in finite Galois extensions of
  fraction fields of discrete valuation rings;
- sampled owner declarations:
  `Ideal.inertia`,
  `Ideal.inertia_le_stabilizer`,
  `MulAction.stabilizer`,
  `QuotientGroup.quotientMulEquivOfEq`,
  `QuotientGroup.quotientKerEquivOfSurjective`;
- best owner abstraction: the core quotient owner is
  `tameInertiaQuotient K m = (m.inertia Gal(L / K)) ⧸ P`, with `P` the wild inertia subgroup
  inside inertia, and the source-facing owner of the lemma is the canonical quotient equivalence
  `tameInertiaQuotientMulEquiv K m`, from which the induced tame inertia character
  `tameInertiaCharacter K m` is derived;
- primitive data: the ideal-theoretic inertia owners `m.inertia Gal(L / K)` and
  `Ideal.inertia Gal(L / K) (m ^ 2)`, together with the inclusion of the latter into the former;
- derived API: the tame inertia quotient, the canonical equivalence with `μ_e(κ(m))`, and the
  induced surjective character with kernel the wild inertia subgroup.

Layer triage:
- `source-facing`: `wildInertiaSubgroup`, `tameInertiaQuotient`, the canonical quotient
  equivalence `tameInertiaQuotientMulEquiv`, and the induced tame inertia character
  `tameInertiaCharacter`;
- `core/canonical`: `Ideal.inertia`, `MulAction.stabilizer`, subgroup normality, quotient groups,
  and quotient-by-kernel equivalences;
- `bridge/view`: the inclusion `P ≤ I` and the passage from the quotient equivalence
  `I_t ≃ μ_e(κ(m))` to the map `I → μ_e(κ(m))`. -/

variable {A : Type u} [CommRing A] [IsDomain A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [IsGalois K L]

local notation "B" => integralClosure A L

/-- The wild inertia subgroup `P`, consisting of the Galois automorphisms acting trivially modulo
`m²`. It will be viewed source-faithfully below as a subgroup of both the inertia and
decomposition groups. -/
abbrev wildInertiaSubgroup (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L] [IsGalois K L]
    (m : Ideal (integralClosure A L)) : Subgroup Gal(L/K) :=
  Ideal.inertia Gal(L/K) (m ^ 2)

local instance integralClosureMulSemiringAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

variable (m : Ideal (integralClosure A L))

local notation "D" => MulAction.stabilizer Gal(L/K) m
local notation "I" => m.inertia Gal(L/K)

/-- The wild inertia subgroup lies inside the inertia group. -/
theorem wildInertiaSubgroup_le_inertia (m : Ideal B) :
    wildInertiaSubgroup K m ≤ m.inertia Gal(L/K) := sorry

/-- The wild inertia subgroup lies inside the decomposition group. -/
theorem wildInertiaSubgroup_le_decompositionGroup (m : Ideal B) :
    wildInertiaSubgroup K m ≤ MulAction.stabilizer Gal(L/K) m :=
  (wildInertiaSubgroup_le_inertia m).trans (Ideal.inertia_le_stabilizer m)

/-- The tame inertia quotient `I_t = I / P` attached to `m`. -/
abbrev tameInertiaQuotient (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L] [IsGalois K L]
    (m : Ideal (integralClosure A L)) :=
  (m.inertia Gal(L/K)) ⧸ (wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L/K))

section RootsOfUnity

variable {R : Type*} [CommMonoid R] {m n : ℕ}

/-- Powering by `n / m` sends `μ_n(R)` to `μ_m(R)` whenever `m ∣ n`. -/
def rootsOfUnityPowMap (h : m ∣ n) :
    rootsOfUnity n R →* rootsOfUnity m R where
  toFun ζ :=
    ⟨(ζ : Units R) ^ (n / m), by
      rw [mem_rootsOfUnity]
      calc
        ((ζ : Units R) ^ (n / m)) ^ m = (ζ : Units R) ^ ((n / m) * m) := by
          rw [pow_mul]
        _ = (ζ : Units R) ^ (m * (n / m)) := by
          rw [Nat.mul_comm]
        _ = (ζ : Units R) ^ n := by
          rw [Nat.mul_div_cancel' h]
        _ = 1 := (mem_rootsOfUnity _ _).mp ζ.prop⟩
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_pow]

@[simp] theorem rootsOfUnityPowMap_coe_apply
    (h : m ∣ n) (ζ : rootsOfUnity n R) :
    (rootsOfUnityPowMap h ζ : Units R) = (ζ : Units R) ^ (n / m) :=
  rfl

end RootsOfUnity

section RootsOfUnityCard

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]

/-- The order of the finite cyclic group `μ_n(R)` divides `n`. -/
theorem natCard_rootsOfUnity_dvd :
    Nat.card (rootsOfUnity n R) ∣ n := by
  rw [← IsCyclic.exponent_eq_card (α := rootsOfUnity n R)]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one fun ζ ↦
    OneMemClass.coe_eq_one.mp ζ.prop

end RootsOfUnityCard

-- Proof sketch: unfold `wildInertiaSubgroup`; by definition it is the inertia subgroup of the
-- square ideal `m ^ 2` for the action of the decomposition group `D` on the integral closure.
/-- An element of the Galois group lies in the wild inertia subgroup exactly when it acts
trivially on `B / m²`, equivalently when `σ(x) - x ∈ m²` for every `x ∈ B`. -/
theorem mem_wildInertiaSubgroup_iff
    (m : Ideal B)
    (σ : Gal(L/K)) :
    σ ∈ wildInertiaSubgroup K m ↔
      ∀ x : B, σ • x - x ∈ m ^ 2 := sorry

/-- The wild inertia subgroup is a normal subgroup of the decomposition group. -/
theorem wildInertiaSubgroup_normal_in_decompositionGroup :
    Subgroup.Normal
      ((wildInertiaSubgroup K m).subgroupOf D) := sorry

/-- The wild inertia subgroup is normal inside the inertia group, so the tame inertia quotient is
well defined. -/
instance wildInertiaSubgroup_normalInst :
    Subgroup.Normal
      ((wildInertiaSubgroup K m).subgroupOf I) := sorry

section Tame

variable [IsDiscreteValuationRing A] [FiniteDimensional K L] [m.IsMaximal]
variable (K)

local notation "p" => maximalIdeal A
local notation "e" => Ideal.ramificationIdxIn p B

-- Proof sketch: construct the tame inertia homomorphism using the action on a uniformizer of the
-- localization `B_m`, identify its kernel with `P`, and prove surjectivity onto `μ_e(κ(m))`.
private theorem exists_tameInertiaCharacterHom (m : Ideal B) [m.IsMaximal] :
    ∃ θ : m.inertia Gal(L/K) →* rootsOfUnity e m.ResidueField,
      θ.ker = (wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L/K)) ∧
        Function.Surjective θ := sorry

private theorem existsUnique_tameInertiaQuotientMulEquiv
    (m : Ideal B) [m.IsMaximal] :
    ∃! eθ : tameInertiaQuotient K m ≃* rootsOfUnity e m.ResidueField,
      ∃ θ : m.inertia Gal(L/K) →* rootsOfUnity e m.ResidueField,
        θ.ker = (wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L/K)) ∧
          Function.Surjective θ ∧
          ∀ σ : m.inertia Gal(L/K), eθ (QuotientGroup.mk σ) = θ σ := by
  rcases exists_tameInertiaCharacterHom K m with ⟨θ, hker, hsurj⟩
  let eθ : tameInertiaQuotient K m ≃* rootsOfUnity e m.ResidueField :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hsurj)
  refine ⟨eθ, ?_, ?_⟩
  · refine ⟨θ, hker, hsurj, ?_⟩
    intro σ
    change
      (QuotientGroup.quotientKerEquivOfSurjective θ hsurj)
          ((QuotientGroup.quotientMulEquivOfEq hker.symm) (QuotientGroup.mk σ)) =
        θ σ
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  · intro eθ' heθ'
    sorry

/-- Lemma 15.113.5: the tame inertia quotient `I_t = I / P` is canonically identified with the
group `μ_e(κ(m))` of `e`th roots of unity in the residue field, where
`e = Ideal.ramificationIdxIn (maximalIdeal A) B`. -/
noncomputable def tameInertiaQuotientMulEquiv (m : Ideal B) [m.IsMaximal] :
    tameInertiaQuotient K m ≃* rootsOfUnity e m.ResidueField :=
  Classical.choose (ExistsUnique.exists (existsUnique_tameInertiaQuotientMulEquiv K m))

/-- Definition 15.113.6: the tame inertia character is the surjective map induced by the
canonical quotient equivalence from Lemma 15.113.5. -/
noncomputable def tameInertiaCharacter (m : Ideal B) [m.IsMaximal] :
    m.inertia Gal(L/K) →* rootsOfUnity e m.ResidueField :=
  (tameInertiaQuotientMulEquiv K m).toMonoidHom.comp
    (QuotientGroup.mk' ((wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L/K))))

/-- The canonical quotient equivalence and the tame inertia character agree on quotient classes. -/
theorem tameInertiaQuotientMulEquiv_mk
    (m : Ideal B) [m.IsMaximal]
    (σ : m.inertia Gal(L/K)) :
    tameInertiaQuotientMulEquiv K m (QuotientGroup.mk σ) = tameInertiaCharacter K m σ := rfl

/-- The tame inertia character has kernel equal to the wild inertia subgroup inside inertia. -/
theorem tameInertiaCharacter_ker
    (m : Ideal B) [m.IsMaximal] :
    (tameInertiaCharacter K m).ker =
      (wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L/K)) := by
  let P : Subgroup (m.inertia Gal(L/K)) :=
    (wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L/K))
  let eθ : tameInertiaQuotient K m ≃* rootsOfUnity e m.ResidueField :=
    tameInertiaQuotientMulEquiv K m
  calc
    (tameInertiaCharacter K m).ker = (QuotientGroup.mk' P).ker := by
      change (((eθ : tameInertiaQuotient K m →* rootsOfUnity e m.ResidueField).comp
          (QuotientGroup.mk' P)).ker = (QuotientGroup.mk' P).ker)
      exact MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' P) eθ
    _ = P := QuotientGroup.ker_mk' P
    _ = (wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L/K)) := rfl

/-- The tame inertia character is surjective onto `μ_e(κ(m))`. -/
theorem tameInertiaCharacter_surjective
    (m : Ideal B) [m.IsMaximal] :
    Function.Surjective (tameInertiaCharacter K m) := by
  intro ζ
  obtain ⟨σ, rfl⟩ := (tameInertiaQuotientMulEquiv K m).surjective ζ
  obtain ⟨τ, rfl⟩ :=
    QuotientGroup.mk'_surjective
      ((wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L/K))) σ
  exact ⟨τ, rfl⟩

end Tame

end

/-! ### Definition_15_113_6 (from Chap15) -/
universe u v

section

/- Domain-style sampling for Definition 15.113.6:
- primary domain: wild and tame inertia attached to a maximal ideal in a finite Galois extension
  of fraction fields of discrete valuation rings;
- sampled owner declarations:
  `Ideal.inertia`,
  `wildInertiaSubgroup`,
  `tameInertiaQuotient`,
  `tameInertiaQuotientMulEquiv`;
- best owner abstraction: the source-facing owners introduced in `Lemma_15_113_5`, built from the
  canonical inertia subgroup `m.inertia Gal(L / K)` and its wild inertia subgroup;
- primitive data: the inertia subgroup `m.inertia Gal(L / K)` and the wild inertia subgroup
  `wildInertiaSubgroup K m`;
- derived API: the tame inertia quotient, the canonical quotient equivalence with
  `μ_e(κ(m))`, and the induced tame inertia character.

Layer triage:
- `source-facing`: `wildInertiaSubgroup`, `tameInertiaQuotient`,
  `tameInertiaQuotientMulEquiv`, and `tameInertiaCharacter`;
- `core/canonical`: `Ideal.inertia`, subgroup inclusions, and quotient-group constructions;
- `bridge/view`: the passage from the quotient equivalence `I_t ≃ μ_e(κ(m))` to the induced
  character `I → μ_e(κ(m))`.

This file should therefore remain a pure recall layer, reusing the Chapter 15 owners directly and
introducing no parallel local wrappers. -/

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

/- Definition 15.113.6 (1): with the notation of Lemma 15.113.5, the wild inertia group of `m`
is the canonical subgroup `wildInertiaSubgroup K m` of `Gal(L / K)`, lying inside the
decomposition group and hence inside the inertia group by the companion inclusion theorems. -/
set_option linter.hashCommand false in
#check (wildInertiaSubgroup K m)

/- Definition 15.113.6 (2): with the notation of Lemma 15.113.5, the tame inertia group of `m`
is the canonical quotient
`tameInertiaQuotient K m = (m.inertia Gal(L / K)) ⧸
  (wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L / K))`. -/
set_option linter.hashCommand false in
#check (tameInertiaQuotient K m)

/- Definition 15.113.6 (3): with the notation of Lemma 15.113.5, the canonical quotient
equivalence `I_t ≃ μ_e(κ(m))` is `tameInertiaQuotientMulEquiv K m`, and the induced tame inertia
character `I → μ_e(κ(m))` is `tameInertiaCharacter K m`. -/
set_option linter.hashCommand false in
#check (tameInertiaQuotientMulEquiv K m)
set_option linter.hashCommand false in
#check (tameInertiaCharacter K m)

end

/-! ### Lemma_15_113_7 (from Chap15) -/
open Ideal IsLocalRing
open scoped Pointwise

universe u v

noncomputable section

section

/- Domain-style sampling for Lemma 15.113.7:
- primary domain: tame inertia characters and the decomposition-group action on the residue field
  in a finite Galois extension over a discrete valuation ring;
- sampled owner declarations:
  `tameInertiaCharacter`,
  `tameInertiaCharacter_ker`,
  `tameInertiaCharacter_surjective`,
  `restrictRootsOfUnity`,
  `MulEquiv.restrictRootsOfUnity`,
  `Ideal.inertia`,
  `MulAction.stabilizer`,
  `IsFractionRing.stabilizerHom`;
- best owner abstraction: the source-facing character owner is already the canonical
  `tameInertiaCharacter K m`, while the genuinely new content of this file is the conjugation
  compatibility with the canonical decomposition-group action on `μ_e(κ(m))` induced from
  `IsFractionRing.stabilizerHom` by `MulEquiv.restrictRootsOfUnity`;
- primitive data: the ideal-theoretic inertia and decomposition groups attached to `m`, together
  with the maximal-ideal specialization of the residue-field action
  `IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField`;
- derived API: the compatibility predicate for a tame inertia character and the existential
  source-facing reformulation obtained by applying it to `tameInertiaCharacter K m`.

Layer triage:
- `source-facing`: the conjugation-compatibility theorem for the canonical tame inertia character
  `tameInertiaCharacter K m`, which is the source character already fixed in Lemma `15.113.5`;
- `core/canonical`: `tameInertiaCharacter K m`, `MulAction.stabilizer Gal(L/K) m`, and
  `m.inertia Gal(L/K)`, together with
  `IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField` and its induced
  `MulEquiv.restrictRootsOfUnity` action on `rootsOfUnity e m.ResidueField`;
- `bridge/view`: the existential source reformulation obtained by packaging the canonical owner
  theorem together with the already established kernel and surjectivity facts from
  Lemma `15.113.5`.

Primitive-vs-derived split:
- primitive data in this file: only the residue-field action of the decomposition group and the
  induced roots-of-unity action of the decomposition group and the compatibility relation with
  conjugation on inertia;
- derived API imported from `15.113.5`: the kernel and surjectivity facts for the canonical tame
  inertia character.

The refinement therefore makes the source-facing numbered item the direct compatibility theorem
for the canonical owner `tameInertiaCharacter K m`, while keeping the existential packaging only
as a derived companion obtained from Lemma `15.113.5`; the compatibility itself is stated directly
against the canonical roots-of-unity action induced from `IsFractionRing.stabilizerHom`. -/

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A
local notation "κA" => Ideal.ResidueField p

local instance integralClosure_mulSemiringAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

private theorem integralClosure_smulCommClass :
    SMulCommClass Gal(L/K) A B := sorry

attribute [local instance] integralClosure_smulCommClass

private theorem integralClosure_isInvariant :
    Algebra.IsInvariant A B Gal(L/K) := sorry

attribute [local instance] integralClosure_isInvariant

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

local notation "D" => MulAction.stabilizer Gal(L/K) m
local notation "I" => m.inertia Gal(L/K)
local notation "e" => Ideal.ramificationIdxIn p B

private local instance liesOver_maximalIdeal_of_isMaximal : m.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

local instance residueFieldAlgebra :
    Algebra κA m.ResidueField :=
  inferInstance

local notation "ρ" => IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField

/-- Conjugating an inertia element by an element of the decomposition group stays in the inertia
subgroup. -/
-- Proof sketch: the inertia subgroup is normal inside the stabilizer of `m`; apply normality to
-- the subgroup inclusion `I ≤ D` and then rewrite the resulting conjugate back in `Gal(L / K)`.
theorem inertia_conj_mem
    (τ : D) (σ : I) :
    τ.1 * σ.1 * τ.1⁻¹ ∈ I := sorry

/-- Conjugation by the decomposition group induces an endomorphism of the inertia subgroup. -/
abbrev inertiaConj (τ : D) (σ : I) : I :=
  ⟨τ.1 * σ.1 * τ.1⁻¹, inertia_conj_mem m τ σ⟩

-- Proof sketch: this is the source content of Lemma `15.113.7`, stated directly for the canonical
-- tame inertia character already fixed in Lemma `15.113.5`.
/-- Lemma 15.113.7: the canonical tame inertia character from Lemma `15.113.5` is compatible with
conjugation by the decomposition group. -/
theorem tameInertiaCharacter_conj_compatible
    (τ : D) (σ : I) :
    tameInertiaCharacter K m (inertiaConj m τ σ) =
      ((ρ τ).toMulEquiv.restrictRootsOfUnity e) (tameInertiaCharacter K m σ) :=
  sorry

-- Proof sketch: package the canonical owner theorem with the kernel and surjectivity statements
-- already proved in Lemma `15.113.5`.
/-- Companion existential reformulation of Lemma `15.113.7`: the canonical tame inertia character
from Lemma `15.113.5` provides a witness with the expected kernel, surjectivity, and conjugation
compatibility properties. -/
theorem exists_tameInertiaCharacter_conj_compatible_companion :
    ∃ θ : I →* rootsOfUnity e m.ResidueField,
      θ.ker = (wildInertiaSubgroup K m).subgroupOf I ∧
        Function.Surjective θ ∧
        ∀ (τ : D) (σ : I),
          θ (inertiaConj m τ σ) =
            ((ρ τ).toMulEquiv.restrictRootsOfUnity e) (θ σ) := by
  refine ⟨tameInertiaCharacter K m, ?_, tameInertiaCharacter_surjective K m,
    fun τ σ ↦ tameInertiaCharacter_conj_compatible m τ σ⟩
  simpa using tameInertiaCharacter_ker K m

end

/-! ### Lemma_15_113_8 (from Chap15) -/
open scoped Pointwise
open IntermediateField
open Algebra

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [Algebra.IsAlgebraic K L]

local notation "G" => Gal(L / K)
local notation "B" => integralClosure A L
local notation "B[" H "]" => FixedPoints.subalgebra A B H
local notation "L[" H "]" => IntermediateField.fixedField H

/- Domain-style sampling for Lemma 15.113.8:
- primary domain: integral closures and fixed objects for subgroup actions of `Gal(L / K)` on the
  integral closure `B = integralClosure A L`;
- sampled owner declarations:
  `Ideal.inertia`,
  `FixedPoints.subalgebra`,
  `IntermediateField.fixedField`,
  `algebraMap_galRestrict_apply`;
- best owner abstraction: for a subgroup `H : Subgroup Gal(L / K)`, the fixed `A`-subalgebra
  `FixedPoints.subalgebra A B H` of the integral closure and the fixed field
  `IntermediateField.fixedField H`;
- primitive data: the canonical fixed-subalgebra owner `FixedPoints.subalgebra A B H`;
- derived API: the canonical map `B^H → L^H` and the source-facing inertia specialization obtained
  by setting `H = m.inertia G`.

Layer triage:
- `source-facing`: the inertia specialization saying `B^I` is the integral closure of `A` in
  `L^I`, together with the later local étale statement;
- `core/canonical`: the owner pair `FixedPoints.subalgebra A B H` /
  `IntermediateField.fixedField H`;
- `bridge/view`: the canonical map from the fixed subalgebra to the fixed field.

The bridge layer therefore belongs at the general subgroup level. Only the final étale statement
should remain in the local inertia/maximal-ideal section. -/

variable (H : Subgroup Gal(L/K))

-- Proof sketch: an element of the fixed subalgebra is fixed in `L` by every element of `H`, so
-- its image lies in the fixed field `L^H`.
private theorem fixedSubalgebra_mem_fixedField (x : B[H]) :
    algebraMap B L x ∈ L[H] :=
  sorry

private noncomputable abbrev fixedSubalgebraToFixedField : B[H] →ₐ[A] L[H] :=
  show B[H] →ₐ[A] L[H] from
    AlgHom.codRestrict
      ((IsScalarTower.toAlgHom A B L).comp (B[H]).val)
      (((L[H]).toSubalgebra : Subalgebra K L).restrictScalars A)
      (fixedSubalgebra_mem_fixedField H)

private noncomputable instance fixedSubalgebraToFixedFieldAlgebra :
    Algebra B[H] L[H] :=
  (fixedSubalgebraToFixedField H).toRingHom.toAlgebra

-- Proof sketch: an element of `L^H` integral over `A` already lies in the ambient integral
-- closure `B`, and the fixed-field condition forces it to land in the fixed subalgebra `B^H`.
/-- Companion bridge theorem: for any subgroup `H ≤ Gal(L / K)`, the fixed subalgebra `B^H` of
the integral closure `B` is the integral closure of `A` in the fixed field `L^H`. -/
theorem fixedSubalgebra_isIntegralClosure
    : IsIntegralClosure B[H] A L[H] := sorry

variable (m : Ideal (integralClosure A L))

local notation "I" => m.inertia Gal(L / K)

/-- Lemma 15.113.8 (1): the inertia fixed subalgebra `B^I` is the integral closure of `A` in the
inertia fixed field `L^I`. -/
theorem inertiaFixedSubalgebra_isIntegralClosure
    : IsIntegralClosure B[I] A L[I] :=
  fixedSubalgebra_isIntegralClosure I

end

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "G" => Gal(L / K)
local notation "B" => integralClosure A L
local notation "B[" H "]" => FixedPoints.subalgebra A B H

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

local notation "I" => m.inertia G

-- Proof sketch: let `m' = B^I ∩ m`. Show that the extension of discrete valuation rings
-- `A → (B^I)_{m'}` is weakly unramified and has separable residue-field extension, then apply the
-- étale criterion of Lemma `10.143.7`.
/-- Lemma 15.113.8 (2): if `m' = B^I ∩ m`, then `A → (B^I)_{m'}` is étale, expressed as the
statement that `A → B^I` is étale at the prime `m'`. -/
theorem inertiaFixedSubalgebra_isEtaleAt_under
    : IsEtaleAt A (m.under B[I]) := sorry

end

/-! ### Remark_15_113_9 (from Chap15) -/
open scoped Pointwise
open Ideal IsLocalRing Algebra IntermediateField

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "G" => Gal(L / K)
local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A
local notation "κA" => Ideal.ResidueField p

/-- The Galois group acts on the integral closure through the induced automorphisms of the ambient
field. -/
private instance integralClosureMulSemiringActionRemark :
    MulSemiringAction G B :=
  IsIntegralClosure.MulSemiringAction A K L B

private theorem integralClosure_smulCommClass :
    SMulCommClass G A B := sorry

attribute [local instance] integralClosure_smulCommClass

private theorem integralClosure_isInvariant :
    Algebra.IsInvariant A B G := sorry

attribute [local instance] integralClosure_isInvariant

/- Domain-style sampling for Remark 15.113.9:
- primary domain: fixed subalgebras and fixed fields attached to the wild inertia, inertia, and
  decomposition subgroups of a maximal ideal in a finite Galois extension of fraction fields of a
  discrete valuation ring, together with the contracted primes and their residue-field /
  ramification behavior;
- sampled owner declarations:
  `FixedPoints.subalgebra`,
  `IntermediateField.fixedField`,
  `wildInertiaSubgroup`,
  `tameInertiaQuotient`,
  `fixedSubalgebra_isIntegralClosure`,
  `inertiaFixedSubalgebra_isEtaleAt_under`,
  `Ideal.ResidueField.map`,
  `Ideal.ramificationIdx`;
- best owner abstraction: the fixed-object owners `FixedPoints.subalgebra A B H` and
  `IntermediateField.fixedField H` for `H = P, I, D`; the tower maps between the fixed subalgebras
  and fixed fields are derived from subgroup inclusions `P ≤ I ≤ D`, not primitive data;
- primitive data: the subgroup owners `P`, `I`, `D`, their fixed subalgebras `B^P`, `B^I`, `B^D`,
  and their fixed fields `L^P`, `L^I`, `L^D`;
- derived API: the inclusion algebras along the tower, the contracted ideals
  `m^P`, `m^I`, `m^D`, the induced residue-field maps, and the local étale / ramification /
  separability conclusions.

Layer triage:
- `source-facing`: the fifteen clauses of the Stacks remark about the full chain
  `P ⊂ I ⊂ D`, especially the `B^P` unique-prime and residue-field / ramification statements;
- `core/canonical`: `FixedPoints.subalgebra`, `IntermediateField.fixedField`,
  `wildInertiaSubgroup`, `tameInertiaQuotient`, `Ideal.under`, `Ideal.ResidueField.map`, and
  `Ideal.ramificationIdx`;
- `bridge/view`: the canonical inclusions `B^D ⊆ B^I ⊆ B^P ⊆ B` and the corresponding residue
  field maps.

Primitive-vs-derived split:
- primitive public data in this file: none beyond the source-facing subgroup/fixed-object owners
  already established earlier in the chapter;
- derived public API in this file: the source-facing consequences for the tower
  `B^D ⊆ B^I ⊆ B^P ⊆ B`, keeping exact-interface recall when an upstream chapter theorem already
  has the desired statement. -/

private theorem fixedSubalgebra_le_of_le {H H' : Subgroup G} (h : H ≤ H') :
    FixedPoints.subalgebra A B H' ≤ FixedPoints.subalgebra A B H := by
  intro x hx g
  exact hx ⟨g.1, h g.2⟩

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

local notation "D" => MulAction.stabilizer G m
local notation "I" => m.inertia G
local notation "P" => wildInertiaSubgroup K m
local notation "I_t" => tameInertiaQuotient K m

local notation "B[D]" => FixedPoints.subalgebra A B D
local notation "B[I]" => FixedPoints.subalgebra A B I
local notation "B[P]" => FixedPoints.subalgebra A B P

local notation "L[D]" => IntermediateField.fixedField D
local notation "L[I]" => IntermediateField.fixedField I
local notation "L[P]" => IntermediateField.fixedField P

local notation "mD" => m.under B[D]
local notation "mI" => m.under B[I]
local notation "mP" => m.under B[P]

local notation "κD" => Ideal.ResidueField mD
local notation "κI" => Ideal.ResidueField mI
local notation "κP" => Ideal.ResidueField mP

local instance liesOver_maximalIdeal_of_isMaximal : m.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

noncomputable instance decompositionToInertiaFixedSubalgebraAlgebra :
    Algebra B[D] B[I] :=
  ((Subalgebra.inclusion
      (fixedSubalgebra_le_of_le (Ideal.inertia_le_stabilizer m))).toRingHom).toAlgebra

noncomputable instance inertiaToWildInertiaFixedSubalgebraAlgebra :
    Algebra B[I] B[P] :=
  ((Subalgebra.inclusion
      (fixedSubalgebra_le_of_le (wildInertiaSubgroup_le_inertia m))).toRingHom).toAlgebra

noncomputable instance decompositionToWildInertiaFixedSubalgebraAlgebra :
    Algebra B[D] B[P] :=
  ((Subalgebra.inclusion
      (fixedSubalgebra_le_of_le (wildInertiaSubgroup_le_decompositionGroup m))).toRingHom).toAlgebra

noncomputable instance decompositionToInertiaFixedFieldAlgebra :
    Algebra L[D] L[I] :=
  ((IntermediateField.inclusion
      (IntermediateField.fixedField_le (Ideal.inertia_le_stabilizer m))).toRingHom).toAlgebra

noncomputable instance inertiaToWildInertiaFixedFieldAlgebra :
    Algebra L[I] L[P] :=
  ((IntermediateField.inclusion
      (IntermediateField.fixedField_le (wildInertiaSubgroup_le_inertia m))).toRingHom).toAlgebra

noncomputable instance decompositionToWildInertiaFixedFieldAlgebra :
    Algebra L[D] L[P] :=
  ((IntermediateField.inclusion
      (IntermediateField.fixedField_le (wildInertiaSubgroup_le_decompositionGroup m))).toRingHom).toAlgebra

theorem under_decomposition_over_base :
    p = Ideal.comap (algebraMap A B[D]) mD := by
  change p = Ideal.comap ((algebraMap B[D] B).comp (algebraMap A B[D])) m
  simpa using (Ideal.over_def m p)

omit [m.IsMaximal] in
theorem under_inertia_over_decomposition :
    mD = Ideal.comap (algebraMap B[D] B[I]) mI := by
  change Ideal.comap (algebraMap B[D] B) m =
    Ideal.comap ((algebraMap B[I] B).comp (algebraMap B[D] B[I])) m
  rfl

omit [m.IsMaximal] in
theorem under_wildInertia_over_inertia :
    mI = Ideal.comap (algebraMap B[I] B[P]) mP := by
  change Ideal.comap (algebraMap B[I] B) m =
    Ideal.comap ((algebraMap B[P] B).comp (algebraMap B[I] B[P])) m
  rfl

omit [m.IsMaximal] in
theorem under_wildInertia_over_decomposition :
    mD = Ideal.comap (algebraMap B[D] B[P]) mP := by
  change Ideal.comap (algebraMap B[D] B) m =
    Ideal.comap ((algebraMap B[P] B).comp (algebraMap B[D] B[P])) m
  rfl

theorem under_wildInertia_over_base :
    p = Ideal.comap (algebraMap A B[P]) mP := by
  change p = Ideal.comap ((algebraMap B[P] B).comp (algebraMap A B[P])) m
  simpa using (Ideal.over_def m p)

noncomputable instance baseToDecompositionResidueFieldAlgebra :
    Algebra κA κD :=
  (Ideal.ResidueField.map p mD (algebraMap A B[D]) (under_decomposition_over_base m)).toAlgebra

noncomputable instance decompositionToInertiaResidueFieldAlgebra :
    Algebra κD κI :=
  (Ideal.ResidueField.map mD mI (algebraMap B[D] B[I])
      (under_inertia_over_decomposition m)).toAlgebra

noncomputable instance inertiaToWildInertiaResidueFieldAlgebra :
    Algebra κI κP :=
  (Ideal.ResidueField.map mI mP (algebraMap B[I] B[P])
      (under_wildInertia_over_inertia m)).toAlgebra

noncomputable instance decompositionToWildInertiaResidueFieldAlgebra :
    Algebra κD κP :=
  (Ideal.ResidueField.map mD mP (algebraMap B[D] B[P])
      (under_wildInertia_over_decomposition m)).toAlgebra

noncomputable instance baseToWildInertiaResidueFieldAlgebra :
    Algebra κA κP :=
  (Ideal.ResidueField.map p mP (algebraMap A B[P]) (under_wildInertia_over_base m)).toAlgebra

omit [m.IsMaximal] in
private instance inertiaContractedIdeal_liesOver_decompositionContractedIdeal :
    Ideal.LiesOver mI mD :=
  ⟨(under_inertia_over_decomposition m).symm⟩

omit [m.IsMaximal] in
private instance wildInertiaContractedIdeal_liesOver_inertiaContractedIdeal :
    Ideal.LiesOver mP mI :=
  ⟨(under_wildInertia_over_inertia m).symm⟩

omit [m.IsMaximal] in
private instance wildInertiaContractedIdeal_liesOver_decompositionContractedIdeal :
    Ideal.LiesOver mP mD :=
  ⟨(under_wildInertia_over_decomposition m).symm⟩

private instance integralClosure_maximalIdeal_liesOver_wildInertiaContractedIdeal :
    Ideal.LiesOver m mP := by
  simpa using (Ideal.over_under m : Ideal.LiesOver m (m.under B[P]))

private instance integralClosure_maximalIdeal_liesOver_inertiaContractedIdeal :
    Ideal.LiesOver m mI := by
  simpa using (Ideal.over_under m : Ideal.LiesOver m (m.under B[I]))

private instance integralClosure_maximalIdeal_liesOver_decompositionContractedIdeal :
    Ideal.LiesOver m mD := by
  simpa using (Ideal.over_under m : Ideal.LiesOver m (m.under B[D]))

/- The inertia fixed subalgebra `B^I` is the integral closure of `A` in `L^I`. -/
recall inertiaFixedSubalgebra_isIntegralClosure

-- Proof sketch: this is the first Galois-theoretic clause of the remark, viewing `L^I / L^D`
-- through the canonical fixed-field tower attached to `I ≤ D`.
/-- Remark 15.113.9 (1): the fixed-field extension `L^I / L^D` is Galois. -/
theorem inertiaFixedField_isGalois_over_decompositionFixedField :
    IsGalois L[D] L[I] := sorry

-- Proof sketch: the Galois group in `(1)` is the quotient `D / I`.
/-- Companion cardinal statement for Remark 15.113.9 (1): the Galois group of `L^I / L^D` has the
same cardinality as the quotient `D / I`. -/
theorem card_gal_inertiaFixedField_over_decompositionFixedField :
    Nat.card (Gal(L[I] / L[D])) = Nat.card (D ⧸ Subgroup.subgroupOf I D) := sorry

-- Proof sketch: clause `(2)` is the wild-inertia step in the fixed-field tower.
/-- Remark 15.113.9 (2): the fixed-field extension `L^P / L^I` is Galois. -/
theorem wildInertiaFixedField_isGalois_over_inertiaFixedField :
    IsGalois L[I] L[P] := sorry

-- Proof sketch: the Galois group in `(2)` is the tame inertia quotient `I_t = I / P`.
/-- Companion cardinal statement for Remark 15.113.9 (2): the Galois group of `L^P / L^I` has the
same cardinality as `I_t = I / P`. -/
theorem card_gal_wildInertiaFixedField_over_inertiaFixedField :
    Nat.card (Gal(L[P] / L[I])) = Nat.card I_t := sorry

-- Proof sketch: clause `(3)` is the composite Galois step `L^P / L^D`.
/-- Remark 15.113.9 (3): the fixed-field extension `L^P / L^D` is Galois. -/
theorem wildInertiaFixedField_isGalois_over_decompositionFixedField :
    IsGalois L[D] L[P] := sorry

-- Proof sketch: the Galois group in `(3)` is the quotient `D / P`.
/-- Companion cardinal statement for Remark 15.113.9 (3): the Galois group of `L^P / L^D` has the
same cardinality as the quotient `D / P`. -/
theorem card_gal_wildInertiaFixedField_over_decompositionFixedField :
    Nat.card (Gal(L[P] / L[D])) = Nat.card (D ⧸ Subgroup.subgroupOf P D) := sorry

-- Proof sketch: `m^I` is the unique prime of `B^I` above `m^D`.
/-- Remark 15.113.9 (4): the contracted ideal `m^I` is the unique prime of `B^I` lying over
`m^D`. -/
theorem inertiaContractedIdeal_unique_prime_over_decompositionContractedIdeal
    (q : Ideal.primesOver mD B[I]) :
    q.1 = mI := sorry

-- Proof sketch: `m^P` is the unique prime of `B^P` above `m^I`.
/-- Remark 15.113.9 (5): the contracted ideal `m^P` is the unique prime of `B^P` lying over
`m^I`. -/
theorem wildInertiaContractedIdeal_unique_prime_over_inertiaContractedIdeal
    (q : Ideal.primesOver mI B[P]) :
    q.1 = mP := sorry

-- Proof sketch: `m` is the unique prime of `B` above `m^P`.
/-- Remark 15.113.9 (6): the maximal ideal `m` is the unique prime of `B` lying over `m^P`. -/
theorem integralClosure_maximalIdeal_unique_prime_over_wildInertiaContractedIdeal
    (q : Ideal.primesOver mP B) :
    q.1 = m := sorry

-- Proof sketch: combine `(4)` and `(5)` to descend uniqueness from `B^P` to `B^D`.
/-- Remark 15.113.9 (7): the contracted ideal `m^P` is the unique prime of `B^P` lying over
`m^D`. -/
theorem wildInertiaContractedIdeal_unique_prime_over_decompositionContractedIdeal
    (q : Ideal.primesOver mD B[P]) :
    q.1 = mP := sorry

-- Proof sketch: combine `(5)` and `(6)` to ascend uniqueness from `B^I` to `B`.
/-- Remark 15.113.9 (8): the maximal ideal `m` is the unique prime of `B` lying over `m^I`. -/
theorem integralClosure_maximalIdeal_unique_prime_over_inertiaContractedIdeal
    (q : Ideal.primesOver mI B) :
    q.1 = m := sorry

-- Proof sketch: combine `(7)` and `(6)` to ascend uniqueness from `B^D` to `B`.
/-- Remark 15.113.9 (9): the maximal ideal `m` is the unique prime of `B` lying over `m^D`. -/
theorem integralClosure_maximalIdeal_unique_prime_over_decompositionContractedIdeal
    (q : Ideal.primesOver mD B) :
    q.1 = m := sorry

-- Proof sketch: `B^D_{m^D}` is the unramified-local branch over `A`.
/-- Remark 15.113.9 (10): `A → B^D` is étale at the contracted ideal `m^D`. -/
theorem decompositionFixedSubalgebra_isEtaleAt_under :
    IsEtaleAt A mD := sorry

-- Proof sketch: clause `(10)` also says the induced residue-field extension is trivial.
/-- Remark 15.113.9 (10): the induced residue-field map `κA → κ(m^D)` is bijective. -/
theorem baseToDecompositionResidueField_bijective :
    Function.Bijective (algebraMap κA κD) := sorry

-- Proof sketch: the relative step `B^D_{m^D} → B^I_{m^I}` is the étale residue-field Galois step
-- with group `D / I`.
/-- Remark 15.113.9 (11): `B^D → B^I` is étale at the contracted ideal `m^I`. -/
theorem decompositionToInertiaFixedSubalgebra_isEtaleAt_under :
    IsEtaleAt B[D] mI := sorry

-- Proof sketch: the residue-field extension in `(11)` is Galois.
/-- Remark 15.113.9 (11): the induced residue-field extension `κ(m^I) / κ(m^D)` is Galois. -/
theorem decompositionToInertiaResidueField_isGalois :
    IsGalois κD κI := sorry

-- Proof sketch: the Galois group of the residue-field extension in `(11)` has cardinality
-- `|D / I|`.
/-- Companion cardinal statement for Remark 15.113.9 (11): the residue-field Galois group has the
same cardinality as `D / I`. -/
theorem card_gal_decompositionToInertiaResidueField :
    Nat.card (Gal(κI / κD)) = Nat.card (D ⧸ Subgroup.subgroupOf I D) := sorry

/- Remark 15.113.9 (12): `A → B^I` is étale at the contracted ideal `m^I`. -/
recall inertiaFixedSubalgebra_isEtaleAt_under

-- Proof sketch: clause `(13)` is the tame local branch over `B^I`, with ramification index
-- `|I_t|` and trivial residue field extension.
/-- Remark 15.113.9 (13): the ramification index of the branch `B^I ⊂ B^P` at
`m^I ⊂ m^P` is `|I_t|`. -/
theorem inertiaToWildInertiaFixedSubalgebra_ramificationIdx_eq :
    Ideal.ramificationIdx mI mP = Nat.card I_t := sorry

-- Proof sketch: the residue-field extension in `(13)` is trivial.
/-- Remark 15.113.9 (13): the induced residue-field map `κ(m^I) → κ(m^P)` is bijective. -/
theorem inertiaToWildInertiaResidueField_bijective :
    Function.Bijective (algebraMap κI κP) := sorry

-- Proof sketch: the ramification index in `(13)` is prime to the residue characteristic of
-- `κ(m^I)`.
/-- Remark 15.113.9 (13): the ramification index `|I_t|` is prime to the residue characteristic of
`κ(m^I)`. -/
theorem inertiaToWildInertiaFixedSubalgebra_ramificationIdx_coprime_residueChar
    (q : ℕ) [Fact q.Prime] [CharP κI q] :
    Nat.Coprime (Ideal.ramificationIdx mI mP) q := sorry

-- Proof sketch: clause `(14)` is the composite branch `B^D ⊂ B^P`.
/-- Remark 15.113.9 (14): the ramification index of the branch `B^D ⊂ B^P` at
`m^D ⊂ m^P` is `|I_t|`. -/
theorem decompositionToWildInertiaFixedSubalgebra_ramificationIdx_eq :
    Ideal.ramificationIdx mD mP = Nat.card I_t := sorry

-- Proof sketch: the residue-field extension in `(14)` is separable.
/-- Remark 15.113.9 (14): the induced residue-field extension `κ(m^P) / κ(m^D)` is separable. -/
theorem decompositionToWildInertiaResidueField_isSeparable :
    Algebra.IsSeparable κD κP := sorry

-- Proof sketch: the ramification index in `(14)` is prime to the residue characteristic of
-- `κ(m^D)`.
/-- Remark 15.113.9 (14): the ramification index `|I_t|` is prime to the residue characteristic of
`κ(m^D)`. -/
theorem decompositionToWildInertiaFixedSubalgebra_ramificationIdx_coprime_residueChar
    (q : ℕ) [Fact q.Prime] [CharP κD q] :
    Nat.Coprime (Ideal.ramificationIdx mD mP) q := sorry

-- Proof sketch: clause `(15)` is the total branch `A ⊂ B^P`.
/-- Remark 15.113.9 (15): the ramification index of the branch `A ⊂ B^P` at `p ⊂ m^P`
is `|I_t|`. -/
theorem baseToWildInertiaFixedSubalgebra_ramificationIdx_eq :
    Ideal.ramificationIdx p mP = Nat.card I_t := sorry

-- Proof sketch: the residue-field extension in `(15)` is separable.
/-- Remark 15.113.9 (15): the induced residue-field extension `κ(m^P) / κA` is separable. -/
theorem baseToWildInertiaResidueField_isSeparable :
    Algebra.IsSeparable κA κP := sorry

-- Proof sketch: the ramification index in `(15)` is prime to the residue characteristic of
-- `κA`.
/-- Remark 15.113.9 (15): the ramification index `|I_t|` is prime to the residue characteristic of
`κA`. -/
theorem baseToWildInertiaFixedSubalgebra_ramificationIdx_coprime_residueChar
    (q : ℕ) [Fact q.Prime] [CharP κA q] :
    Nat.Coprime (Ideal.ramificationIdx p mP) q := sorry

end
