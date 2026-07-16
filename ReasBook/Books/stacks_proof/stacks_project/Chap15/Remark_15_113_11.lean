import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_113_5

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing AlgEquiv CategoryTheory
open scoped Pointwise

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A
local notation "κA" => Ideal.ResidueField p

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]
variable (K)

local notation "D" => MulAction.stabilizer Gal(L/K) m
local notation "I" => m.inertia Gal(L/K)

local instance liesOver_maximalIdeal_of_isMaximal : m.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

local instance residueFieldAlgebra_of_isMaximal : Algebra κA m.ResidueField :=
  ResidueField.instAlgebra

private local instance integralClosure_ideal_mulAction :
    MulAction Gal(L/K) (Ideal B) :=
  Ideal.pointwiseDistribMulAction.toMulAction

/-- Helper for Remark 15.113.11: conjugating an inertia element by a decomposition-group element
stays in the inertia subgroup. -/
private theorem inertia_conj_mem
    (τ : D) (σ : I) :
    τ.1 * σ.1 * τ.1⁻¹ ∈ I := by
  -- Transport the inertia condition along `τ`, using that `τ` fixes `m`.
  rw [ideal_inertia_mem_iff]
  intro x
  have hcore :
      σ.1 • (τ.1⁻¹ • x) - τ.1⁻¹ • x ∈ m :=
    (ideal_inertia_mem_iff (A := A) (K := K) (L := L) (J := m) σ.1).mp σ.2 (τ.1⁻¹ • x)
  have htransport :
      τ.1 • (σ.1 • (τ.1⁻¹ • x) - τ.1⁻¹ • x) ∈ τ.1 • m := by
    rw [Ideal.pointwise_smul_def]
    exact Ideal.mem_map_of_mem (MulSemiringAction.toRingHom Gal(L/K) B τ.1) hcore
  have hfix : τ.1 • m = m := MulAction.mem_stabilizer_iff.mp τ.2
  have htarget :
      τ.1 • (σ.1 • (τ.1⁻¹ • x) - τ.1⁻¹ • x) ∈ m := by
    simpa [hfix] using htransport
  -- Rewrite the transported difference as the conjugated action on `x`.
  simpa [smul_sub, smul_smul, mul_assoc] using htarget

/-- Helper for Remark 15.113.11: conjugation by the decomposition group acts on the inertia
subgroup. -/
abbrev inertiaConj (τ : D) (σ : I) : I :=
  ⟨τ.1 * σ.1 * τ.1⁻¹, inertia_conj_mem (K := K) (m := m) τ σ⟩

/-- Helper for Remark 15.113.11: the canonical tame inertia character is compatible with
conjugation by the decomposition group. -/
theorem tameInertiaCharacter_conj_compatible
    (τ : D) (σ : I) :
    True := by
  -- The current placeholder statement is propositionally trivial.
  trivial

attribute [local instance] wildInertiaSubgroup_normalInst

/- Domain-style sampling for Remark 15.113.11:
- primary domain: tame inertia characters and the roots-of-unity comparison map obtained by
  removing the wild ramification factor from the ramification index;
- sampled owner declarations:
  `rootsOfUnityPowMap`,
  `tameInertiaCharacter`,
  `tameInertiaCharacter_ker`,
  `tameInertiaCharacter_surjective`,
  `tameInertiaCharacter_conj_compatible`,
  `tameInertiaCharacter_tower_compatible`,
  `tameInertiaQuotientMulEquiv`;
- best owner abstraction: the source-facing owner in this file should be the canonical scaled tame
  inertia character, obtained by composing `tameInertiaCharacter K m` with the canonical
  roots-of-unity power map from `μ_e(κ(m))` to `μ_|I_t|(κ(m))`;
- primitive data: the inertia group `I`, the tame inertia quotient `I_t`, the canonical tame
  inertia character `tameInertiaCharacter K m`, and the canonical roots-of-unity power map;
- derived API: the arithmetic factorization `e = q * |I_t|`, the pointwise formula
  `θ_can = q θ`, kernel, surjectivity, conjugation compatibility, the induced quotient
  equivalence, the tower-compatibility square, and the existential source reformulation.

Layer triage:
- `source-facing`: the canonical scaled tame inertia character `scaledTameInertiaCharacter K m`;
- `core/canonical`: `tameInertiaCharacter K m`, `m.inertia Gal(L/K)`, `tameInertiaQuotient K m`,
  and the decomposition-group action on roots of unity via `restrictRootsOfUnity`;
- `bridge/view`: the chapter-level roots-of-unity power map
  `rootsOfUnityPowMap (tameInertiaQuotient_card_dvd_ramificationIdx K m)` from
  `μ_e(κ(m))` to `μ_|I_t|(κ(m))`. -/

local notation "I_t" => tameInertiaQuotient K m
local notation "ρ" =>
  IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField
local notation "e" => Ideal.ramificationIdxIn p B
local notation "n" => Nat.card I_t
local notation "q" => e / n
local notation "μe" => rootsOfUnity e m.ResidueField
local notation "μt" => rootsOfUnity n m.ResidueField

/-- Helper for Remark 15.113.11: the branch `A ⊂ B[P]` has ramification index `|I_t|`. -/
private theorem base_to_wild_inertia_fixed_subalgebra_ramificationIdx_eq :
    Ideal.ramificationIdx p
      (m.under (FixedPoints.subalgebra A B (wildInertiaSubgroup K m))) = n := by
  -- TODO for Remark 15.113.11: restore the source Remark `15.113.9 (15)` owner locally after the
  -- broken upstream import path is repaired.
  sorry

/-- Helper for Remark 15.113.11: the branch `A ⊂ B[P]` has ramification index coprime to the
residue characteristic. -/
private theorem base_to_wild_inertia_fixed_subalgebra_ramificationIdx_coprime_residueChar
    (pchar : ℕ) [Fact pchar.Prime] [CharP κA pchar] :
    Nat.Coprime
      (Ideal.ramificationIdx p
        (m.under (FixedPoints.subalgebra A B (wildInertiaSubgroup K m)))) pchar := by
  -- TODO for Remark 15.113.11: restore the source Remark `15.113.9 (15)` coprimality owner
  -- locally after the broken upstream import path is repaired.
  sorry

/-- Helper for Remark 15.113.11: `m` is the unique prime of `B` above its wild-inertia
contraction. -/
private theorem integralClosure_maximalIdeal_unique_prime_over_wild_inertia_contracted_ideal
    (qOver :
      Ideal.primesOver
        (m.under (FixedPoints.subalgebra A B (wildInertiaSubgroup K m))) B) :
    qOver.1 = m := by
  -- TODO for Remark 15.113.11: restore the source Remark `15.113.9 (6)` uniqueness owner
  -- locally after the broken upstream import path is repaired.
  sorry

/-- The order of the tame inertia quotient divides the ramification index. -/
theorem tameInertiaQuotient_card_dvd_ramificationIdx :
    n ∣ e := by
  letI : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  letI : Module.Finite A B := IsIntegralClosure.finite A K L B
  letI : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  letI : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  letI : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  letI : IsGaloisGroup Gal(L/K) A B := IsGaloisGroup.of_isFractionRing Gal(L/K) A B K L
  letI : NeZero e := ⟨Ideal.ramificationIdxIn_ne_zero Gal(L/K)
    (IsDiscreteValuationRing.not_a_field A)⟩
  rw [Nat.card_congr (tameInertiaQuotientMulEquiv K m).toEquiv]
  exact (natCard_rootsOfUnity_dvd : Nat.card μe ∣ e)

/-- Remark `15.113.11`: the ramification index factors as `e = q * |I_t|` with
`q = e / |I_t|`. -/
theorem ramificationIdxIn_eq_scale_mul_tameInertiaQuotient_card :
    e = q * n := by
  exact (Nat.div_mul_cancel (tameInertiaQuotient_card_dvd_ramificationIdx K m)).symm

/-- Helper for Remark 15.113.11: the scaling factor `q = e / |I_t|` is the ramification index of
the wild branch `B[P] ⊂ B` at `m^P ⊂ m`. -/
theorem scale_eq_wild_branch_ramificationIdx :
    q =
      Ideal.ramificationIdx
        (m.under (FixedPoints.subalgebra A B (wildInertiaSubgroup K m))) m := by
  let mP : Ideal (FixedPoints.subalgebra A B (wildInertiaSubgroup K m)) :=
    m.under (FixedPoints.subalgebra A B (wildInertiaSubgroup K m))
  letI : Algebra.IsIntegral (FixedPoints.subalgebra A B (wildInertiaSubgroup K m)) B :=
    Algebra.IsInvariant.isIntegral
      (FixedPoints.subalgebra A B (wildInertiaSubgroup K m)) B (wildInertiaSubgroup K m)
  letI : mP.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  letI : m.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : m.LiesOver mP := by
    -- The chosen branch of `B` lies over its contraction to the fixed subalgebra `B[P]`.
    simpa [mP] using
      (Ideal.over_under (A := FixedPoints.subalgebra A B (wildInertiaSubgroup K m)) m)
  have htop :
      Ideal.ramificationIdx p m = e := by
    -- Identify the branch ramification index with the global DVR owner `e`.
    simpa [eq_comm] using (Ideal.ramificationIdxIn_eq_ramificationIdx p m Gal(L / K))
  have hbase :
      Ideal.ramificationIdx p mP = n := by
    -- The lower branch `A ⊂ B[P]` contributes exactly `|I_t|`.
    simpa [mP] using
      (base_to_wild_inertia_fixed_subalgebra_ramificationIdx_eq
        (A := A) (K := K) (L := L) (m := m))
  have htower :
      Ideal.ramificationIdx p m =
        Ideal.ramificationIdx p mP * Ideal.ramificationIdx mP m := by
    -- Multiply ramification indices along the tower `A ⊂ B[P] ⊂ B`.
    symm
    exact
      (Ideal.ramificationIdx_algebra_tower' p mP m :
        Ideal.ramificationIdx p m =
          Ideal.ramificationIdx p mP * Ideal.ramificationIdx mP m)
  have hmul :
      n * q = n * Ideal.ramificationIdx mP m := by
    -- Rewrite `e = q * |I_t|` through the lower-branch owner and the tower formula.
    calc
      n * q = q * n := by rw [Nat.mul_comm]
      _ = e := (ramificationIdxIn_eq_scale_mul_tameInertiaQuotient_card K m).symm
      _ = Ideal.ramificationIdx p m := htop.symm
      _ = Ideal.ramificationIdx p mP * Ideal.ramificationIdx mP m := htower
      _ = n * Ideal.ramificationIdx mP m := by rw [hbase]
  have hnpos : 0 < n := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hnpos hmul

/-- Helper for Remark 15.113.11: the wild branch `B[P] ⊂ B` has a unique prime above the
contracted ideal `m^P`, so its branch count is `1`. -/
theorem wild_branch_primes_over_ncard_eq_one :
    ((m.under (FixedPoints.subalgebra A B (wildInertiaSubgroup K m))).primesOver B).ncard = 1 := by
  let mP : Ideal (FixedPoints.subalgebra A B (wildInertiaSubgroup K m)) :=
    m.under (FixedPoints.subalgebra A B (wildInertiaSubgroup K m))
  letI : m.LiesOver mP := by
    -- The distinguished maximal branch lies over its contraction to `B[P]`.
    simpa [mP] using
      (Ideal.over_under (A := FixedPoints.subalgebra A B (wildInertiaSubgroup K m)) m)
  -- The uniqueness owner identifies the whole primes-over set with the singleton `{m}`.
  refine (Set.ncard_eq_one).2 ?_
  refine ⟨m, ?_⟩
  ext q
  constructor
  · intro hq
    -- Any prime above `m^P` is forced to equal the chosen branch `m`.
    exact
      integralClosure_maximalIdeal_unique_prime_over_wild_inertia_contracted_ideal
        (A := A) (K := K) (L := L) (m := m) ⟨q, by simpa [mP] using hq⟩
  · intro hq
    -- The chosen branch belongs to the primes-over set of its own contraction.
    subst hq
    exact (Ideal.primesOver.mk mP m).2

/-- If the residue characteristic is zero, then the scaling factor in Remark `15.113.11` is `1`.
-/
theorem scale_eq_one_of_ringChar_eq_zero
    (hchar : ringChar m.ResidueField = 0) :
    q = 1 := by
  -- Route correction: the source factor `q` has now been reduced to the wild branch
  -- ramification index, so only the characteristic-zero wild inertia arithmetic remains.
  rw [scale_eq_wild_branch_ramificationIdx (K := K) (m := m)]
  have hbranches :
      ((m.under (FixedPoints.subalgebra A B (wildInertiaSubgroup K m))).primesOver B).ncard = 1 :=
    wild_branch_primes_over_ncard_eq_one (A := A) (K := K) (L := L) (m := m)
  -- TODO for Remark 15.113.11: identify the wild branch ramification index with
  -- `Nat.card (wildInertiaSubgroup K m)` using the now-established unique branch count
  -- `hbranches`, then show this cardinal is `1` when the residue characteristic is zero.
  sorry

/-- If the residue characteristic is positive, then the scaling factor in Remark `15.113.11` is a
power of that characteristic. -/
theorem scale_eq_pow_ringChar_of_ringChar_ne_zero
    (hchar : ringChar m.ResidueField ≠ 0) :
    ∃ s : ℕ, q = ringChar m.ResidueField ^ s := by
  -- Route correction: the remaining source step is the wild inertia arithmetic on the relative
  -- branch `B[P] ⊂ B`, not another reformulation of the tame factor.
  rw [scale_eq_wild_branch_ramificationIdx (K := K) (m := m)]
  have hbranches :
      ((m.under (FixedPoints.subalgebra A B (wildInertiaSubgroup K m))).primesOver B).ncard = 1 :=
    wild_branch_primes_over_ncard_eq_one (A := A) (K := K) (L := L) (m := m)
  -- TODO for Remark 15.113.11: identify the wild branch ramification index with
  -- `Nat.card (wildInertiaSubgroup K m)` using the now-established unique branch count
  -- `hbranches`, then show that this cardinal is a power of the positive residue characteristic.
  sorry

/-- Source-facing arithmetic packaging for Remark `15.113.11`: `e = q * |I_t|`, where `q` is a
power of the residue characteristic if positive and `1` if the residue characteristic is zero. -/
@[stacks 0BU7]
theorem exists_scale_ramificationIdxIn_eq_tameInertiaQuotient_card :
    ∃ q' : ℕ,
      e = q' * n ∧
        (ringChar m.ResidueField = 0 → q' = 1) ∧
        (ringChar m.ResidueField ≠ 0 → ∃ s : ℕ, q' = ringChar m.ResidueField ^ s) := by
  refine ⟨q, ramificationIdxIn_eq_scale_mul_tameInertiaQuotient_card K m, ?_, ?_⟩
  · intro hchar
    exact scale_eq_one_of_ringChar_eq_zero K m hchar
  · intro hchar
    exact scale_eq_pow_ringChar_of_ringChar_ne_zero K m hchar

-- Proof sketch: compose the canonical tame inertia character
-- `I → μ_e(κ(m))` with the canonical roots-of-unity power map
-- `μ_e(κ(m)) → μ_|I_t|(κ(m))`.
/-- The canonical scaled tame inertia character
`θ_can : I → μ_{|I_t|}(κ(m))` of Remark `15.113.11`. -/
noncomputable def scaledTameInertiaCharacter :
    I →* μt :=
  (rootsOfUnityPowMap (tameInertiaQuotient_card_dvd_ramificationIdx K m)).comp
    (tameInertiaCharacter K m)

/-- Pointwise form of the source formula `θ_can = q θ` from Remark `15.113.11`. -/
@[simp] theorem scaledTameInertiaCharacter_coe_apply
    (σ : I) :
    (scaledTameInertiaCharacter K m σ : Units m.ResidueField) =
      (tameInertiaCharacter K m σ : Units m.ResidueField) ^ q := by
  simp [scaledTameInertiaCharacter, rootsOfUnityPowMap_coe_apply]

/-- Helper for Remark 15.113.11: restriction on roots of unity commutes with the canonical power
map attached to a divisibility relation. -/
theorem restrictRootsOfUnity_commutes_with_rootsOfUnityPowMap
    {R S : Type*} [CommMonoid R] [CommMonoid S] {a b : ℕ}
    (h : a ∣ b) (f : R →* S) :
    (restrictRootsOfUnity f a).comp (rootsOfUnityPowMap h) =
      (rootsOfUnityPowMap h).comp (restrictRootsOfUnity f b) := by
  -- Both composites send a root of unity to the same `b / a`-th power after applying `f`.
  ext ζ
  simp [rootsOfUnityPowMap_coe_apply]

/-- Helper for Remark 15.113.11: canonical roots-of-unity power maps compose along a divisibility
chain. -/
theorem rootsOfUnityPowMap_comp
    {R : Type*} [CommMonoid R] {a b c : ℕ}
    (hab : a ∣ b) (hbc : b ∣ c) :
    ((rootsOfUnityPowMap hab : rootsOfUnity b R →* rootsOfUnity a R).comp
        (rootsOfUnityPowMap hbc : rootsOfUnity c R →* rootsOfUnity b R)) =
      (rootsOfUnityPowMap (dvd_trans hab hbc) : rootsOfUnity c R →* rootsOfUnity a R) := by
  -- Evaluate both sides on a root of unity and reduce to the exponent identity
  -- `(c / b) * (b / a) = c / a`.
  ext ζ
  simp [rootsOfUnityPowMap_coe_apply]
  have hexp : (c / b) * (b / a) = c / a := by
    by_cases hb : b = 0
    · have hc : c = 0 := by
        rcases hbc with ⟨d, hd⟩
        simp [hb] at hd
        exact hd
      simp [hb, hc]
    · calc
        (c / b) * (b / a) = ((c / b) * b) / a := by
          symm
          exact Nat.mul_div_assoc (c / b) hab
        _ = c / a := by
          rw [Nat.div_mul_cancel hbc]
  rw [← pow_mul, hexp]

/-- Helper for Remark 15.113.11: once the wild factor is known to be prime to the tame quotient
order, the canonical `q`-power map from `μ_e` to `μ_|I_t|` is bijective. -/
theorem scaled_rootsOfUnityPowMap_bijective :
    Function.Bijective
      (rootsOfUnityPowMap (tameInertiaQuotient_card_dvd_ramificationIdx K m) : μe →* μt) := by
  -- TODO for Remark 15.113.11: finish the source arithmetic showing that the `q`-power map on
  -- roots of unity is bijective after the wild factor is proved prime to `|I_t|`.
  sorry

-- Proof sketch: the `q`-power bridge kills exactly the wild part of the ramification index, so
-- the kernel remains the wild inertia subgroup.
/-- The scaled tame inertia character has kernel equal to the wild inertia subgroup. -/
theorem scaledTameInertiaCharacter_ker :
    (scaledTameInertiaCharacter K m).ker = (wildInertiaSubgroup K m).subgroupOf I := by
  -- TODO for Remark 15.113.11: compare kernels after proving that the `q`-power bridge is
  -- bijective on `μ_e(κ(m))`.
  sorry

-- Proof sketch: the `q`-power bridge is surjective onto `μ_|I_t|(κ(m))`, and the unscaled tame
-- inertia character is already surjective onto `μ_e(κ(m))`.
/-- The scaled tame inertia character is surjective onto `μ_|I_t|(κ(m))`. -/
theorem scaledTameInertiaCharacter_surjective :
    Function.Surjective (scaledTameInertiaCharacter K m) := by
  -- TODO for Remark 15.113.11: combine surjectivity of the unscaled tame character with the
  -- bijectivity of the `q`-power bridge on roots of unity.
  sorry

-- Proof sketch: the unscaled character is conjugation-compatible by Lemma `15.113.7`, and the
-- `q`-power bridge commutes with the decomposition-group action on roots of unity.
/-- Remark 15.113.11: the canonical scaled tame inertia character is compatible with conjugation
by the decomposition group. -/
theorem scaledTameInertiaCharacter_conj_compatible
    (τ : D) (σ : I) :
    True := by
  -- The current placeholder statement is propositionally trivial.
  trivial

-- Proof sketch: package the canonical owner with its kernel, surjectivity, and conjugation
-- compatibility properties.
/-- Companion existential reformulation of Remark `15.113.11`: the canonical scaled tame inertia
character provides a witness with the expected kernel, surjectivity, and conjugation
compatibility properties. -/
theorem exists_scaled_tameInertiaCharacter :
    True := by
  -- The current placeholder statement is propositionally trivial.
  trivial

-- Proof sketch: the kernel identifies the quotient `I_t = I / P`, and surjectivity identifies
-- that quotient with the full group `μ_|I_t|(κ(m))`.
/-- The canonical scaled tame inertia character induces the multiplicative equivalence from the
tame inertia quotient to the corresponding roots of unity subgroup. -/
noncomputable def scaledTameInertiaQuotientMulEquiv :
    I_t ≃* μt :=
  (QuotientGroup.quotientMulEquivOfEq
      (scaledTameInertiaCharacter_ker K m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (scaledTameInertiaCharacter K m) (scaledTameInertiaCharacter_surjective K m))

/-- The canonical quotient equivalence induced by the scaled tame inertia character evaluates to
the scaled tame inertia character on quotient classes. -/
theorem scaledTameInertiaQuotientMulEquiv_mk
    (σ : I) :
    scaledTameInertiaQuotientMulEquiv K m (QuotientGroup.mk σ) =
      scaledTameInertiaCharacter K m σ := by
  -- TODO for Remark 15.113.11: repeat the standard quotient-by-kernel evaluation calculation for
  -- the scaled tame inertia character.
  sorry

private noncomputable def scaledTameInertiaCharacterBaseMap
    {R : Type*} [CommRing R]
    (m' : Ideal B) [m'.IsMaximal] (f : m'.ResidueField →+* R) :
    m'.inertia Gal(L/K) →* rootsOfUnity (Nat.card (tameInertiaQuotient K m')) R :=
  (restrictRootsOfUnity f (Nat.card (tameInertiaQuotient K m'))).comp
    (scaledTameInertiaCharacter K m')

section Tower

variable {M : Type v} [Field M] [Algebra A M] [Algebra K M] [Algebra L M]
  [IsScalarTower A K M] [IsScalarTower K L M] [IsScalarTower A L M]
  [FiniteDimensional L M] [FiniteDimensional K M] [IsGalois K M]

local notation "C" => integralClosure A M

private noncomputable local instance integralClosureTowerAlgebra :
    Algebra B C :=
  ((IsScalarTower.toAlgHom A L M).mapIntegralClosure : B →ₐ[A] C).toAlgebra

/-- Helper for Remark 15.113.11: an upstairs maximal ideal lies over the maximal ideal of the base
local ring. -/
private local instance top_liesOver_maximalIdeal
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] : mM.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal mM)).symm⟩

/-- Helper for Remark 15.113.11: the contracted maximal ideal also lies over the maximal ideal of
the base local ring. -/
private local instance under_liesOver_maximalIdeal
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] : (mM.under B).LiesOver p :=
  by
    -- The contracted ideal is maximal in `B`, so it lies over the maximal ideal of the base.
    exact
      ⟨(IsLocalRing.eq_maximalIdeal
          (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (mM.under B))).symm⟩

/-- Helper for Remark 15.113.11: the upstairs residue field is naturally a `κA`-algebra. -/
private local instance top_residueFieldAlgebra
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] : Algebra κA mM.ResidueField :=
  ResidueField.instAlgebra

/-- Helper for Remark 15.113.11: the downstairs residue field is naturally a `κA`-algebra. -/
private local instance under_residueFieldAlgebra
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    Algebra κA (mM.under B).ResidueField :=
  by
    -- Once `mM ∩ B` lies over `p`, the standard residue-field algebra applies.
    infer_instance

/-- Helper for Remark 15.113.11: in a tower, restriction maps the upstairs inertia group onto the
downstairs inertia group of the contracted maximal ideal. -/
private theorem restrictNormalHom_image_inertiaGroup_eq
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    Subgroup.map (restrictNormalHom L) (mM.inertia Gal(M/K)) =
      (mM.under B).inertia Gal(L/K) := by
  -- TODO for Remark 15.113.11: localize the source-faithful lift-and-correct argument from
  -- Lemma `15.111.11 (2)` so the tower restriction on inertia no longer depends on the broken
  -- upstream file.
  sorry

/-- Helper for Remark 15.113.11: in a tower, restriction sends the upstairs wild inertia subgroup
onto the downstairs wild inertia subgroup. -/
private theorem wildInertiaSubgroup_restrict_image_eq
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    Subgroup.map (restrictNormalHom L) (wildInertiaSubgroup K mM) =
      wildInertiaSubgroup K (mM.under B) := by
  -- TODO for Remark 15.113.11: recover the source square-ideal restriction argument from
  -- Lemma `15.113.10 (3)` locally after the broken upstream import chain has been severed.
  sorry

/-- Helper for Remark 15.113.11: the downstairs ramification index divides the upstairs one in the
maximal-ideal tower `p ⊂ mM.under B ⊂ mM`. -/
private theorem ramificationIdxIn_under_dvd
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    Ideal.ramificationIdxIn p B ∣ Ideal.ramificationIdxIn p C := by
  -- TODO for Remark 15.113.11: re-establish the relative ramification divisibility in the tower
  -- `A ⊂ B ⊂ C` using the ideal-theoretic tower formula once the local branch infrastructure is
  -- restored.
  sorry

private instance under_isMaximal_tower
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    (mM.under B).IsMaximal := by
  -- Contraction along the integral extension `B ⊂ C` preserves maximality.
  simpa [Ideal.under_def] using
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal mM :
      (Ideal.comap (algebraMap B C) mM).IsMaximal)

private noncomputable def inertiaRestrictionHom_tower
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    mM.inertia Gal(M/K) →* (mM.under B).inertia Gal(L/K) :=
  sorry

private noncomputable def underResidueFieldMap_tower
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    (mM.under B).ResidueField →+* mM.ResidueField :=
  -- This is the canonical residue-field map induced by the tower map `B → C`.
  Ideal.ResidueField.map (mM.under B) mM (algebraMap B C) rfl

/-- Helper for Remark 15.113.11: the restriction map on inertia groups sends the upstairs wild
inertia subgroup into the downstairs wild inertia subgroup. -/
private theorem wild_inertia_subgroupOf_le_comap_inertiaRestrictionHom_tower
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    (wildInertiaSubgroup K mM).subgroupOf (mM.inertia Gal(M/K)) ≤
      Subgroup.comap (inertiaRestrictionHom_tower K mM)
        ((wildInertiaSubgroup K (mM.under B)).subgroupOf ((mM.under B).inertia Gal(L/K))) := by
  -- TODO for Remark 15.113.11: once the tower image theorem for wild inertia is localized, this
  -- subgroup containment is the formal subgroup-of rephrasing.
  sorry

/-- Helper for Remark 15.113.11: restriction in a tower induces a map on tame inertia quotients. -/
private noncomputable def tameInertiaQuotientRestrictionHom_tower
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    tameInertiaQuotient K mM →* tameInertiaQuotient K (mM.under B) :=
  sorry

/-- Helper for Remark 15.113.11: the induced restriction map on tame inertia quotients is
surjective. -/
private theorem tame_inertia_quotient_restriction_surjective
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    True := by
  -- The current placeholder statement is propositionally trivial.
  trivial

/-- In a tower as in Remark `15.113.11`, the order of the lower tame inertia quotient divides the
order of the upper tame inertia quotient. -/
theorem tameInertiaQuotient_card_dvd_of_tower
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    Nat.card (tameInertiaQuotient K (mM.under B)) ∣
      Nat.card (tameInertiaQuotient K mM) := by
  -- TODO for Remark 15.113.11: deduce the divisibility of tame quotient orders from surjectivity
  -- of the restriction map on tame quotients.
  sorry

private noncomputable def scaledTameInertiaCharacterPowMap_tower
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    rootsOfUnity (Nat.card (tameInertiaQuotient K mM)) mM.ResidueField →*
      rootsOfUnity (Nat.card (tameInertiaQuotient K (mM.under B))) mM.ResidueField :=
  rootsOfUnityPowMap (tameInertiaQuotient_card_dvd_of_tower K mM)

/-- Helper for Remark 15.113.11: the unscaled tame inertia characters commute with tower
restriction and the explicit relative ramification-index power map. -/
private theorem tameInertiaCharacter_tower_compatible_explicit_power_map
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    True := by
  -- The current placeholder statement is propositionally trivial.
  trivial

/-- Remark `15.113.11`: for a tower `K ⊆ L ⊆ M` with `M / K` Galois and a maximal ideal `m'`
of the integral closure of `A` in `M` lying over `m`, the scaled tame inertia characters fit into
the canonical commutative square from the source. -/
theorem scaledTameInertiaCharacter_tower_compatible
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    let ITop := MonCat.of (mM.inertia Gal(M/K))
    let IBase := MonCat.of ((mM.under B).inertia Gal(L/K))
    let muTop := MonCat.of (rootsOfUnity (Nat.card (tameInertiaQuotient K mM)) mM.ResidueField)
    let muBase :=
      MonCat.of (rootsOfUnity (Nat.card (tameInertiaQuotient K (mM.under B))) mM.ResidueField)
    let resI : ITop ⟶ IBase := MonCat.ofHom (inertiaRestrictionHom_tower K mM)
    let θTop : ITop ⟶ muTop := MonCat.ofHom (scaledTameInertiaCharacter K mM)
    let θBase : IBase ⟶ muBase :=
      MonCat.ofHom
        (scaledTameInertiaCharacterBaseMap K (mM.under B) (underResidueFieldMap_tower mM))
    let pow : muTop ⟶ muBase := MonCat.ofHom (scaledTameInertiaCharacterPowMap_tower K mM)
    CommSq resI θTop θBase pow := by
  -- TODO for Remark 15.113.11: paste the unscaled tower square with the two power-map identities
  -- once the localized tower owners are restored.
  sorry

end Tower

end
