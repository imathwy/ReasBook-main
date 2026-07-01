import Mathlib
import stacks_project.Chap15.Lemma_15_113_10
import stacks_project.Chap15.Lemma_15_113_7

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

/-- The Galois group acts on the integral closure through the induced automorphisms of the ambient
field. -/
private instance integralClosureMulSemiringActionRemark :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

private theorem integralClosure_smulCommClass :
    SMulCommClass Gal(L/K) A B := sorry

attribute [local instance] integralClosure_smulCommClass

private theorem integralClosure_isInvariant :
    Algebra.IsInvariant A B Gal(L/K) := sorry

attribute [local instance] integralClosure_isInvariant

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]
variable (K)

local notation "D" => MulAction.stabilizer Gal(L/K) m
local notation "I" => m.inertia Gal(L/K)

private local instance liesOver_maximalIdeal_of_isMaximal : m.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

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

/-- If the residue characteristic is zero, then the scaling factor in Remark `15.113.11` is `1`.
-/
theorem scale_eq_one_of_ringChar_eq_zero
    (hchar : ringChar m.ResidueField = 0) :
    q = 1 := by
  sorry

/-- If the residue characteristic is positive, then the scaling factor in Remark `15.113.11` is a
power of that characteristic. -/
theorem scale_eq_pow_ringChar_of_ringChar_ne_zero
    (hchar : ringChar m.ResidueField ≠ 0) :
    ∃ s : ℕ, q = ringChar m.ResidueField ^ s := by
  sorry

/-- Source-facing arithmetic packaging for Remark `15.113.11`: `e = q * |I_t|`, where `q` is a
power of the residue characteristic if positive and `1` if the residue characteristic is zero. -/
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

-- Proof sketch: the `q`-power bridge kills exactly the wild part of the ramification index, so
-- the kernel remains the wild inertia subgroup.
/-- The scaled tame inertia character has kernel equal to the wild inertia subgroup. -/
theorem scaledTameInertiaCharacter_ker :
    (scaledTameInertiaCharacter K m).ker = (wildInertiaSubgroup K m).subgroupOf I := sorry

-- Proof sketch: the `q`-power bridge is surjective onto `μ_|I_t|(κ(m))`, and the unscaled tame
-- inertia character is already surjective onto `μ_e(κ(m))`.
/-- The scaled tame inertia character is surjective onto `μ_|I_t|(κ(m))`. -/
theorem scaledTameInertiaCharacter_surjective :
    Function.Surjective (scaledTameInertiaCharacter K m) := sorry

-- Proof sketch: the unscaled character is conjugation-compatible by Lemma `15.113.7`, and the
-- `q`-power bridge commutes with the decomposition-group action on roots of unity.
/-- Remark 15.113.11: the canonical scaled tame inertia character is compatible with conjugation
by the decomposition group. -/
theorem scaledTameInertiaCharacter_conj_compatible
    (τ : D) (σ : I) :
    scaledTameInertiaCharacter K m (inertiaConj m τ σ) =
      ((ρ τ).toMulEquiv.restrictRootsOfUnity n)
        (scaledTameInertiaCharacter K m σ) := sorry

-- Proof sketch: package the canonical owner with its kernel, surjectivity, and conjugation
-- compatibility properties.
/-- Companion existential reformulation of Remark `15.113.11`: the canonical scaled tame inertia
character provides a witness with the expected kernel, surjectivity, and conjugation
compatibility properties. -/
theorem exists_scaled_tameInertiaCharacter :
    ∃ θcan : I →* μt,
      θcan.ker = (wildInertiaSubgroup K m).subgroupOf I ∧
        Function.Surjective θcan ∧
        ∀ (τ : D) (σ : I),
          θcan (inertiaConj m τ σ) =
            ((ρ τ).toMulEquiv.restrictRootsOfUnity n) (θcan σ) := by
  refine ⟨scaledTameInertiaCharacter K m, scaledTameInertiaCharacter_ker K m,
    scaledTameInertiaCharacter_surjective K m, ?_⟩
  intro τ σ
  exact scaledTameInertiaCharacter_conj_compatible K m τ σ

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
      scaledTameInertiaCharacter K m σ := sorry

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

private instance under_isMaximal_tower
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    (mM.under B).IsMaximal := by
  simpa [Ideal.under_def] using
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal mM :
      (Ideal.comap (algebraMap B C) mM).IsMaximal)

private noncomputable def inertiaRestrictionHom_tower
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    mM.inertia Gal(M/K) →* (mM.under B).inertia Gal(L/K) where
  toFun σ := ⟨restrictNormalHom L σ.1, by
    have hσ :
        restrictNormalHom L σ.1 ∈
          Subgroup.map (restrictNormalHom L) (mM.inertia Gal(M / K)) :=
      ⟨σ.1, σ.2, rfl⟩
    simpa [restrictNormalHom_image_inertiaGroup_eq mM] using hσ⟩
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp

private noncomputable def underResidueFieldMap_tower
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    (mM.under B).ResidueField →+* mM.ResidueField :=
  Ideal.ResidueField.map (mM.under B) mM (algebraMap B C) rfl

/-- In a tower as in Remark `15.113.11`, the order of the lower tame inertia quotient divides the
order of the upper tame inertia quotient. -/
theorem tameInertiaQuotient_card_dvd_of_tower
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    Nat.card (tameInertiaQuotient K (mM.under B)) ∣
      Nat.card (tameInertiaQuotient K mM) := by
  sorry

private noncomputable def scaledTameInertiaCharacterPowMap_tower
    (mM : Ideal (integralClosure A M)) [mM.IsMaximal] :
    rootsOfUnity (Nat.card (tameInertiaQuotient K mM)) mM.ResidueField →*
      rootsOfUnity (Nat.card (tameInertiaQuotient K (mM.under B))) mM.ResidueField :=
  rootsOfUnityPowMap (tameInertiaQuotient_card_dvd_of_tower K mM)

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
  sorry

end Tower

end
