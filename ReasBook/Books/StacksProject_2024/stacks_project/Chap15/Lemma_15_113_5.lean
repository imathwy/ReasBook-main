import Mathlib
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap15.Lemma_15_112_4
import StacksProject_2024.Chap15.Lemma_15_113_2

-- Declarations for this item will be appended below by the statement pipeline.

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
  inferInstance

local instance integralClosureIdealMulAction :
    MulAction Gal(L/K) (Ideal B) :=
  Ideal.pointwiseDistribMulAction.toMulAction

variable (m : Ideal (integralClosure A L))

local notation "D" => MulAction.stabilizer Gal(L/K) m
local notation "I" => m.inertia Gal(L/K)

/-- Helper for Lemma 15.113.5: ideal-theoretic inertia membership is the pointwise congruence
condition modulo the ideal. -/
theorem ideal_inertia_mem_iff
    (J : Ideal B)
    (σ : Gal(L/K)) :
    σ ∈ Ideal.inertia Gal(L/K) J ↔
      ∀ x : B, σ • x - x ∈ J := by
  -- Route correction: unfold the owner `Ideal.inertia` once so the pointwise criterion is reused
  -- uniformly instead of fighting the competing ideal-action elaborations in each theorem.
  rfl

/-- An element of the Galois group lies in the wild inertia subgroup exactly when it acts
trivially on `B / m²`, equivalently when `σ(x) - x ∈ m²` for every `x ∈ B`. -/
theorem mem_wildInertiaSubgroup_iff
    (m : Ideal B)
    (σ : Gal(L/K)) :
    σ ∈ wildInertiaSubgroup K m ↔
      ∀ x : B, σ • x - x ∈ m ^ 2 := by
  -- The wild inertia subgroup is the inertia subgroup of the square ideal `m ^ 2`.
  simpa [wildInertiaSubgroup] using
    (ideal_inertia_mem_iff (K := K) (J := m ^ 2) σ)

/-- The wild inertia subgroup lies inside the inertia group. -/
theorem wildInertiaSubgroup_le_inertia (m : Ideal B) :
    wildInertiaSubgroup K m ≤ m.inertia Gal(L/K) := by
  -- Passing from `m²` to `m` is just monotonicity of the inertia condition.
  have hm_sq_le : m ^ 2 ≤ m := by
    simpa [pow_two] using (Ideal.mul_le_inf : m * m ≤ m ⊓ m)
  intro σ hσ
  rw [mem_wildInertiaSubgroup_iff] at hσ
  -- Unfold the defining congruence condition and weaken `m²`-membership to `m`-membership.
  rw [ideal_inertia_mem_iff]
  intro x
  exact hm_sq_le (hσ x)

/-- The wild inertia subgroup lies inside the decomposition group. -/
theorem wildInertiaSubgroup_le_decompositionGroup (m : Ideal B) :
    wildInertiaSubgroup K m ≤ MulAction.stabilizer Gal(L/K) m := by
  -- Follow the source route `P ≤ I ≤ D`: first weaken the congruence ideal, then use the
  -- canonical owner theorem `Ideal.inertia_le_stabilizer`.
  intro σ hσ
  exact
    (Ideal.inertia_le_stabilizer (M := Gal(L/K)) (R := B) m)
      ((wildInertiaSubgroup_le_inertia (K := K) m) hσ)

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

/-- Helper for Lemma 15.113.5: an element of the decomposition group stabilizes the square ideal
`m ^ 2` because ideal transport commutes with powers. -/
theorem stabilizer_preserves_ideal_square
    {τ : Gal(L/K)} (hτ : τ ∈ D) :
    τ • (m ^ 2) = m ^ 2 := by
  -- First rewrite the ideal action as transport along the ring automorphism induced by `τ`.
  have hτm : τ • m = m := MulAction.mem_stabilizer_iff.mp hτ
  calc
    τ • (m ^ 2) = Ideal.map (MulSemiringAction.toRingHom Gal(L/K) B τ) (m ^ 2) := by
      rw [Ideal.pointwise_smul_def]
    _ = Ideal.map (MulSemiringAction.toRingHom Gal(L/K) B τ) m ^ 2 := by
      rw [Ideal.map_pow]
    _ = (τ • m) ^ 2 := by
      rw [← Ideal.pointwise_smul_def]
    _ = m ^ 2 := by
      rw [hτm]

/-- The wild inertia subgroup is a normal subgroup of the decomposition group. -/
theorem wildInertiaSubgroup_normal_in_decompositionGroup :
    Subgroup.Normal
      ((wildInertiaSubgroup K m).subgroupOf D) := by
  have hPD : wildInertiaSubgroup K m ≤ D := by
    exact wildInertiaSubgroup_le_decompositionGroup (K := K) (m := m)
  rw [Subgroup.normal_subgroupOf_iff hPD]
  intro σ τ hσ hτ
  rw [mem_wildInertiaSubgroup_iff]
  intro x
  -- Apply the wild inertia condition to `τ⁻¹ • x` and then transport back along `τ`.
  have hcore :
      σ • (τ⁻¹ • x) - τ⁻¹ • x ∈ m ^ 2 :=
    (mem_wildInertiaSubgroup_iff (K := K) (m := m) σ).mp hσ (τ⁻¹ • x)
  have htransport :
      τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈ τ • (m ^ 2) := by
    rw [Ideal.pointwise_smul_def]
    exact Ideal.mem_map_of_mem (MulSemiringAction.toRingHom Gal(L/K) B τ) hcore
  -- The decomposition group fixes `m`, hence also fixes `m ^ 2`.
  have hsquare : τ • (m ^ 2) = m ^ 2 :=
    stabilizer_preserves_ideal_square (K := K) (m := m) hτ
  have htarget :
      τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈ m ^ 2 := by
    simpa [hsquare] using htransport
  -- This transported difference is exactly the conjugated action on `x`.
  simpa [smul_sub, smul_smul, mul_assoc] using htarget

/-- The wild inertia subgroup is normal inside the inertia group, so the tame inertia quotient is
well defined. -/
instance wildInertiaSubgroup_normalInst :
    Subgroup.Normal
      ((wildInertiaSubgroup K m).subgroupOf I) := by
  have hPI : wildInertiaSubgroup K m ≤ I :=
    wildInertiaSubgroup_le_inertia (K := K) m
  have hPD : wildInertiaSubgroup K m ≤ D := by
    exact wildInertiaSubgroup_le_decompositionGroup (K := K) (m := m)
  rw [Subgroup.normal_subgroupOf_iff hPI]
  intro σ τ hσ hτ
  -- Reuse the already-proved conjugation stability in the larger decomposition group.
  exact
    (Subgroup.normal_subgroupOf_iff hPD).mp
      (wildInertiaSubgroup_normal_in_decompositionGroup (K := K) (m := m))
      σ τ hσ ((Ideal.inertia_le_stabilizer m) hτ)

section Tame

variable [IsDiscreteValuationRing A] [FiniteDimensional K L] [m.IsMaximal]
variable (K)

local notation "p" => maximalIdeal A
local notation "e" => Ideal.ramificationIdxIn p B
local notation "C" => Localization.AtPrime m

/-- Helper for Lemma 15.113.5: a maximal ideal of the integral closure of the discrete valuation
ring `A` lies over `maximalIdeal A`. This is the local branch input for the localization
`A → B_m`. -/
private local instance liesOver_maximalIdeal_of_isMaximal :
    m.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

/-- Helper for Lemma 15.113.5: the localized branch `C = B_m` is a discrete valuation ring. This
is the source-faithful branch-DVR package used before choosing a branch uniformizer. -/
private theorem branchLocalization_isDiscreteValuationRing
    (K0 : Type v) [Field K0] [Algebra A K0] [IsFractionRing A K0]
    [Algebra K0 L] [IsScalarTower A K0 L] [FiniteDimensional K0 L] [IsGalois K0 L] :
    IsDiscreteValuationRing C := by
  -- Localize the Dedekind normalization of `A` at the chosen maximal branch `m`.
  let _ : IsFractionRing B L :=
    integralClosure.isFractionRing_of_finite_extension K0 L
  let _ : Module.Finite A B :=
    IsIntegralClosure.finite A K0 L B
  let _ : IsDedekindDomain B :=
    integralClosure.isDedekindDomain A K0 L
  have hinjAB : Function.Injective (algebraMap A B) :=
    algebraMap_injective_of_field_isFractionRing A B K0 L
  have hm_ne : m ≠ (⊥ : Ideal B) := by
    intro hm
    have hp_bot : p = (⊥ : Ideal A) := by
      have hcomap_bot : Ideal.comap (algebraMap A B) (⊥ : Ideal B) = (⊥ : Ideal A) := by
        ext a
        simp only [Ideal.mem_comap, Ideal.mem_bot]
        constructor
        · intro ha
          exact hinjAB (by simpa using ha)
        · intro ha
          simpa [ha]
      calc
        p = m.under A := m.over_def p
        _ = ⊥ := by
          simpa [Ideal.under, hm] using hcomap_bot
    exact (IsDiscreteValuationRing.not_a_field A) hp_bot
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hm_ne C

/-- Helper for Lemma 15.113.5: in any local ring, the maximal-ideal residue field agrees with the
ambient residue field. This is the standard bridge used below for the localized branch `C`. -/
private noncomputable abbrev maximalIdeal_residueField_equiv
    (R : Type*) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Lemma 15.113.5: localizing the chosen branch at `m` does not change the residue
field. This is the branch residue-field identification used to transport the source character from
`C` back to `κ(m)`. -/
private noncomputable abbrev branchLocalization_maximalResidueField_equiv :
    (maximalIdeal C).ResidueField ≃+* m.ResidueField := by
  -- Reinterpret the prime residue field of `m` as the maximal-ideal residue field of its
  -- localization.
  change (maximalIdeal (Localization.AtPrime m)).ResidueField ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime m)
  exact maximalIdeal_residueField_equiv (Localization.AtPrime m)

/-- Helper for Lemma 15.113.5: localizing the chosen branch at `m` does not change the residue
field. This is the branch residue-field identification used to transport the source character from
`C` back to `κ(m)`. -/
private noncomputable abbrev branchLocalization_residueField_ringEquiv :
    ResidueField C ≃+* m.ResidueField :=
  -- Reinterpret the local residue field as the prime-ideal residue field of the original branch.
  (maximalIdeal_residueField_equiv C).symm.trans
    (branchLocalization_maximalResidueField_equiv (m := m))

/-- Helper for Lemma 15.113.5: the standard identification between the maximal-ideal residue field
of a local ring and its ambient residue field sends residue classes of elements to the canonical
local residue classes. -/
private theorem maximalIdeal_residueField_equiv_apply_algebraMap
    (R : Type*) [CommRing R] [IsLocalRing R] (a : R) :
    maximalIdeal_residueField_equiv R (algebraMap R (maximalIdeal R).ResidueField a) =
      IsLocalRing.residue R a := by
  -- Compare both sides through the inverse quotient/residue-field equivalence.
  rw [show algebraMap R (maximalIdeal R).ResidueField a =
      algebraMap (ResidueField R) (maximalIdeal R).ResidueField (IsLocalRing.residue R a) by rfl]
  change
    maximalIdeal_residueField_equiv R
        ((maximalIdeal_residueField_equiv R).symm (IsLocalRing.residue R a)) =
      IsLocalRing.residue R a
  exact (maximalIdeal_residueField_equiv R).apply_symm_apply (IsLocalRing.residue R a)

/-- Helper for Lemma 15.113.5: the maximal ideal of the localized branch is the extension of `m`.
This fixes the main ideal owner before transporting congruence statements from `B` to `C`. -/
private theorem branchLocalization_map_eq_maximalIdeal :
    Ideal.map (algebraMap B C) m = maximalIdeal C := by
  -- In a localization at a prime, the extended prime is exactly the closed point.
  simpa using IsLocalization.AtPrime.map_eq_maximalIdeal m C

/-- Helper for Lemma 15.113.5: localizing `m²` identifies it with the square of the maximal ideal
of the branch `C`. This is the canonical-form rewrite needed for the mod-`m²` kernel step. -/
private theorem branchLocalization_map_square :
    Ideal.map (algebraMap B C) (m ^ 2) = maximalIdeal C ^ 2 := by
  -- First move powers across localization, then rewrite the localized branch ideal.
  calc
    Ideal.map (algebraMap B C) (m ^ 2) = Ideal.map (algebraMap B C) m ^ 2 := by
      rw [Ideal.map_pow]
    _ = maximalIdeal C ^ 2 := by
      rw [branchLocalization_map_eq_maximalIdeal (m := m)]

/-- Helper for Lemma 15.113.5: a decomposition-group element transports the branch ideal `m`
to itself as an actual ideal map. This is the exact localizing hypothesis for the branch action on
`C = B_m`. -/
private theorem branchLocalization_stabilizer_map_eq_self
    (σ : D) :
    Ideal.map (MulSemiringAction.toRingHom Gal(L/K) B σ.1) m = m := by
  -- Unpack the stabilizer condition and rewrite the ideal action as the induced ideal map.
  simpa [Ideal.pointwise_smul_def] using MulAction.mem_stabilizer_iff.mp σ.2

/-- Helper for Lemma 15.113.5: the branch ideal also satisfies the needed comap equality under a
decomposition-group element. This is the canonical input for `Localization.localRingHom`. -/
private theorem branchLocalization_stabilizer_comap_eq_self
    (σ : D) :
    m = Ideal.comap (MulSemiringAction.toRingHom Gal(L/K) B σ.1) m := by
  let eB : B ≃ₐ[A] B := MulSemiringAction.toAlgEquiv A B σ.1
  have hmap :
      Ideal.map eB.toRingHom m = m :=
    by
      simpa [Ideal.pointwise_smul_def] using MulAction.mem_stabilizer_iff.mp σ.2
  -- Convert the ideal-map equality into the comap equality required by localization.
  calc
    m = Ideal.comap eB.toRingHom (Ideal.map eB.toRingHom m) := by
      simpa using
        (m.comap_map_of_bijective eB.toRingEquiv eB.toRingEquiv.bijective).symm
    _ = Ideal.comap eB.toRingHom m := by
      rw [hmap]

/-- Helper for Lemma 15.113.5: a decomposition-group element acts on the localized branch
`C = B_m` by the canonical localized `A`-algebra endomorphism. This is the source owner for the
formula `σ(π_C) = u_σ π_C`. -/
private noncomputable def branchLocalizationAlgHom
    (σ : D) :
    C →ₐ[A] C where
  toRingHom :=
    Localization.localRingHom
      m m
      (MulSemiringAction.toRingHom Gal(L/K) B σ.1)
      (branchLocalization_stabilizer_comap_eq_self
        (A := A) (K := K) (L := L) (m := m) (σ := σ))
  commutes' a := by
    -- Reduce the localized action on `A`-scalars to the original `A`-linearity of `σ`.
    change
      Localization.localRingHom
          m m
          (MulSemiringAction.toRingHom Gal(L/K) B σ.1)
          (branchLocalization_stabilizer_comap_eq_self
            (A := A) (K := K) (L := L) (m := m) (σ := σ))
          (algebraMap B C (algebraMap A B a)) =
        algebraMap B C (algebraMap A B a)
    rw [Localization.localRingHom_to_map]
    exact congrArg (algebraMap B C) ((MulSemiringAction.toAlgEquiv A B σ.1).commutes a)

/-- Helper for Lemma 15.113.5: the localized branch action extends the original Galois action on
elements coming from `B`. -/
private theorem branchLocalizationAlgHom_apply_algebraMap
    (σ : D) (x : B) :
    branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ (algebraMap B C x) =
      algebraMap B C (σ.1 • x) := by
  -- `Localization.localRingHom` is characterized by its value on base elements.
  have hcomap :
      m = Ideal.comap (MulSemiringAction.toRingHom Gal(L/K) B σ.1) m :=
    branchLocalization_stabilizer_comap_eq_self
      (A := A) (K := K) (L := L) (m := m) (σ := σ)
  change
    Localization.localRingHom
        m m
        (MulSemiringAction.toRingHom Gal(L/K) B σ.1)
        hcomap
        (algebraMap B C x) =
      algebraMap B C (σ.1 • x)
  calc
    Localization.localRingHom
        m m
        (MulSemiringAction.toRingHom Gal(L/K) B σ.1)
        hcomap
        (algebraMap B C x) =
      algebraMap B C ((MulSemiringAction.toRingHom Gal(L/K) B σ.1) x) := by
        rw [Localization.localRingHom_to_map]
    _ = algebraMap B C (σ.1 • x) := by
      rfl

/-- Helper for Lemma 15.113.5: the localized branch action is multiplicative in the
decomposition-group variable. This is the action law needed before defining the tame character
from a uniformizer of `C = B_m`. -/
private theorem branchLocalizationAlgHom_mul
    (σ τ : D) :
    branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) (σ * τ) =
      (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ).comp
        (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) τ) := by
  -- First prove equality on the underlying localized ring homomorphisms.
  have hring :
      (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) (σ * τ)).toRingHom =
        ((branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ).comp
          (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) τ)).toRingHom := by
    change
      Localization.localRingHom
          m m
          (MulSemiringAction.toRingHom Gal(L/K) B (σ * τ).1)
          (branchLocalization_stabilizer_comap_eq_self
            (A := A) (K := K) (L := L) (m := m) (σ := σ * τ)) =
        ((branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ).comp
          (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) τ)).toRingHom
    apply Localization.localRingHom_unique
    intro x
    -- Reduce the comparison to the action law on the original Galois action on `B`.
    change
      branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ
          (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) τ
            (algebraMap B C x)) =
        algebraMap B C ((MulSemiringAction.toRingHom Gal(L/K) B (σ * τ).1) x)
    rw [branchLocalizationAlgHom_apply_algebraMap, branchLocalizationAlgHom_apply_algebraMap]
    rfl
  -- Algebra homomorphisms agree once their underlying ring maps agree.
  apply DFunLike.ext
  intro z
  exact congrArg (fun f : C →+* C => f z) hring

/-- Helper for Lemma 15.113.5: an association can be rewritten as equality up to a unit factor on
the left. -/
private theorem eq_unit_mul_of_associated {M : Type*} [CommMonoid M] {x y : M}
    (hxy : Associated x y) :
    ∃ u : Units M, x = (u : M) * y := by
  -- Reverse the association so the displayed unit multiplies the target into the source.
  rcases hxy.symm with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  simpa [mul_comm] using hu.symm

/-- Helper for Lemma 15.113.5: the localized branch action of the identity stabilizer element is
the identity endomorphism of `C = B_m`. -/
private theorem branchLocalizationAlgHom_one :
    branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) (1 : D) = AlgHom.id A C := by
  -- The localization action is determined by its values on the image of `B`.
  have hring :
      (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) (1 : D)).toRingHom =
        (AlgHom.id A C).toRingHom := by
    apply IsLocalization.ringHom_ext m.primeCompl
    ext x
    simp [RingHom.comp_apply, branchLocalizationAlgHom_apply_algebraMap]
  apply DFunLike.ext
  intro z
  exact congrArg (fun f : C →+* C ↦ f z) hring

/-- Helper for Lemma 15.113.5: composing the localized branch action of `σ` with that of `σ⁻¹`
gives the identity. This is the right-inverse identity used to prove branch bijectivity. -/
private theorem branchLocalizationAlgHom_comp_inv
    (σ : D) :
    (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ).comp
        (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ⁻¹) =
      AlgHom.id A C := by
  -- The multiplicative action law reduces the composition to the identity element of `D`.
  calc
    (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ).comp
        (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ⁻¹) =
      branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) (σ * σ⁻¹) := by
        symm
        exact branchLocalizationAlgHom_mul (A := A) (K := K) (L := L) (m := m) σ σ⁻¹
    _ = branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) (1 : D) := by
        simp
    _ = AlgHom.id A C := branchLocalizationAlgHom_one (A := A) (K := K) (L := L) (m := m)

/-- Helper for Lemma 15.113.5: composing the localized branch action of `σ⁻¹` with that of `σ`
also gives the identity. This is the left-inverse identity used to prove branch bijectivity. -/
private theorem branchLocalizationAlgHom_inv_comp
    (σ : D) :
    (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ⁻¹).comp
        (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ) =
      AlgHom.id A C := by
  -- The inverse-first composition is the same multiplicative reduction with the factors swapped.
  calc
    (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ⁻¹).comp
        (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ) =
      branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) (σ⁻¹ * σ) := by
        symm
        exact branchLocalizationAlgHom_mul (A := A) (K := K) (L := L) (m := m) σ⁻¹ σ
    _ = branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) (1 : D) := by
        simp
    _ = AlgHom.id A C := branchLocalizationAlgHom_one (A := A) (K := K) (L := L) (m := m)

/-- Helper for Lemma 15.113.5: every localized branch action is bijective, with inverse given by
the action of the inverse decomposition-group element. -/
private theorem branchLocalizationAlgHom_bijective
    (σ : D) :
    Function.Bijective (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h' :=
      congrArg
        (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ⁻¹)
        hxy
    change
      ((branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ⁻¹).comp
          (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ)) x =
        ((branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ⁻¹).comp
          (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ)) y at h'
    rw [branchLocalizationAlgHom_inv_comp (A := A) (K := K) (L := L) (m := m) σ] at h'
    simpa using h'
  · intro z
    refine ⟨branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ⁻¹ z, ?_⟩
    have h :=
      congrArg
        (fun f : C →ₐ[A] C ↦ f z)
        (branchLocalizationAlgHom_comp_inv (A := A) (K := K) (L := L) (m := m) σ)
    simpa [AlgHom.comp_apply] using h

/-- Helper for Lemma 15.113.5: each localized branch action is a local ring homomorphism. This is
the owner fact needed to transport maximal ideals under the branch action. -/
private theorem branchLocalizationAlgHom_isLocalHom
    (σ : D) :
    IsLocalHom
      (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ).toRingHom := by
  -- `branchLocalizationAlgHom` is built from the canonical local map on the localization at `m`.
  simpa [branchLocalizationAlgHom] using
    (Localization.isLocalHom_localRingHom
      m m
      (MulSemiringAction.toRingHom Gal(L/K) B σ.1)
      (branchLocalization_stabilizer_comap_eq_self
        (A := A) (K := K) (L := L) (m := m) (σ := σ)))

/-- Helper for Lemma 15.113.5: every localized branch action sends the maximal ideal of `C = B_m`
to itself. This is the ideal-theoretic input for the uniformizer-ratio construction. -/
private theorem branchLocalization_map_maximalIdeal
    (σ : D) :
    Ideal.map
        (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ).toRingHom
        (maximalIdeal C) =
      maximalIdeal C := by
  -- Surjective local endomorphisms of a local ring preserve the maximal ideal exactly.
  let _ :
      IsLocalHom
        (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ).toRingHom :=
    branchLocalizationAlgHom_isLocalHom (A := A) (K := K) (L := L) (m := m) σ
  exact IsLocalRing.map_maximalIdeal_of_surjective
    (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ).toRingHom
    (branchLocalizationAlgHom_bijective (A := A) (K := K) (L := L) (m := m) σ).2

/-- Helper for Lemma 15.113.5: a decomposition-group element sends a chosen branch uniformizer to
a unit multiple of that same uniformizer. This is the missing structural package behind the source
formula `σ(π_C) = θ_σ π_C`. -/
private theorem branch_uniformizer_ratio_unit
    (πC : C)
    (hπC : maximalIdeal C = Ideal.span ({πC} : Set C))
    (σ : D) :
    ∃ u : Units C,
      branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ πC = (u : C) * πC := by
  -- First show that the image of the chosen uniformizer generates the same maximal ideal.
  have hspan :
      Ideal.span
          ({branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ πC} : Set C) =
        Ideal.span ({πC} : Set C) := by
    calc
      Ideal.span
          ({branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ πC} : Set C) =
        Ideal.map
          (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ).toRingHom
          (Ideal.span ({πC} : Set C)) := by
            simpa [Set.image_singleton] using
              (Ideal.map_span
                ((branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ).toRingHom)
                ({πC} : Set C)).symm
      _ =
        Ideal.map
          (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ).toRingHom
          (maximalIdeal C) := by
            rw [← hπC]
      _ = maximalIdeal C := by
            exact branchLocalization_map_maximalIdeal
              (A := A) (K := K) (L := L) (m := m) σ
      _ = Ideal.span ({πC} : Set C) := by
            rw [hπC]
  -- Then read equality of principal ideals as association and unwrap the association into a unit.
  exact eq_unit_mul_of_associated ((Ideal.span_singleton_eq_span_singleton).mp hspan)

/-- Helper for Lemma 15.113.5: for every decomposition-group element, one can choose a branch
uniformizer whose image differs by a unit factor. This packages the exact source datum
`σ(π_C) = u_σ π_C` without yet constructing the tame character. -/
private theorem exists_branch_uniformizer_ratio_unit
    (σ : D) :
    ∃ πC : C, maximalIdeal C = Ideal.span ({πC} : Set C) ∧
      ∃ u : Units C,
        branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m) σ πC = (u : C) * πC := by
  -- First choose a branch uniformizer, then apply the already-proved ratio-unit lemma.
  let _ : IsDiscreteValuationRing C :=
    branchLocalization_isDiscreteValuationRing
      (A := A) (L := L) (m := m) (K0 := K)
  obtain ⟨πC, -, hπC⟩ := exists_uniformizer_generator C
  obtain ⟨u, hu⟩ :=
    branch_uniformizer_ratio_unit (A := A) (K := K) (L := L) (m := m) πC hπC σ
  exact ⟨πC, hπC, u, hu⟩

/-- Helper for Lemma 15.113.5: the residue-field action of a decomposition-group element on the
original branch residue field `κ(m)` is the canonical map induced by the stabilized ideal `m`. -/
private noncomputable def decompositionGroupResidueFieldMap
    (σ : D) :
    m.ResidueField →+* m.ResidueField :=
  Ideal.ResidueField.map m m
    (MulSemiringAction.toRingHom Gal(L/K) B σ.1)
    (branchLocalization_stabilizer_comap_eq_self
      (A := A) (K := K) (L := L) (m := m) (σ := σ))

/-- Helper for Lemma 15.113.5: inertia fixes every residue class coming from `B`. This is the
pointwise residue-field input needed before transporting the action to the localized branch
`C = B_m`. -/
private theorem inertia_residueFieldMap_apply_algebraMap
    (σ : I) (x : B) :
    decompositionGroupResidueFieldMap (A := A) (K := K) (L := L) (m := m)
        ⟨σ.1, (Ideal.inertia_le_stabilizer m) σ.2⟩ ((algebraMap B m.ResidueField) x) =
      (algebraMap B m.ResidueField) x := by
  -- First rewrite the residue-field action on generators to the original Galois action on `B`.
  rw [decompositionGroupResidueFieldMap, Ideal.ResidueField.map_algebraMap]
  -- Then use the defining inertia congruence modulo `m`.
  have hσ := σ.2
  rw [ideal_inertia_mem_iff] at hσ
  have hquot : Ideal.Quotient.mk m (σ.1 • x) = Ideal.Quotient.mk m x :=
    Ideal.Quotient.eq.mpr (hσ x)
  change
    (algebraMap (B ⧸ m) m.ResidueField) (Ideal.Quotient.mk m (σ.1 • x)) =
      (algebraMap (B ⧸ m) m.ResidueField) (Ideal.Quotient.mk m x)
  exact congrArg (algebraMap (B ⧸ m) m.ResidueField) hquot

/-- Helper for Lemma 15.113.5: the canonical branch-local residue map `C → κ(m)` is the local
residue map of `C`, viewed through the branch residue-field identification. -/
private noncomputable def branchLocalizationResidueRingHom :
    C →+* m.ResidueField :=
  (branchLocalization_residueField_ringEquiv (m := m)).toRingHom.comp
    (algebraMap C (ResidueField C))

/-- Helper for Lemma 15.113.5: the branch-local residue map sends elements coming from `B` to
their usual residue classes modulo `m`. -/
private theorem branchLocalizationResidueRingHom_apply_algebraMap
    (x : B) :
    branchLocalizationResidueRingHom (m := m) (algebraMap B C x) =
      algebraMap B m.ResidueField x := by
  -- Unfold the branch residue map and identify both sides with the same local residue class.
  unfold branchLocalizationResidueRingHom
  change branchLocalization_residueField_ringEquiv (m := m)
      (algebraMap C (ResidueField C) (algebraMap B C x)) =
    algebraMap B m.ResidueField x
  change branchLocalization_maximalResidueField_equiv (m := m)
      ((maximalIdeal_residueField_equiv C).symm
        (IsLocalRing.residue C (algebraMap B C x))) =
    algebraMap B m.ResidueField x
  calc
    branchLocalization_maximalResidueField_equiv (m := m)
        ((maximalIdeal_residueField_equiv C).symm
          (IsLocalRing.residue C (algebraMap B C x))) =
      IsLocalRing.residue C (algebraMap B C x) := by
        simpa using
          maximalIdeal_residueField_equiv_apply_algebraMap
            (R := C) (a := algebraMap B C x)
    _ = algebraMap B m.ResidueField x := by
      rfl

/-- Helper for Lemma 15.113.5: vanishing under the branch-local residue map is exactly membership
in the maximal ideal of the localized branch. -/
private theorem branchLocalizationResidueRingHom_eq_zero_iff
    (z : C) :
    branchLocalizationResidueRingHom (m := m) z = 0 ↔ z ∈ maximalIdeal C := by
  -- The branch residue map is the ordinary local residue map of `C`, up to an equivalence.
  unfold branchLocalizationResidueRingHom
  change branchLocalization_residueField_ringEquiv (m := m)
      ((IsLocalRing.residue C z : ResidueField C)) = 0 ↔
    z ∈ maximalIdeal C
  rw [RingEquiv.map_eq_zero_iff]
  simpa using (IsLocalRing.residue_eq_zero_iff (R := C) (a := z))

/-- Helper for Lemma 15.113.5: after passing to the branch-local residue field, inertia acts
trivially on the localization `C = B_m`. -/
private theorem branchLocalizationResidueRingHom_comp_branchLocalization
    (σ : I) :
    (branchLocalizationResidueRingHom (m := m)).comp
        (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m)
          ⟨σ.1, (Ideal.inertia_le_stabilizer m) σ.2⟩).toRingHom =
      branchLocalizationResidueRingHom (m := m) := by
  -- Compare the two maps on the dense image of `B` inside the localization `C`.
  apply IsLocalization.ringHom_ext m.primeCompl
  ext x
  change
      branchLocalizationResidueRingHom (m := m)
        (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m)
          ⟨σ.1, (Ideal.inertia_le_stabilizer m) σ.2⟩ (algebraMap B C x)) =
    branchLocalizationResidueRingHom (m := m) (algebraMap B C x)
  rw [branchLocalizationAlgHom_apply_algebraMap, branchLocalizationResidueRingHom_apply_algebraMap,
    branchLocalizationResidueRingHom_apply_algebraMap]
  -- On generators from `B`, this is exactly the defining congruence modulo `m`.
  have hσ := σ.2
  rw [ideal_inertia_mem_iff] at hσ
  have hquot : Ideal.Quotient.mk m (σ.1 • x) = Ideal.Quotient.mk m x :=
    Ideal.Quotient.eq.mpr (hσ x)
  change
    (algebraMap (B ⧸ m) m.ResidueField) (Ideal.Quotient.mk m (σ.1 • x)) =
      (algebraMap (B ⧸ m) m.ResidueField) (Ideal.Quotient.mk m x)
  exact congrArg (algebraMap (B ⧸ m) m.ResidueField) hquot

/-- Helper for Lemma 15.113.5: inertia translates of branch-local elements differ from the
identity by an element of the maximal ideal of `C = B_m`. This is the direct localized form of the
source statement that inertia acts trivially on the residue field. -/
private theorem inertia_branchLocalization_sub_mem_maximalIdeal
    (σ : I) (z : C) :
    branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m)
        ⟨σ.1, (Ideal.inertia_le_stabilizer m) σ.2⟩ z - z ∈ maximalIdeal C := by
  -- First compare the residue classes of `z` and its inertia translate.
  have hres :
      branchLocalizationResidueRingHom (m := m)
        (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m)
          ⟨σ.1, (Ideal.inertia_le_stabilizer m) σ.2⟩ z) =
      branchLocalizationResidueRingHom (m := m) z := by
    have hcomp :=
      branchLocalizationResidueRingHom_comp_branchLocalization
        (A := A) (K := K) (L := L) (m := m) σ
    exact congrArg (fun f : C →+* m.ResidueField => f z) hcomp
  -- Then read equality of residues as maximal-ideal membership of the difference.
  have hzero :
      branchLocalizationResidueRingHom (m := m)
        (branchLocalizationAlgHom (A := A) (K := K) (L := L) (m := m)
          ⟨σ.1, (Ideal.inertia_le_stabilizer m) σ.2⟩ z - z) = 0 := by
    rw [(branchLocalizationResidueRingHom (m := m)).map_sub]
    rw [hres, sub_self]
  exact (branchLocalizationResidueRingHom_eq_zero_iff (m := m) _).mp hzero

-- Proof sketch: construct the tame inertia homomorphism using the action on a uniformizer of the
-- localization `B_m`, identify its kernel with `P`, and prove surjectivity onto `μ_e(κ(m))`.
-- TODO: the source-faithful branch data now includes the localized action owner
-- `branchLocalizationAlgHom σ : C →ₐ[A] C`, its composition law, and the pointwise residue
-- triviality of inertia on the branch localization `C = B_m` itself via
-- `inertia_branchLocalization_sub_mem_maximalIdeal`. The remaining blocker is the genuine
-- uniformizer/DVR step: package this residue-trivial action into the branch character
-- `I → μ_e(κ(m))`, prove its kernel is the mod-`m²` condition, and then finish the
-- cardinality/surjectivity squeeze from Lemmas `15.113.2` and `15.113.4`.
private theorem exists_tameInertiaCharacterHom (m : Ideal B) [m.IsMaximal] :
    ∃ θ : m.inertia Gal(L/K) →* rootsOfUnity e m.ResidueField,
      θ.ker = (wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L/K)) ∧
        Function.Surjective θ := sorry

private theorem exists_tameInertiaQuotientMulEquiv
    (m : Ideal B) [m.IsMaximal] :
    ∃ eθ : tameInertiaQuotient K m ≃* rootsOfUnity e m.ResidueField,
      ∃ θ : m.inertia Gal(L/K) →* rootsOfUnity e m.ResidueField,
        θ.ker = (wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L/K)) ∧
          Function.Surjective θ ∧
          ∀ σ : m.inertia Gal(L/K), eθ (QuotientGroup.mk σ) = θ σ := by
  rcases exists_tameInertiaCharacterHom K m with ⟨θ, hker, hsurj⟩
  let eθ : tameInertiaQuotient K m ≃* rootsOfUnity e m.ResidueField :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hsurj)
  refine ⟨eθ, ?_⟩
  refine ⟨θ, hker, hsurj, ?_⟩
  intro σ
  change
    (QuotientGroup.quotientKerEquivOfSurjective θ hsurj)
        ((QuotientGroup.quotientMulEquivOfEq hker.symm) (QuotientGroup.mk σ)) =
      θ σ
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- Lemma 15.113.5: the tame inertia quotient `I_t = I / P` is canonically identified with the
group `μ_e(κ(m))` of `e`th roots of unity in the residue field, where
`e = Ideal.ramificationIdxIn (maximalIdeal A) B`. -/
noncomputable def tameInertiaQuotientMulEquiv (m : Ideal B) [m.IsMaximal] :
    tameInertiaQuotient K m ≃* rootsOfUnity e m.ResidueField :=
  Classical.choose (exists_tameInertiaQuotientMulEquiv K m)

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
