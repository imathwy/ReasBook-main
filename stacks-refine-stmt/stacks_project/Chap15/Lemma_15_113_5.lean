import Mathlib

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
