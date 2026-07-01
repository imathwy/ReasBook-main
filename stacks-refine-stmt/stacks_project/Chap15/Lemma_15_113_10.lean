import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap15.Lemma_15_113_5
import stacks_project.Chap15.Lemma_15_111_11

-- Declarations for this item will be appended below by the statement pipeline.

open AlgEquiv CategoryTheory Ideal IsLocalRing
open scoped Pointwise

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [IsGalois K L]
variable {M : Type v} [Field M] [Algebra A M] [Algebra K M] [Algebra L M]
  [IsScalarTower A K M] [IsScalarTower K L M] [IsScalarTower A L M]
  [IsGalois K M]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A M
local notation "p" => IsLocalRing.maximalIdeal A
local notation "κA" => Ideal.ResidueField p

/- Domain-style sampling for Lemma 15.113.10:
- primary domain: decomposition, inertia, and wild inertia in towers of Galois extensions over
  integral closures in the discrete-valuation setting, together with the induced residue-field
  and tame-character comparison maps;
- sampled owner declarations:
  `restrictNormalHom_image_decompositionGroup_eq`,
  `restrictNormalHom_image_inertiaGroup_eq`,
  `IsFractionRing.stabilizerHom`,
  `tameInertiaCharacter`,
  `CategoryTheory.CommSq`,
  `CommRingCat.ofHom`,
  `MonCat.ofHom`,
  `wildInertiaSubgroup`,
  `MulAction.stabilizer`,
  `Ideal.inertia`;
- best owner abstraction: the tower restriction owner `restrictNormalHom` acting on the canonical
  subgroup owners `MulAction.stabilizer`, `Ideal.inertia`, and `wildInertiaSubgroup`, together
  with the residue-field action owner `IsFractionRing.stabilizerHom`, the source-facing tame
  inertia character owner `tameInertiaCharacter`, and the square owner `CommSq` for the two
  compatibility diagrams;
- primitive data: the tower-induced ring map `B →+* C` and a prime ideal `r : Ideal C`, with the
  maximal-ideal contraction `m = B ∩ m'`;
- derived API: the restriction-image equalities for decomposition, inertia, and wild inertia, and
  the two source-facing compatibility diagrams on residue fields and tame inertia characters.

Source/core/bridge triage:
- `source-facing`: the three numbered clauses of Lemma 15.113.10;
- `core/canonical`: `MulAction.stabilizer`, `Ideal.inertia`, `wildInertiaSubgroup`, and
  `restrictNormalHom`, `IsFractionRing.stabilizerHom`, and `tameInertiaCharacter`;
- `bridge/view`: contraction of `mC` along the canonical integral-closure map `B →+* C`.
-/

private noncomputable local instance : Algebra B C :=
  ((IsScalarTower.toAlgHom A L M).mapIntegralClosure : B →ₐ[A] C).toAlgebra

private local instance : IsScalarTower A B C := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  ext
  simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A L M]

private instance algebraIsIntegral_base : Algebra.IsIntegral A B :=
  IsIntegralClosure.isIntegral_algebra A L

private instance algebraIsIntegral_top : Algebra.IsIntegral A C :=
  IsIntegralClosure.isIntegral_algebra A M

private instance algebraIsIntegral_tower : Algebra.IsIntegral B C :=
  Algebra.IsIntegral.tower_top A

/-- The Galois group `Gal(L / K)` acts on the integral closure `B` through the induced
automorphisms of `L`. -/
private instance integralClosureMulSemiringAction_base :
    MulSemiringAction Gal(L / K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

/-- The Galois group `Gal(M / K)` acts on the integral closure `C` through the induced
automorphisms of `M`. -/
private instance integralClosureMulSemiringAction_top :
    MulSemiringAction Gal(M / K) C :=
  IsIntegralClosure.MulSemiringAction A K M C

private theorem integralClosure_smulCommClass_base :
    SMulCommClass Gal(L / K) A B := by
  sorry

private theorem integralClosure_smulCommClass_top :
    SMulCommClass Gal(M / K) A C := by
  sorry

attribute [local instance] integralClosure_smulCommClass_base
attribute [local instance] integralClosure_smulCommClass_top

private theorem integralClosure_isInvariant_base :
    Algebra.IsInvariant A B Gal(L / K) := by
  sorry

private theorem integralClosure_isInvariant_top :
    Algebra.IsInvariant A C Gal(M / K) := by
  sorry

attribute [local instance] integralClosure_isInvariant_base
attribute [local instance] integralClosure_isInvariant_top

private instance liesOver_maximalIdeal_base
    (mB : Ideal B) [mB.IsMaximal] : mB.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal mB)).symm⟩

private instance liesOver_maximalIdeal_top
    (mC : Ideal C) [mC.IsMaximal] : mC.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal mC)).symm⟩

private instance under_isMaximal
    (mC : Ideal C) [mC.IsMaximal] : (mC.under B).IsMaximal := by
  simpa [Ideal.under_def] using
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal mC :
      (Ideal.comap (algebraMap B C) mC).IsMaximal)

private instance residueFieldAlgebra_base
    (mB : Ideal B) [mB.IsMaximal] : Algebra κA mB.ResidueField :=
  inferInstance

private instance residueFieldAlgebra_top
    (mC : Ideal C) [mC.IsMaximal] : Algebra κA mC.ResidueField :=
  inferInstance

private noncomputable instance quotientResidueFieldAlgebra_base
    (mB : Ideal B) [mB.IsMaximal] : Algebra (A ⧸ p) mB.ResidueField :=
  ((Ideal.ResidueField.map p mB (algebraMap A B) (Ideal.over_def mB p)).comp
    (algebraMap (A ⧸ p) κA)).toAlgebra

private noncomputable instance quotientResidueFieldAlgebra_top
    (mC : Ideal C) [mC.IsMaximal] : Algebra (A ⧸ p) mC.ResidueField :=
  ((Ideal.ResidueField.map p mC (algebraMap A C) (Ideal.over_def mC p)).comp
    (algebraMap (A ⧸ p) κA)).toAlgebra

private noncomputable instance residueField_isScalarTower_base
    (mB : Ideal B) [mB.IsMaximal] : IsScalarTower (A ⧸ p) κA mB.ResidueField :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable instance residueField_isScalarTower_top
    (mC : Ideal C) [mC.IsMaximal] : IsScalarTower (A ⧸ p) κA mC.ResidueField :=
  IsScalarTower.of_algebraMap_eq' rfl

private theorem residueFieldMap_comp_quotient_base
    (mB : Ideal B) [mB.IsMaximal] :
    (Ideal.ResidueField.map p mB (algebraMap A B) (Ideal.over_def mB p)).comp
        (algebraMap (A ⧸ p) κA) =
      (algebraMap (B ⧸ mB) mB.ResidueField).comp (algebraMap (A ⧸ p) (B ⧸ mB)) := by
  sorry

private theorem residueFieldMap_comp_quotient_top
    (mC : Ideal C) [mC.IsMaximal] :
    (Ideal.ResidueField.map p mC (algebraMap A C) (Ideal.over_def mC p)).comp
        (algebraMap (A ⧸ p) κA) =
      (algebraMap (C ⧸ mC) mC.ResidueField).comp (algebraMap (A ⧸ p) (C ⧸ mC)) := by
  sorry

private noncomputable instance quotientResidueField_isScalarTower_base
    (mB : Ideal B) [mB.IsMaximal] : IsScalarTower (A ⧸ p) (B ⧸ mB) mB.ResidueField :=
  IsScalarTower.of_algebraMap_eq' (residueFieldMap_comp_quotient_base mB)

private noncomputable instance quotientResidueField_isScalarTower_top
    (mC : Ideal C) [mC.IsMaximal] : IsScalarTower (A ⧸ p) (C ⧸ mC) mC.ResidueField :=
  IsScalarTower.of_algebraMap_eq' (residueFieldMap_comp_quotient_top mC)

/- Lemma 15.113.10 (1): clause `(1)` is the canonical tower-compatibility statement for
decomposition groups under restriction, already recorded upstream in the more general prime-ideal
form `restrictNormalHom_image_decompositionGroup_eq`. -/
recall restrictNormalHom_image_decompositionGroup_eq

/- Lemma 15.113.10 (2): clause `(2)` is the corresponding canonical restriction-image statement
for inertia groups, already recorded upstream as
`restrictNormalHom_image_inertiaGroup_eq`. -/
recall restrictNormalHom_image_inertiaGroup_eq

omit [IsLocalRing A] in
theorem restrictNormalHom_mem_decompositionGroup
    (mC : Ideal C) [mC.IsMaximal]
    (σ : MulAction.stabilizer Gal(M/K) mC) :
    restrictNormalHom L σ.1 ∈ MulAction.stabilizer Gal(L/K) (mC.under B) := by
  have hσ :
      restrictNormalHom L σ.1 ∈
        Subgroup.map (restrictNormalHom L)
          (MulAction.stabilizer Gal(M / K) mC) :=
    ⟨σ.1, σ.2, rfl⟩
  simpa [restrictNormalHom_image_decompositionGroup_eq mC] using hσ

omit [IsLocalRing A] in
theorem restrictNormalHom_mem_inertiaGroup
    (mC : Ideal C) [mC.IsMaximal]
    (σ : mC.inertia Gal(M/K)) :
    restrictNormalHom L σ.1 ∈ (mC.under B).inertia Gal(L/K) := by
  have hσ :
      restrictNormalHom L σ.1 ∈
        Subgroup.map (restrictNormalHom L)
          (mC.inertia Gal(M / K)) :=
    ⟨σ.1, σ.2, rfl⟩
  simpa [restrictNormalHom_image_inertiaGroup_eq mC] using hσ

-- Proof sketch: this is the source-facing wild-inertia analogue of clause `(2)`, stated directly
-- on the ambient Galois groups so the public surface remains the canonical owner
-- `restrictNormalHom`.
/- Lemma 15.113.10 (3): if `m' ⊂ C` is maximal and `m = m' ∩ B`, then the induced restriction map
on inertia groups sends the wild inertia group of `m'` onto the wild inertia group of `m`. -/
omit [IsLocalRing A] in
theorem wildInertiaSubgroup_restrict_image_eq
    (mC : Ideal C) [mC.IsMaximal] :
    Subgroup.map (restrictNormalHom L) (wildInertiaSubgroup K mC) =
      wildInertiaSubgroup K (mC.under B) := by
  sorry

private noncomputable def underResidueFieldMap
    (mC : Ideal C) [mC.IsMaximal] :
    (mC.under B).ResidueField →+* mC.ResidueField :=
  Ideal.ResidueField.map (mC.under B) mC (algebraMap B C) rfl

private noncomputable def decompositionGroupRestriction
    (mC : Ideal C) [mC.IsMaximal]
    (σ : MulAction.stabilizer Gal(M/K) mC) :
    MulAction.stabilizer Gal(L/K) (mC.under B) :=
  ⟨restrictNormalHom L σ.1, restrictNormalHom_mem_decompositionGroup mC σ⟩

private noncomputable def decompositionGroupResidueFieldActionBase
    (mC : Ideal C) [mC.IsMaximal]
    (σ : MulAction.stabilizer Gal(M/K) mC) :
    (mC.under B).ResidueField →+* (mC.under B).ResidueField :=
  (IsFractionRing.stabilizerHom Gal(L/K) p (mC.under B) κA (mC.under B).ResidueField
    (decompositionGroupRestriction mC σ)).toRingEquiv.toRingHom

private noncomputable def decompositionGroupResidueFieldActionTop
    (mC : Ideal C) [mC.IsMaximal]
    (σ : MulAction.stabilizer Gal(M/K) mC) :
    mC.ResidueField →+* mC.ResidueField :=
  (IsFractionRing.stabilizerHom Gal(M/K) p mC κA mC.ResidueField σ).toRingEquiv.toRingHom

/- Lemma 15.113.10: the restriction map on decomposition groups is compatible with the induced
actions on the residue fields. This is the first commutative diagram in the source, stated
through the canonical square owner `CommSq` with the residue-field comparison map named
explicitly. -/
theorem decompositionGroup_residueFieldAction_comm
    (mC : Ideal C) [mC.IsMaximal]
    (σ : MulAction.stabilizer Gal(M/K) mC) :
    let κB := CommRingCat.of (mC.under B).ResidueField
    let κC := CommRingCat.of mC.ResidueField
    let actB : κB ⟶ κB := CommRingCat.ofHom (decompositionGroupResidueFieldActionBase mC σ)
    let res : κB ⟶ κC := CommRingCat.ofHom (underResidueFieldMap mC)
    let actC : κC ⟶ κC := CommRingCat.ofHom (decompositionGroupResidueFieldActionTop mC σ)
    CommSq actB res res actC := by
  sorry

section Tame

variable [IsDiscreteValuationRing A] [FiniteDimensional K L] [FiniteDimensional K M]

private noncomputable def inertiaRestrictionHom
    (mC : Ideal C) [mC.IsMaximal] :
    mC.inertia Gal(M/K) →* (mC.under B).inertia Gal(L/K) where
  toFun σ := ⟨restrictNormalHom L σ.1, restrictNormalHom_mem_inertiaGroup mC σ⟩
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp

private theorem ramificationIdxIn_under_dvd
    (mC : Ideal C) [mC.IsMaximal] :
    Ideal.ramificationIdxIn p B ∣ Ideal.ramificationIdxIn p C := by
  sorry

private noncomputable def baseResidueFieldRootsOfUnityMap
    (mC : Ideal C) [mC.IsMaximal] :
    rootsOfUnity (Ideal.ramificationIdxIn p B) (mC.under B).ResidueField →*
      rootsOfUnity (Ideal.ramificationIdxIn p B) mC.ResidueField :=
  restrictRootsOfUnity (underResidueFieldMap mC) (Ideal.ramificationIdxIn p B)

private abbrev relativeRamificationRootsOfUnityMap
    (mC : Ideal C) [mC.IsMaximal] :
    rootsOfUnity (Ideal.ramificationIdxIn p C) mC.ResidueField →*
      rootsOfUnity (Ideal.ramificationIdxIn p B) mC.ResidueField :=
  rootsOfUnityPowMap (ramificationIdxIn_under_dvd mC)

private noncomputable def tameInertiaCharacterBaseMap
    (mC : Ideal C) [mC.IsMaximal] :
    (mC.under B).inertia Gal(L/K) →*
      rootsOfUnity (Ideal.ramificationIdxIn p B) mC.ResidueField :=
  (baseResidueFieldRootsOfUnityMap mC).comp (tameInertiaCharacter K (mC.under B))

/-- Lemma 15.113.10: the canonical tame inertia characters for `m'` and `m = m' ∩ B` are
compatible with restriction along the tower. This is the second commutative diagram in the source,
expressed through the canonical square owner `CommSq` with the natural roots-of-unity comparison
maps named explicitly. -/
theorem tameInertiaCharacter_tower_compatible
    (mC : Ideal C) [mC.IsMaximal]
    :
    let ITop := MonCat.of (mC.inertia Gal(M/K))
    let IBase := MonCat.of ((mC.under B).inertia Gal(L/K))
    let muTop := MonCat.of (rootsOfUnity (Ideal.ramificationIdxIn p C) mC.ResidueField)
    let muBase := MonCat.of (rootsOfUnity (Ideal.ramificationIdxIn p B) mC.ResidueField)
    let ρ : ITop ⟶ IBase := MonCat.ofHom (inertiaRestrictionHom mC)
    let θTop : ITop ⟶ muTop := MonCat.ofHom (tameInertiaCharacter K mC)
    let θBase : IBase ⟶ muBase := MonCat.ofHom (tameInertiaCharacterBaseMap mC)
    let pow : muTop ⟶ muBase := MonCat.ofHom (relativeRamificationRootsOfUnityMap mC)
    CommSq ρ θTop θBase pow := by
  sorry

end Tame

end
