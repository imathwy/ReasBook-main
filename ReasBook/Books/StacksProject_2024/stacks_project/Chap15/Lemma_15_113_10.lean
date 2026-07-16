import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap15.Lemma_15_113_5

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

private noncomputable local instance : Algebra B C :=
  ((IsScalarTower.toAlgHom A L M).mapIntegralClosure : B →ₐ[A] C).toAlgebra

private local instance integralClosureMulSemiringAction_top :
    MulSemiringAction Gal(M/K) C :=
  IsIntegralClosure.MulSemiringAction A K M C

private local instance integralClosureMulSemiringAction_base :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

private local instance : IsScalarTower A B C := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  ext
  simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A L M]

private instance algebraIsIntegral_tower : Algebra.IsIntegral B C :=
  Algebra.IsIntegral.tower_top A

/-- Helper for Lemma 15.113.10: a maximal ideal of the upper integral closure lies over the
maximal ideal of the base local ring. -/
private local instance top_liesOver_maximalIdeal
    (mC : Ideal C) [mC.IsMaximal] : mC.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal mC)).symm⟩

/-- Helper for Lemma 15.113.10: the contracted maximal ideal also lies over the maximal ideal of
the base local ring. -/
private local instance under_liesOver_maximalIdeal
    (mC : Ideal C) [mC.IsMaximal] : (mC.under B).LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (mC.under B))).symm⟩

/-- Helper for Lemma 15.113.10: the upper residue field is naturally a `κ_A`-algebra. -/
private local instance top_residueFieldAlgebra
    (mC : Ideal C) [mC.IsMaximal] : Algebra κA mC.ResidueField :=
  inferInstance

/-- Helper for Lemma 15.113.10: the lower residue field is naturally a `κ_A`-algebra. -/
private local instance under_residueFieldAlgebra
    (mC : Ideal C) [mC.IsMaximal] : Algebra κA (mC.under B).ResidueField :=
  inferInstance

/-- Helper for Lemma 15.113.10: the lower branch obtained by contraction of a maximal ideal of
`C` is again maximal in `B`. -/
private instance under_isMaximal
    (mC : Ideal C) [mC.IsMaximal] : (mC.under B).IsMaximal := by
  simpa [Ideal.under_def] using
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal mC :
      (Ideal.comap (algebraMap B C) mC).IsMaximal)

/-- Helper for Lemma 15.113.10: the canonical map on residue fields induced by `B → C`. -/
private noncomputable def underResidueFieldMap
    (mC : Ideal C) [mC.IsMaximal] :
    (mC.under B).ResidueField →+* mC.ResidueField :=
  -- This is the canonical residue-field map attached to the tower map `B → C`.
  Ideal.ResidueField.map (mC.under B) mC (algebraMap B C) rfl

/-- Helper for Lemma 15.113.10: the tower map on integral closures intertwines the upper Galois
action with the restricted lower action. -/
private theorem smul_algebraMap_eq_algebraMap_restrictNormalHom_smul
    (τ : Gal(M/K)) (b : B) :
    τ • algebraMap B C b = algebraMap B C (restrictNormalHom L τ • b) := by
  -- Compare the two integral-closure elements in the ambient field `M`.
  ext
  simpa [AlgEquiv.smul_def] using
    (AlgEquiv.restrictNormal_commutes (χ := τ) (E := L) (x := (b : L))).symm

/-- Helper for Lemma 15.113.10: contraction commutes with the action of a restricted Galois
element along the tower. -/
private theorem under_smul_eq_restrictNormalHom_smul_under
    (τ : Gal(M/K)) (mC : Ideal C) :
    (τ • mC).under B = restrictNormalHom L τ • (mC.under B) := by
  -- Compare ideal membership after rewriting both actions through the tower map `B → C`.
  ext b
  constructor
  · intro hb
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hb_top : algebraMap B C b ∈ τ • mC := by
      simpa [Ideal.under_def] using hb
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb_top
    have htop :
        algebraMap B C ((restrictNormalHom L τ)⁻¹ • b) ∈ mC := by
      simpa [smul_algebraMap_eq_algebraMap_restrictNormalHom_smul, mul_smul] using hb_top
    simpa [Ideal.under_def] using htop
  · intro hb
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
    have hb_top :
        algebraMap B C ((restrictNormalHom L τ)⁻¹ • b) ∈ mC := by
      simpa [Ideal.under_def] using hb
    have htop : algebraMap B C b ∈ τ • mC := by
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [smul_algebraMap_eq_algebraMap_restrictNormalHom_smul, mul_smul] using hb_top
    simpa [Ideal.under_def] using htop

/-- Helper for Lemma 15.113.10: restricting a decomposition-group element upstairs keeps the
contracted ideal fixed downstairs. -/
private theorem restrictNormalHom_mem_decompositionGroup_local
    (mC : Ideal C) [mC.IsMaximal]
    (σ : MulAction.stabilizer Gal(M/K) mC) :
    restrictNormalHom L σ.1 ∈ MulAction.stabilizer Gal(L/K) (mC.under B) := by
  -- Contract the stabilizer equality from `C` to `B`.
  rw [MulAction.mem_stabilizer_iff]
  calc
    restrictNormalHom L σ.1 • (mC.under B) = (σ.1 • mC).under B := by
      symm
      exact under_smul_eq_restrictNormalHom_smul_under (A := A) (K := K) (L := L) σ.1 mC
    _ = mC.under B := by
      simpa using congrArg (fun I : Ideal C ↦ I.under B) (MulAction.mem_stabilizer_iff.mp σ.2)

/-- Helper for Lemma 15.113.10: restricting an inertia element upstairs acts trivially modulo the
contracted maximal ideal downstairs. -/
private theorem restrictNormalHom_mem_inertiaGroup_local
    (mC : Ideal C) [mC.IsMaximal]
    (σ : mC.inertia Gal(M/K)) :
    restrictNormalHom L σ.1 ∈ (mC.under B).inertia Gal(L/K) := by
  have hσ : ∀ c : C, σ.1 • c - c ∈ mC := by
    -- Unpack the upstairs inertia condition as congruence modulo `mC`.
    exact (ideal_inertia_mem_iff (A := A) (K := K) (L := M) (J := mC) σ.1).mp σ.2
  rw [ideal_inertia_mem_iff (A := A) (K := K) (L := L) (J := mC.under B)]
  intro b
  -- Evaluate the upstairs congruence on the image of `b : B`.
  simpa [Ideal.under_def, map_sub, smul_algebraMap_eq_algebraMap_restrictNormalHom_smul] using
    hσ (algebraMap B C b)

/-- Helper for Lemma 15.113.10: the residue-field action downstairs induced by restricting a
decomposition-group element. -/
private noncomputable def decompositionGroupResidueFieldActionBase
    (mC : Ideal C) [mC.IsMaximal]
    (σ : MulAction.stabilizer Gal(M/K) mC) :
    (mC.under B).ResidueField →+* (mC.under B).ResidueField :=
  -- First restrict `σ` to the lower field, then apply the canonical stabilizer action on the
  -- residue field of the contracted maximal ideal.
  let σBase : MulAction.stabilizer Gal(L/K) (mC.under B) :=
    ⟨restrictNormalHom L σ.1, by
      exact restrictNormalHom_mem_decompositionGroup_local (A := A) (K := K) (L := L) mC σ⟩
  (IsFractionRing.stabilizerHom Gal(L/K) p (mC.under B) κA (mC.under B).ResidueField
      σBase).toRingHom

/-- Helper for Lemma 15.113.10: the residue-field action upstairs induced by a decomposition-group
element. -/
private noncomputable def decompositionGroupResidueFieldActionTop
    (mC : Ideal C) [mC.IsMaximal]
    (σ : MulAction.stabilizer Gal(M/K) mC) :
    mC.ResidueField →+* mC.ResidueField :=
  -- Upstairs this is the canonical residue-field action of the decomposition group.
  (IsFractionRing.stabilizerHom Gal(M/K) p mC κA mC.ResidueField σ).toRingHom

-- Proof sketch: the source proof identifies wild inertia with the image of the upstairs square
-- ideal inertia subgroup under restriction. The current blocker is the missing square-ideal bridge
-- between `mC ^ 2` and `(mC.under B) ^ 2` in this tower.
/- Lemma 15.113.10 (3): if `m' ⊂ C` is maximal and `m = m' ∩ B`, then the induced restriction map
on inertia groups sends the wild inertia group of `m'` onto the wild inertia group of `m`. -/
omit [IsLocalRing A] in
theorem wildInertiaSubgroup_restrict_image_eq
    (mC : Ideal C) [mC.IsMaximal] :
    Subgroup.map (restrictNormalHom L) (wildInertiaSubgroup K mC) =
      wildInertiaSubgroup K (mC.under B) := by
  -- Route correction: keep the theorem at the owner level `wildInertiaSubgroup`; the missing
  -- input is the local square-ideal restriction theorem, not another reformulation of the goal.
  sorry

/-- Helper for Lemma 15.113.10: on residue classes of elements from `B`, the upstairs and
downstairs decomposition-group actions agree after applying the canonical residue-field map. -/
private theorem decompositionGroup_residueFieldAction_comm_on_generators
    (mC : Ideal C) [mC.IsMaximal]
    (σ : MulAction.stabilizer Gal(M/K) mC) (b : B) :
    underResidueFieldMap mC
        (decompositionGroupResidueFieldActionBase (A := A) (K := K) (L := L) mC σ
          (algebraMap B (mC.under B).ResidueField b)) =
      decompositionGroupResidueFieldActionTop (A := A) (K := K) (L := L) mC σ
        (underResidueFieldMap mC (algebraMap B (mC.under B).ResidueField b)) := by
  -- Reduce both composites to the residue class of the same element of `C`.
  rw [decompositionGroupResidueFieldActionBase, decompositionGroupResidueFieldActionTop]
  rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.map_algebraMap,
    Ideal.ResidueField.map_algebraMap]
  -- The tower map intertwines the upstairs action with the restricted downstairs action.
  simpa [smul_algebraMap_eq_algebraMap_restrictNormalHom_smul]
    using congrArg (algebraMap C mC.ResidueField)
      (smul_algebraMap_eq_algebraMap_restrictNormalHom_smul (A := A) (K := K) (L := L) σ.1 b)

-- Proof sketch: this is the first source diagram, phrased directly as a categorical square on the
-- residue-field actions induced by the decomposition groups.
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
  -- Compare both composites on residue classes of elements of `B`.
  refine ⟨?_⟩
  apply Ideal.ResidueField.ringHom_ext
  intro b
  exact decompositionGroup_residueFieldAction_comm_on_generators
    (A := A) (K := K) (L := L) mC σ b

section Tame

variable [IsDiscreteValuationRing A] [FiniteDimensional K L] [FiniteDimensional K M]

/-- Helper for Lemma 15.113.10: the restriction homomorphism from upstairs inertia to downstairs
inertia. -/
private noncomputable def inertiaRestrictionHom
    (mC : Ideal C) [mC.IsMaximal] :
    mC.inertia Gal(M/K) →* (mC.under B).inertia Gal(L/K) :=
  -- Restriction preserves inertia by the earlier tower image theorem.
  { toFun := fun σ ↦
      ⟨restrictNormalHom L σ.1, by
        exact restrictNormalHom_mem_inertiaGroup_local (A := A) (K := K) (L := L) mC σ⟩
    map_one' := by
      ext
      simp
    map_mul' := by
      intro σ τ
      ext
      simp }

/-- Helper for Lemma 15.113.10: the lower tame character viewed in the upper residue field. -/
private noncomputable def baseResidueFieldRootsOfUnityMap
    (mC : Ideal C) [mC.IsMaximal] :
    rootsOfUnity (Ideal.ramificationIdxIn p B) (mC.under B).ResidueField →*
      rootsOfUnity (Ideal.ramificationIdxIn p B) mC.ResidueField :=
  -- Restrict roots of unity along the canonical residue-field map.
  restrictRootsOfUnity (underResidueFieldMap mC)
    (Ideal.ramificationIdxIn p B)

/-- Helper for Lemma 15.113.10: the lower ramification index divides the upper one in the tower
of contracted maximal ideals. -/
theorem ramificationIdxIn_under_dvd
    (mC : Ideal C) [mC.IsMaximal] :
    Ideal.ramificationIdxIn p B ∣ Ideal.ramificationIdxIn p C := by
  letI : (mC.under B).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : mC.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : mC.LiesOver (mC.under B) := by
    simpa using (Ideal.over_under (A := B) mC)
  let _ : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  let _ : IsDedekindDomain C := integralClosure.isDedekindDomain A K M
  have htop :
      Ideal.ramificationIdxIn p C = Ideal.ramificationIdx p mC := by
    simpa using (Ideal.ramificationIdxIn_eq_ramificationIdx p mC Gal(M/K))
  have hbase :
      Ideal.ramificationIdxIn p B = Ideal.ramificationIdx p (mC.under B) := by
    simpa using (Ideal.ramificationIdxIn_eq_ramificationIdx p (mC.under B) Gal(L/K))
  refine ⟨Ideal.ramificationIdx (mC.under B) mC, ?_⟩
  -- Specialize the ideal-theoretic tower formula to the branch `mC.under B ⊂ mC`.
  rw [hbase, htop]
  symm
  exact
    (Ideal.ramificationIdx_algebra_tower' p (mC.under B) mC :
      Ideal.ramificationIdx p mC =
        Ideal.ramificationIdx p (mC.under B) * Ideal.ramificationIdx (mC.under B) mC)

/-- Helper for Lemma 15.113.10: the right vertical map in the tame square. -/
private noncomputable def relativeRamificationRootsOfUnityMap
    (mC : Ideal C) [mC.IsMaximal] :
    rootsOfUnity (Ideal.ramificationIdxIn p C) mC.ResidueField →*
      rootsOfUnity (Ideal.ramificationIdxIn p B) mC.ResidueField :=
  -- The source diagram uses the canonical power map coming from `e ∣ e'`.
  rootsOfUnityPowMap (ramificationIdxIn_under_dvd (A := A) (K := K) (L := L) mC)

/-- Helper for Lemma 15.113.10: the lower tame inertia character composed with the residue-field
comparison map. -/
private noncomputable def tameInertiaCharacterBaseMap
    (mC : Ideal C) [mC.IsMaximal] :
    (mC.under B).inertia Gal(L/K) →*
      rootsOfUnity (Ideal.ramificationIdxIn p B) mC.ResidueField :=
  -- The lower tame character is viewed upstairs through the residue-field comparison map.
  (baseResidueFieldRootsOfUnityMap mC).comp
    (tameInertiaCharacter K (mC.under B))

-- Proof sketch: after choosing compatible uniformizers upstairs and downstairs, the source proof
-- compares the unit factors in `σ'(π') = c π'` and `σ(π) = b π`, then reduces to the triviality
-- of the residue class of `σ'(c') / c'` for inertia elements.
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
  -- Route correction: this square is not accessible from the abstract kernel/surjectivity API
  -- alone; it needs the source-faithful uniformizer evaluation of `tameInertiaCharacter`.
  sorry

/-- Public explicit restatement of Lemma 15.113.10: the tower square for tame inertia characters
uses the canonical residue-field map and the explicit roots-of-unity power map coming from
`ramificationIdxIn_under_dvd`. -/
theorem tameInertiaCharacter_tower_compatible_explicit_power_map
    (mC : Ideal C) [mC.IsMaximal]
    :
    let ITop := MonCat.of (mC.inertia Gal(M/K))
    let IBase := MonCat.of ((mC.under B).inertia Gal(L/K))
    let muTop := MonCat.of (rootsOfUnity (Ideal.ramificationIdxIn p C) mC.ResidueField)
    let muBase := MonCat.of (rootsOfUnity (Ideal.ramificationIdxIn p B) mC.ResidueField)
    let ρ : ITop ⟶ IBase :=
      MonCat.ofHom
        { toFun := fun σ ↦
            ⟨restrictNormalHom L σ.1, by
              exact
                restrictNormalHom_mem_inertiaGroup_local (A := A) (K := K) (L := L) mC σ⟩
          map_one' := by
            ext
            simp
          map_mul' := by
            intro σ τ
            ext
            simp }
    let θTop : ITop ⟶ muTop := MonCat.ofHom (tameInertiaCharacter K mC)
    let θBase : IBase ⟶ muBase :=
      MonCat.ofHom
        ((restrictRootsOfUnity
            (Ideal.ResidueField.map (mC.under B) mC (algebraMap B C) rfl)
            (Ideal.ramificationIdxIn p B)).comp
          (tameInertiaCharacter K (mC.under B)))
    let pow : muTop ⟶ muBase :=
      MonCat.ofHom (rootsOfUnityPowMap (ramificationIdxIn_under_dvd (A := A) (K := K) (L := L) mC))
    CommSq ρ θTop θBase pow := by
  -- Unfold only the private packaging so the public theorem exposes the source square in the
  -- explicit power-map form needed by later tower arguments.
  simpa [inertiaRestrictionHom, tameInertiaCharacterBaseMap, baseResidueFieldRootsOfUnityMap,
    underResidueFieldMap, relativeRamificationRootsOfUnityMap] using
    tameInertiaCharacter_tower_compatible (A := A) (K := K) (L := L) (M := M) mC

end Tame

end
