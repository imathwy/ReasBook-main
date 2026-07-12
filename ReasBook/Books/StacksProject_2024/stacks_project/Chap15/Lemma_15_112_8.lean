import Mathlib
import StacksProject_2024.Chap09.Lemma_9_16_6
import StacksProject_2024.Chap10.Lemma_10_37_12
import StacksProject_2024.Chap10.Lemma_10_143_3
import StacksProject_2024.Chap10.Lemma_10_143_5
import StacksProject_2024.Chap10.Lemma_10_143_7
import StacksProject_2024.Chap10.Lemma_10_163_9
import StacksProject_2024.Chap09.Lemma_9_21_5
import StacksProject_2024.Chap15.Definition_15_112_7
import StacksProject_2024.Chap15.Lemma_15_9_4
import StacksProject_2024.Chap15.Lemma_15_112_3
import StacksProject_2024.Chap15.Lemma_15_44_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open IntermediateField
open Ideal IsLocalRing Algebra
open PrimeSpectrum Topology
open scoped PrimeSpectrum

/- Domain-style sampling:
- source-facing owner: `IsUnramifiedWithRespectTo A L` from `Definition_15_112_7`;
- sampled canonical declarations in this domain:
  `IsUnramifiedWithRespectTo`,
  `isUnramifiedAt_of_integralClosure_tower`,
  `normalClosure K L (AlgebraicClosure L)`,
  `isGalois_normalClosure_of_separable`,
  `IntermediateField.finiteDimensional_sup`,
  `IntermediateField.isSeparable_sup`;
- best owner abstraction: the chapter owner `IsUnramifiedWithRespectTo`, with
  the source-facing existential overfield statement as the main theorem for clause `(2)`,
  the canonical Galois-closure field `normalClosure K L (AlgebraicClosure L)` as its preferred
  bridge witness, and `isUnramifiedAt_of_integralClosure_tower` as the canonical bridge from
  branchwise `Algebra.IsUnramifiedAt` data along integral-closure towers;
- primitive-vs-derived split: the finite/separable hypotheses on the bottom extension
  `L / FractionRing A` are primitive because they supply the integral-closure finite-type owner
  needed by `IsUnramifiedWithRespectTo A L`, while the tower hypotheses
  `[FiniteDimensional K L]`, `[FiniteDimensional L M]`, `[Algebra.IsSeparable K L]`, and
  `[Algebra.IsSeparable L M]` canonically derive the corresponding finite/separable structure on
  `M / K`, hence also the `Algebra.EssFiniteType A (integralClosure A M)` owner needed to state
  `IsUnramifiedWithRespectTo A M`; in the theorem surface below, those top-extension instances are
  derived locally from the tower rather than exposed as public binders.

This file is therefore a `bridge/view` layer: its numbered statements remain source-facing
existence theorems, while the canonical tower, normal-closure, and compositum owners serve only as
bridge infrastructure rather than parallel local wrappers.
-/

end

section

open IntermediateField

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

section Tower

variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L]
variable {M : Type w} [Field M] [Algebra A M] [Algebra (FractionRing A) M] [Algebra L M]
variable [IsScalarTower A (FractionRing A) M] [IsScalarTower (FractionRing A) L M]
variable [FiniteDimensional (FractionRing A) L] [FiniteDimensional L M]
variable [Algebra.IsSeparable (FractionRing A) L] [Algebra.IsSeparable L M]

local notation "K" => FractionRing A
local notation "B" => integralClosure A L
local notation "C" => integralClosure A M
local notation "κA" => Ideal.ResidueField (IsLocalRing.maximalIdeal A)

noncomputable section

local instance : IsScalarTower A L M := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  -- The `A → M` structure factors through `K → L → M`.
  rw [IsScalarTower.algebraMap_apply A K M, IsScalarTower.algebraMap_apply A K L,
    IsScalarTower.algebraMap_apply K L M]

/-- Helper for Lemma 15.112.8: the canonical map on integral closures induced by the tower
`L → M`. -/
private noncomputable abbrev integralClosureTowerMap : B →ₐ[A] C :=
  (IsScalarTower.toAlgHom A L M).mapIntegralClosure

noncomputable local instance : Algebra B C :=
  integralClosureTowerMap.toAlgebra

local instance : IsScalarTower A B C := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  ext
  simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A L M]

/-- Helper for Lemma 15.112.8: the intermediate integral closure has the expected fraction field. -/
private local instance integralClosure_isFractionRing_base :
    IsFractionRing B L :=
  integralClosure.isFractionRing_of_finite_extension K L

/-- Helper for Lemma 15.112.8: the intermediate integral closure is finite over the base discrete
valuation ring. -/
private local instance integralClosure_moduleFinite_base :
    Module.Finite A B :=
  IsIntegralClosure.finite A K L B

/-- Helper for Lemma 15.112.8: the intermediate integral closure is Dedekind. -/
private local instance integralClosure_isDedekindDomain_base :
    IsDedekindDomain B :=
  integralClosure.isDedekindDomain A K L

/-- Helper for Lemma 15.112.8: the intermediate field extension is torsion-free over the base
ring. -/
private local instance torsionFree_fraction_base :
    Module.IsTorsionFree A L :=
  .trans_faithfulSMul A K L

/-- Helper for Lemma 15.112.8: the top field extension is torsion-free over the base ring. -/
private local instance torsionFree_fraction_top :
    Module.IsTorsionFree A M :=
  .trans_faithfulSMul A K M

/-- Helper for Lemma 15.112.8: torsion-freeness of the intermediate integral closure over the
base ring. -/
private local instance integralClosure_torsionFree_base :
    Module.IsTorsionFree A B :=
  IsIntegralClosure.isTorsionFree A L

/-- Helper for Lemma 15.112.8: torsion-freeness of the top integral closure over the base ring. -/
private local instance integralClosure_torsionFree_top :
    Module.IsTorsionFree A C :=
  IsIntegralClosure.isTorsionFree A M

/-- Helper for Lemma 15.112.8: the top field is a faithful `B`-algebra because `L` is the
fraction field of `B`. -/
private local instance faithfulSmul_topField :
    FaithfulSMul B M :=
  FaithfulSMul.of_field_isFractionRing B M L M

/-- Helper for Lemma 15.112.8: the algebra map `B → C` is injective, so `C` is a faithful
`B`-algebra. -/
private local instance faithfulSmul_tower :
    FaithfulSMul B C := by
  refine (faithfulSMul_iff_algebraMap_injective B C).mpr fun x y hxy ↦ ?_
  have hxyM : algebraMap B M x = algebraMap B M y := by
    exact congrArg (fun z : C ↦ (z : M)) hxy
  change algebraMap B M x = algebraMap B M y at hxyM
  exact FaithfulSMul.algebraMap_injective B M hxyM

/-- Helper for Lemma 15.112.8: the top integral closure is torsion-free over the intermediate
integral closure. -/
private local instance integralClosure_torsionFree_tower :
    Module.IsTorsionFree B C := by
  -- Embed the tower into the ambient field `M` and use that fields have no zero divisors.
  refine Module.IsTorsionFree.of_smul_eq_zero fun b c h ↦ ?_
  change (algebraMap B C b) * c = 0 at h
  rcases mul_eq_zero.mp h with hzero | hzero
  · have hzero' : algebraMap B M b = algebraMap B M 0 := by
      simpa using congrArg (fun x : C ↦ (x : M)) hzero
    exact Or.inl <| FaithfulSMul.algebraMap_injective B M hzero'
  · exact Or.inr hzero

/-- Helper for Lemma 15.112.8: the tower map on integral closures is integral. -/
private local instance integralClosure_isIntegral_tower :
    Algebra.IsIntegral B C :=
  Algebra.IsIntegral.tower_top A

/-- Helper for Lemma 15.112.8: every maximal ideal of the intermediate integral closure lies over
the maximal ideal of the base discrete valuation ring. -/
private local instance liesOver_maximalIdeal_base (p : Ideal B) [p.IsMaximal] :
    p.LiesOver (IsLocalRing.maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p)).symm⟩

/-- Helper for Lemma 15.112.8: every maximal ideal of the top integral closure lies over the
maximal ideal of the base discrete valuation ring. -/
private local instance liesOver_maximalIdeal_top (P : Ideal C) [P.IsMaximal] :
    P.LiesOver (IsLocalRing.maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)).symm⟩

/-- Helper for Lemma 15.112.8: a maximal ideal of the intermediate integral closure lifts to a
maximal ideal of the top integral closure. -/
private lemma exists_maximal_liesOver_of_integralClosure_tower
    (p : Ideal B) [p.IsMaximal] :
    ∃ P : Ideal C, P.IsMaximal ∧ P.LiesOver p := by
  -- Use lying-over for the integral map `B → C` to lift the chosen branch.
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := C) p
  exact ⟨P, hPmax, hPover⟩

/-- Helper for Lemma 15.112.8: ramification indices along a lifted branch multiply in the tower
`A ⊂ B ⊂ C`. -/
private lemma ramificationIdx_maximalIdeal_eq_mul_of_branch_liesOver
    (p : Ideal B) [p.IsMaximal] [p.LiesOver (IsLocalRing.maximalIdeal A)]
    (P : Ideal C) [P.IsMaximal] [P.LiesOver p] :
    Ideal.ramificationIdx (IsLocalRing.maximalIdeal A) P =
      Ideal.ramificationIdx (IsLocalRing.maximalIdeal A) p * Ideal.ramificationIdx p P := by
  -- Install the top branch over `maximalIdeal A` and specialize the tower formula.
  letI : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.LiesOver (IsLocalRing.maximalIdeal A) :=
    Ideal.LiesOver.trans P p (IsLocalRing.maximalIdeal A)
  let _ : FiniteDimensional K M := FiniteDimensional.trans K L M
  let _ : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  let _ : IsDedekindDomain C := integralClosure.isDedekindDomain A K M
  simpa using
    (Ideal.ramificationIdx_algebra_tower' (IsLocalRing.maximalIdeal A) p P :
      Ideal.ramificationIdx (IsLocalRing.maximalIdeal A) P =
        Ideal.ramificationIdx (IsLocalRing.maximalIdeal A) p * Ideal.ramificationIdx p P)

/-- Helper for Lemma 15.112.8: on the intermediate branch, the residue-field map from `κA`
agrees with the ambient algebra map. -/
private lemma residueField_map_eq_algebraMap_base
    (p : Ideal B) [p.IsMaximal] [p.LiesOver (IsLocalRing.maximalIdeal A)] :
    Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) p (algebraMap A B)
        (p.over_def (IsLocalRing.maximalIdeal A)) =
      algebraMap κA p.ResidueField := by
  letI : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  ext a
  change
    Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) p (algebraMap A B)
        (p.over_def (IsLocalRing.maximalIdeal A)) ((algebraMap A κA) a) =
      (algebraMap κA p.ResidueField) ((algebraMap A κA) a)
  rw [Ideal.ResidueField.map_algebraMap (IsLocalRing.maximalIdeal A) p (algebraMap A B)
    (p.over_def (IsLocalRing.maximalIdeal A)) a]
  -- Both maps send the image of `a : A` to the same residue class.
  have hB : (algebraMap B p.ResidueField) ((algebraMap A B) a) =
      (algebraMap A p.ResidueField) a := by
    exact IsScalarTower.algebraMap_apply A B p.ResidueField a
  have hκ : (algebraMap κA p.ResidueField) ((algebraMap A κA) a) =
      (algebraMap A p.ResidueField) a := by
    exact (IsScalarTower.algebraMap_apply A κA p.ResidueField a).symm
  exact hB.trans hκ.symm

/-- Helper for Lemma 15.112.8: on the lifted top branch, the residue-field map from `κA`
agrees with the ambient algebra map. -/
private lemma residueField_map_eq_algebraMap_top
    (P : Ideal C) [P.IsMaximal] [P.LiesOver (IsLocalRing.maximalIdeal A)] :
    Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) P (algebraMap A C)
        (P.over_def (IsLocalRing.maximalIdeal A)) =
      algebraMap κA P.ResidueField := by
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  ext a
  change
    Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) P (algebraMap A C)
        (P.over_def (IsLocalRing.maximalIdeal A)) ((algebraMap A κA) a) =
      (algebraMap κA P.ResidueField) ((algebraMap A κA) a)
  rw [Ideal.ResidueField.map_algebraMap (IsLocalRing.maximalIdeal A) P (algebraMap A C)
    (P.over_def (IsLocalRing.maximalIdeal A)) a]
  -- Both maps send the image of `a : A` to the same residue class.
  have hC : (algebraMap C P.ResidueField) ((algebraMap A C) a) =
      (algebraMap A P.ResidueField) a := by
    exact IsScalarTower.algebraMap_apply A C P.ResidueField a
  have hκ : (algebraMap κA P.ResidueField) ((algebraMap A κA) a) =
      (algebraMap A P.ResidueField) a := by
    exact (IsScalarTower.algebraMap_apply A κA P.ResidueField a).symm
  exact hC.trans hκ.symm

/-- Helper for Lemma 15.112.8: for a lifted branch `p ⊂ P`, the residue fields form a tower
`κA → κ(p) → κ(P)`. -/
private lemma residueField_isScalarTower_of_branch_liesOver
    (p : Ideal B) [p.IsMaximal] [p.LiesOver (IsLocalRing.maximalIdeal A)]
    (P : Ideal C) [P.IsMaximal] [P.LiesOver p] :
    IsScalarTower κA p.ResidueField P.ResidueField := by
  -- Compare the two maps `κA → P.ResidueField` on residue classes coming from `A`.
  letI : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.LiesOver (IsLocalRing.maximalIdeal A) := inferInstance
  letI : Algebra κA p.ResidueField := inferInstance
  letI : Algebra κA P.ResidueField := inferInstance
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  obtain ⟨a, rfl⟩ := (IsLocalRing.maximalIdeal A).algebraMap_residueField_surjective x
  rw [← residueField_map_eq_algebraMap_top (P := P),
    ← residueField_map_eq_algebraMap_base (p := p)]
  rw [Ideal.ResidueField.map_algebraMap (IsLocalRing.maximalIdeal A) P (algebraMap A C)
      (P.over_def (IsLocalRing.maximalIdeal A)) a,
    Ideal.ResidueField.map_algebraMap (IsLocalRing.maximalIdeal A) p (algebraMap A B)
      (p.over_def (IsLocalRing.maximalIdeal A)) a]
  rw [IsScalarTower.algebraMap_apply A B C]
  exact
    (Ideal.ResidueField.map_algebraMap p P (algebraMap B C) (P.over_def p)
      ((algebraMap A B) a)).symm

/-- Helper for Lemma 15.112.8: separability of the lifted residue field extension over `κA`
descends to the intermediate residue field. -/
private lemma residueField_separable_of_unramified_over_branch
    (hM : IsUnramifiedWithRespectTo A M)
    (p : Ideal B) [p.IsMaximal] [p.LiesOver (IsLocalRing.maximalIdeal A)]
    (P : Ideal C) [P.IsMaximal] [P.LiesOver p] :
    Algebra.IsSeparable κA p.ResidueField := by
  -- Route correction: descend separability through the residue-field tower
  -- `κA ⊂ κ(p) ⊂ κ(P)` rather than switching to residue-degree numerics.
  letI : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.LiesOver (IsLocalRing.maximalIdeal A) := inferInstance
  letI : Algebra κA p.ResidueField := inferInstance
  letI : Algebra κA P.ResidueField := inferInstance
  letI : IsScalarTower κA p.ResidueField P.ResidueField :=
    residueField_isScalarTower_of_branch_liesOver (A := A) (L := L) (M := M) p P
  letI : Algebra.IsSeparable κA P.ResidueField := by
    simpa using hM.residueField_separable P
  exact Algebra.isSeparable_tower_bot_of_isSeparable κA p.ResidueField P.ResidueField

-- Proof sketch: let `B = integralClosure A L` and `C = integralClosure A M`. For a maximal ideal
-- `p : Ideal B` over `maximalIdeal A`, choose a maximal ideal `P : Ideal C` above `p` by lying
-- over. Since `M` is unramified with respect to `A`, the branch `P` is unramified over `A`, so
-- its ramification index over `maximalIdeal A` is `1` and the residue-field extension is
-- separable. Comparing ramification indices in the tower `A ⊆ B ⊆ C` and descending separability
-- along `κ(P) / κ(p) / κA` gives that `p` is unramified over `A`.
/-- Lemma 15.112.8 (1): in a tower `M/L/K` of finite separable extensions over the fraction field
of a discrete valuation ring `A`, unramifiedness with respect to `A` descends from `M` to `L`. -/
theorem isUnramifiedWithRespectTo_of_tower
    (hM : IsUnramifiedWithRespectTo A M) :
    IsUnramifiedWithRespectTo A L := by
  classical
  let _ : FiniteDimensional K M := FiniteDimensional.trans K L M
  let _ : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  refine
    { residueField_separable := ?_
      ramificationIdx_eq_one := ?_ }
  · intro p _ _
    -- Lift the chosen branch upstairs and descend separability through the residue-field tower.
    obtain ⟨P, hPmax, hPover⟩ :=
      exists_maximal_liesOver_of_integralClosure_tower (A := A) (L := L) (M := M) p
    letI : P.IsMaximal := hPmax
    letI : P.LiesOver p := hPover
    exact residueField_separable_of_unramified_over_branch (A := A) (L := L) (M := M) hM p P
  · intro p _ _
    -- Lift the branch and use multiplicativity of ramification indices to read off `e(p/A) = 1`
    -- from `e(P/A) = 1`.
    obtain ⟨P, hPmax, hPover⟩ :=
      exists_maximal_liesOver_of_integralClosure_tower (A := A) (L := L) (M := M) p
    letI : P.IsMaximal := hPmax
    letI : P.LiesOver p := hPover
    letI : P.LiesOver (IsLocalRing.maximalIdeal A) := inferInstance
    have hmul :
        Ideal.ramificationIdx (IsLocalRing.maximalIdeal A) p * Ideal.ramificationIdx p P = 1 := by
      calc
        Ideal.ramificationIdx (IsLocalRing.maximalIdeal A) p * Ideal.ramificationIdx p P =
            Ideal.ramificationIdx (IsLocalRing.maximalIdeal A) P := by
              symm
              exact
                ramificationIdx_maximalIdeal_eq_mul_of_branch_liesOver
                  (A := A) (L := L) (M := M) p P
        _ = 1 := by
          simpa using hM.ramificationIdx_eq_one P
    exact Nat.eq_one_of_dvd_one ⟨Ideal.ramificationIdx p P, hmul.symm⟩

end

end Tower

section EtaleDomainModel

variable {R : Type v} [CommRing R] [IsDomain R] [Algebra A R]
variable {F : Type w} [Field F] [Algebra A F] [Algebra (FractionRing A) F]
  [IsScalarTower A (FractionRing A) F] [Algebra R F] [IsScalarTower A R F]
variable [FiniteDimensional (FractionRing A) F] [Algebra.IsSeparable (FractionRing A) F]
variable [IsFractionRing R F] [Algebra.IsIntegral A R] [Algebra.Etale A R]

/-- Helper for Lemma 15.112.8: an integral domain `A`-algebra that is integral over `A` and has
fraction field `F` is the integral closure of `A` in `F` as soon as it is integrally closed. -/
private theorem integralClosure_of_integrallyClosed_fractionRing_model
    [IsIntegrallyClosed R] :
    IsIntegralClosure R A F := by
  -- A normal domain sitting inside its own fraction field already realizes the normalization.
  exact IsIntegralClosure.of_isIntegrallyClosed R A F

/-- Helper for Lemma 15.112.8: if a field extension `F / FractionRing A` admits an integral
étale domain model over `A`, then `F` is unramified with respect to `A`. -/
private theorem isUnramifiedWithRespectTo_of_integral_etale_fractionRing_model
    (R : Type v) [CommRing R] [IsDomain R] [Algebra A R] [Algebra R F] [IsScalarTower A R F]
    [IsFractionRing R F] [Algebra.IsIntegral A R] [Algebra.Etale A R] :
    IsUnramifiedWithRespectTo A F := by
  letI : IsNormalRing R := by
    -- Smooth algebras over the normal base DVR remain normal.
    exact isNormalRing_of_smooth
  letI : IsIntegrallyClosed R := by
    exact isIntegrallyClosed_of_isNormalRing
  letI : IsIntegralClosure R A F :=
    integralClosure_of_integrallyClosed_fractionRing_model (A := A) (R := R) (F := F)
  let e : R ≃ₐ[A] integralClosure A F :=
    IsIntegralClosure.equiv A R F (integralClosure A F)
  have hEtaleIntegralClosure : Algebra.Etale A (integralClosure A F) := by
    -- Replace the chosen owner ring model by the canonical integral closure once and for all.
    exact Algebra.Etale.of_equiv e
  letI : Algebra.Etale A (integralClosure A F) := hEtaleIntegralClosure
  refine (IsUnramifiedWithRespectTo.iff_isUnramifiedAt (A := A) (L := F)).2 ?_
  intro P _ _
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.LiesOver (Ideal.under A P) := Ideal.over_under P
  -- Global étaleness gives the `g = 1` neighborhood required by Lemma `10.143.5`.
  refine (Algebra.isUnramifiedAt_iff_map_eq A (Ideal.under A P) P).2 ?_
  refine ⟨?_, ?_⟩
  · exact
      (residueField_finite_and_separable_of_exists_etale_away
        (R := A) (S := integralClosure A F) P
        ⟨1, by
          simpa [Ideal.eq_top_iff_one] using
            (show P ≠ ⊤ from Ideal.IsPrime.ne_top (I := P) inferInstance),
          inferInstance⟩).2
  · simpa using
      (show Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.under A P) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P) from by
        simpa using
          (map_eq_maximalIdeal_of_exists_etale_away
            (R := A) (S := integralClosure A F) P
            ⟨1, by
              simpa [Ideal.eq_top_iff_one] using
                (show P ≠ ⊤ from Ideal.IsPrime.ne_top (I := P) inferInstance),
              inferInstance⟩))

end EtaleDomainModel

section ProductFactorization

/-- Helper for Lemma 15.112.8: a ring map from a finite product of commutative rings to a domain
factors through one coordinate projection. -/
private theorem algHom_to_domain_factors_through_product_component
    {ι : Type*} [Finite ι] {R : ι → Type*} [∀ i, CommRing (R i)]
    {T : Type*} [CommRing T] [IsDomain T]
    (φ : (Π i, R i) →+* T) :
    ∃ i, ∃ ψ : R i →+* T, φ = ψ.comp (Pi.evalRingHom R i) := by
  let p : PrimeSpectrum (Π i, R i) :=
    ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  -- Pick the component selected by the prime kernel of `φ`.
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
  have hker :
      RingHom.ker (Pi.evalRingHom R i) ≤ RingHom.ker φ := by
    intro x hx
    -- Elements killed by the projection land in `0`, hence in the chosen prime of the factor.
    have hx0 : Pi.evalRingHom R i x = 0 := by
      simpa [RingHom.mem_ker] using hx
    have hxq : Pi.evalRingHom R i x ∈ q.asIdeal := by
      simpa [hx0] using (q.asIdeal.zero_mem : (0 : R i) ∈ q.asIdeal)
    -- Reinterpret that membership on the product side through the identified prime kernel.
    rw [show RingHom.ker φ = p.asIdeal by rfl, ← hq, PrimeSpectrum.comap_asIdeal]
    exact hxq
  let ψ : R i →+* T :=
    (Pi.evalRingHom R i).liftOfSurjective (Function.surjective_eval i) ⟨φ, hker⟩
  refine ⟨i, ψ, ?_⟩
  -- The surjective projection characterizes the descended factor map.
  simpa [ψ] using
    (RingHom.liftOfSurjective_comp (f := Pi.evalRingHom R i)
      (hf := Function.surjective_eval i) ⟨φ, hker⟩).symm

/-- Helper for Lemma 15.112.8: a surjective algebra map from a finite product of fields to a
field is already an algebra isomorphism on one factor. -/
private theorem surjective_algHom_from_product_of_fields_factors
    {K : Type*} [Field K] {ι : Type*} [Finite ι] {F : ι → Type*} [∀ i, Field (F i)]
    {N : Type*} [Field N] [Algebra K N] [∀ i, Algebra K (F i)]
    (φ : (Π i, F i) →ₐ[K] N) (hφ : Function.Surjective φ) :
    ∃ i, Nonempty (F i ≃ₐ[K] N) := by
  obtain ⟨i, ψ, hψ⟩ :=
    algHom_to_domain_factors_through_product_component (R := F) (T := N) φ.toRingHom
  let ψA : F i →ₐ[K] N :=
    { toRingHom := ψ
      commutes' := by
        intro x
        -- Compare the factorization on the constant tuple coming from `K`.
        have hconst :=
          congrArg
            (fun f : (Π j, F j) →+* N ↦ f (algebraMap K (Π j, F j) x))
            hψ
        simpa using hconst.symm }
  have hsurjψ : Function.Surjective ψA := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    refine ⟨x i, ?_⟩
    -- Evaluate the ring-level factorization on the chosen preimage tuple.
    have hx := congrArg (fun f : (Π j, F j) →+* N ↦ f x) hψ
    simpa [ψA] using hx.symm
  -- A surjective algebra hom between fields is bijective, hence an algebra equivalence.
  exact ⟨i, ⟨AlgEquiv.ofBijective ψA ⟨ψA.injective, hsurjψ⟩⟩⟩

end ProductFactorization

section IntegralClosureClosedFiber

variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]

local notation "K" => FractionRing A
local notation "B" => integralClosure A L

/-- Helper for Lemma 15.112.8: the residue field at the zero prime of a domain is canonically its
fraction field. -/
private noncomputable def zeroPrime_residueField_algEquiv_fractionRing
    (R : Type*) [CommRing R] [IsDomain R] :
    FractionRing R ≃ₐ[R] ((⊥ : Ideal R).ResidueField) := by
  let e : R ≃ₐ[R] R ⧸ (⊥ : Ideal R) := (AlgEquiv.quotientBot R R).symm
  letI : IsFractionRing R ((⊥ : Ideal R).ResidueField) := by
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap R ((⊥ : Ideal R).ResidueField) x =
      algebraMap (R ⧸ (⊥ : Ideal R)) ((⊥ : Ideal R).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    exact show
        algebraMap (R ⧸ (⊥ : Ideal R)) ((⊥ : Ideal R).ResidueField)
            (Ideal.Quotient.mk (⊥ : Ideal R) x) =
          algebraMap R ((⊥ : Ideal R).ResidueField) x by
      rfl
  -- The generic residue field is already a fraction-ring model, so the standard owner
  -- equivalence identifies it with `FractionRing R`.
  exact FractionRing.algEquiv R ((⊥ : Ideal R).ResidueField)

/-- Helper for Lemma 15.112.8: the zero ideal of the integral closure contracts to the zero ideal
of the base domain. -/
private lemma bot_under_eq_bot_of_integralClosure :
    ((⊥ : Ideal B).under A) = ⊥ := by
  ext a
  constructor
  · intro ha
    change algebraMap A (integralClosure A L) a = 0 at ha
    have hL' : ((algebraMap A (integralClosure A L) a : integralClosure A L) : L) = 0 := by
      simpa using congrArg (fun z : integralClosure A L ↦ (z : L)) ha
    have hL : algebraMap A L a = 0 := by
      simpa using hL'
    have hK : algebraMap A (FractionRing A) a = 0 := by
      apply FaithfulSMul.algebraMap_injective (FractionRing A) L
      simpa [IsScalarTower.algebraMap_apply A (FractionRing A) L] using hL
    have hK' : algebraMap A (FractionRing A) a = algebraMap A (FractionRing A) 0 := by
      simpa using hK
    exact IsFractionRing.injective A (FractionRing A) hK'
  · intro ha
    have ha0 : a = 0 := by
      simpa using ha
    simpa [ha0]

/-- Helper for Lemma 15.112.8: a prime of the integral closure lying over `0` is the generic
point. -/
private lemma zero_contraction_prime_eq_bot_of_integralClosure
    (q : PrimeSpectrum B)
    (hq : q.asIdeal.under A = ⊥) :
    q.asIdeal = ⊥ := by
  by_contra hqne
  letI : q.asIdeal.IsPrime := q.isPrime
  have hqmax : q.asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal (R := integralClosure A L) (p := q.asIdeal) inferInstance hqne
  have hunderMax : (q.asIdeal.under A).IsMaximal := by
    simpa [Ideal.under_def] using
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q.asIdeal)
  have hmaxbot : IsLocalRing.maximalIdeal A = ⊥ := by
    simpa [hq] using (IsLocalRing.eq_maximalIdeal hunderMax).symm
  exact IsDiscreteValuationRing.not_a_field A hmaxbot

/-- Helper for Lemma 15.112.8: the integral closure of a discrete valuation ring in a finite
separable fraction-field extension is flat over the base ring. -/
private theorem integralClosure_flat_over_dvr :
    Module.Flat A B := by
  -- Over the Bezout domain `A`, torsion-freeness is equivalent to flatness.
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
  -- The integral closure sits inside the ambient field, so it is torsion-free over `A`.
  letI : Module.IsTorsionFree A L := .trans_faithfulSMul A (FractionRing A) L
  letI : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  exact (Submodule.isTorsionFree_iff_torsion_eq_bot).mp inferInstance

/-- Helper for Lemma 15.112.8: the zero ideal of the integral closure lies over the zero ideal of
the base domain. -/
private lemma zeroIdeal_liesOver_bot_of_integralClosure :
    (⊥ : Ideal B).LiesOver (⊥ : Ideal A) := by
  -- The zero ideal contracts to zero because the base map into the normalization is injective.
  rw [Ideal.liesOver_iff]
  simpa [Ideal.under_def] using (bot_under_eq_bot_of_integralClosure (A := A) (L := L)).symm

/-- Helper for Lemma 15.112.8: the zero-prime residue-field extension of the integral closure is
the given generic fraction-field extension in disguise, hence separable. -/
private theorem zeroPrime_residueField_separable_of_fraction_extension :
    let _ : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) :=
      zeroIdeal_liesOver_bot_of_integralClosure (A := A) (L := L)
    let _ : Algebra ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) :=
      inferInstance
    Algebra.IsSeparable ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) := by
  let _ : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) :=
    zeroIdeal_liesOver_bot_of_integralClosure (A := A) (L := L)
  let _ : Algebra ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) := inferInstance
  let _ : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  let eFrac : FractionRing A ≃ₐ[A] K := FractionRing.algEquiv A K
  let eZero : FractionRing A ≃ₐ[A] ((⊥ : Ideal A).ResidueField) :=
    zeroPrime_residueField_algEquiv_fractionRing A
  let eBase : K ≃ₐ[A] ((⊥ : Ideal A).ResidueField) := eFrac.symm.trans eZero
  let eFracTop : FractionRing B ≃ₐ[B] L := FractionRing.algEquiv B L
  let eZeroTop : FractionRing B ≃ₐ[B] ((⊥ : Ideal B).ResidueField) :=
    zeroPrime_residueField_algEquiv_fractionRing B
  let eTop : L ≃ₐ[B] ((⊥ : Ideal B).ResidueField) := eFracTop.symm.trans eZeroTop
  have hcomm :
      RingHom.comp
          (algebraMap ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField))
          eBase.toRingHom =
        RingHom.comp eTop.toRingHom (algebraMap K L) := by
    -- The chosen zero-prime residue-field models commute with the generic-fiber maps.
    ext x
    simpa [eBase, eTop] using IsFractionRing.algEquiv_commutes eBase eTop x
  -- Transport separability from `K → L` across the zero-prime residue-field equivalences.
  simpa using
    (Algebra.IsSeparable.of_equiv_equiv eBase.toRingEquiv eTop.toRingEquiv hcomm)

/-- Helper for Lemma 15.112.8: the generic point of the integral closure is étale over the base
discrete valuation ring. -/
private theorem zeroPrime_isEtaleAt_integralClosure :
    Algebra.IsEtaleAt A (⊥ : Ideal B) := by
  let _ : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) :=
    zeroIdeal_liesOver_bot_of_integralClosure (A := A) (L := L)
  let _ : Algebra ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) := inferInstance
  let _ : Algebra.IsSeparable ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal B).ResidueField) :=
    zeroPrime_residueField_separable_of_fraction_extension (A := A) (L := L)
  let _ : Module.Finite A B := IsIntegralClosure.finite A K L B
  let _ : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  let _ : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finitePresentation A B
  have hflatAlg : (algebraMap A B).Flat := by
    -- Proof comment: global flatness of the normalization descends to the algebra map.
    exact RingHom.flat_algebraMap_iff.mpr <|
      integralClosure_flat_over_dvr (A := A) (L := L)
  have hflat :
      (Localization.localRingHom (⊥ : Ideal A) (⊥ : Ideal B)
        (algebraMap A B) ((⊥ : Ideal B).over_def (⊥ : Ideal A))).Flat := by
    -- Proof comment: localize the global flat map at the generic point.
    exact RingHom.Flat.localRingHom hflatAlg (⊥ : Ideal B) (⊥ : Ideal A)
      ((⊥ : Ideal B).over_def (⊥ : Ideal A))
  have hmax :
      (⊥ : Ideal A).map (algebraMap A (Localization.AtPrime (⊥ : Ideal B))) =
        IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal B)) := by
    letI : IsFractionRing B (Localization.AtPrime (⊥ : Ideal B)) := by
      delta IsFractionRing
      simpa [Ideal.primeCompl_bot] using
        (inferInstance :
          IsLocalization ((⊥ : Ideal B).primeCompl) (Localization.AtPrime (⊥ : Ideal B)))
    let _ : IsDomain B := inferInstance
    let _ : Field (Localization.AtPrime (⊥ : Ideal B)) := IsFractionRing.toField B
    have hmaxbot :
        IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal B)) = ⊥ := by
      exact (IsLocalRing.isField_iff_maximalIdeal_eq).mp
        (Field.toIsField (Localization.AtPrime (⊥ : Ideal B)))
    -- Proof comment: localization at the generic point of a domain is a field.
    rw [Ideal.map_bot, hmaxbot]
  -- Proof comment: apply the local flatness-plus-separable-residue-field criterion at `⊥`.
  exact
    Algebra.isEtaleAt_of_flat_localRingHom_of_map_eq_maximalIdeal_of_separableResidueField
      (R := A) (S := B) (p := ⊥) (q := ⊥) hflat hmax

/-- Helper for Lemma 15.112.8: every contracted prime in the local base is either the generic
point or the closed point. -/
private lemma prime_under_eq_bot_or_maximalIdeal
    (q : PrimeSpectrum B) :
    q.asIdeal.under A = ⊥ ∨ q.asIdeal.under A = IsLocalRing.maximalIdeal A := by
  by_cases hq : q.asIdeal.under A = ⊥
  · exact Or.inl hq
  · have hprime : (q.asIdeal.under A).IsPrime := by
      simpa [Ideal.under_def] using
        (Ideal.comap_isPrime (algebraMap A B) q.asIdeal)
    have hmax : (q.asIdeal.under A).IsMaximal :=
      Ideal.IsPrime.isMaximal (R := A) (p := q.asIdeal.under A) hprime hq
    exact Or.inr (IsLocalRing.eq_maximalIdeal hmax)

/-- Helper for Lemma 15.112.8: every prime of the integral closure lying above the closed point of
the base discrete valuation ring is one of the branchwise unramified points supplied by
`IsUnramifiedWithRespectTo`. -/
private theorem closedFiber_branch_isUnramifiedAt
    (hL : IsUnramifiedWithRespectTo A L)
    (q : PrimeSpectrum B)
    (hq : q.asIdeal.under A = IsLocalRing.maximalIdeal A) :
    Algebra.IsUnramifiedAt A q.asIdeal := by
  -- A prime above the maximal ideal is maximal because the integral-closure map is integral.
  have hqmax_comap :
      (Ideal.comap (algebraMap A (integralClosure A L)) q.asIdeal).IsMaximal := by
    simpa [Ideal.under_def, hq] using
      (IsLocalRing.maximalIdeal.isMaximal A :
        Ideal.IsMaximal (IsLocalRing.maximalIdeal A))
  letI : q.asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q.asIdeal hqmax_comap
  letI : q.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) :=
    (Ideal.liesOver_iff q.asIdeal (IsLocalRing.maximalIdeal A)).2 hq.symm
  letI : Module.IsTorsionFree A L := .trans_faithfulSMul A (FractionRing A) L
  letI : Module.IsTorsionFree A (integralClosure A L) := IsIntegralClosure.isTorsionFree A L
  letI : IsUnramifiedWithRespectTo A L := hL
  -- Now the closed-fiber branch matches the owner theorem from Definition `15.112.7`.
  simpa using IsUnramifiedWithRespectTo.isUnramifiedAt (A := A) (L := L) q.asIdeal

/-- Helper for Lemma 15.112.8: if every prime of a finitely presented algebra is étale, then the
whole algebra is étale. -/
private theorem etale_of_forall_prime_isEtaleAt_finitePresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (h : ∀ q : PrimeSpectrum S, Algebra.IsEtaleAt R q.asIdeal) :
    Algebra.Etale R S := by
  have hsubset : ↑(PrimeSpectrum.basicOpen (1 : S)) ⊆ Algebra.etaleLocus R S := by
    intro q _hq
    -- Proof comment: every prime belongs to the étale locus because the hypothesis is global.
    exact (Algebra.mem_etaleLocus_iff (R := R) (A := S) (p := q)).2 (h q)
  have hAway : Algebra.Etale R (Localization.Away (1 : S)) :=
    (Algebra.basicOpen_subset_etaleLocus_iff_etale (R := R) (A := S)).1 hsubset
  let eS : S ≃ₐ[S] Localization.Away (1 : S) :=
    IsLocalization.atUnit S (Localization.Away (1 : S)) 1 isUnit_one
  let e : Localization.Away (1 : S) ≃ₐ[R] S := eS.symm.restrictScalars R
  -- Proof comment: localizing away from `1` does nothing, so the away-model descends to `S`.
  let _ : Algebra.Etale R (Localization.Away (1 : S)) := hAway
  exact Algebra.Etale.of_equiv e

/-- Helper for Lemma 15.112.8: if `L` is unramified with respect to the base discrete valuation
ring, then its integral closure is already a finite étale `A`-algebra. -/
private theorem integralClosure_etale_of_isUnramifiedWithRespectTo
    (hL : IsUnramifiedWithRespectTo A L) :
    Algebra.Etale A B := by
  let _ := hL
  let _ : Module.Finite A B := IsIntegralClosure.finite A K L B
  let _ : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  let _ : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finitePresentation A B
  let _ : Module.Flat A B := integralClosure_flat_over_dvr (A := A) (L := L)
  have hPrime : ∀ q : PrimeSpectrum B, Algebra.IsEtaleAt A q.asIdeal := by
    intro q
    rcases prime_under_eq_bot_or_maximalIdeal (A := A) (L := L) q with hq | hq
    · have hqbot : q.asIdeal = ⊥ :=
        zero_contraction_prime_eq_bot_of_integralClosure (A := A) (L := L) q hq
      -- Proof comment: the generic-contraction branch collapses to the unique zero prime.
      simpa [hqbot] using zeroPrime_isEtaleAt_integralClosure (A := A) (L := L)
    · let _ : Algebra.IsUnramifiedAt A q.asIdeal :=
        closedFiber_branch_isUnramifiedAt (A := A) (L := L) hL q hq
      -- Proof comment: on the closed fiber, flatness upgrades unramifiedness to étaleness.
      exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat (R := A) (S := B) q.asIdeal
  -- Proof comment: the pointwise local-étale statement globalizes by finite presentation.
  exact etale_of_forall_prime_isEtaleAt_finitePresentation (R := A) (S := B) hPrime

end IntegralClosureClosedFiber

section NormalClosure

variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]

local notation "K" => FractionRing A
local notation "N" => normalClosure K L (AlgebraicClosure L)

-- Proof sketch: take the canonical normal closure `normalClosure K L (AlgebraicClosure L)`;
-- Lemma `9.21.5` gives its Galois structure over `K`, and the remaining input is the companion
-- bridge that this normal closure is still unramified with respect to `A`.
/-- Companion bridge for Lemma 15.112.8 (2): the canonical normal closure witness inside
`AlgebraicClosure L` is itself unramified with respect to `A`. -/
theorem isUnramifiedWithRespectTo_normalClosure
    (hL : IsUnramifiedWithRespectTo A L) :
    IsUnramifiedWithRespectTo A N := by
  -- Route correction: the source proof does not localize first. It starts from the surjective
  -- embedding-indexed tensor-product map onto the normal closure and then selects one Dedekind
  -- factor on the integral side.
  have hEtaleIntegralClosure : Algebra.Etale A (integralClosure A L) :=
    integralClosure_etale_of_isUnramifiedWithRespectTo (A := A) (L := L) hL
  -- TODO: upgrade the generic-fiber tensor map to the integral tensor algebra on
  -- `integralClosure A L`, use global étaleness of that integral closure to split the tensor
  -- algebra as a finite product of Dedekind domains, and then apply the product-factor map into
  -- the domain `integralClosure A N`. The remaining blocker is now the source-faithful tensor
  -- endgame from the integral model to the normal-closure field factor, not the local étale
  -- bridge on `integralClosure A L`.
  let _ : Algebra.Etale A (integralClosure A L) := hEtaleIntegralClosure
  sorry

/-- Lemma 15.112.8 (2): if `L / K` is finite separable and unramified with respect to `A`, then
there exists a finite Galois extension of `K` containing `L` that is still unramified with
respect to `A`. The canonical witness is the normal closure of `L / K` inside
`AlgebraicClosure L`. -/
theorem exists_isGalois_unramifiedWithRespectTo
    (hL : IsUnramifiedWithRespectTo A L) :
    ∃ (M : Type v) (_ : Field M) (_ : Algebra A M) (_ : Algebra K M) (_ : Algebra L M)
      (_ : IsScalarTower A K M),
      IsScalarTower K L M ∧ FiniteDimensional K M ∧ IsGalois K M ∧
        IsUnramifiedWithRespectTo A M := by
  refine ⟨N, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact
    ⟨inferInstance, ⟨inferInstance,
      ⟨isGalois_normalClosure_of_separable, isUnramifiedWithRespectTo_normalClosure hL⟩⟩⟩

end NormalClosure

section CommonExtension

variable {L₁ : Type v} [Field L₁] [Algebra A L₁] [Algebra (FractionRing A) L₁]
  [IsScalarTower A (FractionRing A) L₁]
variable {L₂ : Type w} [Field L₂] [Algebra A L₂] [Algebra (FractionRing A) L₂]
  [IsScalarTower A (FractionRing A) L₂]
variable [FiniteDimensional (FractionRing A) L₁] [FiniteDimensional (FractionRing A) L₂]
variable [Algebra.IsSeparable (FractionRing A) L₁] [Algebra.IsSeparable (FractionRing A) L₂]

local notation "K" => FractionRing A

/-- Helper for Lemma 15.112.8: the integral tensor product of two unramified integral-closure
models is again étale over the base discrete valuation ring. -/
private theorem tensorProduct_integralClosures_etale_of_isUnramifiedWithRespectTo
    (hL₁ : IsUnramifiedWithRespectTo A L₁) (hL₂ : IsUnramifiedWithRespectTo A L₂) :
    Algebra.Etale A ((integralClosure A L₁) ⊗[A] (integralClosure A L₂)) := by
  let _ : Algebra.Etale A (integralClosure A L₁) :=
    integralClosure_etale_of_isUnramifiedWithRespectTo (A := A) (L := L₁) hL₁
  let _ : Algebra.Etale A (integralClosure A L₂) :=
    integralClosure_etale_of_isUnramifiedWithRespectTo (A := A) (L := L₂) hL₂
  -- Proof comment: base-change and composition are the permanence steps used in the source proof.
  let _ : Algebra.Etale (integralClosure A L₁)
      ((integralClosure A L₁) ⊗[A] (integralClosure A L₂)) :=
    Algebra.Etale.baseChange A (integralClosure A L₂) (integralClosure A L₁)
  exact
    Algebra.Etale.comp A (integralClosure A L₁)
      ((integralClosure A L₁) ⊗[A] (integralClosure A L₂))

/-- Helper for Lemma 15.112.8: the integral tensor product of the two unramified integral
closures splits as a finite product of Dedekind domains. -/
private theorem exists_finite_product_dedekindDomain_of_integralClosure_tensorProduct
    (hL₁ : IsUnramifiedWithRespectTo A L₁) (hL₂ : IsUnramifiedWithRespectTo A L₂) :
    ∃ (ι : Type (max u v w)) (_ : Finite ι) (R : ι → Type (max u v w))
      (_ : ∀ i, CommRing (R i)) (_ : ∀ i, IsDedekindDomain (R i)),
      Nonempty (((integralClosure A L₁) ⊗[A] (integralClosure A L₂)) ≃+* Π i, R i) := by
  let _ : Algebra.Etale A ((integralClosure A L₁) ⊗[A] (integralClosure A L₂)) :=
    tensorProduct_integralClosures_etale_of_isUnramifiedWithRespectTo
      (A := A) (L₁ := L₁) (L₂ := L₂) hL₁ hL₂
  -- Proof comment: once the tensor algebra is globally étale, Lemma `15.44.4` gives the
  -- Dedekind-factor decomposition required by the source argument.
  exact
    exists_finite_product_dedekindDomain_of_etale
      (A := A) (B := (integralClosure A L₁) ⊗[A] (integralClosure A L₂))

-- Proof sketch: embed both fields into a common normal closure and then pass to the compositum of
-- their images; `IntermediateField.finiteDimensional_sup` and
-- `IntermediateField.isSeparable_sup` provide the canonical finite/separable overfield owner.
/-- Lemma 15.112.8 (3): two finite separable extensions of `K` that are unramified with respect to
`A` embed in a common finite separable extension that is unramified with respect to `A`. -/
theorem exists_common_unramifiedWithRespectTo_extension
    (hL₁ : IsUnramifiedWithRespectTo A L₁) (hL₂ : IsUnramifiedWithRespectTo A L₂) :
    ∃ (L : Type (max v w)) (_ : Field L) (_ : Algebra A L) (_ : Algebra K L)
      (_ : Algebra L₁ L) (_ : Algebra L₂ L) (_ : IsScalarTower A K L),
      IsScalarTower K L₁ L ∧ IsScalarTower K L₂ L ∧
        FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
        IsUnramifiedWithRespectTo A L := by
  -- Route correction: keep the source witness field on the generic tensor-product side
  -- `(L₁ ⊗[K] L₂) ⧸ m`, and use the integral tensor product
  -- `integralClosure A L₁ ⊗[A] integralClosure A L₂` only to build the
  -- unramified Dedekind-domain model for that field.
  have hTensorEtale :
      Algebra.Etale A ((integralClosure A L₁) ⊗[A] (integralClosure A L₂)) :=
    tensorProduct_integralClosures_etale_of_isUnramifiedWithRespectTo
      (A := A) (L₁ := L₁) (L₂ := L₂) hL₁ hL₂
  have hTensorFactors :=
    exists_finite_product_dedekindDomain_of_integralClosure_tensorProduct
      (A := A) (L₁ := L₁) (L₂ := L₂) hL₁ hL₂
  -- TODO: use the two global étale integral-closure models to show
  -- `integralClosure A L₁ ⊗[A] integralClosure A L₂` is finite étale over `A`, split it into
  -- Dedekind factors, and then apply the product-factor map to the chosen generic tensor-product
  -- branch field. The remaining blocker is now the common tensor-product factor extraction on the
  -- integral side, not the proof that `A → integralClosure A Lᵢ` is étale.
  let _ : Algebra.Etale A ((integralClosure A L₁) ⊗[A] (integralClosure A L₂)) := hTensorEtale
  have _ := hTensorFactors
  sorry

end CommonExtension

end
