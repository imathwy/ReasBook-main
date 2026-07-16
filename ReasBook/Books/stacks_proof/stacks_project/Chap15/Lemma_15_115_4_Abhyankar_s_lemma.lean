import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_37_3
import stacks_proof.stacks_project.Chap15.Definition_15_112_1
import stacks_proof.stacks_project.Chap15.Definition_15_112_7
import stacks_proof.stacks_project.Chap15.Lemma_15_112_3
import stacks_proof.stacks_project.Chap15.Lemma_15_112_5
import stacks_proof.stacks_project.Chap15.Lemma_15_37_2
import stacks_proof.stacks_project.Chap15.Lemma_15_108_3
import stacks_proof.stacks_project.Chap15.Lemma_15_115_2
import stacks_proof.stacks_project.Chap15.Lemma_15_115_3
import stacks_proof.stacks_project.Chap15.Remark_15_115_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped TensorProduct

universe u v w x y

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra A K1] [Algebra K K1]
variable [IsScalarTower A K K1] [FiniteDimensional K K1]

local notation "A1" => integralClosure A K1
local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

local instance : CommRing L1 :=
  Ideal.Quotient.commRing _

/- Domain-style sampling for Abhyankar's lemma:
- primary domain: tamely ramified extensions of discrete valuation rings and the localized branch
  maps on the reduced tensor-product integral closure from Remark `15.115.1` /
  Definition `15.116.1`;
- sampled owner declarations:
  `reducedTensorBaseChangeIntegralClosureMap`,
  `isExtensionOfDiscreteValuationRings_localizationBranch`,
  `PrimeToResidueCharacteristic`,
  `formallySmoothForAdic_localization_baseChange_integralClosure`;
- best owner abstraction: the source-facing branch ring is
  `B₁ = integralClosure B ((L ⊗[K] K₁)_red)`;
  the canonical owner in the chapter is the branch map `A₁ → B₁` from Remark `15.115.1`, while
  the tensor product `A₁ ⊗[A] B` is only the comparison bridge and should not be the public owner
  here;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, the fraction
  field extension `K₁ / K`, and the branch ideals `m` and `n`; residue-field separability,
  prime-to-residue-characteristic ramification, and the localized formally smooth branch map on
  `A₁ → B₁` are derived API from the chapter owners.

Source/core/bridge triage:
- `source-facing`: Abhyankar's lemma for localized branches `(A₁)_m → (B₁)_n`;
- `core/canonical`: `ResidueField A`, `ResidueField B`, `ramificationIndex A B`,
  `reducedTensorBaseChangeIntegralClosureMap`, and `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the tensor-base-change presentation `A₁ ⊗[A] B ≃ₐ[A₁] B₁`, available only as
  companion API after the formal-smoothness comparison from Lemma `15.115.3`.
-/

-- Proof sketch: after adjoining an `e`th root of a suitable uniformizer unit, reduce to the
-- Kummer case `K₁ = K[π^(1/e)]`. Lemma `15.115.2` identifies the corresponding integral closure
-- `A₁` as a totally ramified degree-`e` extension, and the coprimality hypothesis makes the
-- induced branch extension on the reduced tensor-product integral closure `B₁` finite étale.
-- Then the local factors above `m` are weakly unramified with separable residue field over
-- `(A₁)_m`, so Lemma `15.112.5` yields formal smoothness for the maximal-ideal-adic topology.
/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): the residue fields in a tower of local discrete
valuation rings form a scalar tower. -/
private theorem residueField_isScalarTower_of_dvr_tower
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S T]
    [IsExtensionOfDiscreteValuationRings R T] :
    let hRS : maximalIdeal R = Ideal.comap (algebraMap R S) (maximalIdeal S) :=
      (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm
    let hST : maximalIdeal S = Ideal.comap (algebraMap S T) (maximalIdeal T) :=
      (IsLocalRing.maximalIdeal_comap (algebraMap S T)).symm
    let hRT : maximalIdeal R = Ideal.comap (algebraMap R T) (maximalIdeal T) :=
      (IsLocalRing.maximalIdeal_comap (algebraMap R T)).symm
    let _ :=
      (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S) hRS).toAlgebra
    let _ :=
      (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal T) (algebraMap S T) hST).toAlgebra
    let _ :=
      (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal T) (algebraMap R T) hRT).toAlgebra
    IsScalarTower ((maximalIdeal R).ResidueField) ((maximalIdeal S).ResidueField)
      ((maximalIdeal T).ResidueField) := by
  -- Compare the two residue-field maps on residue classes coming from the base ring `R`.
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  obtain ⟨a, rfl⟩ := (maximalIdeal R).algebraMap_residueField_surjective x
  rw [Ideal.ResidueField.map_algebraMap (maximalIdeal R) (maximalIdeal T) (algebraMap R T) hRT a,
    Ideal.ResidueField.map_algebraMap (maximalIdeal R) (maximalIdeal S) (algebraMap R S) hRS a]
  rw [IsScalarTower.algebraMap_apply R S T]
  exact
    (Ideal.ResidueField.map_algebraMap (maximalIdeal S) (maximalIdeal T) (algebraMap S T)
      hST ((algebraMap R S) a)).symm

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): weakly unramifiedness descends along a tower of
extensions of discrete valuation rings. -/
private theorem weakly_unramified_left_of_dvr_tower
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S T]
    [IsExtensionOfDiscreteValuationRings R T]
    (hRT : WeaklyUnramified R T) :
    WeaklyUnramified R S := by
  -- Compare ramification indices in the tower and read off the left factor from `e(R,T) = 1`.
  have hRT_one :
      ramificationIndex R T = 1 :=
    (weaklyUnramified_iff_ramificationIndex_eq_one (A := R) (B := T)).1 hRT
  have hmul :
      ramificationIndex R S * ramificationIndex S T = 1 := by
    calc
      ramificationIndex R S * ramificationIndex S T = ramificationIndex R T := by
        symm
        exact ramificationIndex_algebra_tower (A := R) (B := S) (C := T)
      _ = 1 := hRT_one
  have hRS_one : ramificationIndex R S = 1 :=
    Nat.eq_one_of_dvd_one ⟨ramificationIndex S T, hmul.symm⟩
  -- Repackage the ramification-index equality as weakly unramifiedness.
  exact (weaklyUnramified_iff_ramificationIndex_eq_one (A := R) (B := S)).2 hRS_one

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): weakly unramifiedness composes along a tower of
extensions of discrete valuation rings. -/
private theorem weakly_unramified_of_dvr_tower
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S T]
    [IsExtensionOfDiscreteValuationRings R T]
    (hRS : WeaklyUnramified R S) (hST : WeaklyUnramified S T) :
    WeaklyUnramified R T := by
  -- Convert both hypotheses to ramification-index-one statements and multiply in the tower.
  have hRS_one :
      ramificationIndex R S = 1 :=
    (weaklyUnramified_iff_ramificationIndex_eq_one (A := R) (B := S)).1 hRS
  have hST_one :
      ramificationIndex S T = 1 :=
    (weaklyUnramified_iff_ramificationIndex_eq_one (A := S) (B := T)).1 hST
  have hRT_one :
      ramificationIndex R T = 1 := by
    calc
      ramificationIndex R T = ramificationIndex R S * ramificationIndex S T := by
        symm
        exact ramificationIndex_algebra_tower (A := R) (B := S) (C := T)
      _ = 1 * 1 := by rw [hRS_one, hST_one]
      _ = 1 := by simp
  -- Repackage the composite ramification computation as weakly unramifiedness.
  exact (weaklyUnramified_iff_ramificationIndex_eq_one (A := R) (B := T)).2 hRT_one

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): formal smoothness for the maximal-ideal-adic
topology descends along a tower of extensions of discrete valuation rings. -/
private theorem formally_smooth_left_of_dvr_tower
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S T]
    [IsExtensionOfDiscreteValuationRings R T]
    (hRT : (algebraMap R T).formally_smooth_for_adic (maximalIdeal T)) :
    (algebraMap R S).formally_smooth_for_adic (maximalIdeal S) := by
  -- Unpack formal smoothness on the composite branch into weakly unramifiedness plus residue-field
  -- separability, then descend each factor separately along the DVR tower.
  rw [formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField] at hRT ⊢
  let hRS : maximalIdeal R = Ideal.comap (algebraMap R S) (maximalIdeal S) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm
  let hST : maximalIdeal S = Ideal.comap (algebraMap S T) (maximalIdeal T) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap S T)).symm
  let hRT' : maximalIdeal R = Ideal.comap (algebraMap R T) (maximalIdeal T) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R T)).symm
  let _ : Algebra (ResidueField R) (ResidueField S) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S) hRS).toAlgebra
  let _ : Algebra (ResidueField S) (ResidueField T) :=
    (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal T) (algebraMap S T) hST).toAlgebra
  let _ : Algebra (ResidueField R) (ResidueField T) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal T) (algebraMap R T) hRT').toAlgebra
  let _ : IsScalarTower (ResidueField R) (ResidueField S) (ResidueField T) :=
    residueField_isScalarTower_of_dvr_tower (R := R) (S := S) (T := T)
  refine ⟨weakly_unramified_left_of_dvr_tower hRT.1, ?_⟩
  -- Separability descends through the residue-field tower `κ(R) ⊂ κ(S) ⊂ κ(T)`.
  exact Algebra.isSeparable_tower_bot_of_isSeparable
    (ResidueField R) (ResidueField S) (ResidueField T)

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): maximal-ideal-adic formal smoothness composes
along a tower of extensions of discrete valuation rings. -/
private theorem formally_smooth_of_dvr_tower
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S T]
    [IsExtensionOfDiscreteValuationRings R T]
    (hRS : (algebraMap R S).formally_smooth_for_adic (maximalIdeal S))
    (hST : (algebraMap S T).formally_smooth_for_adic (maximalIdeal T)) :
    (algebraMap R T).formally_smooth_for_adic (maximalIdeal T) := by
  -- Unpack both formally smooth maps into weak ramification plus separable residue fields.
  rw [formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField] at hRS hST ⊢
  let hRS' : maximalIdeal R = Ideal.comap (algebraMap R S) (maximalIdeal S) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm
  let hST' : maximalIdeal S = Ideal.comap (algebraMap S T) (maximalIdeal T) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap S T)).symm
  let hRT' : maximalIdeal R = Ideal.comap (algebraMap R T) (maximalIdeal T) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R T)).symm
  let _ : Algebra (ResidueField R) (ResidueField S) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S) hRS').toAlgebra
  let _ : Algebra (ResidueField S) (ResidueField T) :=
    (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal T) (algebraMap S T) hST').toAlgebra
  let _ : Algebra (ResidueField R) (ResidueField T) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal T) (algebraMap R T) hRT').toAlgebra
  let _ : IsScalarTower (ResidueField R) (ResidueField S) (ResidueField T) :=
    residueField_isScalarTower_of_dvr_tower (R := R) (S := S) (T := T)
  refine ⟨weakly_unramified_of_dvr_tower hRS.1 hST.1, ?_⟩
  -- Residue-field separability is transitive along the same tower.
  letI : Algebra.IsSeparable (ResidueField R) (ResidueField S) := hRS.2
  letI : Algebra.IsSeparable (ResidueField S) (ResidueField T) := hST.2
  exact Algebra.IsSeparable.trans (ResidueField R) (ResidueField S) (ResidueField T)

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): after adjoining a local unit root, the source
square reduces formal smoothness of the original branch to formal smoothness of the bottom
horizontal extension and the enlarged right-hand branch. -/
private theorem branch_formally_smooth_of_adjoined_unit_root
    {R : Type*} {R' : Type*} {S : Type*} {S' : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing S'] [IsDomain S'] [IsDiscreteValuationRing S']
    [Algebra R R'] [Algebra R S] [Algebra R S'] [Algebra R' S'] [Algebra S S']
    [IsScalarTower R R' S'] [IsScalarTower R S S']
    [IsExtensionOfDiscreteValuationRings R R']
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings R S']
    [IsExtensionOfDiscreteValuationRings R' S']
    [IsExtensionOfDiscreteValuationRings S S']
    (h_bottom : (algebraMap R R').formally_smooth_for_adic (maximalIdeal R'))
    (h_right : (algebraMap R' S').formally_smooth_for_adic (maximalIdeal S')) :
    (algebraMap R S).formally_smooth_for_adic (maximalIdeal S) := by
  -- First compose formal smoothness along the lower tower `R → R' → S'`.
  have h_composite :
      (algebraMap R S').formally_smooth_for_adic (maximalIdeal S') :=
    formally_smooth_of_dvr_tower
      (R := R) (S := R') (T := S') h_bottom h_right
  -- Then descend from `R → S'` to the original left branch `R → S`.
  exact formally_smooth_left_of_dvr_tower
    (R := R) (S := S) (T := S') h_composite

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): localizing at a prime commutes with transport
across a ring equivalence once the target prime is the image ideal. -/
private noncomputable theorem localization_atPrime_ringEquiv_of_map_prime
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : Ideal R) [q.IsPrime] :
    Localization.AtPrime q ≃+* Localization.AtPrime (Ideal.map e.toRingHom q) := by
  have hPrimeCompl :
      Submonoid.map e.toMonoidHom q.primeCompl =
        (Ideal.map e.toRingHom q).primeCompl := by
    -- Compare the prime complements elementwise through the equivalence.
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ hy
      rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hy
      rcases hy with ⟨z, hz, hzx⟩
      exact hx (e.injective hzx ▸ hz)
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      intro hx
      exact hy (Ideal.mem_map_of_mem e.toRingHom hx)
  -- The localization universal property now gives the transported local ring equivalence.
  exact
    IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime q)
      (Localization.AtPrime (Ideal.map e.toRingHom q))
      e hPrimeCompl

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): maximality is preserved when an ideal is
transported across a ring equivalence. -/
private theorem ideal_map_isMaximal_of_ringEquiv
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : Ideal R) [q.IsMaximal] :
    (Ideal.map e.toRingHom q).IsMaximal := by
  -- Push maximality along the surjective equivalence map.
  refine Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := e.toRingHom) e.surjective ?_
  simpa using (show RingHom.ker e.toRingHom ≤ q from by simp)

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): contracting after transporting an ideal across
a compatible ring equivalence agrees with contracting before transport. -/
private theorem ideal_map_comap_eq_of_ringEquiv_comp
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) (e : S ≃+* T)
    (he : e.toRingHom.comp f = g) (q : Ideal S) :
    (Ideal.map e.toRingHom q).comap g = q.comap f := by
  ext x
  -- Rewrite the contraction through the equivalence and reduce to membership in the original ideal.
  rw [Ideal.mem_comap, ← he, RingHom.comp_apply]
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact e.injective hyx ▸ hy
  · intro hx
    exact ⟨f x, hx, rfl⟩

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): lies-over is preserved when a branch ideal is
transported across a compatible ring equivalence. -/
private theorem ideal_map_liesOver_of_ringEquiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (e : S ≃+* T)
    (he : e.toRingHom.comp (algebraMap R S) = algebraMap R T)
    (p : Ideal R) (q : Ideal S) [q.LiesOver p] :
    (Ideal.map e.toRingHom q).LiesOver p := by
  -- Compare contractions after transport and then reuse the original lies-over identity.
  rw [Ideal.liesOver_iff]
  simpa [Ideal.liesOver_iff] using
    (ideal_map_comap_eq_of_ringEquiv_comp
      (f := algebraMap R S) (g := algebraMap R T) e he q).trans (q.over_def p)

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): once the global branch map is identified with a
transported branch by a compatible ring equivalence, the localized branch maps are conjugate. -/
private theorem localization_localRingHom_conjugation_of_ringEquiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (e : S ≃+* T)
    (he : e.toRingHom.comp (algebraMap R S) = algebraMap R T)
    (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsMaximal] [q.LiesOver p] :
    let qT : Ideal T := Ideal.map e.toRingHom q
    let _ : qT.IsMaximal := ideal_map_isMaximal_of_ringEquiv e q
    let _ : qT.LiesOver p := ideal_map_liesOver_of_ringEquiv e he p q
    let eLoc : Localization.AtPrime q ≃+* Localization.AtPrime qT :=
      localization_atPrime_ringEquiv_of_map_prime e q
    eLoc.toRingHom.comp
        (Localization.localRingHom p q
          (algebraMap R S) (q.over_def p)) =
      Localization.localRingHom p qT
        (algebraMap R T) (qT.over_def p) := by
  let qT : Ideal T := Ideal.map e.toRingHom q
  let _ : qT.IsMaximal := ideal_map_isMaximal_of_ringEquiv e q
  let _ : qT.LiesOver p := ideal_map_liesOver_of_ringEquiv e he p q
  let eLoc : Localization.AtPrime q ≃+* Localization.AtPrime qT :=
    localization_atPrime_ringEquiv_of_map_prime e q
  -- Both localized maps are characterized by the same induced map `R → T` after transport.
  refine Localization.localRingHom_unique
    p qT (algebraMap R T) (qT.over_def p) fun x ↦ ?_
  simp only [eLoc, RingHom.comp_apply, Localization.localRingHom_to_map]
  simpa using congrArg (fun f : R →+* T ↦ f x) he

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): an étale-at prime localization is formally
smooth for the maximal-ideal-adic topology. -/
private theorem formally_smooth_localizationAtPrime_of_isEtaleAt
    {R : Type*} {S : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime]
    (hq : Algebra.IsEtaleAt R q) :
    (algebraMap R (Localization.AtPrime q)).formally_smooth_for_adic
      (maximalIdeal (Localization.AtPrime q)) := by
  -- Unpack the owner `IsEtaleAt`: it is exactly formal étaleness of the prime localization.
  let h_formallyEtale : Algebra.FormallyEtale R (Localization.AtPrime q) := hq
  exact formally_smooth_for_adic_maximalIdeal_of_formallyEtale
    ((RingHom.formallyEtale_algebraMap).2 h_formallyEtale)

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): an étale basic-open neighborhood around a prime
already forces the localized factor to be formally smooth for the maximal-ideal-adic topology. -/
private theorem formally_smooth_localizationAtPrime_of_exists_etale_away
    {R : Type*} {S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [FinitePresentation R S]
    (q : Ideal S) [q.IsPrime]
    (hq : ∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g)) :
    (algebraMap R (Localization.AtPrime q)).formally_smooth_for_adic
      (maximalIdeal (Localization.AtPrime q)) := by
  let p : PrimeSpectrum S := ⟨q, inferInstance⟩
  obtain ⟨g, hgq, hEtale⟩ := hq
  have hp_mem : p ∈ Algebra.etaleLocus R S := by
    -- The chosen basic open lies in the étale locus, so the selected prime is an étale point.
    have hbasic :
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆ Algebra.etaleLocus R S :=
      (Algebra.basicOpen_subset_etaleLocus_iff_etale (R := R) (A := S)).2 hEtale
    exact hbasic (by simpa [PrimeSpectrum.mem_basicOpen] using hgq)
  -- Repackage the étale-locus membership as the formally étale local owner and conclude.
  exact formally_smooth_localizationAtPrime_of_isEtaleAt
    (R := R) (S := S) (q := q)
    ((Algebra.mem_etaleLocus_iff (R := R) (A := S) (p := p)).1 hp_mem)

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): in a commutative ring, an element whose
positive power is a unit is itself a unit. -/
private theorem isUnit_of_pow_of_pos
    {R : Type*} [CommRing R] {x : R} {n : ℕ}
    (hn : 1 ≤ n) (hx : IsUnit (x ^ n)) :
    IsUnit x := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le Nat.zero_lt_one hn))
    with ⟨m, rfl⟩
  -- Peel off one factor from the unit power and cancel it.
  simpa [pow_succ] using isUnit_of_mul_isUnit_left hx

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): in the unit-root quotient
`R[X] / (X^e - u)`, the distinguished root is a unit as soon as `e > 0`. -/
private theorem adjoinRoot_root_isUnit_of_unit_root_polynomial
    {R : Type*} [CommRing R] (u : Rˣ) (e : ℕ) (he : 1 ≤ e) :
    IsUnit (AdjoinRoot.root (X ^ e - C (u : R) : Polynomial R)) := by
  let f : Polynomial R := X ^ e - C (u : R)
  have hpow :
      AdjoinRoot.root f ^ e = algebraMap R (AdjoinRoot f) (u : R) := by
    -- Evaluate the defining relation of the quotient root and rearrange the polynomial identity.
    simpa [f, sub_eq_zero] using (AdjoinRoot.eval₂_root f)
  have hpow_unit : IsUnit (AdjoinRoot.root f ^ e) := by
    rw [hpow]
    exact IsUnit.map (algebraMap R (AdjoinRoot f)) u.isUnit
  -- The root itself is a unit because a positive power of it is a unit.
  simpa [f] using isUnit_of_pow_of_pos (x := AdjoinRoot.root f) he hpow_unit

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): the branch prime in the unit-root quotient
cannot contain the distinguished root, because that root is already a unit. -/
private theorem adjoinRoot_root_not_mem_prime_of_unit_root_polynomial
    {R : Type*} [CommRing R] (u : Rˣ) (e : ℕ) (he : 1 ≤ e)
    (q : Ideal (AdjoinRoot (X ^ e - C (u : R) : Polynomial R))) [q.IsPrime] :
    AdjoinRoot.root (X ^ e - C (u : R) : Polynomial R) ∉ q := by
  have hunit :
      IsUnit (AdjoinRoot.root (X ^ e - C (u : R) : Polynomial R)) :=
    adjoinRoot_root_isUnit_of_unit_root_polynomial u e he
  -- A proper prime ideal cannot contain a unit.
  intro hmem
  exact q.ne_top (Ideal.eq_top_of_isUnit_mem q hunit hmem)

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): a natural number that is prime to the residue
characteristic of a local ring maps to a unit in that ring. -/
private theorem natCast_isUnit_of_primeToResidueCharacteristic
    {R : Type*} [CommRing R] [IsLocalRing R] {e : ℕ}
    (he : 1 ≤ e) (hprime : PrimeToResidueCharacteristic R e) :
    IsUnit (e : R) := by
  have hres_ne_zero : IsLocalRing.residue R (e : R) ≠ 0 := by
    intro hzero
    let p : ℕ := ringChar (ResidueField R)
    have hp_dvd : p ∣ e := by
      exact (ringChar.spec (ResidueField R) e).mp hzero
    have hp_ne_zero : p ≠ 0 := by
      intro hp0
      rw [hp0, zero_dvd_iff] at hp_dvd
      exact Nat.not_eq_of_lt he hp_dvd
    letI : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero (ResidueField R) hp_ne_zero⟩
    have hcoprime : Nat.Coprime e p := hprime p
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hcoprime hp_dvd
  -- A nonzero residue class is equivalent to being a unit in the local source ring.
  exact (IsLocalRing.residue_ne_zero_iff_isUnit (R := R) (x := (e : R))).1 hres_ne_zero

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): in the unit-root quotient
`R[X] / (X^e - u)`, the basic open obtained by inverting the distinguished root is étale. -/
private theorem unit_root_away_root_etale
    {R : Type*} [CommRing R] [IsLocalRing R]
    (u : Rˣ) (e : ℕ) (he : 1 ≤ e) (hprime : PrimeToResidueCharacteristic R e) :
    Algebra.Etale R
      (Localization.Away (AdjoinRoot.root (X ^ e - C (u : R) : Polynomial R))) := by
  have he_nat_unit : IsUnit (e : R) :=
    natCast_isUnit_of_primeToResidueCharacteristic (R := R) he hprime
  let P : Algebra.StandardEtalePair R :=
    { f := X ^ e - C (u : R)
      monic_f := by
        exact Polynomial.monic_X_pow_sub_C (u : R) (Nat.ne_of_lt (lt_of_lt_of_le Nat.zero_lt_one he))
      g := X
      cond := by
        refine ⟨Polynomial.C ↑(he_nat_unit.unit⁻¹), 0, e - 1, ?_⟩
        -- The derivative is `e * X^(e-1)`, and `e` is already a unit in the local base ring.
        calc
          Polynomial.derivative (X ^ e - C (u : R) : Polynomial R) *
              Polynomial.C ↑(he_nat_unit.unit⁻¹) +
            (X ^ e - C (u : R) : Polynomial R) * 0
              = (Polynomial.C (e : R) * X ^ (e - 1)) *
                  Polynomial.C ↑(he_nat_unit.unit⁻¹) := by
                  simp [Polynomial.derivative_X_pow]
          _ = Polynomial.C ((e : R) * ↑(he_nat_unit.unit⁻¹)) * X ^ (e - 1) := by
                simp [Polynomial.C_mul, mul_assoc, mul_comm, mul_left_comm]
          _ = Polynomial.C (1 : R) * X ^ (e - 1) := by
                congr 1
                exact Units.val_mul_inv (he_nat_unit.unit)
          _ = X ^ (e - 1) := by simp }
  letI : Algebra.Etale R P.Ring := inferInstance
  -- Transport the standard-étale owner across the explicit away-localization equivalence.
  simpa [P, AdjoinRoot.mk_X] using Algebra.Etale.of_equiv P.equivAwayAdjoinRoot

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): localizing a unit-root branch at any prime
factor is formally smooth for the maximal-ideal-adic topology. -/
private theorem localized_unit_root_factor_formally_smooth
    {R : Type*} [CommRing R] [IsLocalRing R]
    (u : Rˣ) (e : ℕ) (he : 1 ≤ e) (hprime : PrimeToResidueCharacteristic R e)
    (q : Ideal (AdjoinRoot (X ^ e - C (u : R) : Polynomial R))) [q.IsPrime] :
    (algebraMap R (Localization.AtPrime q)).formally_smooth_for_adic
      (maximalIdeal (Localization.AtPrime q)) := by
  -- The chosen branch prime lies in the étale basic open where the distinguished root is inverted.
  refine formally_smooth_localizationAtPrime_of_exists_etale_away (R := R)
    (S := AdjoinRoot (X ^ e - C (u : R) : Polynomial R)) (q := q) ?_
  refine ⟨AdjoinRoot.root (X ^ e - C (u : R) : Polynomial R), ?_, ?_⟩
  · exact adjoinRoot_root_not_mem_prime_of_unit_root_polynomial u e he q
  · exact unit_root_away_root_etale (R := R) u e he hprime

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): a local target which is obtained by localizing
an étale algebra is formally smooth for the maximal-ideal-adic topology. -/
private theorem formally_smooth_of_etale_localization
    {R : Type*} {S : Type*}
    [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    (h :
      ∃ (C : Type*), CommRing C ∧ Algebra R C ∧ Algebra C S ∧ IsScalarTower R C S ∧
        ∃ M : Submonoid C, Algebra.Etale R C ∧ IsLocalization M S) :
    (algebraMap R S).formally_smooth_for_adic (maximalIdeal S) := by
  obtain ⟨C, _, _, _, _, M, hEtale, hLoc⟩ := h
  letI : Algebra.Etale R C := hEtale
  letI : Algebra.FormallyEtale R C := by
    rw [Algebra.formallyEtale_iff]
    infer_instance
  letI : IsLocalization M S := hLoc
  letI : Algebra.FormallyEtale C S := Algebra.FormallyEtale.of_isLocalization M
  letI : Algebra.FormallyEtale R S := inferInstance
  -- Compose the formally étale presentation with the localization step and conclude.
  exact formally_smooth_for_adic_maximalIdeal_of_formallyEtale
    ((RingHom.formallyEtale_algebraMap).2 inferInstance)

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): the local criterion from Lemma `15.108.3`
upgrades an injective local map with maximal-ideal equality and separable residue field to
maximal-ideal-adic formal smoothness. -/
private theorem formally_smooth_of_geometricallyUnibranch_local_hmax_separable
    {R : Type*} {S : Type*}
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsGeometricallyUnibranch R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S]
    (hinj : Function.Injective (algebraMap R S))
    (hmax : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S)
    (hsep : Algebra.IsSeparable (ResidueField R) (ResidueField S)) :
    (algebraMap R S).formally_smooth_for_adic (maximalIdeal S) := by
  -- First realize the local ring as a localization of an étale `R`-algebra.
  have hloc :
      ∃ (C : Type*), CommRing C ∧ Algebra R C ∧ Algebra C S ∧ IsScalarTower R C S ∧
        ∃ M : Submonoid C, Algebra.Etale R C ∧ IsLocalization M S :=
    exists_etale_localization_of_isGeometricallyUnibranch_of_injective_localHom
      (A := R) (B := S) hinj hmax hsep
  -- Then reuse the generic localization-of-etale bridge above.
  exact formally_smooth_of_etale_localization (R := R) (S := S) hloc

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): if two intermediate discrete valuation rings
inside the same top branch have the same ramification index over the base and one top step is
weakly unramified, then the other top step is weakly unramified as well. -/
private theorem weakly_unramified_of_equal_base_ramification_and_top
    {R : Type*} {S : Type*} {T : Type*} {U : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Algebra R S] [Algebra S U] [Algebra R U] [IsScalarTower R S U]
    [Algebra R T] [Algebra T U] [IsScalarTower R T U]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S U]
    [IsExtensionOfDiscreteValuationRings R U]
    [IsExtensionOfDiscreteValuationRings R T]
    [IsExtensionOfDiscreteValuationRings T U]
    (hbase : ramificationIndex R S = ramificationIndex R T)
    (hSU : WeaklyUnramified S U) :
    WeaklyUnramified T U := by
  -- Convert the weakly unramified hypothesis on `S → U` into the corresponding ramification
  -- computation, compare the two factorizations of `e(R,U)`, and cancel the common base factor.
  have hSU_one : ramificationIndex S U = 1 :=
    (weaklyUnramified_iff_ramificationIndex_eq_one (A := S) (B := U)).1 hSU
  have hRU_eq : ramificationIndex R U = ramificationIndex R S := by
    calc
      ramificationIndex R U = ramificationIndex R S * ramificationIndex S U := by
        symm
        exact ramificationIndex_algebra_tower (A := R) (B := S) (C := U)
      _ = ramificationIndex R S * 1 := by rw [hSU_one]
      _ = ramificationIndex R S := by simp
  have hcancel :
      ramificationIndex R T * ramificationIndex T U = ramificationIndex R T * 1 := by
    calc
      ramificationIndex R T * ramificationIndex T U = ramificationIndex R U := by
        symm
        exact ramificationIndex_algebra_tower (A := R) (B := T) (C := U)
      _ = ramificationIndex R S := hRU_eq
      _ = ramificationIndex R T := hbase
      _ = ramificationIndex R T * 1 := by simp
  have hTU_one : ramificationIndex T U = 1 := by
    refine Nat.eq_of_mul_eq_mul_left
      (IsExtensionOfDiscreteValuationRings.ramificationIndex_pos (A := R) (B := T)) ?_
    simpa using hcancel
  -- Repackage the ramification-index equality as weakly unramifiedness on `T → U`.
  exact (weaklyUnramified_iff_ramificationIndex_eq_one (A := T) (B := U)).2 hTU_one

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): in two residue-field towers over the same base
and top branch, separability along one intermediate residue extension and on the other base change
forces separability of the remaining top residue extension. -/
private theorem residueField_separable_of_two_dvr_towers
    {R : Type*} {S : Type*} {T : Type*} {U : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Algebra R S] [Algebra S U] [Algebra R U] [IsScalarTower R S U]
    [Algebra R T] [Algebra T U] [IsScalarTower R T U]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S U]
    [IsExtensionOfDiscreteValuationRings R U]
    [IsExtensionOfDiscreteValuationRings R T]
    [IsExtensionOfDiscreteValuationRings T U]
    (hRS : Algebra.IsSeparable (ResidueField R) (ResidueField S))
    (hRT : Algebra.IsSeparable (ResidueField R) (ResidueField T))
    (hSU : Algebra.IsSeparable (ResidueField S) (ResidueField U)) :
    Algebra.IsSeparable (ResidueField T) (ResidueField U) := by
  let hRS' : maximalIdeal R = Ideal.comap (algebraMap R S) (maximalIdeal S) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm
  let hSU' : maximalIdeal S = Ideal.comap (algebraMap S U) (maximalIdeal U) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap S U)).symm
  let hRU' : maximalIdeal R = Ideal.comap (algebraMap R U) (maximalIdeal U) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R U)).symm
  let _ : Algebra (ResidueField R) (ResidueField S) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S) hRS').toAlgebra
  let _ : Algebra (ResidueField S) (ResidueField U) :=
    (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal U) (algebraMap S U) hSU').toAlgebra
  let _ : Algebra (ResidueField R) (ResidueField U) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal U) (algebraMap R U) hRU').toAlgebra
  let _ : IsScalarTower (ResidueField R) (ResidueField S) (ResidueField U) :=
    residueField_isScalarTower_of_dvr_tower (R := R) (S := S) (T := U)
  letI : Algebra.IsSeparable (ResidueField R) (ResidueField S) := hRS
  letI : Algebra.IsSeparable (ResidueField S) (ResidueField U) := hSU
  have hRU : Algebra.IsSeparable (ResidueField R) (ResidueField U) :=
    Algebra.IsSeparable.trans (ResidueField R) (ResidueField S) (ResidueField U)
  let hRT' : maximalIdeal R = Ideal.comap (algebraMap R T) (maximalIdeal T) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R T)).symm
  let hTU' : maximalIdeal T = Ideal.comap (algebraMap T U) (maximalIdeal U) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap T U)).symm
  let _ : Algebra (ResidueField R) (ResidueField T) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal T) (algebraMap R T) hRT').toAlgebra
  let _ : Algebra (ResidueField T) (ResidueField U) :=
    (Ideal.ResidueField.map (maximalIdeal T) (maximalIdeal U) (algebraMap T U) hTU').toAlgebra
  let _ : IsScalarTower (ResidueField R) (ResidueField T) (ResidueField U) :=
    residueField_isScalarTower_of_dvr_tower (R := R) (S := T) (T := U)
  letI : Algebra.IsSeparable (ResidueField R) (ResidueField T) := hRT
  letI : Algebra.IsSeparable (ResidueField R) (ResidueField U) := hRU
  -- The second tower now sits over the same separable top extension `κ(R) ⊂ κ(U)`.
  exact
    Algebra.isSeparable_tower_top_of_isSeparable
      (F := ResidueField R) (E := ResidueField T) (K := ResidueField U)

/-- Helper for Lemma 15.115.4 (Abhyankar's lemma): the pure-Kummer closing argument only needs an
abstract comparison of ramification indices over the same top branch together with the residue
field separability data on both intermediate DVRs. -/
private theorem formally_smooth_of_equal_base_ramification_and_top_formally_smooth
    {R : Type*} {S : Type*} {T : Type*} {U : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Algebra R S] [Algebra S U] [Algebra R U] [IsScalarTower R S U]
    [Algebra R T] [Algebra T U] [IsScalarTower R T U]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S U]
    [IsExtensionOfDiscreteValuationRings R U]
    [IsExtensionOfDiscreteValuationRings R T]
    [IsExtensionOfDiscreteValuationRings T U]
    (hbase : ramificationIndex R S = ramificationIndex R T)
    (hRS : Algebra.IsSeparable (ResidueField R) (ResidueField S))
    (hRT : Algebra.IsSeparable (ResidueField R) (ResidueField T))
    (hSU : (algebraMap S U).formally_smooth_for_adic (maximalIdeal U)) :
    (algebraMap T U).formally_smooth_for_adic (maximalIdeal U) := by
  rw [formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField] at hSU ⊢
  refine ⟨?_, ?_⟩
  · -- The weakly unramified part is the ramification-index comparison from the source proof.
    exact weakly_unramified_of_equal_base_ramification_and_top
      (R := R) (S := S) (T := T) (U := U) hbase hSU.1
  · -- The residue-field part is the separability comparison between the two residue towers.
    exact residueField_separable_of_two_dvr_towers
      (R := R) (S := S) (T := T) (U := U) hRS hRT hSU.2

/-- Lemma 15.115.4 (Abhyankar's lemma): let `A ⊂ B` be an extension of discrete valuation rings,
let `K` and `L` be the fraction fields of `A` and `B`, and let `K₁ / K` be a finite extension.
Using the notation of Remark `15.115.1` / Definition `15.116.1`, write
`A₁ = integralClosure A K₁`,
`L₁ = (L ⊗[K] K₁)_red`, and
`B₁ = integralClosure B L₁`.
Assume the residue-field extension `ResidueField B / ResidueField A` is separable and that the
ramification index of `A ⊂ B` is prime to the residue characteristic of `A`.
If `m` is a maximal ideal of `A₁` such that `ramificationIndex A B` divides
`Ideal.ramificationIdx (maximalIdeal A) m`, then every maximal ideal `n` of `B₁` lying over `m`
yields a formally smooth branch map `(A₁)_m → (B₁)_n` for the
`maximalIdeal (Localization.AtPrime n)`-adic topology. -/
@[stacks 0BRM]
theorem formallySmoothForAdic_localization_branch_of_tame_and_dvd_ramificationIdx
    (hsep : Algebra.IsSeparable (ResidueField A) (ResidueField B))
    (hprime : PrimeToResidueCharacteristic A (ramificationIndex A B))
    (m : Ideal A1) [m.IsMaximal]
    (n : Ideal B1) [n.IsMaximal] [n.LiesOver m]
    (hmul : ramificationIndex A B ∣
      Ideal.ramificationIdx (maximalIdeal A) m) :
    (Localization.localRingHom m n (algebraMap A1 B1) (n.over_def m)).formally_smooth_for_adic
      (maximalIdeal (Localization.AtPrime n)) := by
  -- Route correction: the source proof has three reductions, and the generic descent lemma above
  -- handles only the final transport step once the branch is reduced to a pure Kummer layer.
  -- First adjoin an `e`th root of the unit factor in the local expression
  -- `π = u * π₁ ^ e₁`, so the horizontal maps in the resulting square are finite étale.
  -- Next pass to the subextension `K(θ) / K` with `θ ^ e = π`, and use the localized base-change
  -- comparison of Lemma `15.115.3` to transport formal smoothness from that Kummer subextension
  -- back to the original branch.
  -- Finally, in the pure Kummer case `K₁ = K[π^(1/e)]`, prove the localized branch is weakly
  -- unramified with separable residue field. The abstract closing argument for this last paragraph
  -- is now packaged by `formally_smooth_of_equal_base_ramification_and_top_formally_smooth`; the
  -- remaining missing owners are only the branch-local unit-root formal smoothness input and the
  -- `K(θ) / K` transport back to the original branch.
  -- TODO: the abstract square-descent step is now isolated in
  -- `branch_formally_smooth_of_adjoined_unit_root`, and the pure-Kummer endgame has been reduced
  -- to the abstract ramification/residue comparison above. The remaining blocker is owner-level:
  -- the new unit-root helpers already show that the distinguished `AdjoinRoot.root` is a unit and
  -- hence stays out of every branch prime. What is still missing is the actual étale/formally
  -- smooth owner for the quotient `R[X] / (X^e - u)` at that branch, together with the
  -- branch-local `K(θ) / K` transport using
  -- `formallySmoothForAdic_localization_baseChange_integralClosure`.
  sorry

end
