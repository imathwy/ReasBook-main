import StacksProject_2024.Chap10.Remark_10_127_12.Index
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w₀

section

open DirectedLocalHomApproximation
open scoped DualNumber TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-
Domain sampling:
* Primary domain: directed approximation systems for local homomorphisms of local rings in
  commutative algebra.
* Owner declarations inspected in this domain:
  - `DirectedLocalHomApproximation`
  - `DirectedLocalHomApproximation.HasLocalizationOfQuotientTransitions`
  - `DirectedLocalHomApproximation.HasPrimeLocalizationTransitions`
  - `DirectedLocalHomApproximation.HasFailingPrimeLocalizationTransition`
* Best owner abstraction: `DirectedLocalHomApproximation f`.
* Layer targeted here: `source-facing`. The remark asserts existence of one local essentially
  finitely presented map together with two approximation systems on the same owner object,
  distinguished only by derived transition properties.
* Primitive vs. derived: the directed system, stage rings, local stage maps, colimit
  identifications, and stagewise essential finite-type data are primitive owner data from
  `Lemma_10_127_9`; the good/bad transition conditions are derived properties already owned by
  `Lemma_10_127_10` and `Lemma_10_127_11`, so no extra wrapper predicate is needed here.
-/

namespace DirectedLocalHomApproximation

/-- Helper for Remark 10.127.12: prime-localization transitions persist after `ULift` reindexing,
because the reindexed transition maps are literally the original ones. -/
private theorem hasPrimeLocalizationTransitions_reindex_ulift {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {f : R →+* S}
    {A : DirectedLocalHomApproximation.{u, v, 0} f}
    (hA : A.HasPrimeLocalizationTransitions) :
    (A.reindex_ulift).HasPrimeLocalizationTransitions := by
  intro i j hij
  simpa [DirectedLocalHomApproximation.reindex_ulift] using hA (i := i.down) (j := j.down) hij

/-- Helper for Remark 10.127.12: localization-of-quotient transitions also persist after `ULift`
reindexing. -/
private theorem hasLocalizationOfQuotientTransitions_reindex_ulift {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {f : R →+* S}
    {A : DirectedLocalHomApproximation.{u, v, 0} f}
    (hA : A.HasLocalizationOfQuotientTransitions) :
    (A.reindex_ulift).HasLocalizationOfQuotientTransitions := by
  intro i j hij
  simpa [DirectedLocalHomApproximation.reindex_ulift] using hA (i := i.down) (j := j.down) hij

/-- Helper for Remark 10.127.12: a failing prime-localization transition survives `ULift`
reindexing by lifting the same bad indices. -/
private theorem hasFailingPrimeLocalizationTransition_reindex_ulift {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {f : R →+* S}
    {A : DirectedLocalHomApproximation.{u, v, 0} f}
    (hA : A.HasFailingPrimeLocalizationTransition) :
    (A.reindex_ulift).HasFailingPrimeLocalizationTransition := by
  rcases hA with ⟨i, j, hij, hbad⟩
  refine ⟨ULift.up i, ULift.up j, hij, ?_⟩
  simpa [DirectedLocalHomApproximation.reindex_ulift] using hbad

end DirectedLocalHomApproximation


/-- Helper for Remark 10.127.12: a surjective ring homomorphism is already a quotient map, hence a
localization of a quotient. -/
private theorem isLocalizationOfQuotient_of_surjective {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] (f : A →+* B) (hf : Function.Surjective f) :
    RingHom.IsLocalizationOfQuotient f := by
  let e : A ⧸ RingHom.ker f ≃+* B := RingHom.quotientKerEquivOfSurjective hf
  let M : Submonoid (A ⧸ RingHom.ker f) := IsUnit.submonoid _
  letI : Algebra (A ⧸ RingHom.ker f) B := e.toRingHom.toAlgebra
  letI : IsLocalization M (A ⧸ RingHom.ker f) := IsLocalization.at_units _ fun _ hx ↦ hx
  let eAlg : (A ⧸ RingHom.ker f) ≃ₐ[A ⧸ RingHom.ker f] B :=
    AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  letI : IsLocalization M B := IsLocalization.isLocalization_of_algEquiv M eAlg
  -- Proof comment: package the quotient presentation and then identify it with the original
  -- surjective map on each source element.
  refine ⟨RingHom.ker f, inferInstance, M, inferInstance, ?_⟩
  ext x
  simpa [M, e, RingHom.algebraMap_toAlgebra] using
    (RingHom.quotientKerEquivOfSurjective_apply_mk (f := f) hf x)

/-- Helper for Remark 10.127.12: every self-transition base-change map is surjective because
`s ⊗ 1` maps back to `s`. -/
private theorem stageBaseChangeMap_self_surjective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {f : R →+* S} (A : DirectedLocalHomApproximation f) (i : A.Λ) :
    Function.Surjective (A.stageBaseChangeMap (i := i) (j := i) le_rfl) := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage i) := (A.map i i le_rfl).toAlgebra
  intro s
  refine ⟨s ⊗ₜ[A.RStage i] (1 : A.RStage i), ?_⟩
  -- Proof comment: the self-transition sends `s ⊗ 1` to `s * 1`, because both directed-system
  -- self maps act as the identity on elements.
  have htarget : A.targetMap i i le_rfl s = s := by
    simpa using (DirectedSystem.map_self (f := fun j k h ↦ A.targetMap j k h) s)
  calc
    A.stageBaseChangeMap (i := i) (j := i) le_rfl (s ⊗ₜ[A.RStage i] (1 : A.RStage i)) =
      A.targetMap i i le_rfl s * A.stageMap i (1 : A.RStage i) := by
        simpa using
          (DirectedLocalHomApproximation.stageBaseChangeMap_tmul' A (i := i) (j := i) le_rfl s
            (1 : A.RStage i))
    _ = s * 1 := by rw [htarget, map_one]
    _ = s := by simp

/-- Helper for Remark 10.127.12: the singleton target transition is definitionally the identity
map on `ULift 𝔽₂`. -/
private theorem lifted_goodSystem_self_targetMap_eq_id
    (h : (PUnit.unit : PUnit) ≤ PUnit.unit) :
    (lifted_goodSystem.{u, v}).targetMap PUnit.unit PUnit.unit h = RingHom.id _ := by
  -- Proof comment: the singleton target system has only identity transition maps.
  rfl

/-- Helper for Remark 10.127.12: scalar multiplication through two copies of `ULift 𝔽₂` on
`ULift 𝔽₂` is associative. -/
private instance ulift_zmodTwo_self_zmodTwo_isScalarTower :
    IsScalarTower (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) where
  smul_assoc x y z := by
    ext
    simp [mul_assoc]

/-- Helper for Remark 10.127.12: scalar multiplication through two copies of `ULift 𝔽₂` on
`ULift (𝔽₂[ε])` is associative. -/
private instance ulift_zmodTwo_self_dualNumber_isScalarTower :
    IsScalarTower (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
      (ULift.{v} ((ZMod 2)[ε])) where
  smul_assoc x y z := by
    ext <;> simp [mul_assoc]

/-- Helper for Remark 10.127.12: the singleton self-transition base-change source identifies with
the target ring by the tensor right-unit equivalence. -/
private noncomputable abbrev lifted_goodSystem_self_stageBaseChange_ridEquiv :
    let algTarget : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) :=
      (RingHom.ulift (RingHom.id (ZMod 2))).toAlgebra
    let algSelf : Algebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) :=
      (RingHom.id _).toAlgebra
    let _ : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) := algTarget
    let _ : Algebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) := algSelf
    let _ : Semiring (ULift.{v} (ZMod 2) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) :=
      @Algebra.TensorProduct.instSemiring (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2))
        (ULift.{u} (ZMod 2)) _ _ algTarget _ algSelf
    let _ : Algebra (ULift.{u} (ZMod 2))
        (ULift.{v} (ZMod 2) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) :=
      @Algebra.TensorProduct.leftAlgebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
        (ULift.{v} (ZMod 2)) (ULift.{u} (ZMod 2)) _ _ algTarget _ algSelf _ algTarget
        inferInstance
    ULift.{v} (ZMod 2) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2) ≃+*
      ULift.{v} (ZMod 2) :=
  -- Proof comment: the owner self-transition tensor source is the standard right-unit tensor
  -- product for the lifted identity stage map.
  let algSelf : Algebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) :=
    (RingHom.id _).toAlgebra
  let algTarget : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) :=
    (RingHom.ulift (RingHom.id (ZMod 2))).toAlgebra
  let tower :
      @IsScalarTower (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2))
        algSelf.toSMul algTarget.toSMul algTarget.toSMul :=
    @IsScalarTower.of_algebraMap_eq (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
      (ULift.{v} (ZMod 2)) _ _ _ algSelf algTarget algTarget (fun _ ↦ rfl)
  letI : Algebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) := algSelf
  letI : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) := algTarget
  letI : Module (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) := Algebra.toModule
  letI : Module (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) := Algebra.toModule
  letI : Semiring (ULift.{v} (ZMod 2) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) :=
    @Algebra.TensorProduct.instSemiring (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2))
      (ULift.{u} (ZMod 2)) _ _ algTarget _ algSelf
  letI : Algebra (ULift.{u} (ZMod 2))
      (ULift.{v} (ZMod 2) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) :=
    @Algebra.TensorProduct.leftAlgebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
      (ULift.{v} (ZMod 2)) (ULift.{u} (ZMod 2)) _ _ algTarget _ algSelf _ algTarget
      inferInstance
  letI :
      @IsScalarTower (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2))
        algSelf.toSMul algTarget.toSMul algTarget.toSMul := tower
  let eAlg :
      ULift.{v} (ZMod 2) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2) ≃ₐ[ULift.{u} (ZMod 2)]
        ULift.{v} (ZMod 2) :=
    @Algebra.TensorProduct.rid (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
      (ULift.{v} (ZMod 2)) _ _ algSelf _ algTarget algTarget tower
  eAlg.toRingEquiv

/-- Helper for Remark 10.127.12: the singleton self-transition base-change map becomes the identity
after collapsing the tensor source by the right-unit equivalence. -/
private theorem lifted_goodSystem_self_stageBaseChange_rid_forward :
    ∀ z : (lifted_goodSystem.{u, v}).targetStageBaseChange
        (i := PUnit.unit) (j := PUnit.unit) le_rfl,
      (lifted_goodSystem.{u, v}).stageBaseChangeMap (i := PUnit.unit) (j := PUnit.unit) le_rfl z =
        (RingHom.id (ULift.{v} (ZMod 2)))
          (lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v} z) := by
  let algSelf : Algebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) :=
    (RingHom.id _).toAlgebra
  let algTarget : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) :=
    (RingHom.ulift (RingHom.id (ZMod 2))).toAlgebra
  let tower :
      @IsScalarTower (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2))
        algSelf.toSMul algTarget.toSMul algTarget.toSMul :=
    @IsScalarTower.of_algebraMap_eq (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
      (ULift.{v} (ZMod 2)) _ _ _ algSelf algTarget algTarget (fun _ ↦ rfl)
  letI : Algebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) := algSelf
  letI : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) := algTarget
  letI : Module (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) := Algebra.toModule
  letI : Module (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) := Algebra.toModule
  letI : Semiring (ULift.{v} (ZMod 2) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) :=
    @Algebra.TensorProduct.instSemiring (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2))
      (ULift.{u} (ZMod 2)) _ _ algTarget _ algSelf
  letI : Algebra (ULift.{u} (ZMod 2))
      (ULift.{v} (ZMod 2) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) :=
    @Algebra.TensorProduct.leftAlgebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
      (ULift.{v} (ZMod 2)) (ULift.{u} (ZMod 2)) _ _ algTarget _ algSelf _ algTarget
      inferInstance
  letI :
      @IsScalarTower (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2))
        algSelf.toSMul algTarget.toSMul algTarget.toSMul := tower
  letI :
      Algebra ((lifted_goodSystem.{u, v}).RStage PUnit.unit)
        ((lifted_goodSystem.{u, v}).SStage PUnit.unit) :=
    ((lifted_goodSystem.{u, v}).stageMap PUnit.unit).toAlgebra
  letI :
      Algebra ((lifted_goodSystem.{u, v}).RStage PUnit.unit)
        ((lifted_goodSystem.{u, v}).RStage PUnit.unit) :=
    ((lifted_goodSystem.{u, v}).map PUnit.unit PUnit.unit le_rfl).toAlgebra
  letI :
      Module ((lifted_goodSystem.{u, v}).RStage PUnit.unit)
        ((lifted_goodSystem.{u, v}).SStage PUnit.unit) := Algebra.toModule
  letI :
      Module ((lifted_goodSystem.{u, v}).RStage PUnit.unit)
        ((lifted_goodSystem.{u, v}).RStage PUnit.unit) := Algebra.toModule
  letI :
      Algebra (ULift.{u} (ZMod 2)) ((lifted_goodSystem.{u, v}).SStage PUnit.unit) :=
    ((lifted_goodSystem.{u, v}).stageMap PUnit.unit).toAlgebra
  letI :
      Algebra (ULift.{u} (ZMod 2)) ((lifted_goodSystem.{u, v}).RStage PUnit.unit) :=
    ((lifted_goodSystem.{u, v}).map PUnit.unit PUnit.unit le_rfl).toAlgebra
  letI :
      Module (ULift.{u} (ZMod 2)) ((lifted_goodSystem.{u, v}).SStage PUnit.unit) :=
    Algebra.toModule
  letI :
      Module (ULift.{u} (ZMod 2)) ((lifted_goodSystem.{u, v}).RStage PUnit.unit) :=
    Algebra.toModule
  change ∀ z : ULift.{v} (ZMod 2) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2),
      (lifted_goodSystem.{u, v}).stageBaseChangeMap
          (i := PUnit.unit) (j := PUnit.unit) le_rfl z =
        (RingHom.id (ULift.{v} (ZMod 2)))
          (lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v} z)
  intro z
  -- Proof comment: reduce the equality of ring maps to pure tensors, where the owner formula and
  -- the right-unit tensor formula both read as multiplication by the image of the base element.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · rfl
  · intro s r
    have hleft :=
      DirectedLocalHomApproximation.stageBaseChangeMap_tmul' lifted_goodSystem.{u, v}
        (i := PUnit.unit) (j := PUnit.unit) le_rfl s r
    have hright :
        lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v}
            (s ⊗ₜ[ULift.{u} (ZMod 2)] r) =
          (RingHom.ulift (RingHom.id (ZMod 2)) r) * s := by
      have h0 :
          (Algebra.TensorProduct.rid (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
            (ULift.{v} (ZMod 2))) (s ⊗ₜ[ULift.{u} (ZMod 2)] r) =
              algebraMap (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) r * s := by
        simpa [Algebra.smul_def] using
          (Algebra.TensorProduct.rid_tmul (R := ULift.{u} (ZMod 2))
            (S := ULift.{u} (ZMod 2)) (A := ULift.{v} (ZMod 2)) r s)
      have hscalar :
          algebraMap (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) r =
            RingHom.ulift (RingHom.id (ZMod 2)) r := by
        ext
        rfl
      calc
        lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v}
            (s ⊗ₜ[ULift.{u} (ZMod 2)] r) =
            algebraMap (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) r * s := h0
        _ = (RingHom.ulift (RingHom.id (ZMod 2)) r) * s := by rw [hscalar]
    calc
      (lifted_goodSystem.{u, v}).stageBaseChangeMap
          (i := PUnit.unit) (j := PUnit.unit) le_rfl (s ⊗ₜ[ULift.{u} (ZMod 2)] r) =
          (RingHom.id (ULift.{v} (ZMod 2))) s *
            (RingHom.ulift (RingHom.id (ZMod 2)) r) := by
        simpa [lifted_goodSystem] using hleft
      _ = (RingHom.id (ULift.{v} (ZMod 2)))
          ((RingHom.ulift (RingHom.id (ZMod 2)) r) * s) := by
        ext
        simp [RingHom.ulift_apply, mul_comm]
      _ =
          (RingHom.id (ULift.{v} (ZMod 2)))
            (lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v}
              (s ⊗ₜ[ULift.{u} (ZMod 2)] r)) := by
        simpa using congrArg (RingHom.id (ULift.{v} (ZMod 2))) hright.symm
  · intro z w hz hw
    calc
      (lifted_goodSystem.{u, v}).stageBaseChangeMap
          (i := PUnit.unit) (j := PUnit.unit) le_rfl (z + w) =
          (lifted_goodSystem.{u, v}).stageBaseChangeMap
              (i := PUnit.unit) (j := PUnit.unit) le_rfl z +
            (lifted_goodSystem.{u, v}).stageBaseChangeMap
              (i := PUnit.unit) (j := PUnit.unit) le_rfl w := by
        exact map_add ((lifted_goodSystem.{u, v}).stageBaseChangeMap
          (i := PUnit.unit) (j := PUnit.unit) le_rfl) z w
      _ = (RingHom.id (ULift.{v} (ZMod 2)))
            (lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v} z) +
          (RingHom.id (ULift.{v} (ZMod 2)))
            (lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v} w) := by
        exact congrArg₂ (fun a b ↦ a + b) hz hw
      _ = (RingHom.id (ULift.{v} (ZMod 2)))
          (lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v} (z + w)) := by
        calc
          (RingHom.id (ULift.{v} (ZMod 2)))
              (lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v} z) +
            (RingHom.id (ULift.{v} (ZMod 2)))
              (lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v} w) =
              (RingHom.id (ULift.{v} (ZMod 2)))
                (lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v} z +
                  lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v} w) := by
            exact (map_add (RingHom.id (ULift.{v} (ZMod 2)))
              (lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v} z)
              (lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v} w)).symm
          _ = (RingHom.id (ULift.{v} (ZMod 2)))
              (lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v} (z + w)) := by
            rw [← lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v}.map_add]
            rfl

/-- Helper for Remark 10.127.12: the identity map on a local ring is the localization map at the
complement of the maximal ideal. -/
private theorem maximalIdeal_primeCompl_isLocalizationMap_id (A : Type*) [CommRing A]
    [IsLocalRing A] :
    (IsLocalRing.maximalIdeal A).primeCompl.IsLocalizationMap (RingHom.id A) := by
  letI : Algebra A A := (RingHom.id A).toAlgebra
  have hloc : IsLocalization (IsLocalRing.maximalIdeal A).primeCompl A :=
    IsLocalization.at_units (IsLocalRing.maximalIdeal A).primeCompl fun x hx ↦
      (IsLocalRing.notMem_maximalIdeal (R := A) (x := x)).mp hx
  -- Proof comment: convert the standard localization-at-units instance into the explicit
  -- localization-map predicate for `RingHom.id`.
  exact (isLocalization_iff_isLocalizationMap
    (M := (IsLocalRing.maximalIdeal A).primeCompl) (S := A)).mp hloc

/-- Helper for Remark 10.127.12: a prime-localization witness on an owner base-change map can be
transported across a source ring equivalence when the transported map is given in forward form. -/
private theorem exists_prime_localization_witness_of_domain_equiv_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}
    (A : DirectedLocalHomApproximation f) {i j : A.Λ} (h : i ≤ j)
    {T : Type*} [CommRing T] (e : A.targetStageBaseChange h ≃+* T)
    (φ : T →+* A.SStage j)
    (hφ : ∀ z : A.targetStageBaseChange h, A.stageBaseChangeMap h z = φ (e z))
    (ht : A.TransitionIsLocalizationAtPrime h) :
    ∃ p : Ideal T, ∃ _ : p.IsPrime, p.primeCompl.IsLocalizationMap φ := by
  rcases ht with ⟨q, hq, hmapq⟩
  let p : Ideal T := Ideal.comap e.symm.toRingHom q
  letI : q.IsPrime := hq
  have hp : p.IsPrime := by
    -- Proof comment: prime ideals pull back along ring homomorphisms, so the transported prime
    -- on the equivalent source ring stays prime.
    simpa [p] using Ideal.comap_isPrime e.symm.toRingHom q
  letI : Algebra (A.targetStageBaseChange h) (A.SStage j) := (A.stageBaseChangeMap h).toAlgebra
  haveI hlocq : IsLocalization q.primeCompl (A.SStage j) :=
    (isLocalization_iff_isLocalizationMap
      (M := q.primeCompl) (S := A.SStage j)).mpr hmapq
  letI : Algebra T (A.SStage j) := φ.toAlgebra
  have hpmap : p.primeCompl.map e.symm.toMonoidHom = q.primeCompl := by
    -- Proof comment: `p` was defined as the pullback of `q` along `e.symm`, so complements match
    -- after mapping along the same equivalence.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [p, Ideal.mem_comap] using hy
    · intro hx
      refine ⟨e x, ?_, by simp⟩
      simpa [p, Ideal.mem_comap] using hx
  have htransport :
      IsLocalization p.primeCompl (A.SStage j) := by
    -- Proof comment: reinterpret the transported source algebra as `φ` using the forward
    -- compatibility, then move the localization structure across `e.symm`.
    exact IsLocalization.of_ringEquiv_left
      (e := e.symm)
      hpmap
      (fun x ↦ by
        change φ x = A.stageBaseChangeMap h (e.symm x)
        simpa using (hφ (e.symm x)).symm)
  letI : p.IsPrime := hp
  exact ⟨p, hp,
    (isLocalization_iff_isLocalizationMap
      (M := p.primeCompl) (S := A.SStage j)).mp htransport⟩

/-- Helper for Remark 10.127.12: a prime-localization witness can be transported from an
explicit equivalent source ring to the owner base-change source. -/
private theorem transitionIsLocalizationAtPrime_of_domain_equiv_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}
    (A : DirectedLocalHomApproximation f) {i j : A.Λ} (h : i ≤ j)
    {T : Type w} [CommRing T] (e : A.targetStageBaseChange h ≃+* T)
    (p : Ideal T) [p.IsPrime] (φ : T →+* A.SStage j)
    (hφ : ∀ z : A.targetStageBaseChange h, A.stageBaseChangeMap h z = φ (e z))
    (hmap : p.primeCompl.IsLocalizationMap φ) :
    A.TransitionIsLocalizationAtPrime h := by
  let q : Ideal (A.targetStageBaseChange h) := Ideal.comap e.toRingHom p
  have hq : q.IsPrime := by
    -- Proof comment: the prime on the explicit source pulls back across the source equivalence.
    simpa [q] using Ideal.comap_isPrime e.toRingHom p
  letI : Algebra T (A.SStage j) := φ.toAlgebra
  haveI hpLoc : IsLocalization p.primeCompl (A.SStage j) :=
    (isLocalization_iff_isLocalizationMap
      (M := p.primeCompl) (S := A.SStage j)).mpr hmap
  have hqmap : q.primeCompl.map e.toMonoidHom = p.primeCompl := by
    -- Proof comment: `q` is the contraction of `p`, so the complements correspond under `e`.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [q, Ideal.mem_comap] using hy
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      change e (e.symm x) ∉ p
      simpa using hx
  letI : Algebra (A.targetStageBaseChange h) (A.SStage j) :=
    (A.stageBaseChangeMap h).toAlgebra
  have hloc :
      IsLocalization q.primeCompl (A.SStage j) := by
    -- Proof comment: after identifying the source algebra through `e`, the explicit
    -- localization structure is the owner base-change localization structure.
    exact IsLocalization.of_ringEquiv_left
      (e := e)
      hqmap
      (fun x ↦ by
        change A.stageBaseChangeMap h x = φ (e x)
        exact hφ x)
  exact ⟨q, hq,
    (isLocalization_iff_isLocalizationMap
      (M := q.primeCompl) (S := A.SStage j)).mp hloc⟩

/-- Helper for Remark 10.127.12: the unique transition in the good singleton system is a
localization at the maximal ideal of the target stage. -/
private theorem lifted_goodSystem_hasPrimeLocalizationTransitions :
    (lifted_goodSystem.{u, v}).HasPrimeLocalizationTransitions := by
  intro i j h
  cases i
  cases j
  have hh : h = le_rfl := Subsingleton.elim h le_rfl
  rw [hh]
  let e := lifted_goodSystem_self_stageBaseChange_ridEquiv.{u, v}
  let p : Ideal (ULift.{v} (ZMod 2)) := IsLocalRing.maximalIdeal (ULift.{v} (ZMod 2))
  letI : p.IsPrime := (IsLocalRing.maximalIdeal.isMaximal (ULift.{v} (ZMod 2))).isPrime
  -- Proof comment: the tensor unitor identifies the owner base-change map with the identity map,
  -- which is the localization at the complement of the maximal ideal in a local ring.
  refine transitionIsLocalizationAtPrime_of_domain_equiv_map
    (R := ULift.{u} (ZMod 2)) (S := ULift.{v} (ZMod 2))
    (T := ULift.{v} (ZMod 2))
    lifted_goodSystem.{u, v} le_rfl e p (RingHom.id (ULift.{v} (ZMod 2))) ?_ ?_
  · exact lifted_goodSystem_self_stageBaseChange_rid_forward
  · exact maximalIdeal_primeCompl_isLocalizationMap_id (ULift.{v} (ZMod 2))

/-- Helper for Remark 10.127.12: the lifted projection `ULift (𝔽₂[ε]) → ULift 𝔽₂` is surjective. -/
private theorem lifted_dualNumber_fst_surjective :
    Function.Surjective lifted_dualNumber_fst := by
  intro y
  refine ⟨ULift.up ((TrivSqZeroExt.inl y.down : (ZMod 2)[ε])), ?_⟩
  ext
  rfl

/-- Helper for Remark 10.127.12: every prime ideal of `ULift (𝔽₂[ε])` is the maximal ideal, so
its prime complement is exactly the unit submonoid. -/
private theorem ulift_dualNumber_primeCompl_eq_isUnit_submonoid
    (q : Ideal (ULift.{v} ((ZMod 2)[ε]))) [hq : q.IsPrime] :
    q.primeCompl = IsUnit.submonoid (ULift.{v} ((ZMod 2)[ε])) := by
  let q' : Ideal ((ZMod 2)[ε]) := Ideal.comap
    (ULift.ringEquiv.symm.toRingHom : (ZMod 2)[ε] →+* ULift.{v} ((ZMod 2)[ε])) q
  have hq' : q'.IsPrime := by
    simpa [q'] using Ideal.comap_isPrime
      (ULift.ringEquiv.symm.toRingHom : (ZMod 2)[ε] →+* ULift.{v} ((ZMod 2)[ε])) q
  have hεsq : (ULift.up (ε : (ZMod 2)[ε]) : ULift.{v} ((ZMod 2)[ε])) ^ 2 = 0 := by
    apply ULift.ext
    ext <;> simp [pow_two]
  have hεmem : (ε : (ZMod 2)[ε]) ∈ q' := by
    apply Ideal.mem_comap.mpr
    have hpow : (ULift.up (ε : (ZMod 2)[ε]) : ULift.{v} ((ZMod 2)[ε])) ^ 2 ∈ q := by
      simpa [hεsq] using (show (0 : ULift.{v} ((ZMod 2)[ε])) ∈ q from Ideal.zero_mem q)
    exact hq.mem_of_pow_mem 2 hpow
  have hεne : (ε : (ZMod 2)[ε]) ≠ 0 := by
    intro h
    have hsnd := congrArg TrivSqZeroExt.snd h
    simpa using hsnd
  have hq'span : q' = Ideal.span ({(ε : (ZMod 2)[ε])} : Set ((ZMod 2)[ε])) := by
    rcases DualNumber.ideal_trichotomy q' with hbot | hspan | htop
    · exfalso
      rw [hbot] at hεmem
      exact hεne hεmem
    · exact hspan
    · exact False.elim (hq'.ne_top htop)
  have hbase :
      q'.primeCompl = IsUnit.submonoid ((ZMod 2)[ε]) := by
    ext x
    change x ∉ q' ↔ x ∈ IsUnit.submonoid ((ZMod 2)[ε])
    rw [hq'span, ← DualNumber.maximalIdeal_eq_span_singleton_eps]
    change x ∉ IsLocalRing.maximalIdeal ((ZMod 2)[ε]) ↔
      x ∈ IsUnit.submonoid ((ZMod 2)[ε])
    constructor
    · intro hx
      simpa using (IsLocalRing.notMem_maximalIdeal (R := (ZMod 2)[ε]) (x := x)).mp hx
    · intro hx
      exact (IsLocalRing.notMem_maximalIdeal (R := (ZMod 2)[ε]) (x := x)).mpr (by
        simpa using hx)
  ext x
  cases x with
  | up x =>
      change (ULift.up x : ULift.{v} ((ZMod 2)[ε])) ∈ q.primeCompl ↔
        IsUnit (ULift.up x : ULift.{v} ((ZMod 2)[ε]))
      change x ∈ q'.primeCompl ↔ IsUnit (ULift.up x : ULift.{v} ((ZMod 2)[ε]))
      rw [hbase]
      constructor
      · intro hx
        exact hx.map (ULift.ringEquiv.symm.toRingHom : (ZMod 2)[ε] →+* ULift.{v} ((ZMod 2)[ε]))
      · intro hx
        exact hx.map (ULift.ringEquiv.toRingHom : ULift.{v} ((ZMod 2)[ε]) →+* (ZMod 2)[ε])

/-- Helper for Remark 10.127.12: the lifted dual-number generator `ε` is nonzero in
`ULift (𝔽₂[ε])`. -/
private theorem ulift_dualNumber_eps_ne_zero :
    (ULift.up (ε : (ZMod 2)[ε]) : ULift.{v} ((ZMod 2)[ε])) ≠ 0 := by
  intro hzero
  have hsnd := congrArg (fun x : ULift.{v} ((ZMod 2)[ε]) ↦ TrivSqZeroExt.snd x.down) hzero
  simpa using hsnd

/-- Helper for Remark 10.127.12: the lifted projection `ULift (𝔽₂[ε]) → ULift 𝔽₂` cannot be a
localization at a prime, because that would force it to be a localization at units and hence
bijective, contradicting the killed nonzero element `ε`. -/
private theorem lifted_dualNumber_fst_not_isLocalizationMap_at_prime :
    ¬ ∃ q : Ideal (ULift.{v} ((ZMod 2)[ε])),
        ∃ _ : q.IsPrime, q.primeCompl.IsLocalizationMap lifted_dualNumber_fst := by
  intro h
  rcases h with ⟨q, hq, hmapq⟩
  letI : q.IsPrime := hq
  have hmapUnits :
      (IsUnit.submonoid (ULift.{v} ((ZMod 2)[ε]))).IsLocalizationMap lifted_dualNumber_fst := by
    rwa [ulift_dualNumber_primeCompl_eq_isUnit_submonoid q] at hmapq
  letI : Algebra (ULift.{v} ((ZMod 2)[ε])) (ULift.{v} (ZMod 2)) :=
    lifted_dualNumber_fst.toAlgebra
  have hloc :
      IsLocalization (IsUnit.submonoid (ULift.{v} ((ZMod 2)[ε]))) (ULift.{v} (ZMod 2)) :=
    (isLocalization_iff_isLocalizationMap
      (M := IsUnit.submonoid (ULift.{v} ((ZMod 2)[ε])))
      (S := ULift.{v} (ZMod 2))).mpr hmapUnits
  let e :
      ULift.{v} ((ZMod 2)[ε]) ≃ₐ[ULift.{v} ((ZMod 2)[ε])] ULift.{v} (ZMod 2) :=
    IsLocalization.atUnits
      (R := ULift.{v} ((ZMod 2)[ε]))
      (M := IsUnit.submonoid (ULift.{v} ((ZMod 2)[ε])))
      (S := ULift.{v} (ZMod 2))
      (by intro x hx; simpa using hx)
  have heq : e.toRingHom = lifted_dualNumber_fst := by
    ext x
    rfl
  have hinj : Function.Injective lifted_dualNumber_fst := by
    rw [← heq]
    exact e.injective
  have hzero :
      lifted_dualNumber_fst (ULift.up (ε : (ZMod 2)[ε]) : ULift.{v} ((ZMod 2)[ε])) = 0 := by
    rfl
  exact ulift_dualNumber_eps_ne_zero (hinj hzero)

/-- Helper for Remark 10.127.12: the bad false-to-true base-change map becomes the lifted dual
number projection after collapsing the tensor source by the right-unit equivalence. -/
private theorem bool_false_le_true : (false : Bool) ≤ true := by
  decide

/-- Helper for Remark 10.127.12: the concrete bad false-to-true base-change tensor source identifies
with the dual-number stage by the tensor right-unit equivalence. -/
private noncomputable abbrev lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete :
    let algTarget : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε])) :=
      lifted_zmodTwo_to_dualNumber.toAlgebra
    let algSelf : Algebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) :=
      (RingHom.id _).toAlgebra
    let _ : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε])) := algTarget
    let _ : Algebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) := algSelf
    let _ : Module (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε])) := Algebra.toModule
    let _ : Module (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) := Algebra.toModule
    let _ :
        Semiring (ULift.{v} ((ZMod 2)[ε]) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) :=
      @Algebra.TensorProduct.instSemiring (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε]))
        (ULift.{u} (ZMod 2)) _ _ algTarget _ algSelf
    let _ : Algebra (ULift.{u} (ZMod 2))
        (ULift.{v} ((ZMod 2)[ε]) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) :=
      @Algebra.TensorProduct.leftAlgebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
        (ULift.{v} ((ZMod 2)[ε])) (ULift.{u} (ZMod 2)) _ _ algTarget _ algSelf _
        algTarget inferInstance
    ULift.{v} ((ZMod 2)[ε]) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2) ≃+*
      ULift.{v} ((ZMod 2)[ε]) :=
  -- Proof comment: the nontrivial base-change source is again the standard right-unit tensor
  -- product over `ULift 𝔽₂`.
  let algSelf : Algebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) :=
    (RingHom.id _).toAlgebra
  let algTarget : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε])) :=
    lifted_zmodTwo_to_dualNumber.toAlgebra
  let tower :
      @IsScalarTower (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
        (ULift.{v} ((ZMod 2)[ε])) algSelf.toSMul algTarget.toSMul algTarget.toSMul :=
    @IsScalarTower.of_algebraMap_eq (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
      (ULift.{v} ((ZMod 2)[ε])) _ _ _ algSelf algTarget algTarget (fun _ ↦ rfl)
  letI : Algebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) := algSelf
  letI : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε])) := algTarget
  letI : Module (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) := Algebra.toModule
  letI : Module (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε])) := Algebra.toModule
  letI :
      Semiring (ULift.{v} ((ZMod 2)[ε]) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) :=
    @Algebra.TensorProduct.instSemiring (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε]))
      (ULift.{u} (ZMod 2)) _ _ algTarget _ algSelf
  letI : Algebra (ULift.{u} (ZMod 2))
      (ULift.{v} ((ZMod 2)[ε]) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) :=
    @Algebra.TensorProduct.leftAlgebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
      (ULift.{v} ((ZMod 2)[ε])) (ULift.{u} (ZMod 2)) _ _ algTarget _ algSelf _ algTarget
      inferInstance
  letI :
      @IsScalarTower (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
        (ULift.{v} ((ZMod 2)[ε])) algSelf.toSMul algTarget.toSMul algTarget.toSMul := tower
  let eAlg :
      ULift.{v} ((ZMod 2)[ε]) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2) ≃ₐ[ULift.{u} (ZMod 2)]
        ULift.{v} ((ZMod 2)[ε]) :=
    @Algebra.TensorProduct.rid (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
      (ULift.{v} ((ZMod 2)[ε])) _ _ algSelf _ algTarget algTarget tower
  eAlg.toRingEquiv

/-- Helper for Remark 10.127.12: the owner-spelled bad false-to-true base-change source is the same
concrete tensor source. -/
private noncomputable abbrev lifted_badSystem_false_true_stageBaseChange_ridEquiv :
    (lifted_badSystem.{u, v}).targetStageBaseChange (i := false) (j := true)
      bool_false_le_true ≃+* ULift.{v} ((ZMod 2)[ε]) :=
  lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v}

/-- Helper for Remark 10.127.12: the bad false-to-true base-change map becomes the lifted dual
number projection after collapsing the tensor source by the right-unit equivalence. -/
private theorem lifted_badSystem_false_true_stageBaseChange_rid_forward :
    ∀ z : (lifted_badSystem.{u, v}).targetStageBaseChange (i := false) (j := true)
        bool_false_le_true,
      (lifted_badSystem.{u, v}).stageBaseChangeMap (i := false) (j := true)
          bool_false_le_true z =
        lifted_dualNumber_fst
          (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v} z) := by
  let algSelf : Algebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) :=
    (RingHom.id _).toAlgebra
  let algTarget : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε])) :=
    lifted_zmodTwo_to_dualNumber.toAlgebra
  let tower :
      @IsScalarTower (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
        (ULift.{v} ((ZMod 2)[ε])) algSelf.toSMul algTarget.toSMul algTarget.toSMul :=
    @IsScalarTower.of_algebraMap_eq (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
      (ULift.{v} ((ZMod 2)[ε])) _ _ _ algSelf algTarget algTarget (fun _ ↦ rfl)
  letI : Algebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) := algSelf
  letI : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε])) := algTarget
  letI : Module (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) := Algebra.toModule
  letI : Module (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε])) := Algebra.toModule
  letI :
      Semiring (ULift.{v} ((ZMod 2)[ε]) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) :=
    @Algebra.TensorProduct.instSemiring (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε]))
      (ULift.{u} (ZMod 2)) _ _ algTarget _ algSelf
  letI : Algebra (ULift.{u} (ZMod 2))
      (ULift.{v} ((ZMod 2)[ε]) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) :=
    @Algebra.TensorProduct.leftAlgebra (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
      (ULift.{v} ((ZMod 2)[ε])) (ULift.{u} (ZMod 2)) _ _ algTarget _ algSelf _ algTarget
      inferInstance
  letI :
      @IsScalarTower (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
        (ULift.{v} ((ZMod 2)[ε])) algSelf.toSMul algTarget.toSMul algTarget.toSMul := tower
  letI :
      Algebra ((lifted_badSystem.{u, v}).RStage false)
        ((lifted_badSystem.{u, v}).SStage false) :=
    ((lifted_badSystem.{u, v}).stageMap false).toAlgebra
  letI :
      Algebra ((lifted_badSystem.{u, v}).RStage false)
        ((lifted_badSystem.{u, v}).RStage true) :=
    ((lifted_badSystem.{u, v}).map false true bool_false_le_true).toAlgebra
  letI :
      Module ((lifted_badSystem.{u, v}).RStage false)
        ((lifted_badSystem.{u, v}).SStage false) := Algebra.toModule
  letI :
      Module ((lifted_badSystem.{u, v}).RStage false)
        ((lifted_badSystem.{u, v}).RStage true) := Algebra.toModule
  letI :
      Algebra (ULift.{u} (ZMod 2)) ((lifted_badSystem.{u, v}).SStage false) :=
    ((lifted_badSystem.{u, v}).stageMap false).toAlgebra
  letI :
      Algebra (ULift.{u} (ZMod 2)) ((lifted_badSystem.{u, v}).RStage true) :=
    ((lifted_badSystem.{u, v}).map false true bool_false_le_true).toAlgebra
  letI :
      Module (ULift.{u} (ZMod 2)) ((lifted_badSystem.{u, v}).SStage false) :=
    Algebra.toModule
  letI :
      Module (ULift.{u} (ZMod 2)) ((lifted_badSystem.{u, v}).RStage true) :=
    Algebra.toModule
  change ∀ z : ULift.{v} ((ZMod 2)[ε]) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2),
      (lifted_badSystem.{u, v}).stageBaseChangeMap
          (i := false) (j := true) bool_false_le_true z =
        lifted_dualNumber_fst
          (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v} z)
  intro z
  -- Proof comment: the only nontrivial two-stage transition is checked on pure tensors; the
  -- compatibility `lifted_dualNumber_fst_comp_inl` identifies the base scalar after projection.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · rfl
  · intro s r
    have hleft :=
      DirectedLocalHomApproximation.stageBaseChangeMap_tmul' lifted_badSystem.{u, v}
        (i := false) (j := true) bool_false_le_true s r
    have hright :
        lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v}
            (s ⊗ₜ[ULift.{u} (ZMod 2)] r) =
          lifted_zmodTwo_to_dualNumber r * s := by
      have h0 :
          (Algebra.TensorProduct.rid (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
            (ULift.{v} ((ZMod 2)[ε]))) (s ⊗ₜ[ULift.{u} (ZMod 2)] r) =
              algebraMap (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε])) r * s := by
        simpa [Algebra.smul_def] using
          (Algebra.TensorProduct.rid_tmul (R := ULift.{u} (ZMod 2))
            (S := ULift.{u} (ZMod 2)) (A := ULift.{v} ((ZMod 2)[ε])) r s)
      have hscalar :
          algebraMap (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε])) r =
            lifted_zmodTwo_to_dualNumber r := by
        ext <;> rfl
      calc
        lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v}
            (s ⊗ₜ[ULift.{u} (ZMod 2)] r) =
            algebraMap (ULift.{u} (ZMod 2)) (ULift.{v} ((ZMod 2)[ε])) r * s := h0
        _ = lifted_zmodTwo_to_dualNumber r * s := by rw [hscalar]
    calc
      (lifted_badSystem.{u, v}).stageBaseChangeMap
          (i := false) (j := true) bool_false_le_true (s ⊗ₜ[ULift.{u} (ZMod 2)] r) =
          lifted_dualNumber_fst s *
            (RingHom.ulift (RingHom.id (ZMod 2)) r) := by
        simpa [lifted_badSystem] using hleft
      _ = lifted_dualNumber_fst
          (lifted_zmodTwo_to_dualNumber r * s) := by
        ext
        simp [lifted_dualNumber_fst_comp_inl, RingHom.comp_apply, RingHom.ulift_apply,
          lifted_zmodTwo_to_dualNumber, lifted_dualNumber_fst,
          TrivSqZeroExt.fst_inl, mul_comm]
      _ =
          lifted_dualNumber_fst
            (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v}
              (s ⊗ₜ[ULift.{u} (ZMod 2)] r)) := by
        simpa using congrArg lifted_dualNumber_fst hright.symm
  · intro z w hz hw
    calc
      (lifted_badSystem.{u, v}).stageBaseChangeMap
          (i := false) (j := true) bool_false_le_true (z + w) =
          (lifted_badSystem.{u, v}).stageBaseChangeMap
              (i := false) (j := true) bool_false_le_true z +
            (lifted_badSystem.{u, v}).stageBaseChangeMap
              (i := false) (j := true) bool_false_le_true w := by
        exact map_add ((lifted_badSystem.{u, v}).stageBaseChangeMap
          (i := false) (j := true) bool_false_le_true) z w
      _ = lifted_dualNumber_fst
            (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v} z) +
          lifted_dualNumber_fst
            (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v} w) := by
        exact congrArg₂ (fun a b ↦ a + b) hz hw
      _ = lifted_dualNumber_fst
          (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v} (z + w)) := by
        calc
          lifted_dualNumber_fst
              (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v} z) +
            lifted_dualNumber_fst
              (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v} w) =
              lifted_dualNumber_fst
                (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v} z +
                  lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v} w) := by
            exact (map_add lifted_dualNumber_fst
              (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v} z)
              (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v} w)).symm
          _ = lifted_dualNumber_fst
              (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v} (z + w)) := by
            rw [← lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v}.map_add]

/-- Helper for Remark 10.127.12: the unique nontrivial transition in the bad system is a
localization of a quotient but not a localization at a prime. -/
private theorem lifted_badSystem_false_true_transition_properties
    (hFT : (false : Bool) ≤ true) :
    RingHom.IsLocalizationOfQuotient ((lifted_badSystem.{u, v}).stageBaseChangeMap hFT) ∧
      ¬ (lifted_badSystem.{u, v}).TransitionIsLocalizationAtPrime hFT := by
  have hh : hFT = bool_false_le_true := Subsingleton.elim hFT bool_false_le_true
  rw [hh]
  constructor
  · apply isLocalizationOfQuotient_of_surjective
    intro y
    rcases lifted_dualNumber_fst_surjective y with ⟨x, hx⟩
    refine ⟨lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v}.symm x, ?_⟩
    -- Proof comment: pull a preimage through the tensor unitor and use the forward formula to
    -- reduce surjectivity to the explicit projection.
    have hforward :=
      lifted_badSystem_false_true_stageBaseChange_rid_forward
        (lifted_badSystem_false_true_stageBaseChange_ridEquivConcrete.{u, v}.symm x)
    simpa [hx, RingEquiv.apply_symm_apply] using hforward
  · intro ht
    -- Proof comment: any prime-localization witness for the owner transition transports to one
    -- for the explicit dual-number projection, contradicting its dedicated obstruction lemma.
    exact lifted_dualNumber_fst_not_isLocalizationMap_at_prime
      (exists_prime_localization_witness_of_domain_equiv_map
        (R := ULift.{u} (ZMod 2)) (S := ULift.{v} (ZMod 2))
        (T := ULift.{v} ((ZMod 2)[ε]))
        lifted_badSystem.{u, v} bool_false_le_true
        lifted_badSystem_false_true_stageBaseChange_ridEquiv.{u, v}
        lifted_dualNumber_fst
        lifted_badSystem_false_true_stageBaseChange_rid_forward ht)

/-- Helper for Remark 10.127.12: once the two explicit lifted systems are packaged, the good one
has prime-localization transitions and the bad one fails at a prime-localization transition. -/
private theorem lifted_systems_have_target_properties :
    (lifted_goodSystem.{u, v}).HasPrimeLocalizationTransitions ∧
      (lifted_badSystem.{u, v}).HasLocalizationOfQuotientTransitions ∧
        (lifted_badSystem.{u, v}).HasFailingPrimeLocalizationTransition :=
  by
    constructor
    · exact lifted_goodSystem_hasPrimeLocalizationTransitions
    constructor
    · intro i j hij
      -- Proof comment: the two self-transitions are surjective quotient maps; the only
      -- nontrivial false-to-true transition is handled by the explicit bad-transition theorem.
      cases i <;> cases j
      · have hh : hij = le_rfl := Subsingleton.elim hij le_rfl
        rw [hh]
        exact isLocalizationOfQuotient_of_surjective
          ((lifted_badSystem.{u, v}).stageBaseChangeMap (i := false) (j := false) le_rfl)
          (stageBaseChangeMap_self_surjective lifted_badSystem.{u, v} false)
      · exact (lifted_badSystem_false_true_transition_properties hij).1
      · exact False.elim (bool_true_not_le_false hij)
      · have hh : hij = le_rfl := Subsingleton.elim hij le_rfl
        rw [hh]
        exact isLocalizationOfQuotient_of_surjective
          ((lifted_badSystem.{u, v}).stageBaseChangeMap (i := true) (j := true) le_rfl)
          (stageBaseChangeMap_self_surjective lifted_badSystem.{u, v} true)
    · exact ⟨false, true, bool_false_le_true,
        (lifted_badSystem_false_true_transition_properties bool_false_le_true).2⟩

/-- Helper for Remark 10.127.12: the good approximation system has explicit index universe `0`,
so it can be reindexed cleanly into any ambient approximation universe. -/
private noncomputable abbrev goodSystem₀ :
    DirectedLocalHomApproximation.{u, v, 0}
      (RingHom.ulift (RingHom.id (ZMod 2))) :=
  lifted_goodSystem.{u, v}

/-- Helper for Remark 10.127.12: the bad approximation system has explicit index universe `0`,
so it can be reindexed cleanly into any ambient approximation universe. -/
private noncomputable abbrev badSystem₀ :
    DirectedLocalHomApproximation.{u, v, 0}
      (RingHom.ulift (RingHom.id (ZMod 2))) :=
  lifted_badSystem.{u, v}

-- Proof sketch: use the explicit `k = 𝔽₂` example from the remark. The system with
-- `Sₙ = Rₙ / (z, yₙ²)` gives an approximation of the map `R → R / zR` whose successor base-change
-- maps kill `1 ⊗ y_{n + 1}²`, so some transition is not a localization at a prime ideal. Replacing
-- those targets by `Rₙ / zRₙ` gives another approximation of the same local essentially finite
-- presentation map whose transition maps are localizations at prime ideals.
/-- Chap10 Remark 10 127 12: there exists a local homomorphism of local rings which is essentially of
finite presentation and admits both a good approximation system whose transition maps are
localizations at prime ideals and a different approximation system whose transition maps are still
localizations of quotients but fail to be localizations at prime ideals. -/
@[stacks 00QW]
theorem exists_essentially_finitePresentation_local_map_with_wrong_approximation_system :
    ∃ (R : Type u) (S : Type v) (_ : CommRing R) (_ : CommRing S) (_ : IsLocalRing R)
      (_ : IsLocalRing S) (f : R →+* S) (_ : IsLocalHom f)
      (_ : RingHom.EssFinitePresentation f) (goodSystem : DirectedLocalHomApproximation f),
      goodSystem.HasPrimeLocalizationTransitions ∧
        ∃ badSystem : DirectedLocalHomApproximation f,
            badSystem.HasLocalizationOfQuotientTransitions ∧
              badSystem.HasFailingPrimeLocalizationTransition := by
  have hprops := lifted_systems_have_target_properties
  rcases hprops with ⟨hgood, hbadQuot, hbadPrime⟩
  have hgood₀ : goodSystem₀.HasPrimeLocalizationTransitions := by
    intro i j hij
    simpa [goodSystem₀] using hgood (i := i) (j := j) hij
  have hbadQuot₀ : badSystem₀.HasLocalizationOfQuotientTransitions := by
    intro i j hij
    simpa [badSystem₀] using hbadQuot (i := i) (j := j) hij
  have hbadPrime₀ : badSystem₀.HasFailingPrimeLocalizationTransition := by
    simpa [badSystem₀] using hbadPrime
  refine ⟨ULift.{u} (ZMod 2), ULift.{v} (ZMod 2), inferInstance, inferInstance,
    inferInstance, inferInstance, RingHom.ulift (RingHom.id (ZMod 2)),
    ulift_zmodTwo_id_isLocalHom, ?_, goodSystem₀.reindex_ulift, ?_⟩
  · simpa using ulift_zmodTwo_id_essFinitePresentation
  · refine ⟨?_, ?_⟩
    · exact DirectedLocalHomApproximation.hasPrimeLocalizationTransitions_reindex_ulift
        (A := goodSystem₀) hgood₀
    · refine ⟨badSystem₀.reindex_ulift, ?_⟩
      exact ⟨DirectedLocalHomApproximation.hasLocalizationOfQuotientTransitions_reindex_ulift
          (A := badSystem₀) hbadQuot₀,
        DirectedLocalHomApproximation.hasFailingPrimeLocalizationTransition_reindex_ulift
          (A := badSystem₀) hbadPrime₀⟩

end
