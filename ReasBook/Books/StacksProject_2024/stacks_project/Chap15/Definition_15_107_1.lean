import Mathlib.Algebra.Field.TransferInstance
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Topology.Inseparable
import StacksProject_2024.stacks_project.Chap15.Definition_15_107_1_Basic
import StacksProject_2024.stacks_project.Chap15.Lemma_15_105_23

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open scoped Unibranch

universe u

section

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- Helper for Definition 15.107.1: the reduction of a field is canonically the field itself. -/
noncomputable def unibranchReductionEquivField (K : Type u) [Field K] :
    (K)_red ≃+* K :=
  (Ideal.quotEquivOfEq (nilradical_eq_zero K)).trans (RingEquiv.quotientBot K)

/-- Helper for Definition 15.107.1: the normalization of the reduction of a field is canonically
the field itself. -/
noncomputable def unibranchNormalizationEquivField (K : Type u) [Field K] :
    K′ ≃+* K := by
  let eRed : (K)_red ≃+* K := unibranchReductionEquivField K
  letI : Field (K)_red := eRed.toEquiv.field
  letI : IsIntegrallyClosed (K)_red := IsIntegrallyClosed.of_equiv eRed.symm
  let hbot : integralClosure (K)_red (FractionRing (K)_red) = ⊥ :=
    IsIntegrallyClosed.integralClosure_eq_bot (K)_red (FractionRing (K)_red)
  -- We first collapse the integral closure to the bottom subalgebra, then identify the latter
  -- with the base field via the injective fraction-ring map.
  let eClosure : K′ ≃ₐ[(K)_red] (K)_red :=
    (Subalgebra.equivOfEq (integralClosure (K)_red (FractionRing (K)_red)) ⊥ hbot).trans
      (Algebra.botEquivOfInjective (IsFractionRing.injective (K)_red (FractionRing (K)_red)))
  exact eClosure.toRingEquiv.trans eRed

/-- Helper for Definition 15.107.1: the residue field of a field is canonically the field
itself. -/
noncomputable def residueFieldEquivField (K : Type u) [Field K] :
    ResidueField K ≃+* K :=
  (Ideal.quotEquivOfEq ((maximalIdeal K).eq_bot_of_prime)).trans (RingEquiv.quotientBot K)

/-- Helper for Definition 15.107.1: the canonical residue-field equivalence of a field sends the
residue class of an element to that element. -/
lemma residueFieldEquivField_apply_algebraMap
    (K : Type u) [Field K] (a : K) :
    residueFieldEquivField K (algebraMap K (ResidueField K) a) = a := by
  -- The quotient by the zero maximal ideal identifies `a` with its residue class.
  change residueFieldEquivField K (residue K a) = a
  unfold residueFieldEquivField RingEquiv.quotientBot
  rfl

/-- Helper for Definition 15.107.1: the reduction equivalence of a field respects the quotient
map from the field to its reduction. -/
lemma unibranchReductionEquivField_apply_algebraMap
    (K : Type u) [Field K] (a : K) :
    unibranchReductionEquivField K (algebraMap K (K)_red a) = a := by
  -- The nilradical of a field is zero, so the reduction map is the identity.
  simp [unibranchReductionEquivField, unibranchReduction]

/-- Helper for Definition 15.107.1: the normalization equivalence of a field respects the base
map from the field to its normalization. -/
lemma unibranchNormalizationEquivField_apply_algebraMap
    (K : Type u) [Field K] (a : K) :
    unibranchNormalizationEquivField K (algebraMap K K′ a) = a := by
  -- Route correction: use the source-faithful collapse through the reduction and then through the
  -- integral closure, instead of trying to recover algebra compatibility afterward.
  let eRed : (K)_red ≃+* K := unibranchReductionEquivField K
  letI : Field (K)_red := eRed.toEquiv.field
  letI : IsIntegrallyClosed (K)_red := IsIntegrallyClosed.of_equiv eRed.symm
  let hbot : integralClosure (K)_red (FractionRing (K)_red) = ⊥ :=
    IsIntegrallyClosed.integralClosure_eq_bot (K)_red (FractionRing (K)_red)
  let eClosure : K′ ≃ₐ[(K)_red] (K)_red :=
    (Subalgebra.equivOfEq (integralClosure (K)_red (FractionRing (K)_red)) ⊥ hbot).trans
      (Algebra.botEquivOfInjective (IsFractionRing.injective (K)_red (FractionRing (K)_red)))
  -- The algebra equivalence `eClosure` reduces the normalization element back to the reduction.
  change eRed (eClosure.toRingEquiv (algebraMap K K′ a)) = a
  rw [show algebraMap K K′ a = algebraMap (K)_red K′ (algebraMap K (K)_red a) by rfl]
  calc
    eRed (eClosure.toRingEquiv (algebraMap (K)_red K′ (algebraMap K (K)_red a))) =
        eRed (algebraMap K (K)_red a) := by
          simpa using congrArg eRed (eClosure.commutes (algebraMap K (K)_red a))
    _ = a := unibranchReductionEquivField_apply_algebraMap K a

/-- Helper for Definition 15.107.1: the maximal ideal of the normalization of a field is zero,
because the normalization identifies with a field. -/
lemma maximalIdeal_eq_bot_unibranchNormalization_of_field
    (K : Type u) [Field K] [IsLocalRing K′] :
    maximalIdeal K′ = ⊥ := by
  let eNorm : K′ ≃+* K := unibranchNormalizationEquivField K
  have hbot : (⊥ : Ideal K′).IsMaximal := by
    -- Maximality of the zero ideal transports back across the normalization equivalence.
    let hKbot : (⊥ : Ideal K).IsMaximal := Ideal.bot_isMaximal
    have hmap : (Ideal.map eNorm.symm.toRingHom (⊥ : Ideal K)).IsMaximal := by
      refine Ideal.IsMaximal.map_of_surjective_of_ker_le
        (f := eNorm.symm.toRingHom) eNorm.symm.surjective ?_
      simpa
    rw [Ideal.map_bot] at hmap
    exact hmap
  exact (IsLocalRing.eq_maximalIdeal hbot).symm

/-- Helper for Definition 15.107.1: after identifying the normalization of a field with the
field, its residue field also identifies with the same field. -/
noncomputable def residueField_unibranchNormalizationEquivField
    (K : Type u) [Field K] [IsLocalRing K′] :
    ResidueField K′ ≃+* K :=
  let hbot : maximalIdeal K′ = ⊥ :=
    maximalIdeal_eq_bot_unibranchNormalization_of_field K
  let eResidue : ResidueField K′ ≃+* K′ :=
    (Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot K′)
  let eNorm : K′ ≃+* K := unibranchNormalizationEquivField K
  eResidue.trans eNorm

/-- Helper for Definition 15.107.1: the residue-field identification of the normalization of a
field sends residues of normalization elements to their images in the base field. -/
lemma residueField_unibranchNormalizationEquivField_apply_residue
    (K : Type u) [Field K] [IsLocalRing K′] (x : K′) :
    residueField_unibranchNormalizationEquivField K
        (residue K′ x) =
      unibranchNormalizationEquivField K x := by
  -- First identify the residue field of `K′` with `K′`, then apply the normalization equivalence.
  unfold residueField_unibranchNormalizationEquivField
  change
    (((Ideal.quotEquivOfEq (maximalIdeal_eq_bot_unibranchNormalization_of_field K)).trans
          (RingEquiv.quotientBot K′)).trans
        (unibranchNormalizationEquivField K))
      (residue K′ x) =
    unibranchNormalizationEquivField K x
  unfold RingEquiv.quotientBot
  rfl

/-- Helper for Definition 15.107.1: the canonical residue-field map attached to the normalization
of a field is bijective because both residue fields identify with the same field. -/
lemma residueFieldMap_bijective_unibranchNormalization_of_field
    (K : Type u) [Field K] [IsLocalRing K′] :
    Function.Bijective (IsLocalRing.ResidueField.map (algebraMap K K′)) := by
  let _ : IsLocalHom (algebraMap K K′) := by
    let _ : Algebra.IsIntegral K K′ := inferInstance
    exact algebraMap_isLocalHom_of_isLocalRing_of_integral
  let ρ : ResidueField K →+* ResidueField K′ :=
    IsLocalRing.ResidueField.map (algebraMap K K′)
  let eSource : IsLocalRing.ResidueField K ≃+* K := residueFieldEquivField K
  let eTarget : ResidueField K′ ≃+* K :=
    residueField_unibranchNormalizationEquivField K
  let e : ResidueField K ≃+* ResidueField K′ :=
    eSource.trans eTarget.symm
  have he : e.toRingHom = ρ := by
    -- Both residue-field maps agree on residue classes of elements of `K`.
    refine Ideal.Quotient.ringHom_ext ?_
    ext a
    change
      e ((algebraMap K (ResidueField K)) a) =
        ρ
          ((algebraMap K (ResidueField K)) a)
    rw [show algebraMap K (ResidueField K) a = residue K a by rfl]
    rw [IsLocalRing.ResidueField.map_residue]
    apply eTarget.injective
    change
      eTarget (e (residue K a)) =
        residueField_unibranchNormalizationEquivField K
          (residue K′ ((algebraMap K K′) a))
    simpa [e] using
      (show eSource (residue K a) =
          residueField_unibranchNormalizationEquivField K
            (residue K′ ((algebraMap K K′) a)) from by
          rw [show residue K a = algebraMap K (ResidueField K) a by rfl]
          rw [residueFieldEquivField_apply_algebraMap]
          rw [residueField_unibranchNormalizationEquivField_apply_residue]
          rw [unibranchNormalizationEquivField_apply_algebraMap])
  have hfun : (e : ResidueField K → ResidueField K′) = ρ := by
    ext x
    exact congrArg (fun f : ResidueField K →+* ResidueField K′ => f x) he
  change Function.Bijective ρ
  exact hfun ▸ e.bijective

/-- Helper for Definition 15.107.1: the reduction of a field is a domain. -/
lemma isDomain_unibranchReduction_of_field (K : Type u) [Field K] :
    IsDomain (K)_red := by
  let e : (K)_red ≃+* K := unibranchReductionEquivField K
  -- The quotient by the nilradical is ring-equivalent to the original field.
  exact Function.Injective.isDomain e e.injective

/-- Helper for Definition 15.107.1: the normalization of the reduction of a field is local. -/
lemma isLocalRing_unibranchNormalization_of_field (K : Type u) [Field K] :
    IsLocalRing K′ := by
  let e : K′ ≃+* K := unibranchNormalizationEquivField K
  -- After identifying the normalization with the field, locality is immediate.
  exact e.symm.isLocalRing

/-- Helper for Definition 15.107.1: the residue-field extension for the normalization of a field
is purely inseparable because both residue fields identify with the same field. -/
lemma residueField_isPurelyInseparable_unibranchNormalization_of_field
    (K : Type u) [Field K] [IsLocalRing K′] :
    IsPurelyInseparable (ResidueField K) (ResidueField K′) := by
  -- Route correction: instead of post hoc algebra-compatibility repair, first show that the
  -- canonical residue-field map is bijective, then upgrade it directly to an algebra equivalence.
  let _ : IsLocalHom (algebraMap K K′) := by
    let _ : Algebra.IsIntegral K K′ := inferInstance
    exact algebraMap_isLocalHom_of_isLocalRing_of_integral
  let f : ResidueField K →ₐ[ResidueField K] ResidueField K′ :=
    Algebra.ofId (ResidueField K) (ResidueField K′)
  have hbij : Function.Bijective f := by
    simpa using residueFieldMap_bijective_unibranchNormalization_of_field K
  let e :
      ResidueField K ≃ₐ[ResidueField K] ResidueField K′ :=
    AlgEquiv.ofBijective f hbij
  -- A residue-field isomorphism over the base field transports pure inseparability from the
  -- identity extension.
  exact AlgEquiv.isPurelyInseparable e

/-- A field is unibranch. -/
instance (K : Type u) [Field K] : IsUnibranch K := by
  -- The field case follows the source route: reduction and normalization both collapse to `K`.
  refine
    { toIsDomain := isDomain_unibranchReduction_of_field K
      isLocalRing_unibranchNormalization := ?_ }
  exact isLocalRing_unibranchNormalization_of_field K

/-- A field is geometrically unibranch. -/
instance (K : Type u) [Field K] :
    IsGeometricallyUnibranch K := by
  -- The residue-field extension is trivial after identifying both residue fields with `K`.
  refine
    { toIsUnibranch := inferInstance
      residueField_isPurelyInseparable := ?_ }
  exact residueField_isPurelyInseparable_unibranchNormalization_of_field K

end
