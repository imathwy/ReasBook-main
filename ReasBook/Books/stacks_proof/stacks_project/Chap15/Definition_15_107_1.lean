import Mathlib.Algebra.Field.TransferInstance
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Topology.Inseparable
import stacks_proof.stacks_project.Chap15.Lemma_15_105_23
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing

universe u

section

variable (A : Type u) [CommRing A]

/-- The reduction `A_red` of a commutative ring `A`. -/
abbrev unibranchReduction :=
  A ⧸ nilradical A

/-- The normalization of the reduction of a commutative ring inside its fraction field. -/
abbrev unibranchNormalization :=
  integralClosure (unibranchReduction A) (FractionRing (unibranchReduction A))

namespace Unibranch

/- The textbook notation is `A_red`. Lean parses bare `A_red` as a single identifier, so the
owner-level term notation is parenthesized as `(A)_red`. -/
/-- Scoped notation for the reduction `A_red` of a commutative ring `A`. -/
scoped notation:max "(" R ")" "_red" => unibranchReduction R

/-- Scoped notation for the unibranch normalization `A'`. -/
scoped postfix:max "′" => unibranchNormalization

end Unibranch

open scoped Unibranch

/-- The unibranch normalization inherits an `A`-algebra structure through the quotient map
`A → (A)_red`. -/
instance : Algebra A A′ :=
  ((algebraMap (A)_red A′).comp (algebraMap A (A)_red)).toAlgebra

/-- The unibranch normalization lies over the reduction `(A)_red` as an `A`-algebra tower. -/
instance : IsScalarTower A (A)_red A′ :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The unibranch normalization is integral over `A`. -/
instance : Algebra.IsIntegral A A′ :=
  Algebra.IsIntegral.trans (A)_red

variable [IsLocalRing A]

/-- The reduction of a local ring is again local. -/
instance :
    IsLocalRing (A)_red := by
  let _ : Nontrivial (A ⧸ nilradical A) := Ideal.Quotient.nontrivial_iff.2 <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
      (nilradical_le_prime (maximalIdeal A))
  simpa [unibranchReduction, Ideal.Quotient.algebraMap_eq] using
    (IsLocalRing.of_surjective' (Ideal.Quotient.mk (nilradical A)) Ideal.Quotient.mk_surjective :
      IsLocalRing (A ⧸ nilradical A))

/-- The canonical quotient map from a local ring to its reduction is local. -/
instance : IsLocalHom (algebraMap A (A)_red) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

/-- The residue field `κ(m)` at a maximal point `m`. -/
abbrev MaximalSpectrum.ResidueField {R : Type u} [CommRing R] (m : MaximalSpectrum R) :=
  m.asIdeal.ResidueField

/-- Any maximal ideal of the unibranch normalization `A'` contracts to the maximal ideal of the
local base ring `A`. -/
theorem unibranchNormalization_comap_maximalIdeal
    {m : Ideal A′} (hm : m.IsMaximal) :
    Ideal.comap (algebraMap A A′) m = maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)

private noncomputable abbrev maximalIdealResidueFieldEquiv :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- The canonical residue-field map `κ(A) → κ(m')` induced by the local base map
`A → A' = unibranchNormalization A`. -/
noncomputable def unibranchNormalizationResidueFieldMap
    (m : MaximalSpectrum A′) :
    ResidueField A →+* m.ResidueField :=
  (Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A A′)
      (unibranchNormalization_comap_maximalIdeal A m.isMaximal).symm).comp
    (maximalIdealResidueFieldEquiv A).symm.toRingHom

/-- The residue field at a maximal point of the unibranch normalization is canonically a
`ResidueField A`-algebra. -/
noncomputable instance (m : MaximalSpectrum A′) :
    Algebra (ResidueField A) m.ResidueField :=
  (unibranchNormalizationResidueFieldMap A m).toAlgebra

/-- Definition 15.107.1 (1): a local ring is unibranch if its reduction is a domain and the
normalization of that reduction in its fraction field is local. -/
@[stacks 0BPZ]
class IsUnibranch : Prop where
  toIsDomain : IsDomain (A)_red
  isLocalRing_unibranchNormalization :
    letI : IsDomain (A)_red := toIsDomain
    IsLocalRing A′

instance [h : IsUnibranch A] : IsDomain (A)_red :=
  h.toIsDomain

instance [h : IsUnibranch A] : IsLocalRing A′ := by
  letI : IsDomain (A)_red := h.toIsDomain
  exact h.isLocalRing_unibranchNormalization

/-- The canonical map `A → A'` to the unibranch normalization is local. -/
instance [IsUnibranch A] : IsLocalHom (algebraMap A A′) :=
  algebraMap_isLocalHom_of_isLocalRing_of_integral

/-- Definition 15.107.1 (2): a local ring is geometrically unibranch if it is unibranch and the
canonical residue-field extension induced by `A → A'` is purely inseparable. -/
@[stacks 0BPZ]
class IsGeometricallyUnibranch : Prop where
  toIsUnibranch : IsUnibranch A
  residueField_isPurelyInseparable :
    letI : IsUnibranch A := toIsUnibranch
    IsPurelyInseparable (ResidueField A) (ResidueField A′)

instance [h : IsGeometricallyUnibranch A] : IsUnibranch A :=
  h.toIsUnibranch

instance [h : IsGeometricallyUnibranch A] :
    IsPurelyInseparable (ResidueField A) (ResidueField A′) := by
  letI : IsUnibranch A := h.toIsUnibranch
  exact h.residueField_isPurelyInseparable

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
