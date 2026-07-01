import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Topology.Inseparable
import stacks_project.Chap15.Lemma_15_105_23

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

/-- A field is unibranch. -/
instance (K : Type u) [Field K] : IsUnibranch K := sorry

/-- A field is geometrically unibranch. -/
instance (K : Type u) [Field K] :
    IsGeometricallyUnibranch K := sorry

end
