import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_166_2
import stacks_proof.stacks_project.Chap10.Lemma_10_112_8
import stacks_proof.stacks_project.Chap10.Lemma_10_140_3
import stacks_proof.stacks_project.Chap15.Lemma_15_42_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u v w x

open IsLocalRing
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {k : Type u} {A : Type v} {B : Type w}
variable [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable [Algebra.Smooth A B] [IsGeometricallyRegular k A]

/- Domain-style sampling pass:
* primary domain: geometric regularity of algebras over a field and its permanence under smooth
  algebra maps;
* sampled owner declarations:
  `IsGeometricallyRegular`,
  `IsGeometricallyRegular.isRegularRing_baseChange`,
  `Algebra.Smooth.baseChange`,
  `isRegularRing_of_smooth`;
* best owner abstraction: `IsGeometricallyRegular` is the core owner, while smoothness and the
  regularity of tensor base changes are derived API that should not be repackaged locally.

Primitive data vs. derived API:
* primitive public inputs: `[Algebra.Smooth A B]` and `[IsGeometricallyRegular k A]`;
* derived API: for each finite purely inseparable extension `K / k`, the base-changed algebra
  `K ⊗[k] B` is smooth over `K ⊗[k] A`, and its regularity follows from
  `isRegularRing_of_smooth`.

Source/core/bridge triage:
* `source-facing`: `isGeometricallyRegular_of_smooth`;
* `core/canonical`: `IsGeometricallyRegular`;
* `bridge/view`: smooth tensor base change along `k → K` and the closed-fiber criterion for
  regular local rings.
-/
-- Proof sketch: for a finite purely inseparable field extension `K/k`, Lemma `10.137.3` gives
-- that `K ⊗[k] A → K ⊗[k] B` is smooth. Geometric regularity of `A` over `k` means `K ⊗[k] A`
-- is regular. Localizing at a prime of `K ⊗[k] B`, the smooth localized map has regular local
-- source and smooth closed fiber over a field, so the closed-fiber criterion `10.112.8` makes
-- the target localization regular. This proves `K ⊗[k] B` is regular.
/-- Helper for Chap10 Lemma 10 166 4: regularity transports across a ring equivalence. -/
private lemma regularRingOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (hR : IsRegularRing R) :
    IsRegularRing S := by
  -- Proof comment: descend regularity along the inverse isomorphism, viewed as a faithfully flat
  -- map, instead of unfolding all prime localizations.
  exact _root_.isRegularRing_of_faithfullyFlat e.symm.toRingHom
    (RingHom.FaithfullyFlat.of_bijective e.symm.bijective)

/-- Helper for Chap10 Lemma 10 166 4: a smooth algebra over a field is a regular ring. -/
private lemma isRegularRingOfSmoothOverField
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S] [Algebra.Smooth K S] :
    IsRegularRing S := by
  -- Proof comment: smoothness over a field puts every prime in the smooth locus, and
  -- `10.140.3` upgrades those local smooth points to regular local rings.
  letI : Algebra.FinitePresentation K S := inferInstance
  letI : Algebra.FiniteType K S := inferInstance
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  refine { isRegularLocalRing_atPrime := fun q ↦ ?_ }
  have hsmoothLocus : Algebra.smoothLocus K S = Set.univ := Algebra.smoothLocus_eq_univ
  have hqSmooth : Algebra.IsSmoothAt K q.asIdeal := by
    simpa [Algebra.smoothLocus] using (Set.eq_univ_iff_forall.mp hsmoothLocus) q
  simpa using Algebra.isRegularLocalRing_of_isSmoothAt (k := K) (S := S) q.asIdeal hqSmooth

/-- Helper for Chap10 Lemma 10 166 4: a smooth algebra over a field is geometrically regular. -/
private lemma isGeometricallyRegularOfSmoothOverField
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S] [Algebra.Smooth K S] :
    IsGeometricallyRegular K S := by
  -- Proof comment: after any finite purely inseparable field extension, smoothness base-changes
  -- to a smooth algebra over a field, hence to a regular ring by the previous helper.
  rw [isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
  intro L _ _ _ _
  letI : Algebra.Smooth L (_root_.TensorProduct K L S) := inferInstance
  exact isRegularRingOfSmoothOverField (K := L) (S := _root_.TensorProduct K L S)

/-- Helper for Chap10 Lemma 10 166 4: regularity ascends along a smooth algebra map. -/
private lemma isRegularRingOfSmoothOfIsRegularRing
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] [IsRegularRing R] :
    IsRegularRing S := by
  -- Proof comment: package the smooth map as a regular ring map. Its residue-field fibers are
  -- smooth over fields, so the field-level geometric-regularity helper supplies the fiber clause.
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let hSmooth : (algebraMap R S).Smooth := (RingHom.smooth_algebraMap).2 inferInstance
  let _ : (algebraMap R S).IsRegularRingMap := by
    exact
      { toFlat := RingHom.flat_algebraMap_iff.mpr inferInstance
        isGeometricallyRegular_fiber := fun p ↦ by
          letI : Algebra R S := (algebraMap R S).toAlgebra
          letI : Algebra.Smooth R S := (RingHom.smooth_algebraMap).1 hSmooth
          letI : Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
          exact isGeometricallyRegularOfSmoothOverField
            (K := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber S) }
  exact Algebra.isRegularRing_of_regularRingMap R

/-- Helper for Chap10 Lemma 10 166 4: geometric regularity tests may be shrunk to the universe of
the source algebra. -/
private lemma regularRingTensorBaseChangeOfGeometricallyRegular
    {K : Type x} [Field K] [Algebra k K] [FiniteDimensional k K]
    [IsPurelyInseparable k K] :
    IsRegularRing (_root_.TensorProduct k K A) := by
  -- Proof comment: finite-dimensionality makes the test field small enough to replace by
  -- `Shrink`; the definition tests that small model, and tensor congruence transports back.
  letI : Small.{max u v} K := Module.Finite.small (R := k) (M := K)
  let Ksmall := Shrink.{max u v} K
  letI : Field Ksmall := inferInstance
  letI : Algebra k Ksmall := inferInstance
  letI : FiniteDimensional k Ksmall :=
    (Shrink.algEquiv k K).symm.toLinearEquiv.finiteDimensional
  letI : IsPurelyInseparable k Ksmall :=
    (Shrink.algEquiv k K).symm.isPurelyInseparable
  have hSmall : IsRegularRing (_root_.TensorProduct k Ksmall A) :=
    IsGeometricallyRegular.isRegularRing_baseChange (k := k) (A := A) Ksmall
  let eSmall : (_root_.TensorProduct k Ksmall A) ≃+* (_root_.TensorProduct k K A) :=
    (Algebra.TensorProduct.congr
      (Shrink.algEquiv k K : Ksmall ≃ₐ[k] K)
      (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv
  exact regularRingOfRingEquiv eSmall hSmall

/-- Helper for Chap10 Lemma 10 166 4: every finite purely inseparable tensor base change of `B`
is regular once the corresponding tensor base change of `A` is regular and `A → B` is smooth. -/
lemma tensorBaseChange_isRegularRing_of_geometricallyRegularSource
    {A : Type v} [CommRing A] [Algebra k A] [Algebra A B] [IsScalarTower k A B]
    [Algebra.Smooth A B] [IsGeometricallyRegular k A]
    (K : Type x) [Field K] [Algebra k K] [FiniteDimensional k K]
    [IsPurelyInseparable k K] :
    IsRegularRing (_root_.TensorProduct k K B) := by
  -- Proof comment: first regularize the source tensor product, commute it into the orientation
  -- used by base-change cancellation, ascend regularity along the smooth base change, and then
  -- cancel the iterated tensor product back to `K ⊗[k] B`.
  have hSource : IsRegularRing (_root_.TensorProduct k K A) :=
    regularRingTensorBaseChangeOfGeometricallyRegular (k := k) (A := A) (K := K)
  let T := _root_.TensorProduct k A K
  letI : IsRegularRing T :=
    regularRingOfRingEquiv (Algebra.TensorProduct.comm (R := k) (A := K) (B := A)).toRingEquiv
      hSource
  letI : Algebra A T := Algebra.TensorProduct.leftAlgebra
  letI : Algebra K T := Algebra.TensorProduct.rightAlgebra
  letI : Algebra.Smooth T (_root_.TensorProduct A T B) := inferInstance
  have hTargetModel : IsRegularRing (_root_.TensorProduct A T B) :=
    isRegularRingOfSmoothOfIsRegularRing (R := T) (S := _root_.TensorProduct A T B)
  let eCancel : (_root_.TensorProduct A T B) ≃+* (_root_.TensorProduct k K B) :=
    (Algebra.IsPushout.cancelBaseChangeAlg (R := k) (S := K) (A := A)
      (B := T) (C := B)).toRingEquiv
  exact regularRingOfRingEquiv eCancel hTargetModel

include A

/-- Chap10 Lemma 10 166 4: if `A → B` is a smooth map of `k`-algebras and `A` is
geometrically regular over `k`, then `B` is geometrically regular over `k`. -/
@[stacks 07QF]
theorem isGeometricallyRegular_of_smooth :
    IsGeometricallyRegular k B := by
  -- Proof comment: geometric regularity is tested after tensoring with each finite purely
  -- inseparable field extension of `k`.
  rw [isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
  intro K _ _ _ _
  -- Proof comment: for the chosen test field `K`, the tensor source is regular and the
  -- base-changed smooth map is regular, so the tensor target is regular.
  exact tensorBaseChange_isRegularRing_of_geometricallyRegularSource (k := k) (A := A) (B := B) K

omit A in
/-- Smooth algebras over the field `k` are geometrically regular over `k`. -/
instance [Algebra.Smooth k B] : IsGeometricallyRegular k B :=
  isGeometricallyRegular_of_smooth (k := k) (A := k) (B := B)

end

end Algebra
