import Mathlib
import StacksProject_2024.Chap10.Definition_10_161_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain triage: this file is in the commutative algebra of localization stability for the
source-facing `N-1` and `N-2` properties of domains.

Owner abstractions sampled for this item:
- `IsN1Ring`, the source-facing owner from `Definition_10_161_1`;
- `IsN2Ring`, the source-facing owner from `Definition_10_161_1`;
- `IsLocalization.integralClosure`, the canonical localization owner for normalization;
- `integralClosure.isFractionRing_of_finite_extension`, the canonical fraction-field owner used to
  compare finite extensions before and after localization.

Primitive data here are only the localization datum `R → Rₘ` and the owner assumptions
`[IsN1Ring R]` or `[IsN2Ring R]`. The finiteness statements for integral closures and the
fraction-ring identifications are derived API internal to the proofs. These results should stay as
theorems, not global instances: the localization parameter `M` is genuine primitive data and is
not recoverable from the target ring `Rₘ` alone.

Layer triage:
- `source-facing`: localization preserves the textbook `N-1` and `N-2` properties;
- `core/canonical`: `IsN1Ring`, `IsN2Ring`, `IsLocalization.integralClosure`, and fraction-ring
  comparison for finite extensions;
- `bridge/view`: the proof-level transport of finite integral-closure modules across the chosen
  localization.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable (M : Submonoid R) {Rₘ : Type v} [CommRing Rₘ] [Algebra R Rₘ]
  [IsLocalization M Rₘ] [IsDomain Rₘ]

/-- Helper for Lemma 10.161.3: if a localization of a domain is again a domain, every element of
the localized submonoid is a nonzerodivisor. -/
lemma localization_submonoid_le_nonZeroDivisors
    (Rₘ : Type v) [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ] [IsDomain Rₘ] :
    M ≤ nonZeroDivisors R := by
  intro x hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hx0
  have hunit : IsUnit (algebraMap R Rₘ x) := IsLocalization.map_units Rₘ ⟨x, hx⟩
  rw [hx0, map_zero] at hunit
  exact hunit.ne_zero rfl

/-- Lemma 10.161.3 (1): any localization of an N-1 domain that is still a domain is again
N-1. -/
-- Proof sketch: identify `FractionRing R` as a fraction ring of the chosen localization `Rₘ`,
-- localize the
-- finite `R`-module `integralClosure R (FractionRing R)`, and then use
-- `IsLocalization.integralClosure` to identify that localization with
-- `integralClosure Rₘ (FractionRing R)`.
theorem isN1Ring_of_isLocalization (M : Submonoid R) [IsLocalization M Rₘ] [IsN1Ring R] :
    IsN1Ring Rₘ := by
  let hM := localization_submonoid_le_nonZeroDivisors (R := R) (Rₘ := Rₘ) M
  letI : Algebra Rₘ (FractionRing R) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Rₘ (FractionRing R) M (nonZeroDivisors R) hM
  letI : IsScalarTower R Rₘ (FractionRing R) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      Rₘ (FractionRing R) M (nonZeroDivisors R) hM
  letI : IsFractionRing Rₘ (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Rₘ (FractionRing R)
  refine IsN1Ring.mk ?_
  have hfinite_common : Module.Finite Rₘ (integralClosure Rₘ (FractionRing R)) := by
    -- Localizing the finite normalization of `R` gives finiteness in the shared fraction field.
    have hSfUnits :
        Algebra.algebraMapSubmonoid (FractionRing R) M ≤ IsUnit.submonoid (FractionRing R) := by
      rintro _ ⟨x, hx, rfl⟩
      change IsUnit (algebraMap R (FractionRing R) x)
      rw [isUnit_iff_ne_zero]
      intro hx0
      exact (mem_nonZeroDivisors_iff_ne_zero.mp (hM hx))
        ((IsFractionRing.injective R (FractionRing R)) (by simpa using hx0))
    letI : IsLocalization (Algebra.algebraMapSubmonoid (FractionRing R) M) (FractionRing R) :=
      IsLocalization.self hSfUnits
    have hle :
        integralClosure R (FractionRing R) ≤
          (integralClosure Rₘ (FractionRing R)).restrictScalars R := by
      intro x hx
      change IsIntegral Rₘ x
      exact IsIntegral.map_of_comp_eq (φ := algebraMap R Rₘ) (ψ := RingHom.id _)
        (by
          ext y
          simp [IsScalarTower.algebraMap_apply R Rₘ (FractionRing R)]) hx
    let f :
        integralClosure R (FractionRing R) →+* integralClosure Rₘ (FractionRing R) :=
      (Subalgebra.inclusion hle).toRingHom
    letI : Algebra (integralClosure R (FractionRing R)) (integralClosure Rₘ (FractionRing R)) :=
      f.toAlgebra
    letI :
        SMul (integralClosure R (FractionRing R)) (integralClosure Rₘ (FractionRing R)) :=
      (show
          Algebra (integralClosure R (FractionRing R)) (integralClosure Rₘ (FractionRing R)) from
            inferInstance).toSMul
    letI :
        IsScalarTower R (integralClosure R (FractionRing R))
          (integralClosure Rₘ (FractionRing R)) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <| by rfl
    letI :
        IsScalarTower (integralClosure R (FractionRing R))
          (integralClosure Rₘ (FractionRing R)) (FractionRing R) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ by
        cases x
        rfl
    letI :
        IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R (FractionRing R)) M)
          (integralClosure Rₘ (FractionRing R)) :=
      IsLocalization.integralClosure (R := R) (S := FractionRing R)
        (Rf := Rₘ) (Sf := FractionRing R) M
    exact Module.Finite.of_isLocalization R (integralClosure R (FractionRing R)) M
  -- Transport the finite normalization back from the common fraction field to `FractionRing Rₘ`.
  exact Module.Finite.equiv
    ((FractionRing.algEquiv Rₘ (FractionRing R)).mapIntegralClosure.symm.toLinearEquiv)

/-- Lemma 10.161.3 (2): any localization of an N-2 domain that is still a domain is again
N-2. -/
-- Proof sketch: for a finite extension `L / FractionRing Rₘ`, transport the
-- fraction-ring structure along localization so that `L` is also a finite extension of
-- `FractionRing R`; apply the `N-2` hypothesis on `R`, then use localization of finite modules and
-- `IsLocalization.integralClosure` to obtain finiteness for the localized integral closure.
theorem isN2Ring_of_isLocalization (M : Submonoid R) [IsLocalization M Rₘ] [IsN2Ring R] :
    IsN2Ring Rₘ := by
  let hM := localization_submonoid_le_nonZeroDivisors (R := R) (Rₘ := Rₘ) M
  letI : Algebra Rₘ (FractionRing R) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Rₘ (FractionRing R) M (nonZeroDivisors R) hM
  letI : IsScalarTower R Rₘ (FractionRing R) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      Rₘ (FractionRing R) M (nonZeroDivisors R) hM
  letI : IsFractionRing Rₘ (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Rₘ (FractionRing R)
  refine IsN2Ring.mk fun L => ?_
  intro _ _ _ _ _
  letI : Algebra R L := (RingHom.comp (algebraMap Rₘ L) (algebraMap R Rₘ)).toAlgebra
  letI : IsScalarTower R Rₘ L := IsScalarTower.of_algebraMap_eq' rfl
  let e : FractionRing Rₘ ≃ₐ[Rₘ] FractionRing R := FractionRing.algEquiv Rₘ (FractionRing R)
  let fL : FractionRing R →ₐ[Rₘ] L :=
    (IsScalarTower.toAlgHom Rₘ (FractionRing Rₘ) L).comp e.symm
  letI : Algebra (FractionRing R) L := fL.toRingHom.toAlgebra
  letI : IsScalarTower R (FractionRing R) L := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    calc
      algebraMap R L x = algebraMap Rₘ L (algebraMap R Rₘ x) := by
        simpa [IsScalarTower.algebraMap_apply R Rₘ L]
      _ = algebraMap (FractionRing R) L
            (algebraMap Rₘ (FractionRing R) (algebraMap R Rₘ x)) := by
        exact IsScalarTower.algebraMap_apply Rₘ (FractionRing R) L (algebraMap R Rₘ x)
      _ = algebraMap (FractionRing R) L (algebraMap R (FractionRing R) x) := by
        rw [IsScalarTower.algebraMap_apply R Rₘ (FractionRing R)]
  have hfinite_fraction : Module.Finite (FractionRing R) L := by
    letI : Module.Finite (FractionRing Rₘ) L := inferInstance
    have hcompat :
        RingHom.comp (algebraMap (FractionRing R) L) ↑e.toRingEquiv =
          RingHom.comp (RingEquiv.refl L) (algebraMap (FractionRing Rₘ) L) := by
      ext x
      simpa using
        (IsFractionRing.algEquiv_commutes e
          (show L ≃ₐ[FractionRing R] L from AlgEquiv.refl) x)
    exact Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl L) hcompat
  letI : FiniteDimensional (FractionRing R) L := by infer_instance
  have hfinite_integralClosure : Module.Finite R (integralClosure R L) := by
    -- The `N-2` hypothesis on `R` applies once `L` is viewed as a finite `FractionRing R`-extension.
    exact IsN2Ring.integralClosure_finite_of_finiteDimensional (R := R) (L := L)
  -- Localizing the finite integral closure over `R` identifies it with the integral closure over
  -- the chosen localization `Rₘ`.
  have hLUnits : Algebra.algebraMapSubmonoid L M ≤ IsUnit.submonoid L := by
    rintro _ ⟨x, hx, rfl⟩
    change IsUnit (algebraMap R L x)
    rw [isUnit_iff_ne_zero]
    intro hxL
    have hxRₘ : algebraMap R Rₘ x ≠ 0 := by
      intro hxRₘ
      exact (mem_nonZeroDivisors_iff_ne_zero.mp (hM hx))
        ((IsLocalization.injective Rₘ hM) (by simpa using hxRₘ))
    exact hxRₘ
      ((algebraMap_injective_of_field_isFractionRing Rₘ L (FractionRing Rₘ) L)
        (by simpa [IsScalarTower.algebraMap_apply R Rₘ L] using hxL))
  letI : IsLocalization (Algebra.algebraMapSubmonoid L M) L :=
    IsLocalization.self hLUnits
  have hle :
      integralClosure R L ≤ (integralClosure Rₘ L).restrictScalars R := by
    intro x hx
    change IsIntegral Rₘ x
    exact IsIntegral.map_of_comp_eq (φ := algebraMap R Rₘ) (ψ := RingHom.id _)
      (by
        ext y
        simp [IsScalarTower.algebraMap_apply R Rₘ L]) hx
  let f : integralClosure R L →+* integralClosure Rₘ L :=
    (Subalgebra.inclusion hle).toRingHom
  letI : Algebra (integralClosure R L) (integralClosure Rₘ L) :=
    f.toAlgebra
  letI : SMul (integralClosure R L) (integralClosure Rₘ L) :=
    (show Algebra (integralClosure R L) (integralClosure Rₘ L) from inferInstance).toSMul
  letI : IsScalarTower R (integralClosure R L) (integralClosure Rₘ L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <| by rfl
  letI : IsScalarTower (integralClosure R L) (integralClosure Rₘ L) L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      cases x
      rfl
  letI :
      IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R L) M)
        (integralClosure Rₘ L) :=
    IsLocalization.integralClosure (R := R) (S := L) (Rf := Rₘ) (Sf := L) M
  exact Module.Finite.of_isLocalization R (integralClosure R L) M

end
