import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain triage: this file is in the commutative algebra of finite normalization over a domain and
over its finite fraction-field extensions.

Source/core/bridge triage for the public declarations:
- source-facing owners: `IsN1Ring` and `IsN2Ring`, the textbook `N-1` and `N-2` conditions;
- core data: the corresponding finite-module structures on integral closures, with the `N-2`
  owner storing the finite-extension family directly in the small-universe owner surface;
- bridge/view: the arbitrary-universe `N-2` finiteness theorem and the derived implication
  `IsN2Ring R → IsN1Ring R`.

The primitive data are exactly the two finiteness properties. The `N-2 → N-1` implication is
derived API, so it should stay an instance rather than an extra field of `IsN2Ring`.
-/

section

variable (R : Type u) [CommRing R] [IsDomain R]

/-- Definition 10.161.1 (1): An N-1 domain is a domain whose integral closure in its
fraction field is a finite module over the domain. -/
class IsN1Ring : Prop where
  /-- The integral closure of `R` in its fraction field is finite over `R`. -/
  integralClosure_finite :
    Module.Finite R (integralClosure R (FractionRing R))

/-- Definition 10.161.1 (2): An `N-2` ring, equivalently a Japanese domain, is a domain such
that for every finite extension of its fraction field, the integral closure of the domain in that
extension is finite over the domain. -/
class IsN2Ring : Prop where
  /-- The integral closure of `R` in every finite extension of its fraction field is finite over
  `R`. This is the small-universe owner field; the arbitrary-universe form is derived below by
  shrinking finite-dimensional extensions. -/
  integralClosure_finite
    (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L] :
    Module.Finite R (integralClosure R L)

attribute [instance] IsN1Ring.integralClosure_finite
attribute [instance] IsN2Ring.integralClosure_finite

end

namespace IsN2Ring

variable {R : Type u} [CommRing R] [IsDomain R]
variable (L : Type v) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
variable [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]

/-- The defining `N-2` finiteness statement for an arbitrary finite extension of the fraction
field. -/
theorem integralClosure_finite_of_finiteDimensional [hR : IsN2Ring R] :
    Module.Finite R (integralClosure R L) := by
  letI : Module.Finite (FractionRing R) L := inferInstance
  letI : Small.{u} L := Module.Finite.small (FractionRing R) L
  letI : Algebra R (Shrink.{u} L) := inferInstance
  letI : Algebra (FractionRing R) (Shrink.{u} L) := inferInstance
  letI : IsScalarTower R (FractionRing R) (Shrink.{u} L) :=
    LinearEquiv.isScalarTower (FractionRing R) (Shrink.linearEquiv R L)
  letI : FiniteDimensional (FractionRing R) (Shrink.{u} L) := by infer_instance
  letI : Module.Finite R (integralClosure R (Shrink.{u} L)) :=
    hR.integralClosure_finite (Shrink.{u} L)
  exact Module.Finite.equiv (Shrink.algEquiv R L).mapIntegralClosure.toLinearEquiv

attribute [instance] integralClosure_finite_of_finiteDimensional

end IsN2Ring

/-- A field has finite normalization in every finite extension of itself. -/
private theorem field_integralClosure_finite
    (K : Type u) [Field K] {L : Type v} [Field L] [Algebra K L] [Algebra (FractionRing K) L]
    [IsScalarTower K (FractionRing K) L] [FiniteDimensional (FractionRing K) L] :
    Module.Finite K (integralClosure K L) := by
  have hfinL : Module.Finite K L := by
    let e₁ : FractionRing K ≃+* K := (FractionRing.algEquiv K K).toRingEquiv
    let e₂ : L ≃+* L := RingEquiv.refl _
    letI : Module.Finite (FractionRing K) L := inferInstance
    let f : L ≃ₐ[K] L := AlgEquiv.refl
    have he : RingHom.comp (algebraMap K L) ↑e₁ =
        RingHom.comp ↑e₂ (algebraMap (FractionRing K) L) := by
      ext x
      simpa [e₁, e₂] using
        IsFractionRing.algEquiv_commutes
          (FractionRing.algEquiv K K) f x
    exact Module.Finite.of_equiv_equiv e₁ e₂ he
  letI : Module.Finite K L := hfinL
  letI : Algebra.IsIntegral K L := inferInstance
  have htop : integralClosure K L = ⊤ :=
    integralClosure_eq_top_iff.2 inferInstance
  let e : integralClosure K L ≃ₐ[K] L :=
    (Subalgebra.equivOfEq (integralClosure K L) ⊤ htop).trans
      (show (⊤ : Subalgebra K L) ≃ₐ[K] L from Subalgebra.topEquiv)
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- A field is `N-2`. -/
noncomputable instance (K : Type u) [Field K] : IsN2Ring K where
  integralClosure_finite := by
    intro L _ _ _ _ _
    exact field_integralClosure_finite K

/-- The `N-2` finiteness statement specialized to the fraction field. -/
private theorem integralClosure_finite_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsN2Ring R] :
    Module.Finite R (integralClosure R (FractionRing R)) := by
  let h : IsN2Ring R := inferInstance
  exact h.integralClosure_finite (FractionRing R)

/-- Every N-2 ring is N-1. -/
-- Proof sketch: apply the N-2 finiteness statement to the finite extension
-- `FractionRing R / FractionRing R`.
instance (R : Type u) [CommRing R] [IsDomain R] [h : IsN2Ring R] :
    IsN1Ring R where
  integralClosure_finite := by
    letI : IsN2Ring R := h
    exact integralClosure_finite_fractionRing R
