import Mathlib
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_161_1 (from Chap10) -/
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

/-! ### Example_10_161_2 (from Chap10) -/
universe u

/-
Domain triage: this file is in commutative algebra of Japanese/Nagata-style finiteness and
Noetherianity for polynomial rings in infinitely many variables.

Source/core/bridge triage for the target declarations:
- source-facing: the two public example theorems for `MvPolynomial ℕ+ k` and `MvPolynomial ℕ+ ℤ`;
- core/canonical: `IsN2Ring` and `MvPolynomial.idealOfVars`;
- bridge/view: the private reduction from the countable-variable ring to the finite-variable family.

Owner abstractions sampled for this item:
- `IsN2Ring`, the source-facing `N-2` owner from `Definition_10_161_1`;
- `MvPolynomial.idealOfVars`, the canonical owner ideal generated by all variables;
- the finite-variable polynomial-ring owner theorem `isN2Ring_polynomial`, iterated through
  `MvPolynomial.finSuccEquiv` in the proof sketches below.

Primitive data here are only the coefficient ring and the countably many polynomial variables.
The `N-2` claim and the failure of Noetherianity are derived properties, so the public API should
stay as the two source-facing conjunction theorems while any reusable proof decomposition remains
private.
-/

-- Proof sketch: if `MvPolynomial σ R` were Noetherian, then the owner ideal
-- `MvPolynomial.idealOfVars σ R` would be finitely generated. Any finite generating family uses
-- only finitely many variables, so choosing a variable outside that finite support shows the
-- corresponding generator `X i` is not in the generated ideal, contradiction.
private theorem mvPolynomial_not_isNoetherianRing_of_infinite
    (σ : Type*) [Infinite σ] (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ IsNoetherianRing (MvPolynomial σ R) := by
  sorry

-- Proof sketch: let `L / FractionRing (MvPolynomial ℕ+ R)` be a finite extension. Any finite set
-- of coefficients and structural constants arising from `L` and from generators of the relevant
-- integral closure involves only finitely many variables, so everything descends to some
-- finite-variable subring `MvPolynomial (Fin n) R`. Applying the supplied finite-variable `N-2`
-- hypothesis there and then extending scalars back to countably many variables gives the desired
-- finiteness.
private theorem countableVariableMvPolynomial_isN2Ring_of_finiteVariable
    {R : Type u} [CommRing R] [IsDomain R]
    (hfinite : ∀ n : ℕ, IsN2Ring (MvPolynomial (Fin n) R)) :
    IsN2Ring (MvPolynomial ℕ+ R) := by
  sorry

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsN2Ring R]

local notation "R∞" => MvPolynomial ℕ+ R

-- Proof sketch: induct on the number of variables using the canonical equivalence between
-- `MvPolynomial (Fin (n + 1)) R` and `Polynomial (MvPolynomial (Fin n) R)`, and apply the owner
-- theorem `isN2Ring_polynomial` at each step.
private theorem finiteVariableMvPolynomial_isN2Ring (n : ℕ) :
    IsN2Ring (MvPolynomial (Fin n) R) := by
  sorry

private theorem countableVariableMvPolynomial_isN2Ring_and_not_isNoetherian :
    IsN2Ring R∞ ∧ ¬ IsNoetherianRing R∞ := by
  exact ⟨countableVariableMvPolynomial_isN2Ring_of_finiteVariable
      finiteVariableMvPolynomial_isN2Ring,
    mvPolynomial_not_isNoetherianRing_of_infinite ℕ+ R⟩

end

section

variable (k : Type u) [Field k]

local notation "Rinf" => MvPolynomial ℕ+ k

-- Proof sketch: write any finite extension of `FractionRing Rinf` over a finitely generated
-- subfield `L₀ / k(x₁, …, xₙ)`, use the finite-variable case for the integral closure over
-- `k[x₁, …, xₙ]`, and then adjoin the remaining transcendental variables. For non-Noetherianity,
-- use the generic infinite-variable lemma based on the owner ideal `MvPolynomial.idealOfVars`.
/-- Example 10.161.2: for a field `k`, the polynomial ring `k[x₁, x₂, x₃, \ldots]`, modeled as
`MvPolynomial ℕ+ k`, is `N-2` and is not Noetherian. -/
theorem countableVariablePolynomialRing_isN2Ring_and_not_isNoetherian :
    IsN2Ring Rinf ∧ ¬ IsNoetherianRing Rinf := by
  exact countableVariableMvPolynomial_isN2Ring_and_not_isNoetherian

end

section

local notation "Zinf" => MvPolynomial ℕ+ ℤ

-- Proof sketch: repeat the argument of the field case, using the finite-variable Nagata property
-- for `ℤ[x₁, …, xₙ]` in place of the field case. For non-Noetherianity, reuse the generic
-- infinite-variable lemma coming from `MvPolynomial.idealOfVars`.
/-- The same countable-variable polynomial-ring example over `ℤ` is `N-2` and not Noetherian. -/
theorem countableVariableIntegerPolynomialRing_isN2Ring_and_not_isNoetherian :
    IsN2Ring Zinf ∧ ¬ IsNoetherianRing Zinf := by
  haveI : IsN2Ring ℤ := by
    sorry
  exact countableVariableMvPolynomial_isN2Ring_and_not_isNoetherian

end

/-! ### Lemma_10_161_3 (from Chap10) -/
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

/-! ### Lemma_10_161_4 (from Chap10) -/
section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-
Domain triage: this file is in the commutative algebra of the `N-1` and `N-2` conditions under a
finite principal-open cover.

Owner abstractions sampled for this item:
- `IsN1Ring` and `IsN2Ring`, the source-facing owners from `Definition_10_161_1`;
- `isN1Ring_of_isLocalization` and `isN2Ring_of_isLocalization`, the localization-stability
  bridge theorems from `Lemma_10_161_3`;
- `Module.Finite.of_localizationSpan_finite`, the canonical finite-module descent theorem over a
  principal-open cover from `Lemma_10_23_2`.

Primitive data are the finite cover `s`, the unit-ideal hypothesis `hs`, and the domain hypotheses
for the chosen localizations. The localized `N-1` / `N-2` conditions are source-facing
assumptions. The finite-normalization statements and localization identifications are derived API
internal to the proofs, so this file should reuse the owners above directly rather than introducing
parallel local wrappers.
-/

/- Lemma 10.161.4, the `N-1` clause, is exactly the owner definition `IsN1Ring`: the forward
direction is `IsN1Ring.integralClosure_finite`, and the reverse direction is `IsN1Ring.mk`. -/
recall IsN1Ring.integralClosure_finite
recall IsN1Ring.mk

/- Lemma 10.161.4, the `N-2` clause, is exactly the owner definition `IsN2Ring`: the forward
direction is `IsN2Ring.integralClosure_finite`, and the reverse direction is `IsN2Ring.mk`. -/
recall IsN2Ring.integralClosure_finite
recall IsN2Ring.mk

variable (s : Finset R)

/-- Helper for Lemma 10.161.4: if the localization `R_f` is a domain, then `f` is nonzero in
`R`. -/
lemma localizationAway_ne_zero
    (f : s) [IsDomain (Localization.Away f.1)] :
    f.1 ≠ 0 := by
  -- A zero element cannot become a unit in a domain localization.
  intro hf
  have hunit : IsUnit (algebraMap R (Localization.Away f.1) f.1) :=
    IsLocalization.map_units (Localization.Away f.1) ⟨f.1, Submonoid.mem_powers _⟩
  have hne : algebraMap R (Localization.Away f.1) f.1 ≠ 0 := hunit.ne_zero
  exact hne <| by simp [hf]

/-- Helper for Lemma 10.161.4: every power of an element with domain localization is a
nonzerodivisor. -/
lemma localizationAway_le_nonZeroDivisors
    (f : s) [IsDomain (Localization.Away f.1)] :
    Submonoid.powers f.1 ≤ nonZeroDivisors R := by
  -- Reduce to the nonvanishing of the generator and then use powers in a domain.
  intro x hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  rcases (show ∃ n : ℕ, f.1 ^ n = x by simpa [Submonoid.mem_powers_iff] using hx) with ⟨n, rfl⟩
  exact pow_ne_zero n (localizationAway_ne_zero (s := s) f)

/-- Helper for Lemma 10.161.4: integral elements over `R` remain integral after localizing the
base ring away from `f`. -/
lemma integralClosure_le_localizationAway_integralClosure
    {L : Type u} [Field L] [Algebra R L] (f : s)
    [Algebra (Localization.Away f.1) L] [IsScalarTower R (Localization.Away f.1) L] :
    integralClosure R L ≤
      (integralClosure (Localization.Away f.1) L).restrictScalars R := by
  -- The localized base ring receives `R`, so integrality is preserved along the map.
  intro x hx
  change IsIntegral (Localization.Away f.1) x
  exact IsIntegral.map_of_comp_eq (φ := algebraMap R (Localization.Away f.1)) (ψ := RingHom.id _)
    (by
      ext y
      simp [IsScalarTower.algebraMap_apply R (Localization.Away f.1) L]) hx

/-- Helper for Lemma 10.161.4: finiteness of the localized integral closures on a principal-open
cover descends to finiteness of the global integral closure. -/
lemma integralClosure_finite_of_localizationAway_cover
    {L : Type u} [Field L] [Algebra R L]
    [∀ f : s, Algebra (Localization.Away f.1) L]
    [∀ f : s, IsScalarTower R (Localization.Away f.1) L]
    [∀ f : s, IsLocalization.Away (algebraMap R L f.1) L]
    (hs : Ideal.span (s : Set R) = ⊤)
    (hfinite : ∀ f : s, Module.Finite (Localization.Away f.1)
      (integralClosure (Localization.Away f.1) L)) :
    Module.Finite R (integralClosure R L) := by
  -- For each generator, compare the localized global normalization with the local normalization.
  let hle : ∀ f : s, integralClosure R L ≤
      (integralClosure (Localization.Away f.1) L).restrictScalars R := fun f ↦
    integralClosure_le_localizationAway_integralClosure (R := R) (s := s) f
  let fint : ∀ f : s, integralClosure R L →+* integralClosure (Localization.Away f.1) L := fun f ↦
    (Subalgebra.inclusion (hle f)).toRingHom
  letI : ∀ f : s, Algebra (integralClosure R L)
      (integralClosure (Localization.Away f.1) L) := fun f ↦
    (fint f).toAlgebra
  letI : ∀ f : s,
      SMul (integralClosure R L) (integralClosure (Localization.Away f.1) L) := fun f ↦
    (show
        Algebra (integralClosure R L) (integralClosure (Localization.Away f.1) L) from
          inferInstance).toSMul
  letI : ∀ f : s, IsScalarTower R (integralClosure R L)
      (integralClosure (Localization.Away f.1) L) := fun f ↦
    IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <| by rfl
  letI : ∀ f : s, IsScalarTower (integralClosure R L)
      (integralClosure (Localization.Away f.1) L) L := fun f ↦
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      cases x
      rfl
  letI : ∀ f : s,
      IsLocalization.Away (algebraMap R (integralClosure R L) f.1)
        (integralClosure (Localization.Away f.1) L) := fun f ↦
    IsLocalization.Away.integralClosure (R := R) (S := L) (Rf := Localization.Away f.1)
      (Sf := L) f.1
  let κ : ∀ f : s, integralClosure R L →ₗ[R] integralClosure (Localization.Away f.1) L := fun f ↦
    (IsScalarTower.toAlgHom R (integralClosure R L)
      (integralClosure (Localization.Away f.1) L)).toLinearMap
  letI : ∀ f : s, IsLocalizedModule (Submonoid.powers f.1) (κ f) := fun f ↦ inferInstance
  -- Apply the principal-open descent theorem to the integral closure itself.
  exact Module.Finite.of_localizationSpan_finite' s hs κ hfinite

/-- Helper for Lemma 10.161.4: the local `N-1` hypothesis gives finiteness of the integral
closure in the common fraction field. -/
lemma localizationAway_integralClosure_finite_fractionRing
    (f : s) [IsDomain (Localization.Away f.1)]
    [Algebra (Localization.Away f.1) (FractionRing R)]
    [IsScalarTower R (Localization.Away f.1) (FractionRing R)]
    [IsFractionRing (Localization.Away f.1) (FractionRing R)]
    [IsN1Ring (Localization.Away f.1)] :
    Module.Finite (Localization.Away f.1)
      (integralClosure (Localization.Away f.1) (FractionRing R)) := by
  -- First use `N-1` over the local fraction ring, then transport along the fraction-field
  -- equivalence to the common ambient fraction field of `R`.
  have hfinite_local :
      Module.Finite (Localization.Away f.1)
        (integralClosure (Localization.Away f.1) (FractionRing (Localization.Away f.1))) := by
    exact IsN1Ring.integralClosure_finite (R := Localization.Away f.1)
  exact Module.Finite.equiv
    (FractionRing.algEquiv (Localization.Away f.1) (FractionRing R)).mapIntegralClosure.toLinearEquiv

/-- Helper for Lemma 10.161.4: after transporting the finite extension structure across the local
fraction-field equivalence, the localized `N-2` hypothesis applies. -/
lemma localizationAway_integralClosure_finite_of_isN2Ring
    {L : Type u} [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] (f : s)
    [IsDomain (Localization.Away f.1)]
    [Algebra (Localization.Away f.1) L]
    [IsScalarTower R (Localization.Away f.1) L]
    [Algebra (FractionRing (Localization.Away f.1)) L]
    [IsScalarTower (Localization.Away f.1) (FractionRing (Localization.Away f.1)) L]
    [FiniteDimensional (FractionRing (Localization.Away f.1)) L]
    [IsN2Ring (Localization.Away f.1)] :
    Module.Finite (Localization.Away f.1)
      (integralClosure (Localization.Away f.1) L) := by
  -- Once `L` is viewed as a finite extension of the local fraction field, the `N-2` owner closes
  -- the local integral-closure finiteness goal immediately.
  exact IsN2Ring.integralClosure_finite_of_finiteDimensional
    (R := Localization.Away f.1) (L := L)

-- Proof sketch: use the local `N-1` assumptions together with `isN1Ring_of_isLocalization` to
-- place the canonical normalization owner on each principal localization, transport that
-- finiteness statement across `IsLocalization.integralClosure`, and descend finiteness of the
-- global normalization via `Module.Finite.of_localizationSpan_finite`.
/-- Lemma 10.161.4 (1): if the elements of `s` generate the unit ideal and each localization
`R_f` is `N-1`, then `R` is `N-1`. -/
theorem isN1Ring_of_isN1Ring_localizationAway
    (hs : Ideal.span (s : Set R) = ⊤)
    (hdom : ∀ f : s, IsDomain (Localization.Away f.1))
    (h : ∀ f : s, let _ : IsDomain (Localization.Away f.1) := hdom f
      IsN1Ring (Localization.Away f.1)) :
    IsN1Ring R := by
  -- Follow the source proof: descend finiteness of the global normalization from the principal
  -- open cover in the common fraction field.
  refine IsN1Ring.mk ?_
  letI : ∀ f : s, IsDomain (Localization.Away f.1) := hdom
  let hpow : ∀ f : s, Submonoid.powers f.1 ≤ nonZeroDivisors R := fun f ↦
    localizationAway_le_nonZeroDivisors (R := R) (s := s) f
  letI : ∀ f : s, Algebra (Localization.Away f.1) (FractionRing R) := fun f ↦
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.Away f.1) (FractionRing R) (Submonoid.powers f.1) (nonZeroDivisors R)
      (hpow f)
  letI : ∀ f : s, IsScalarTower R (Localization.Away f.1) (FractionRing R) := fun f ↦
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.Away f.1) (FractionRing R) (Submonoid.powers f.1) (nonZeroDivisors R)
      (hpow f)
  letI : ∀ f : s, IsFractionRing (Localization.Away f.1) (FractionRing R) := fun f ↦
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f.1)
      (Localization.Away f.1) (FractionRing R)
  letI : ∀ f : s, IsN1Ring (Localization.Away f.1) := fun f ↦ h f
  letI : ∀ f : s, IsLocalization.Away (algebraMap R (FractionRing R) f.1) (FractionRing R) :=
    fun f ↦
      IsLocalization.self <| by
        rintro x hx
        rcases (show ∃ n : ℕ, (algebraMap R (FractionRing R) f.1) ^ n = x by
          simpa [Submonoid.mem_powers_iff] using hx) with ⟨n, rfl⟩
        have hne : algebraMap R (FractionRing R) f.1 ≠ 0 := by
          intro hf0
          exact localizationAway_ne_zero (R := R) (s := s) f <|
            (IsFractionRing.injective R (FractionRing R)) <| by simpa using hf0
        exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hne)
  -- Each localized normalization is finite by the local `N-1` hypothesis transported to the
  -- common fraction field.
  exact integralClosure_finite_of_localizationAway_cover (R := R) (s := s) hs fun f ↦
    localizationAway_integralClosure_finite_fractionRing (R := R) (s := s) f

-- Proof sketch: for a finite extension `L / FractionRing R`, apply the localized owner theorem
-- `isN2Ring_of_isLocalization` to each principal localization, identify the localization of
-- `integralClosure R L` with the local integral closure via `IsLocalization.integralClosure`, and
-- descend finiteness back to `R` using `Module.Finite.of_localizationSpan_finite`.
/-- Lemma 10.161.4 (2): if the elements of `s` generate the unit ideal and each localization
`R_f` is `N-2`, then `R` is `N-2`. -/
theorem isN2Ring_of_isN2Ring_localizationAway
    (hs : Ideal.span (s : Set R) = ⊤)
    (hdom : ∀ f : s, IsDomain (Localization.Away f.1))
    (h : ∀ f : s, let _ : IsDomain (Localization.Away f.1) := hdom f
      IsN2Ring (Localization.Away f.1)) :
    IsN2Ring R := by
  -- Follow the source proof literally for an arbitrary finite extension of the fraction field.
  refine IsN2Ring.mk fun L => ?_
  intro _ _ _ _ _
  letI : ∀ f : s, IsDomain (Localization.Away f.1) := hdom
  let hpow : ∀ f : s, Submonoid.powers f.1 ≤ nonZeroDivisors R := fun f ↦
    localizationAway_le_nonZeroDivisors (R := R) (s := s) f
  letI : ∀ f : s, Algebra (Localization.Away f.1) (FractionRing R) := fun f ↦
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.Away f.1) (FractionRing R) (Submonoid.powers f.1) (nonZeroDivisors R)
      (hpow f)
  letI : ∀ f : s, IsScalarTower R (Localization.Away f.1) (FractionRing R) := fun f ↦
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.Away f.1) (FractionRing R) (Submonoid.powers f.1) (nonZeroDivisors R)
      (hpow f)
  letI : ∀ f : s, IsFractionRing (Localization.Away f.1) (FractionRing R) := fun f ↦
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f.1)
      (Localization.Away f.1) (FractionRing R)
  letI : ∀ f : s, Algebra (Localization.Away f.1) L := fun f ↦
    (RingHom.comp (algebraMap (FractionRing R) L)
      (algebraMap (Localization.Away f.1) (FractionRing R))).toAlgebra
  letI : ∀ f : s, IsScalarTower (Localization.Away f.1) (FractionRing R) L := fun f ↦ by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    rfl
  letI : ∀ f : s, IsScalarTower R (Localization.Away f.1) L := fun f ↦ by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    change (algebraMap R L) x =
      (algebraMap (FractionRing R) L)
        ((algebraMap (Localization.Away f.1) (FractionRing R)) ((algebraMap R (Localization.Away f.1)) x))
    rw [← IsScalarTower.algebraMap_apply R (Localization.Away f.1) (FractionRing R) x]
    exact IsScalarTower.algebraMap_apply R (FractionRing R) L x
  letI : ∀ f : s, IsN2Ring (Localization.Away f.1) := fun f ↦ h f
  let e : ∀ f : s, FractionRing (Localization.Away f.1) ≃ₐ[Localization.Away f.1] FractionRing R :=
    fun f ↦ FractionRing.algEquiv (Localization.Away f.1) (FractionRing R)
  let fL : ∀ f : s, FractionRing (Localization.Away f.1) →ₐ[Localization.Away f.1] L := fun f ↦
    (IsScalarTower.toAlgHom (Localization.Away f.1) (FractionRing R) L).comp (e f)
  letI : ∀ f : s, Algebra (FractionRing (Localization.Away f.1)) L := fun f ↦
    (fL f).toRingHom.toAlgebra
  letI : ∀ f : s, IsScalarTower (Localization.Away f.1)
      (FractionRing (Localization.Away f.1)) L := fun f ↦ by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    calc
      algebraMap (Localization.Away f.1) L x =
          algebraMap (FractionRing R) L
            (algebraMap (Localization.Away f.1) (FractionRing R) x) := by
        exact IsScalarTower.algebraMap_apply (Localization.Away f.1) (FractionRing R) L x
      _ =
          algebraMap (FractionRing (Localization.Away f.1)) L
            (algebraMap (Localization.Away f.1) (FractionRing (Localization.Away f.1)) x) := by
        simpa using
          (IsFractionRing.algEquiv_commutes (e f)
            (show L ≃ₐ[FractionRing (Localization.Away f.1)] L from AlgEquiv.refl)
            (algebraMap (Localization.Away f.1) (FractionRing (Localization.Away f.1)) x))
  letI : ∀ f : s, Module.Finite (FractionRing (Localization.Away f.1)) L := fun f ↦ by
    letI : Module.Finite (FractionRing R) L := inferInstance
    have hcompat :
        RingHom.comp (algebraMap (FractionRing (Localization.Away f.1)) L)
            ↑((e f).symm.toRingEquiv) =
          RingHom.comp (RingEquiv.refl L) (algebraMap (FractionRing R) L) := by
      ext x
      simpa using
        (IsFractionRing.algEquiv_commutes (e f).symm
          (show L ≃ₐ[FractionRing (Localization.Away f.1)] L from AlgEquiv.refl) x)
    exact Module.Finite.of_equiv_equiv ((e f).symm.toRingEquiv) (RingEquiv.refl L) hcompat
  letI : ∀ f : s, FiniteDimensional (FractionRing (Localization.Away f.1)) L := fun f ↦ by
    infer_instance
  letI : ∀ f : s, IsLocalization.Away (algebraMap R L f.1) L := fun f ↦
    IsLocalization.self <| by
      rintro x hx
      rcases (show ∃ n : ℕ, (algebraMap R L f.1) ^ n = x by
        simpa [Submonoid.mem_powers_iff] using hx) with ⟨n, rfl⟩
      have hne : algebraMap R L f.1 ≠ 0 := by
        intro hf0
        exact localizationAway_ne_zero (R := R) (s := s) f <|
          (algebraMap_injective_of_field_isFractionRing R L (FractionRing R) L) <| by
            simpa using hf0
      exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hne)
  -- The localized integral closures are finite over each principal open by the local `N-2`
  -- hypotheses, and then finiteness descends along the cover.
  exact integralClosure_finite_of_localizationAway_cover (R := R) (s := s) hs fun f ↦
    localizationAway_integralClosure_finite_of_isN2Ring (R := R) (s := s) (L := L) f

end

/-! ### Lemma_10_161_5 (from Chap10) -/
universe u v

/-
Domain-style sampling:
* primary domain: quasi-finite finite-type extensions of Noetherian domains and permanence of the
  chapter owner `IsN2Ring`;
* sampled owner/bridge declarations:
  - `Algebra.FiniteType.QuasiFinite`, the chapter source-facing owner for a quasi-finite finite
    type extension from `Definition_10_122_3`;
  - `exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties`, the Zariski-main
    bridge from `Lemma_10_123_14`;
  - `isN2Ring_of_isLocalization`, the localization-stability bridge from `Lemma_10_161_3`;
  - `isN2Ring_of_finite_extension`, the finite-extension bridge from `Lemma_10_161_7`.
* best owner abstraction: the source-facing extension hypothesis is
  `Algebra.FiniteType.QuasiFinite R S`; the public conclusion is the owner `IsN2Ring S`.
* primitive data: the quasi-finite extension owner `hRSqf`, the injectivity hypothesis on
  `algebraMap R S`, and the ambient Noetherian/domain data.
* derived API: the separate finite-type and quasi-finite components, the finite intermediate
  subalgebra from Zariski's Main Theorem, and localization/finite-extension permanence of
  `IsN2Ring`.

Source/core/bridge triage:
* `source-facing`: the permanence theorem for a quasi-finite extension of domains;
* `core/canonical`: `IsN2Ring`;
* `bridge/view`: the Zariski-main finite subalgebra and the localization/finite-extension
  permanence theorems above.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [CommRing S] [IsDomain S] [Algebra R S]

-- Proof sketch: let `K = FractionRing R` and `L = FractionRing S`. Quasi-finiteness and
-- injectivity of `R → S` imply that `L / K` is finite. Applying the `N-2` hypothesis to `R`
-- shows that the integral closure of `R` in `L` is finite over `R`, hence so is the integral
-- closure of `R` in `S`. Zariski's Main Theorem gives a principal-open cover on which `S` agrees
-- with that finite integral closure, reducing to the finite-extension case; then one applies the
-- finite stability of `N-2` together with localization and transitivity of integral closure.
/-- Lemma 10.161.5: if `R` is a Noetherian `N-2` domain and `R ⊂ S` is a quasi-finite extension
of domains, then `S` is `N-2`. -/
theorem isN2Ring_of_quasiFinite_extension
    (hRSqf : Algebra.FiniteType.QuasiFinite R S)
    (hRS : Function.Injective (algebraMap R S)) [IsN2Ring R] :
    IsN2Ring S := sorry

end

/-! ### Lemma_10_161_6 (from Chap10) -/
open scoped LaurentPolynomial

universe u

/-
Domain triage:
- primary domain: `N-1` rings under Laurent-polynomial extension;
- layer: `source-facing`;
- core/canonical owner: `IsN1Ring`;
- sampled bridge/view declarations:
  `R[T;T⁻¹]`, `IsLocalization.Away (X : R[X]) R[T;T⁻¹]`, and `Polynomial.toLaurentAlg`;
- primitive data: the base ring `R` and the canonical Laurent-polynomial ring `R[T;T⁻¹]`;
- derived API: `IsN1Ring.integralClosure_finite`.

The public surface should therefore speak directly about `IsN1Ring R[T;T⁻¹]`, while leaving the
localization presentation as an internal bridge rather than a second owner-level wrapper.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Helper for Lemma 10.161.6: the constant-term inclusion `R → R[T;T⁻¹]` is injective. -/
lemma laurentPolynomial_constant_injective :
    Function.Injective (algebraMap R R[T;T⁻¹]) := by
  intro x y hxy
  -- Compare the coefficients at exponent `0` to recover the original constant.
  have hcoeff : (algebraMap R R[T;T⁻¹] x) 0 = (algebraMap R R[T;T⁻¹] y) 0 :=
    congrArg (fun p : R[T;T⁻¹] => p 0) hxy
  simpa [LaurentPolynomial.C_apply] using hcoeff

/-- Helper for Lemma 10.161.6: the coefficientwise map to Laurent polynomials over the fraction
field is injective. -/
lemma laurentPolynomial_fractionCoeffMap_injective :
    Function.Injective
      (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) :
        R[T;T⁻¹] →ₐ[R] (FractionRing R)[T;T⁻¹]) := by
  intro p q hpq
  -- Equality of Laurent polynomials is coefficientwise equality, and coefficients embed
  -- injectively into the fraction field.
  ext n
  have hcoeff :
      (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) p) n =
        (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) q) n :=
    congrArg (fun f : (FractionRing R)[T;T⁻¹] => f n) hpq
  exact FaithfulSMul.algebraMap_injective R (FractionRing R) <| by
    simpa [AddMonoidAlgebra.mapAlgHom_apply] using hcoeff

/-- Helper for Lemma 10.161.6: Laurent polynomials over the fraction field of `R` are
integrally closed. -/
lemma fractionRing_laurentPolynomial_isIntegrallyClosed :
    IsIntegrallyClosed ((FractionRing R)[T;T⁻¹]) := by
  let K := FractionRing R
  let hX : (Polynomial.X : Polynomial K) ≠ 0 := Polynomial.X_ne_zero
  let hM : Submonoid.powers (Polynomial.X : Polynomial K) ≤ nonZeroDivisors (Polynomial K) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hX
  letI : IsLocalization.Away (Polynomial.X : Polynomial K) K[T;T⁻¹] :=
    LaurentPolynomial.isLocalization
  -- Laurent polynomials are the localization of `K[X]` away from `X`, so we localize the
  -- integrally closed polynomial ring.
  exact isIntegrallyClosed_of_isLocalization
    (S := K[T;T⁻¹]) (R := Polynomial K) (M := Submonoid.powers (Polynomial.X : Polynomial K)) hM

/-- Helper for Lemma 10.161.6: the constant map from `R` into the Laurent fraction field is
injective. -/
lemma laurentFraction_constant_injective :
    Function.Injective (algebraMap R (FractionRing R[T;T⁻¹])) := by
  -- Factor the constant map through the Laurent polynomial ring and use injectivity at each
  -- stage.
  exact (IsFractionRing.injective R[T;T⁻¹] (FractionRing R[T;T⁻¹])).comp
    laurentPolynomial_constant_injective

/-- Helper for Lemma 10.161.6: the fraction field of `R` maps to the Laurent fraction field by
viewing elements as constant Laurent rational functions. -/
noncomputable def fractionRingToLaurentFraction :
    FractionRing R →ₐ[R] FractionRing R[T;T⁻¹] :=
  IsFractionRing.liftAlgHom
    (g := Algebra.ofId R (FractionRing R[T;T⁻¹]))
    laurentFraction_constant_injective

/-- Helper for Lemma 10.161.6: an element integral over `R` stays integral after the constant map
to the Laurent fraction field. -/
lemma isIntegral_fractionRingToLaurentFraction {x : FractionRing R} (hx : IsIntegral R x) :
    IsIntegral R[T;T⁻¹] (fractionRingToLaurentFraction (R := R) x) := by
  -- Keep the same monic relation over `R`, then enlarge scalars to the Laurent polynomial ring.
  have hxR :
      IsIntegral R (fractionRingToLaurentFraction (R := R) x) :=
    hx.map (fractionRingToLaurentFraction (R := R))
  exact IsIntegral.tower_top (A := R[T;T⁻¹]) hxR

/-- Helper for Lemma 10.161.6: the normalization of `R` maps into the normalization of the
Laurent polynomial ring by viewing elements as constant Laurent rational functions. -/
noncomputable def integralClosure_constants_map_to_laurent_normalization
    (x : integralClosure R (FractionRing R)) :
    integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹]) :=
  ⟨fractionRingToLaurentFraction (R := R) (x : FractionRing R),
    isIntegral_fractionRingToLaurentFraction (R := R) x.2⟩

/-- Helper for Lemma 10.161.6: the `R`-span of finitely many fraction-field coefficients is a
finite `R`-module. -/
lemma coeff_span_finite {s : Set (FractionRing R)} (hs : s.Finite) :
    Module.Finite R (Submodule.span R s) := by
  -- The ambient ring is Noetherian, so a span on a finite set is finitely generated.
  exact Module.Finite.span_of_finite R hs

/-- Helper for Lemma 10.161.6: coefficientwise Laurent extension into the common ambient fraction
field. -/
noncomputable def laurent_fraction_base_map :
    R[T;T⁻¹] →+* FractionRing ((FractionRing R)[T;T⁻¹]) :=
  (algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))).comp
    (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R))).toRingHom

/-- Helper for Lemma 10.161.6: the Laurent fraction field over `R` maps into the fraction field of
Laurent polynomials over `FractionRing R`. -/
noncomputable def laurent_fraction_comparison :
    FractionRing R[T;T⁻¹] →+* FractionRing ((FractionRing R)[T;T⁻¹]) :=
  -- Route correction: package the comparison as a plain fraction-field lift so evaluation on
  -- numerators is definitionally `IsFractionRing.lift_algebraMap`.
  IsFractionRing.lift
    (A := R[T;T⁻¹]) (K := FractionRing R[T;T⁻¹])
    (L := FractionRing ((FractionRing R)[T;T⁻¹]))
    (g := laurent_fraction_base_map (R := R))
    ((IsFractionRing.injective ((FractionRing R)[T;T⁻¹])
      (FractionRing ((FractionRing R)[T;T⁻¹]))).comp
      (laurentPolynomial_fractionCoeffMap_injective (R := R))
    )

/-- Helper for Lemma 10.161.6: the comparison map agrees with the coefficientwise Laurent map on
honest Laurent polynomials. -/
lemma laurent_fraction_comparison_algebraMap (p : R[T;T⁻¹]) :
    laurent_fraction_comparison (R := R) (algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) p) =
      algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
        ((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R))) p) := by
  -- Evaluate the fraction-field lift on a numerator before introducing any transport.
  rw [laurent_fraction_comparison]
  rw [IsFractionRing.lift_algebraMap]
  rfl

/-- Helper for Lemma 10.161.6: on base elements of `R`, the two constant routes into the common
Laurent fraction field agree. -/
lemma fractionRingToLaurentFraction_algebraMap_C (r : R) :
    laurent_fraction_comparison (R := R)
      (fractionRingToLaurentFraction (R := R) (algebraMap R (FractionRing R) r)) =
      algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
        (LaurentPolynomial.C (algebraMap R (FractionRing R) r)) := by
  -- Evaluate the first fraction-field lift on a base scalar and rewrite it as the Laurent
  -- numerator `C r`.
  have hconst :
      fractionRingToLaurentFraction (R := R) (algebraMap R (FractionRing R) r) =
        algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (LaurentPolynomial.C r) := by
    rw [fractionRingToLaurentFraction, IsFractionRing.liftAlgHom_apply]
    rw [IsFractionRing.lift_algebraMap]
    -- Rewrite the constant Laurent polynomial through the scalar tower
    -- `R → R[T;T⁻¹] → FractionRing R[T;T⁻¹]`.
    calc
      algebraMap R (FractionRing R[T;T⁻¹]) r =
          algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (algebraMap R R[T;T⁻¹] r) := by
            simpa using
              congrArg (fun f : R →+* FractionRing R[T;T⁻¹] => f r)
                (IsScalarTower.algebraMap_eq R R[T;T⁻¹] (FractionRing R[T;T⁻¹]))
      _ =
          algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (LaurentPolynomial.C r) := by
            rw [LaurentPolynomial.C_eq_algebraMap]
  rw [hconst, laurent_fraction_comparison_algebraMap]
  -- Compare coefficients after the coefficientwise Laurent extension over `FractionRing R`.
  have hmap :
      (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)))
          (LaurentPolynomial.C r) =
        LaurentPolynomial.C (algebraMap R (FractionRing R) r) := by
    ext n
    by_cases h : n = 0
    · simp [AddMonoidAlgebra.mapAlgHom_apply, LaurentPolynomial.C_apply, h]
    · simp [AddMonoidAlgebra.mapAlgHom_apply, LaurentPolynomial.C_apply, h]
  exact congrArg
    (algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))) hmap

/-- Helper for Lemma 10.161.6: the comparison map sends Laurent-normalization elements to
elements integral over `K[T;T⁻¹]`, where `K = FractionRing R`. -/
lemma laurent_fraction_comparison_isIntegral_over_fractionLaurent
    (y : integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])) :
    IsIntegral ((FractionRing R)[T;T⁻¹])
      (laurent_fraction_comparison (R := R) (y : FractionRing R[T;T⁻¹])) := by
  have hcomp :
      (algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))).comp
          ((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R))).toRingHom) =
        (laurent_fraction_comparison (R := R)).comp
          (algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹])) := by
    apply RingHom.ext
    intro p
    exact (laurent_fraction_comparison_algebraMap (R := R) p).symm
  -- Transport the monic relation defining integrality across the comparison of fraction fields.
  exact IsIntegral.map_of_comp_eq
    (((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R))).toRingHom))
    (laurent_fraction_comparison (R := R)) hcomp y.2

/-- Helper for Lemma 10.161.6: every Laurent-normalization generator becomes an honest Laurent
polynomial over `FractionRing R` inside the common ambient fraction field. -/
lemma laurent_normalization_generator_lift
    (y : integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])) :
    ∃ g : (FractionRing R)[T;T⁻¹],
      algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹])) g =
        laurent_fraction_comparison (R := R) (y : FractionRing R[T;T⁻¹]) := by
  letI : IsIntegrallyClosed ((FractionRing R)[T;T⁻¹]) :=
    fractionRing_laurentPolynomial_isIntegrallyClosed (R := R)
  -- The transported normalization element lies in the integrally closed Laurent ring over `K`.
  exact IsIntegrallyClosed.algebraMap_eq_of_integral
    (laurent_fraction_comparison_isIntegral_over_fractionLaurent (R := R) y)

/-- Helper for Lemma 10.161.6: after passing to the common ambient fraction field, a constant
element of `FractionRing R` becomes the constant Laurent polynomial with that coefficient. -/
lemma laurent_fraction_comparison_constant (x : FractionRing R) :
    laurent_fraction_comparison (R := R) (fractionRingToLaurentFraction (R := R) x) =
      algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
        (LaurentPolynomial.C x) := by
  let f₁ : FractionRing R →+* FractionRing ((FractionRing R)[T;T⁻¹]) :=
    (laurent_fraction_comparison (R := R)).comp
      (fractionRingToLaurentFraction (R := R)).toRingHom
  let f₂ : FractionRing R →+* FractionRing ((FractionRing R)[T;T⁻¹]) :=
    (algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))).comp
      (LaurentPolynomial.C : FractionRing R →+* (FractionRing R)[T;T⁻¹])
  have hmaps : f₁ = f₂ := by
    -- Both maps out of the fraction field are determined by their values on the base ring `R`.
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    -- The base case is the direct constant computation proved above.
    simpa [f₁, f₂] using fractionRingToLaurentFraction_algebraMap_C (R := R) r
  -- Evaluate the identified ring-hom equality at the chosen fraction-field element.
  simpa [f₁, f₂] using congrArg
    (fun f : FractionRing R →+* FractionRing ((FractionRing R)[T;T⁻¹]) => f x) hmaps

/-- Helper for Lemma 10.161.6: the normalization embeds linearly into any submodule containing
all of its elements. -/
noncomputable def integralClosure_to_submodule
    (P : Submodule R (FractionRing R))
    (hP : ∀ x : integralClosure R (FractionRing R), (x : FractionRing R) ∈ P) :
    integralClosure R (FractionRing R) →ₗ[R] P where
  toFun x := ⟨x, hP x⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Helper for Lemma 10.161.6: the linear map into a containing submodule is injective because
the normalization is a subtype of the fraction field. -/
lemma integralClosure_to_submodule_injective
    (P : Submodule R (FractionRing R))
    (hP : ∀ x : integralClosure R (FractionRing R), (x : FractionRing R) ∈ P) :
    Function.Injective (integralClosure_to_submodule (R := R) P hP) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : P => (z : FractionRing R)) hxy

/-- Helper for Lemma 10.161.6: left multiplication by a single Laurent monomial shifts
coefficients by the monomial exponent. -/
lemma laurent_single_mul_apply
    (a : FractionRing R) (m k : ℤ) (g : (FractionRing R)[T;T⁻¹]) :
    ((AddMonoidAlgebra.single m a : (FractionRing R)[T;T⁻¹]) * g) k = a * g (k - m) := by
  -- Use the additive-group monoid-algebra coefficient formula and normalize the index.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (AddMonoidAlgebra.single_mul_apply (x := g) (r := a) (g := m) (h := k))

/-- Helper for Lemma 10.161.6: if every coefficient of `g` lies in an `R`-submodule `P`, then
multiplying `g` by a Laurent monomial with coefficient in `R` keeps every coefficient in `P`. -/
lemma coeff_C_mul_T_mul_mem_submodule
    {P : Submodule R (FractionRing R)} {g : (FractionRing R)[T;T⁻¹]}
    (hg : ∀ m : ℤ, g m ∈ P) (r : R) (m k : ℤ) :
    ((((LaurentPolynomial.C (algebraMap R (FractionRing R) r)) * LaurentPolynomial.T m) * g :
      (FractionRing R)[T;T⁻¹]) k) ∈ P := by
  -- Rewrite the Laurent monomial as a single-support term, then use `R`-submodule closure.
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  rw [laurent_single_mul_apply]
  simpa [Algebra.smul_def] using P.smul_mem r (hg (k - m))

/-- Helper for Lemma 10.161.6: the coefficientwise Laurent extension is the canonical finite sum
of mapped Laurent monomials. -/
lemma mapAlgHom_laurent_eq_sum_single (p : R[T;T⁻¹]) :
    AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) p =
      p.sum (fun m r ↦ AddMonoidAlgebra.single m (algebraMap R (FractionRing R) r)) := by
  classical
  ext k
  rw [Finsupp.sum]
  let ev : (FractionRing R)[T;T⁻¹] →+ FractionRing R :=
    { toFun := fun f ↦ f k
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hsum_apply :
      (∑ a ∈ p.support, AddMonoidAlgebra.single a (algebraMap R (FractionRing R) (p a))) k =
        ∑ a ∈ p.support,
          (AddMonoidAlgebra.single a (algebraMap R (FractionRing R) (p a)) :
            (FractionRing R)[T;T⁻¹]) k := by
    change
      ev (∑ a ∈ p.support,
        (AddMonoidAlgebra.single a (algebraMap R (FractionRing R) (p a)) :
          (FractionRing R)[T;T⁻¹])) =
        ∑ a ∈ p.support,
          ev (AddMonoidAlgebra.single a (algebraMap R (FractionRing R) (p a)) :
            (FractionRing R)[T;T⁻¹])
    exact map_sum ev
      (fun x ↦
        (AddMonoidAlgebra.single x (algebraMap R (FractionRing R) (p x)) :
          (FractionRing R)[T;T⁻¹]))
      p.support
  rw [hsum_apply]
  by_cases hk : k ∈ p.support
  · have hsum :
        ∑ x ∈ p.support,
            (AddMonoidAlgebra.single x (algebraMap R (FractionRing R) (p x)) :
              (FractionRing R)[T;T⁻¹]) k =
            (AddMonoidAlgebra.single k (algebraMap R (FractionRing R) (p k)) :
              (FractionRing R)[T;T⁻¹]) k := by
      refine Finset.sum_eq_single k ?_ ?_
      · intro x hx hxk
        simpa only [Finsupp.single_apply, hxk, if_false]
      · intro hk'
        exact (hk' hk).elim
    have hsingle :
        (AddMonoidAlgebra.single k (algebraMap R (FractionRing R) (p k)) :
          (FractionRing R)[T;T⁻¹]) k =
          algebraMap R (FractionRing R) (p k) := by
      simpa only [Finsupp.single_apply, if_true]
    calc
      (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) p) k =
          algebraMap R (FractionRing R) (p k) := by
            simp [AddMonoidAlgebra.mapAlgHom_apply]
      _ =
          (AddMonoidAlgebra.single k (algebraMap R (FractionRing R) (p k)) :
            (FractionRing R)[T;T⁻¹]) k := by
            exact hsingle.symm
      _ =
          ∑ x ∈ p.support,
            (AddMonoidAlgebra.single x (algebraMap R (FractionRing R) (p x)) :
              (FractionRing R)[T;T⁻¹]) k := by
            exact hsum.symm
  · have hsum :
        ∑ x ∈ p.support,
            (AddMonoidAlgebra.single x (algebraMap R (FractionRing R) (p x)) :
              (FractionRing R)[T;T⁻¹]) k = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxk : x ≠ k := by
        intro h
        apply hk
        simpa [h] using hx
      simpa only [Finsupp.single_apply, hxk, if_false]
    calc
      (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) p) k = 0 := by
        simp [AddMonoidAlgebra.mapAlgHom_apply, Finsupp.notMem_support_iff.mp hk]
      _ =
          ∑ x ∈ p.support,
            (AddMonoidAlgebra.single x (algebraMap R (FractionRing R) (p x)) :
              (FractionRing R)[T;T⁻¹]) k := by
            simpa using hsum.symm

/-- Helper for Lemma 10.161.6: if every coefficient of `g` lies in an `R`-submodule `P`, then
the same holds after left multiplication by any Laurent polynomial coming from `R[T;T⁻¹]`. -/
lemma coeff_mem_submodule_of_laurent_mul
    {P : Submodule R (FractionRing R)} {g : (FractionRing R)[T;T⁻¹]}
    (hg : ∀ m : ℤ, g m ∈ P) (p : R[T;T⁻¹]) (k : ℤ) :
    (((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) p) * g) k) ∈ P := by
  -- Decompose the Laurent multiplier into finitely many mapped monomials.
  rw [mapAlgHom_laurent_eq_sum_single]
  rw [Finsupp.sum, Finset.sum_mul]
  let ev : (FractionRing R)[T;T⁻¹] →+ FractionRing R :=
    { toFun := fun f ↦ f k
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hsum_apply :
      (∑ i ∈ p.support, AddMonoidAlgebra.single i (algebraMap R (FractionRing R) (p i)) * g) k =
        ∑ i ∈ p.support,
          ((AddMonoidAlgebra.single i (algebraMap R (FractionRing R) (p i)) * g :
            (FractionRing R)[T;T⁻¹]) k) := by
    change
      ev (∑ i ∈ p.support,
        (AddMonoidAlgebra.single i (algebraMap R (FractionRing R) (p i)) * g :
          (FractionRing R)[T;T⁻¹])) =
        ∑ i ∈ p.support,
          ev (AddMonoidAlgebra.single i (algebraMap R (FractionRing R) (p i)) * g :
            (FractionRing R)[T;T⁻¹])
    exact map_sum ev
      (fun x ↦
        (AddMonoidAlgebra.single x (algebraMap R (FractionRing R) (p x)) * g :
          (FractionRing R)[T;T⁻¹]))
      p.support
  rw [hsum_apply]
  -- Each monomial summand preserves coefficient membership by the previous lemma.
  exact Submodule.sum_mem P fun m hm ↦ by
    simpa [← LaurentPolynomial.single_eq_C_mul_T] using
      (coeff_C_mul_T_mul_mem_submodule (R := R) (P := P) (g := g) hg (p m) m k)

/-- Helper for Lemma 10.161.6: every coefficient of the chosen Laurent lifts lies in the span of
the finite coefficient set obtained by collecting the support coefficients of all lifts. -/
lemma coeff_mem_span_of_generator_coeffs
    {n : ℕ} (g : Fin n → (FractionRing R)[T;T⁻¹]) (i : Fin n) (m : ℤ) :
    g i m ∈
      Submodule.span R
        {a : FractionRing R | ∃ j : Fin n, ∃ k ∈ (g j).support, g j k = a} := by
  by_cases hm : m ∈ (g i).support
  · -- A supported coefficient appears explicitly in the finite union of coefficient images.
    exact Submodule.subset_span ⟨i, m, hm, rfl⟩
  · -- Outside the support the coefficient vanishes, so it lies in the span automatically.
    have hzero : g i m = 0 := Finsupp.notMem_support_iff.mp hm
    simpa [hzero] using
      (Submodule.zero_mem
        (Submodule.span R
          {a : FractionRing R | ∃ j : Fin n, ∃ k ∈ (g j).support, g j k = a}))

/-- Helper for Lemma 10.161.6: coefficients of Laurent combinations of chosen generators stay in
the `R`-submodule already spanned by the generator coefficients. -/
lemma coeff_mem_span_of_laurent_linear_combination
    {n : ℕ} (g : Fin n → (FractionRing R)[T;T⁻¹]) (coeffs : Finset (FractionRing R))
    (hg : ∀ i : Fin n, ∀ m : ℤ, g i m ∈ Submodule.span R (↑coeffs : Set (FractionRing R)))
    (c : Fin n → R[T;T⁻¹]) (k : ℤ) :
    ((∑ i, (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i) k) ∈
      Submodule.span R (↑coeffs : Set (FractionRing R)) := by
  let P : Submodule R (FractionRing R) := Submodule.span R (↑coeffs : Set (FractionRing R))
  have hsummand :
      ∀ i : Fin n, (((AddMonoidAlgebra.mapAlgHom (M := ℤ)
        (Algebra.ofId R (FractionRing R)) (c i)) * g i) k) ∈ P := by
    intro i
    -- Apply the one-generator coefficient-closure lemma to the `i`-th summand.
    exact coeff_mem_submodule_of_laurent_mul (R := R) (P := P) (g := g i) (hg i) (c i) k
  let ev : (FractionRing R)[T;T⁻¹] →+ FractionRing R :=
    { toFun := fun f ↦ f k
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hsum_apply :
      (∑ i, (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i) k =
        ∑ i,
          (((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i) k) := by
    change
      ev (∑ i,
        ((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i :
          (FractionRing R)[T;T⁻¹])) =
        ∑ i,
          ev ((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i :
            (FractionRing R)[T;T⁻¹])
    exact map_sum ev
      (fun i : Fin n ↦
        ((AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i :
          (FractionRing R)[T;T⁻¹]))
      Finset.univ
  rw [hsum_apply]
  exact Submodule.sum_mem P (fun i _ ↦ hsummand i)

/-- Helper for Lemma 10.161.6: reading off coefficient `0` from a Laurent identity shows that the
constant term belongs to the coefficient span. -/
lemma coeff_zero_mem_span_after_transport
    {n : ℕ} (g : Fin n → (FractionRing R)[T;T⁻¹]) (coeffs : Finset (FractionRing R))
    (hg : ∀ i : Fin n, ∀ m : ℤ, g i m ∈ Submodule.span R (↑coeffs : Set (FractionRing R)))
    {x : FractionRing R} {c : Fin n → R[T;T⁻¹]}
    (hEq : LaurentPolynomial.C x =
      ∑ i, (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * g i) :
    x ∈ Submodule.span R (↑coeffs : Set (FractionRing R)) := by
  let P : Submodule R (FractionRing R) := Submodule.span R (↑coeffs : Set (FractionRing R))
  have hcoeff :
      x = ((∑ i, (AddMonoidAlgebra.mapAlgHom (M := ℤ)
        (Algebra.ofId R (FractionRing R)) (c i)) * g i) 0) := by
    -- Coefficient `0` of a constant Laurent polynomial is the constant itself.
    simpa [LaurentPolynomial.C_apply] using congrArg
      (fun p : (FractionRing R)[T;T⁻¹] => p 0) hEq
  have hspan :
      ((∑ i, (AddMonoidAlgebra.mapAlgHom (M := ℤ)
        (Algebra.ofId R (FractionRing R)) (c i)) * g i) 0) ∈ P :=
    coeff_mem_span_of_laurent_linear_combination (R := R) g coeffs hg c 0
  exact hcoeff.symm ▸ hspan

/-- Helper for Lemma 10.161.6: the Laurent combination obtained by applying the coefficientwise
map to the chosen coefficients and multiplying by the lifted generators. -/
noncomputable def lifted_generator_combination {n : ℕ}
    (lifted : Fin n → (FractionRing R)[T;T⁻¹]) (c : Fin n → R[T;T⁻¹]) :
    (FractionRing R)[T;T⁻¹] :=
  ∑ i, (AddMonoidAlgebra.mapAlgHom (M := ℤ) (Algebra.ofId R (FractionRing R)) (c i)) * lifted i

-- Proof sketch: let `R'` be the integral closure of `R` in `FractionRing R`, and let `S'` be the
-- integral closure of `R[T;T⁻¹]` in its fraction field. The `N-1` hypothesis makes `S'` finite
-- over the Laurent polynomial ring. Expanding finitely many generators as finite Laurent sums
-- shows every element of `R'` lies in a finite `R`-submodule of `FractionRing R`; since `R` is
-- Noetherian, `R'` is finite over `R`.
set_option maxHeartbeats 1000000 in
/-- Lemma 10.161.6: if `R` is a Noetherian domain and the Laurent polynomial ring
`R[z, z^{-1}]`, formalized by the canonical owner `R[T;T⁻¹]`, is `N-1`, then `R` is `N-1`. -/
theorem isN1Ring_of_isN1Ring_laurentPolynomial
    (hLaurent : IsN1Ring R[T;T⁻¹]) :
    IsN1Ring R := by
  classical
  letI : IsN1Ring R[T;T⁻¹] := hLaurent
  let K := FractionRing R
  let S := integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])
  refine ⟨?_⟩
  -- Use the Laurent `N-1` hypothesis to choose finitely many generators of the Laurent
  -- normalization.
  have hfiniteS : Module.Finite R[T;T⁻¹] S := by
    change Module.Finite R[T;T⁻¹]
      (integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹]))
    infer_instance
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R[T;T⁻¹] S
  let generators : Fin n → S := fun i => f (Pi.single i 1)
  have hconst :
      ∀ x : integralClosure R K,
        ∃ c : Fin n → R[T;T⁻¹],
          f c = integralClosure_constants_map_to_laurent_normalization (R := R) x := by
    intro x
    exact hf _
  choose lifted hlifted using fun i : Fin n ↦
    laurent_normalization_generator_lift (R := R) (generators i)
  let coeffs : Finset (FractionRing R) :=
    Finset.univ.biUnion fun i ↦ (lifted i).support.image fun m ↦ lifted i m
  let P : Submodule R K := Submodule.span R (↑coeffs : Set K)
  have hcoeffs :
      ∀ i : Fin n, ∀ m : ℤ, lifted i m ∈ P := by
    intro i m
    by_cases hm : m ∈ (lifted i).support
    · -- Supported coefficients are explicit members of the finite coefficient set.
      exact Submodule.subset_span <| by
        change lifted i m ∈ (↑coeffs : Set K)
        refine Finset.mem_biUnion.mpr ?_
        exact ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
    · -- Off-support coefficients vanish, so they lie in the span automatically.
      have hzero : lifted i m = 0 := Finsupp.notMem_support_iff.mp hm
      simpa [P, hzero] using (Submodule.zero_mem P)
  have hcontain :
      ∀ x : integralClosure R K, (x : K) ∈ P := by
    intro x
    obtain ⟨c, hc⟩ := hconst x
    have hPi :
        c = ∑ i, Pi.single i (c i) := by
      simpa using
        (LinearMap.sum_single_apply (φ := fun _ : Fin n ↦ R[T;T⁻¹]) (v := c)).symm
    have hsum :
        f c = ∑ i, c i • generators i := by
      calc
        f c = f (∑ i, Pi.single i (c i)) := by
          exact congrArg f hPi
        _ = ∑ i, f (Pi.single i (c i)) := by
          simpa using (map_sum f (fun i : Fin n ↦ Pi.single i (c i)) Finset.univ)
        _ = ∑ i, c i • generators i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hsingle :
              Pi.single i (c i) =
                c i • (Pi.single i (1 : R[T;T⁻¹]) : Fin n → R[T;T⁻¹]) := by
            ext j
            by_cases hji : j = i
            · subst hji
              simp
            · simp [Pi.single, hji]
          -- Rewrite each basis-vector image as the chosen generator.
          rw [hsingle, LinearMap.map_smul]
    have hdecomp :
        integralClosure_constants_map_to_laurent_normalization (R := R) x =
          ∑ i, c i • generators i := by
      exact hc.symm.trans hsum
    have htransport :
        LaurentPolynomial.C (x : K) =
          lifted_generator_combination (R := R) lifted c := by
      let rhs : (FractionRing R)[T;T⁻¹] := lifted_generator_combination (R := R) lifted c
      have hambient :
          algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
              (LaurentPolynomial.C (x : FractionRing R)) =
            algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹])) rhs := by
        let transport :
            integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹]) →
              FractionRing ((FractionRing R)[T;T⁻¹]) :=
          fun s ↦ laurent_fraction_comparison (R := R) (s : FractionRing R[T;T⁻¹])
        have htransport :
            laurent_fraction_comparison (R := R)
                ((∑ i, c i • generators i :
                  integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])) :
                  FractionRing R[T;T⁻¹]) =
              algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹])) rhs := by
          have hcoe :
              ((∑ i, c i • generators i :
                integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])) :
                FractionRing R[T;T⁻¹]) =
                ∑ i, algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (c i) *
                  (generators i : FractionRing R[T;T⁻¹]) := by
            simpa [Algebra.smul_def]
          calc
            laurent_fraction_comparison (R := R)
                ((∑ i, c i • generators i :
                  integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])) :
                  FractionRing R[T;T⁻¹]) =
                laurent_fraction_comparison (R := R)
                  (∑ i, algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (c i) *
                    (generators i : FractionRing R[T;T⁻¹])) := by
                      rw [hcoe]
            _ = ∑ i, laurent_fraction_comparison (R := R)
                  (algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (c i) *
                    (generators i : FractionRing R[T;T⁻¹])) := by
                  exact map_sum (laurent_fraction_comparison (R := R)).toAddMonoidHom
                    (fun i : Fin n ↦
                      (algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (c i) *
                        (generators i : FractionRing R[T;T⁻¹]) :
                          FractionRing R[T;T⁻¹]))
                    Finset.univ
            _ = ∑ i,
                  algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
                    ((AddMonoidAlgebra.mapAlgHom (M := ℤ)
                      (Algebra.ofId R (FractionRing R)) (c i)) * lifted i) := by
                  refine Finset.sum_congr rfl fun i _ ↦ ?_
                  calc
                    laurent_fraction_comparison (R := R)
                        (algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (c i) *
                          (generators i : FractionRing R[T;T⁻¹])) =
                        laurent_fraction_comparison (R := R)
                          (algebraMap R[T;T⁻¹] (FractionRing R[T;T⁻¹]) (c i)) *
                            laurent_fraction_comparison (R := R)
                              (generators i : FractionRing R[T;T⁻¹]) := by
                                rw [map_mul]
                    _ =
                        algebraMap ((FractionRing R)[T;T⁻¹])
                          (FractionRing ((FractionRing R)[T;T⁻¹]))
                          ((AddMonoidAlgebra.mapAlgHom (M := ℤ)
                            (Algebra.ofId R (FractionRing R)) (c i))) *
                            algebraMap ((FractionRing R)[T;T⁻¹])
                              (FractionRing ((FractionRing R)[T;T⁻¹])) (lifted i) := by
                                rw [laurent_fraction_comparison_algebraMap, ← hlifted i]
                    _ =
                        algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
                          ((AddMonoidAlgebra.mapAlgHom (M := ℤ)
                            (Algebra.ofId R (FractionRing R)) (c i)) * lifted i) := by
                                symm
                                rw [map_mul]
            _ = algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹])) rhs := by
                  dsimp [rhs, lifted_generator_combination]
                  exact (map_sum
                    (RingHom.toAddMonoidHom
                      (algebraMap ((FractionRing R)[T;T⁻¹])
                        (FractionRing ((FractionRing R)[T;T⁻¹]))))
                    (fun i : Fin n ↦
                      ((AddMonoidAlgebra.mapAlgHom (M := ℤ)
                        (Algebra.ofId R (FractionRing R)) (c i)) * lifted i :
                          (FractionRing R)[T;T⁻¹]))
                    Finset.univ).symm
        -- Transport the normalization identity into the common Laurent fraction field.
        calc
          algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹]))
              (LaurentPolynomial.C (x : FractionRing R)) =
            laurent_fraction_comparison (R := R)
              (integralClosure_constants_map_to_laurent_normalization (R := R) x :
                FractionRing R[T;T⁻¹]) := by
                  symm
                  exact laurent_fraction_comparison_constant (R := R) (x : FractionRing R)
          _ =
            laurent_fraction_comparison (R := R)
              ((∑ i, c i • generators i :
                integralClosure R[T;T⁻¹] (FractionRing R[T;T⁻¹])) :
                FractionRing R[T;T⁻¹]) := by
                  exact congrArg transport hdecomp
          _ =
            algebraMap ((FractionRing R)[T;T⁻¹]) (FractionRing ((FractionRing R)[T;T⁻¹])) rhs := htransport
      simpa [rhs] using
        (IsFractionRing.injective ((FractionRing R)[T;T⁻¹])
          (FractionRing ((FractionRing R)[T;T⁻¹]))) hambient
    -- Taking coefficient `0` of the transported Laurent identity lands back in the coefficient
    -- span generated by the finitely many chosen Laurent lifts.
    simpa [lifted_generator_combination] using
      (coeff_zero_mem_span_after_transport (R := R) lifted coeffs hcoeffs htransport)
  have hfiniteP : Module.Finite R P :=
    coeff_span_finite (R := R) (s := (↑coeffs : Set K)) coeffs.finite_toSet
  letI : Module.Finite R P := hfiniteP
  -- Embed the normalization into the finite submodule that contains all of its elements.
  exact Module.Finite.of_injective
    (integralClosure_to_submodule (R := R) P hcontain)
    (integralClosure_to_submodule_injective (R := R) P hcontain)

end
