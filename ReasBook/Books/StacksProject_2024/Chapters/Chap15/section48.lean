import Mathlib
import Mathlib.Algebra.Regular.Defs
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Away.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_48_1 (from Chap15) -/
universe u v

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling for Lemma 15.48.1:
- primary domain: commutative algebra of derivations under adic completion and localization;
- sampled owner declarations of the same kind:
  `Derivation`,
  `Derivation.compAlgebraMap`,
  `LinearMap.compDer`,
  `AdicCompletion.liftAlgHom`,
  `IsLocalization.liftAlgHom`,
  `Localization.awayMapₐ`;
- best owner abstraction: the target of clauses `(1)` and `(2)` is a canonical `Derivation` on the
  completion/localization itself, while the extension property along the structural map is the
  derived source-facing view of the owner-level equality on restricted derivations. For clause
  `(3)`, the chapter's canonical owner for comparison maps between away localizations is
  `Localization.awayMapₐ`, but the source hypothesis is only the existence of an `R`-algebra
  isomorphism between the two away localizations, so the main theorem keeps that source-facing
  shape instead of strengthening it to a statement about the canonical map;
- primitive data: the source derivation `D`, the ideal `I` for completion, and the target
  localization algebra `A`;
- derived API: pointwise restriction-to-`R` formulas, uniqueness lemmas, and the companion `∃!`
  reformulations built from the owner-level restriction equation.

Layer triage:
- `source-facing`: the canonical extensions `D.adicCompletionExtension I` and
  `D.localizationExtension S A`, together with the finite-type existential statement in clause
  `(3)`;
- `core/canonical`: the owner type `Derivation ℤ _ _` on the target algebra;
- `bridge/view`: the companion existence-uniqueness theorems and the restriction formulas along the
  canonical maps `R → AdicCompletion I R` and `R → A`.
-/

namespace Derivation

variable (D : Derivation ℤ R R)

section AdicCompletion

variable (I : Ideal R)

local notation "R̂" => AdicCompletion I R

private theorem existsUnique_adicCompletionExtension_aux :
    ∃! Dhat : Derivation ℤ R̂ R̂,
      Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D := by
  sorry

-- Proof sketch: for `n ≥ 1`, the Leibniz rule implies `D (I ^ (n + 1)) ⊆ I ^ n`, so `D`
-- induces compatible derivations on the quotient system `R ⧸ I ^ (n + 1) → R ⧸ I ^ n`. Passing to
-- the inverse limit yields a derivation on the `I`-adic completion, and uniqueness is checked on
-- the dense image of `R`.
/-- Lemma 15.48.1 (1): for any ideal `I` of a commutative ring `R`, a derivation `D : R → R`
extends canonically to a derivation of the `I`-adic completion `AdicCompletion I R`. -/
noncomputable def adicCompletionExtension : Derivation ℤ R̂ R̂ :=
  (existsUnique_adicCompletionExtension_aux D I).choose

theorem adicCompletionExtension_compAlgebraMap :
    (D.adicCompletionExtension I).compAlgebraMap R = (Algebra.linearMap R R̂).compDer D :=
  (existsUnique_adicCompletionExtension_aux D I).choose_spec.left

@[simp]
theorem adicCompletionExtension_algebraMap (r : R) :
    D.adicCompletionExtension I (algebraMap R R̂ r) = algebraMap R R̂ (D r) :=
  congr_fun (D.adicCompletionExtension_compAlgebraMap I) r

theorem adicCompletionExtension_unique
    (Dhat : Derivation ℤ R̂ R̂)
    (hDhat : Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D) :
    Dhat = D.adicCompletionExtension I := by
  exact (existsUnique_adicCompletionExtension_aux D I).choose_spec.right Dhat hDhat

/-- Existence and uniqueness of the canonical extension of a derivation to the `I`-adic
completion. -/
theorem existsUnique_adicCompletionExtension :
    ∃! Dhat : Derivation ℤ R̂ R̂,
      Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D :=
  ⟨D.adicCompletionExtension I, D.adicCompletionExtension_compAlgebraMap I,
    fun Dhat hDhat ↦ D.adicCompletionExtension_unique I Dhat hDhat⟩

end AdicCompletion

section Localization

private theorem existsUnique_localizationExtension_aux
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A]
    : ∃! Dloc : Derivation ℤ A A,
        Dloc.compAlgebraMap R = (Algebra.linearMap R A).compDer D := by
  sorry

-- Proof sketch: define the candidate by the quotient rule on fractions,
-- `D(r / s) = D(r) / s - r D(s) / s^2`, and prove it is well defined using the localization
-- relation. The derivation axioms follow from direct computation, and uniqueness is forced by the
-- fact that every element of the localization is represented by a fraction.
/-- Lemma 15.48.1 (2): for any multiplicative subset `S` of `R`, a derivation `D : R → R`
extends canonically to any localization `A` of `R` at `S`. -/
noncomputable def localizationExtension (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    Derivation ℤ A A :=
  (existsUnique_localizationExtension_aux D S A).choose

theorem localizationExtension_compAlgebraMap
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    (D.localizationExtension S A).compAlgebraMap R =
      (Algebra.linearMap R A).compDer D :=
  (existsUnique_localizationExtension_aux D S A).choose_spec.left

@[simp]
theorem localizationExtension_algebraMap
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] (r : R) :
    D.localizationExtension S A (algebraMap R A r) = algebraMap R A (D r) :=
  congr_fun (D.localizationExtension_compAlgebraMap S A) r

theorem localizationExtension_unique
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A]
    (Dloc : Derivation ℤ A A)
    (hDloc : Dloc.compAlgebraMap R = (Algebra.linearMap R A).compDer D) :
    Dloc = D.localizationExtension S A := by
  exact (existsUnique_localizationExtension_aux D S A).choose_spec.right Dloc hDloc

/-- Existence and uniqueness of the canonical extension of a derivation to a localization. -/
theorem existsUnique_localizationExtension
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    ∃! Dloc : Derivation ℤ A A,
        Dloc.compAlgebraMap R = (Algebra.linearMap R A).compDer D :=
  ⟨D.localizationExtension S A, D.localizationExtension_compAlgebraMap S A,
    fun Dloc hDloc ↦ D.localizationExtension_unique S A Dloc hDloc⟩

end Localization

section FiniteType

variable {R' : Type v} [CommRing R'] [Algebra R R'] [Algebra.FiniteType R R']

-- Proof sketch: choose finitely many `R`-algebra generators of `R'` and clear denominators after
-- transporting them across an isomorphism between the two away localizations where `g` becomes
-- invertible. For sufficiently large `N`, the scaled derivation `g ^ N • D` carries each
-- generator into `R'`, hence by the Leibniz rule it extends from `R` to an `R'`-valued derivation
-- on the finite type algebra `R'`.
/-- Canonical-owner reformulation of Lemma 15.48.1 (3): if the canonical comparison
`Localization.awayMapₐ (Algebra.ofId R R') g` is bijective and `algebraMap R R' g` is a
nonzerodivisor in `R'`, then some multiple `g ^ N • D` extends to a derivation of `R'`. -/
theorem exists_pow_smul_extension_of_finiteType_of_bijective_awayMap (g : R)
    (hAway : Function.Bijective (Localization.awayMapₐ (Algebra.ofId R R') g))
    (hg : IsRegular (algebraMap R R' g)) :
    ∃ N : ℕ, ∃ D' : Derivation ℤ R' R',
      D'.compAlgebraMap R = (Algebra.linearMap R R').compDer (g ^ N • D) := sorry

/-- Lemma 15.48.1 (3): let `R → R'` be a finite type extension and let `g : R` be such that
`Localization.Away g` and `Localization.Away (algebraMap R R' g)` are isomorphic as `R`-algebras
and `algebraMap R R' g` is a nonzerodivisor in `R'`. Equivalently, the canonical comparison map
`Localization.awayMapₐ (Algebra.ofId R R') g` is bijective. Then some multiple `g ^ N • D`
extends to a derivation of `R'`. -/
theorem exists_pow_smul_extension_of_finiteType_of_away_iso (g : R)
    (eAway : Localization.Away g ≃ₐ[R] Localization.Away (algebraMap R R' g))
    (hg : IsRegular (algebraMap R R' g)) :
    ∃ N : ℕ, ∃ D' : Derivation ℤ R' R',
      D'.compAlgebraMap R = (Algebra.linearMap R R').compDer (g ^ N • D) :=
  D.exists_pow_smul_extension_of_finiteType_of_bijective_awayMap g
    (by
      have hEq : Localization.awayMapₐ (Algebra.ofId R R') g = eAway.toAlgHom := by
        apply Localization.algHom_ext (Submonoid.powers g)
        ext
      simpa [hEq] using eAway.bijective)
    hg

end FiniteType

end Derivation

end

/-! ### Lemma_15_48_2 (from Chap15) -/
universe u

section

variable {R : Type u} [CommRing R] [IsRegularRing R]
variable {f : R}

/- Domain-style sampling:
* primary domain: regular rings, regular local rings on localizations, and absolute derivations on
  a commutative ring;
* sampled owner declarations:
  `IsRegularRing`,
  `IsRegularLocalRing`,
  `IsLocalRing.IsRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal`,
  `Derivation ℤ R R`;
* owner abstraction: the ambient owner is `IsRegularRing R`, localized in the proof sketch through
  the regular-local owner on prime localizations; the derivation datum is the canonical mathlib
  owner `Derivation ℤ R R`.

Primitive vs. derived:
* primitive data: a concrete derivation `D : Derivation ℤ R R` and the unit condition on the class
  of `D f` in `R ⧸ (f)`;
* derived API: the source-facing existential corollary, which packages the same primitive data in
  the textbook existence form.

Source/core/bridge triage:
* source-facing: `isRegularRing_quotient_principalIdeal_of_exists_derivation`, matching the
  textbook existence hypothesis;
* core/canonical: `IsRegularRing`, `IsRegularLocalRing`, and `Derivation ℤ R R`;
* bridge/view: `Derivation.isRegularRing_quotient_principalIdeal_of_isUnit`, which exposes the
  primitive derivation datum directly from the owner object.
-/

-- Proof sketch: regularity is local on `Spec R`, so localize at a maximal ideal of `R ⧸ (f)` and
-- reduce to the case of a regular local ring. There, Lemma `10.106.3` shows it is enough to prove
-- `f ∉ maximalIdeal R ^ 2`. If `f ∈ maximalIdeal R ^ 2`, write `f` as a sum of products of
-- elements of the maximal ideal and apply the Leibniz rule to see that `D f` still lies in the
-- maximal ideal, contradicting that its class in `R ⧸ (f)` is a unit.
namespace Derivation

/-- Primitive-input bridge for Lemma 15.48.2: if `R` is a regular ring and
`D : Derivation ℤ R R` sends `f` to an element whose class in `R ⧸ (f)` is a unit, then
`R ⧸ (f)` is a regular ring. -/
theorem isRegularRing_quotient_principalIdeal_of_isUnit (D : Derivation ℤ R R)
    (hDf : IsUnit (Ideal.Quotient.mk (principalIdeal f) (D f))) :
    IsRegularRing (R ⧸ principalIdeal f) := sorry

end Derivation

/-- Lemma 15.48.2: if `R` is a regular ring and `f` admits a derivation
`D : Derivation ℤ R R` whose value `D f` becomes a unit in `R ⧸ (f)`, then `R ⧸ (f)` is a
regular ring. -/
theorem isRegularRing_quotient_principalIdeal_of_exists_derivation
    (hD : ∃ D : Derivation ℤ R R,
      IsUnit (Ideal.Quotient.mk (principalIdeal f) (D f))) :
    IsRegularRing (R ⧸ principalIdeal f) := by
  obtain ⟨D, hDf⟩ := hD
  exact D.isRegularRing_quotient_principalIdeal_of_isUnit hDf

end

/-! ### Lemma_15_48_3 (from Chap15) -/
universe u

open IsLocalRing
open RingTheory Sequence

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {m : ℕ}

/- Domain-style sampling:
* primary domain: regular local rings, chosen families in the maximal ideal, cotangent-space
  criteria, and regular systems of parameters;
* sampled owner declarations upstream in the chapter/project:
  `parameterIdeal`,
  `IsPartOfRegularSystemOfParameters`,
  `IsPartOfRegularSystemOfParameters.isRegular`,
  `IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal`;
* source/core/bridge triage:
  `source-facing`: the Jacobian determinant criterion for the chosen family
  `x : Fin m → maximalIdeal R`;
  `core/canonical`: `IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x`,
  together with the derived owners `parameterIdeal x` and `IsRegular R (List.ofFn fun i ↦ (x i : R))`;
  `bridge/view`: the two textbook consequences obtained from the Chapter 10 owner API;
* owner abstraction: the main declaration in this file should be exactly the bridge from the
  Jacobian determinant hypothesis to
  `IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x`. The quotient regularity and
  list regularity statements are then canonical downstream views and should stay thin wrappers
  around the Chapter 10 owner theorems, not parallel local APIs;
* primitive data: the family `x`, the derivations `D`, and the unit Jacobian determinant
  hypothesis;
* derived API: `IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x`, regularity of
  the quotient by `parameterIdeal x`, and regularity of `List.ofFn fun i ↦ (x i : R)`, with the
  latter two exposed only as direct owner consequences.

The source hypothesis `1 ≤ m` is mathematically redundant here: the empty family case is still a
valid regular sequence and quotient, so the public API keeps only the primitive data used by the
owner-level statements.
-/

-- Proof sketch: use the determinant hypothesis to show the classes of the `x i` are linearly
-- independent in `maximalIdeal R / (maximalIdeal R) ^ 2`, exactly as in the textbook proof. Extend
-- them to a basis of the cotangent space of the regular local ring `R`, lift that basis to a
-- regular system of parameters, and identify the original family `x` with the initial segment.
/-- Lemma 15.48.3 owner bridge: if the Jacobian determinant of the chosen derivations
`det (D i (x j))` is a unit, then `x` is part of a regular system of parameters. -/
theorem isPartOfRegularSystemOfParameters_of_jacobian_det_isUnit
    (x : Fin m → maximalIdeal R) (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x := sorry

/-- Lemma 15.48.3 (1), derived owner view: if the Jacobian determinant of the chosen absolute
derivations `D i : Derivation ℤ R R` is a unit, then `R ⧸ parameterIdeal x` is a regular local
ring. -/
theorem isRegularLocalRing_quotient_parameterIdeal_of_jacobian_det_isUnit
    (x : Fin m → maximalIdeal R) (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    IsRegularLocalRing (R ⧸ parameterIdeal x) :=
  IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal
    (isPartOfRegularSystemOfParameters_of_jacobian_det_isUnit x D hdet)

/-- Lemma 15.48.3 (2), derived owner view: under the same hypotheses, the underlying list of the
chosen family `x`, encoded as `List.ofFn fun i ↦ (x i : R)`, is a regular sequence in `R`. -/
theorem isRegular_of_jacobian_det_isUnit
    (x : Fin m → maximalIdeal R) (D : Fin m → Derivation ℤ R R)
    (hdet : IsUnit (Matrix.det fun i j ↦ D i (x j : R))) :
    IsRegular R (List.ofFn fun i ↦ (x i : R)) :=
  IsPartOfRegularSystemOfParameters.isRegular
    (isPartOfRegularSystemOfParameters_of_jacobian_det_isUnit x D hdet)

end

/-! ### Lemma_15_48_4 (from Chap15) -/
open Polynomial PolynomialModule

universe u

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
* primary domain: regular rings, polynomial algebras, derivations, and principal hypersurface
  quotients;
* sampled owner declarations:
  `Derivation.mapCoeffs`,
  `Derivation.apply_aeval_eq`,
  `Derivation.isRegularRing_quotient_principalIdeal_of_isUnit`,
  `isRegularRing_of_smooth`;
* best owner abstraction: this file is `source-facing`, while the proof should reuse the chapter
  owner `Derivation.isRegularRing_quotient_principalIdeal_of_isUnit` for principal quotients and
  the canonical mathlib polynomial-derivation owners `Derivation.mapCoeffs` /
  `Derivation.apply_aeval_eq` for the coefficientwise extension to `R[X]`.

Primitive vs. derived:
* primitive data: a derivation `D : Derivation ℤ R R` with `D f` a unit, and the polynomial
  `g = p.map (Int.castRingHom R) - C f`;
* derived API: the induced derivation on `R[X]`, the unit statement for the class of `D' g`, and
  the regularity of the `AdjoinRoot` quotient.

Source/core/bridge triage:
* source-facing: `isRegularRing_adjoinRoot_sub_C_of_exists_derivation`;
* core/canonical: `IsRegularRing`, `AdjoinRoot`, and `Derivation ℤ R R`;
* bridge/view: `Derivation.isRegularRing_adjoinRoot_sub_C_of_isUnit`, which exposes the primitive
  derivation input directly.
-/

-- Proof sketch: `R[X]` is regular because polynomial algebras over regular rings are smooth. Extend
-- the given absolute derivation on `R` to `R[X]` by sending `X` to `0`; this kills every polynomial
-- with integer coefficients, so it sends `p.map (Int.castRingHom R) - C f` to `-D f`, hence to a
-- unit. Lemma `15.48.2` applied to the quotient by this principal polynomial ideal then gives the
-- regularity of the resulting `AdjoinRoot`.
variable [IsRegularRing R] {f : R}

namespace Derivation

/-- Primitive-input bridge for Lemma 15.48.4: if `R` is a regular ring and a derivation
`D : Derivation ℤ R R` sends `f` to a unit, then for every integer polynomial `p` the quotient
`R[z] / (p(z) - f)` is regular, written canonically as
`AdjoinRoot (p.map (Int.castRingHom R) - C f)`. -/
theorem isRegularRing_adjoinRoot_sub_C_of_isUnit (D : Derivation ℤ R R)
    (hDf : IsUnit (D f)) (p : Polynomial ℤ) :
    IsRegularRing (AdjoinRoot (p.map (Int.castRingHom R) - C f)) := by
  letI : Algebra.Smooth R R[X] := ⟨inferInstance, inferInstance⟩
  letI : IsNoetherianRing R[X] := Algebra.FiniteType.isNoetherianRing R R[X]
  let _ : RingHom.IsRegularRingMap (algebraMap R R[X]) := by
    exact
      { toFlat := RingHom.flat_algebraMap_iff.mpr inferInstance
        isGeometricallyRegular_fiber := fun q ↦ by
          letI : Algebra.Smooth q.asIdeal.ResidueField (q.asIdeal.Fiber R[X]) := inferInstance
          letI :
              Algebra.IsGeometricallyRegular q.asIdeal.ResidueField q.asIdeal.ResidueField :=
            inferInstance
          infer_instance }
  haveI : IsRegularRing R[X] := Algebra.isRegularRing_of_regularRingMap R
  let g : R[X] := p.map (Int.castRingHom R) - C f
  have hg : IsRegularRing (R[X] ⧸ principalIdeal g) := by
    letI : Differential R := ⟨D⟩
    let D' : Derivation ℤ R[X] R[X] := Differential.mapCoeffs
    let qC : R →+* R[X] ⧸ principalIdeal g := (Ideal.Quotient.mk (principalIdeal g)).comp C
    refine D'.isRegularRing_quotient_principalIdeal_of_isUnit ?_
    have hX : D' (X : Polynomial R) = 0 := by
      have hX' : Differential.mapCoeffs (X : Polynomial R) = 0 := Differential.mapCoeffs_X
      simpa [D'] using hX'
    have hp : D' (p.map (Int.castRingHom R)) = 0 := by
      ext i
      simp [D']
    have hderivf : Differential.deriv f = D f := rfl
    have hCf : D' (C f) = C (D f) := by
      have hCf' : Differential.mapCoeffs (C f) = C (Differential.deriv f) :=
        Differential.mapCoeffs_C f
      simpa [D', hderivf] using hCf'
    have hmain : D' g = -C (D f) := by
      change D' (p.map (Int.castRingHom R) - C f) = -C (D f)
      rw [map_sub, hp, hCf]
      simp
    have hbase : IsUnit ((Ideal.Quotient.mk (principalIdeal g)) (C (D f))) := by
      simpa [qC] using hDf.map qC
    have hneg : IsUnit (-((Ideal.Quotient.mk (principalIdeal g)) (C (D f)))) := hbase.neg
    have hquot :
        (Ideal.Quotient.mk (principalIdeal g)) (D' g) =
          -((Ideal.Quotient.mk (principalIdeal g)) (C (D f))) := by
      simpa using congrArg (Ideal.Quotient.mk (principalIdeal g)) hmain
    exact hquot ▸ hneg
  change IsRegularRing (R[X] ⧸ principalIdeal g)
  exact hg

end Derivation

/-- Lemma 15.48.4: if `R` is a regular ring and some absolute derivation of `R` sends `f` to a
unit, then for every integer polynomial `p`, the quotient `R[z] / (p(z) - f)` is regular, written
canonically as `AdjoinRoot (p.map (Int.castRingHom R) - C f)`. -/
theorem isRegularRing_adjoinRoot_sub_C_of_exists_derivation
    (hD : ∃ D : Derivation ℤ R R, IsUnit (D f)) (p : Polynomial ℤ) :
    IsRegularRing (AdjoinRoot (p.map (Int.castRingHom R) - C f)) := by
  obtain ⟨D, hDf⟩ := hD
  exact D.isRegularRing_adjoinRoot_sub_C_of_isUnit hDf p

end

/-! ### Lemma_15_48_5 (from Chap15) -/
universe u v

section

variable {B : Type u} [CommRing B] [IsDomain B]

/- Domain-style sampling:
* primary domain: characteristic-`p` commutative algebra of domains, fraction fields, Kähler
  differentials, and absolute derivations;
* sampled owner declarations of the same kind:
  `Derivation`,
  `KaehlerDifferential.D`,
  `KaehlerDifferential.linearMapEquivDerivation`,
  `kaehlerDifferential_eq_zero_iff_exists_pth_root`,
  `Derivation.localizationExtension`;
* best owner abstraction: this numbered item stays `source-facing`; the canonical owner for the
  output is `Derivation ℤ B B`, while the non-`p`th-power input is measured intrinsically in the
  fraction field `FractionRing B`;
* primitive data: the ambient characteristic-`p` domain `B`, the finite-type-over-some-complete-
  local-ring hypothesis, the element `f : B`, and the fraction-field non-`p`th-power hypothesis on
  `f`;
* derived API: the fraction-field differential obstruction from
  `kaehlerDifferential_eq_zero_iff_exists_pth_root`, the existence of a fraction-field derivation
  not killing `f` via `KaehlerDifferential.linearMapEquivDerivation`, and the descent/clearing-
  denominators step yielding a derivation `B → B`.

Source/core/bridge triage:
* `source-facing`: `exists_derivation_with_nonzero_apply_of_not_exists_pth_root`;
* `core/canonical`: `Derivation ℤ B B`, `FractionRing B`, and the universal derivation
  `KaehlerDifferential.D`;
* `bridge/view`: the finite complete-local presentation supplied by `hB` and the fraction-field
  derivation construction/descent used in the proof sketch.
-/

-- Proof sketch: choose a Noetherian complete local ring `R` and a finite type map `R → B` from
-- the given existential hypothesis.
-- Replacing `R` by its image in `B` reduces to the case where `R` is a domain of characteristic
-- `p`. Cohen structure and the finite-type reduction from the source then replace `B` by a finite
-- extension of a mixed power-series/polynomial ring. Lemma `10.158.2` shows that the absolute
-- differential of `f` in `FractionRing B` is nonzero because `f` is not a `p`th power, and Lemma
-- `15.46.5` allows one to choose a derivation of the fraction field that does not kill `f`.
-- Clearing denominators yields the required derivation `B → B`.
/-- Lemma 15.48.5: if `B` is a domain of characteristic `p` which is of finite type over some
Noetherian complete local ring, and `f` is not a `p`th power in `FractionRing B`, then there
exists a derivation `D : B → B` with `D(f) ≠ 0`. -/
theorem exists_derivation_with_nonzero_apply_of_not_exists_pth_root
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (hB :
      ∃ (R : Type v) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : IsCompleteLocalRing R)
        (_ : Algebra R B), Algebra.FiniteType R B)
    (f : B)
    (hf : ¬ ∃ g : FractionRing B, g ^ p = algebraMap B (FractionRing B) f) :
    ∃ D : Derivation ℤ B B, D f ≠ 0 := sorry

end

/-! ### Lemma_15_48_6 (from Chap15) -/
universe u

section

/- Domain-style sampling:
- primary domain: Noetherian complete local domains, the chapter owner `IsJ0Ring`, and the
  finite regular complete-local subring / fraction-field descent machinery used to prove openness
  of the regular locus;
- sampled owner and bridge declarations of the same kind:
  `IsJ0Ring`,
  `PrimeSpectrum.regularLocus`,
  `exists_finite_regular_completeLocalSubring`,
  `Algebra.isJ0Ring_of_injective_finiteType_of_separable_fractionRingExtension`;
- best owner abstraction: the public statement should stay on the chapter owner `IsJ0Ring`,
  with the finite complete-local subring and the separable/purely inseparable fraction-field
  analysis kept internal to the proof route;
- source/core/bridge triage:
  * source-facing: the conclusion that a Noetherian complete local domain is `J-0`;
  * core/canonical: the chapter owner `IsJ0Ring`;
  * bridge/view: the finite regular complete local subring from Cohen structure, the separability
    bridge on fraction fields, and the purely inseparable derivation/adjoin-root regularity step;
- primitive vs. derived: the primitive public data are exactly the ambient assumptions
  `[IsNoetherianRing A]`, `[IsCompleteLocalRing A]`, and `[IsDomain A]`. The finite regular
  complete local subring, the separable versus purely inseparable case split on the fraction
  field extension, and the derivation witness used in the purely inseparable branch are all
  derived implementation data supplied by the chapter bridge lemmas, so this file should keep
  the public surface on `IsJ0Ring A` rather than introducing a parallel wrapper API.
-/

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] [IsDomain A]

-- Proof sketch: choose a finite regular complete local subring `A₀ ⊆ A` using
-- Lemma `10.160.11`.
-- If the induced fraction-field extension is separable, apply Lemma `15.47.5` to descend `J-0`
-- from the regular ring `A₀`. Otherwise, pass to a minimal purely inseparable subextension,
-- produce a derivation on the intermediate ring by Lemma `15.48.5`, and apply Lemma `15.48.4` to
-- obtain regularity on a nonempty open subset of `Spec A`; since the intermediate ring is already
-- `J-0`, this yields `IsJ0Ring A`.
/-- Lemma 15.48.6: a Noetherian complete local domain is `J-0`. -/
theorem isJ0Ring_of_noetherian_completeLocalDomain : IsJ0Ring A := sorry

end

/-! ### Proposition_15_48_7 (from Chap15) -/
universe u v

/- Domain-style sampling:
- primary domain: commutative algebra of the chapter owner `IsJ2Ring`, together with the standard
  complete-local, one-dimensional local, Nagata, Dedekind, and finite-type stability sources for
  the `J-2` property;
- sampled owner declarations of the same kind:
  `IsJ2Ring`,
  `isJ2Ring_iff_forall_finiteType_isJ1`,
  `NagataRing`,
  `IsCompleteLocalRing`;
- best owner abstraction: the public surface should stay on the canonical owner `IsJ2Ring`; pure
  specialization clauses such as the field and integer cases should use direct recall or instance
  inference rather than parallel local wrapper declarations;
- primitive vs. derived: the primitive public data are the ambient ring hypotheses for each source
  clause. The `J-1` conclusions for finite type algebras are derived from `IsJ2Ring`, so this file
  should not introduce any auxiliary data packaging around them.

Source/core/bridge triage:
- `source-facing`: the six proposition clauses listing concrete sources of `IsJ2Ring`;
- `core/canonical`: the chapter owner `IsJ2Ring`;
- `bridge/view`: the Dedekind/Nagata/complete-local specializations and the finite-type stability
  theorem.
-/

section

variable (K : Type u) [Field K]

/- Proposition 15.48.7 (1): fields are `J-2`. -/
#check (inferInstance : IsJ2Ring K)

end

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/-- Proposition 15.48.7 (1): a Noetherian complete local ring is `J-2`. -/
-- Proof sketch: use condition `(3)` of Lemma `15.47.6`. Any finite `R`-algebra is a finite
-- product of Noetherian complete local rings, so by Lemma `15.47.3` it suffices to handle the
-- domain case. That domain case is Lemma `15.48.6`.
instance isJ2Ring_of_noetherian_completeLocalRing : IsJ2Ring R := sorry

end

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Proof sketch: use condition `(3)` of Lemma `15.47.6`. Any finite `R`-algebra has finite
-- spectrum; because the regular locus is stable under generalization, it is open, so every finite
-- `R`-algebra is `J-1`.
/-- Proposition 15.48.7 (3): a Noetherian local ring of Krull dimension `1` is `J-2`. -/
theorem isJ2Ring_of_noetherian_local_ring_dimension_one
    (hdim : ringKrullDim R = 1) : IsJ2Ring R := sorry

end

section

variable (R : Type u) [CommRing R] [NagataRing R]

-- Proof sketch: use condition `(4)` of Lemma `15.47.6`. For a prime `p` and a finite purely
-- inseparable extension of its residue field, if `p` is maximal then the extension ring is finite
-- over a field and hence regular; if `p` is minimal, the Nagata property makes the integral
-- closure finite, and in dimension `1` that normal domain is regular.
/-- Proposition 15.48.7 (4): a Nagata ring of Krull dimension `1` is `J-2`. -/
theorem isJ2Ring_of_nagataRing_dimension_one
    (hdim : ringKrullDim R = 1) : IsJ2Ring R := sorry

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]

/-- Proposition 15.48.7 (5): a Dedekind domain whose fraction field has characteristic zero is
`J-2`. -/
-- Proof sketch: such a ring is Nagata by Proposition `10.162.16`, and a Dedekind domain has
-- Krull dimension `1`; apply the one-dimensional Nagata case.
instance isJ2Ring_of_isDedekindDomain_of_fractionRing_charZero : IsJ2Ring R := sorry

end

section

/- Proposition 15.48.7 (2): the ring of integers `ℤ` is `J-2`, by the Dedekind-domain
characteristic-zero instance above. -/
#check (inferInstance : IsJ2Ring ℤ)

end

section

variable (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Proposition 15.48.7 (6): finite type ring extensions of `J-2` rings are `J-2`. -/
-- Proof sketch: if `T` is a finite type `S`-algebra, then by transitivity it is a finite type
-- `R`-algebra. Since `R` is `J-2`, the ring `T` is `J-1`, so `S` satisfies the defining `J-2`
-- condition.
theorem isJ2Ring_of_finiteType [IsJ2Ring R] [Algebra.FiniteType R S] :
    IsJ2Ring S := by
  refine ⟨?_⟩
  intro A _ _ _
  sorry

end
