import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Derivation.MapCoeffs
import StacksProject_2024.Chap10.Definition_10_110_7
import StacksProject_2024.Chap10.Lemma_10_163_10
import StacksProject_2024.Chap15.Lemma_15_48_2

-- Declarations for this item will be appended below by the statement pipeline.

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
