import Mathlib.RingTheory.Localization.AsSubring

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Localization FractionRing

section

variable (R : Type u) [CommRing R]
variable (S : Submonoid R)

/- Lemma 10.25.3 is a `bridge/view` item. The owner abstractions are
`Localization.mapToFractionRing`, which equips `FractionRing R` with the canonical
`Localization S`-algebra structure when `S ≤ nonZeroDivisors R`, and `FractionRing.algEquiv`,
which identifies any fraction ring of `Localization S` with `FractionRing (Localization S)`. -/

/-- Lemma 10.25.3: if `S` is a multiplicative subset of nonzerodivisors in `R`, then the total
quotient ring `Q(R)` is canonically isomorphic to the total quotient ring of the localization
`S⁻¹R`. -/
noncomputable def fractionRing_localization_equiv (hS : S ≤ nonZeroDivisors R) :
    FractionRing R ≃ₐ[R] FractionRing (Localization S) :=
  let f := mapToFractionRing (FractionRing R) S (Localization S) hS
  letI : Algebra (Localization S) (FractionRing R) := RingHom.toAlgebra f.toRingHom
  letI : IsScalarTower R (Localization S) (FractionRing R) :=
    .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  letI : IsFractionRing (Localization S) (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization S (Localization S) (FractionRing R) hS
  (FractionRing.algEquiv (Localization S) (FractionRing R)).symm.restrictScalars R

/-- The canonical equivalence from `Q(R)` to `Q(S⁻¹R)` commutes with the map from `R`. -/
@[simp]
theorem fractionRing_localization_equiv_apply_algebraMap (hS : S ≤ nonZeroDivisors R) (r : R) :
    fractionRing_localization_equiv R S hS (algebraMap R (FractionRing R) r) =
      algebraMap R (FractionRing (Localization S)) r := by
  exact AlgEquiv.commutes (fractionRing_localization_equiv R S hS) r

end
