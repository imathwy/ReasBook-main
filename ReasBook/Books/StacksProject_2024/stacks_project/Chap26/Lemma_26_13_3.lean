import Mathlib.AlgebraicGeometry.ResidueField

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: mathlib already provides the canonical residue-field API
-- `Scheme.SpecToEquivOfField` together with
-- `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`.

/- Lemma 26.13.3 (1): for a scheme `X` and a field `K`, a morphism `Spec K ⟶ X`
corresponds to a point `x : X` together with a morphism `κ(x) ⟶ K`. This is exactly
the canonical mathlib equivalence `Scheme.SpecToEquivOfField`. -/
#check Scheme.SpecToEquivOfField

/- Lemma 26.13.3 (2): every morphism `f : Spec K ⟶ X` factors through the canonical
map `Spec κ(x) ⟶ X` attached to the image `x` of the unique point of `Spec K`. This is
exactly `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`. -/
#check Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField

/-- Source-facing factorization form of `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`. -/
theorem specToEquivOfField_factorization
    (K : Type u) [Field K] (X : Scheme.{u}) (f : Spec (CommRingCat.of K) ⟶ X) :
    CategoryTheory.CategoryStruct.comp
        (Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo f)))
        (X.fromSpecResidueField (f (IsLocalRing.closedPoint K))) = f := by
  simpa using
    (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X f)

end AlgebraicGeometry.Scheme
