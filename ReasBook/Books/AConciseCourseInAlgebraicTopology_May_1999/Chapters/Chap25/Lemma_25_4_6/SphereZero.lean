import Books.AConciseCourseInAlgebraicTopology_May_1999.BasedCWComplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.SmashProductCoherence

noncomputable section

/-- A chosen based CW model of `S⁰`, presented by a based CW complex together with a based-space
comparison to the Chapter 11 smash-product unit `sphereZero`. -/
structure SphereZeroModel where
  /-- The chosen based CW complex used as the `S⁰` model. -/
  toBasedCWComplex : BasedCWComplex
  /-- The underlying based space of the chosen model is identified with the Chapter 11 `S⁰`
  owner `sphereZero`. -/
  toSphereZero : toBasedCWComplex.1 ≅ sphereZero

namespace SphereZeroModel

/-- The underlying based space of a chosen based CW model of `S⁰`. -/
abbrev basedSpace (model : SphereZeroModel) : BasedSpace :=
  model.toBasedCWComplex.1

/-- A chosen based CW model of `S⁰` comes with its named based-space comparison to `sphereZero`.
-/
abbrev basedSpaceIso (model : SphereZeroModel) : model.basedSpace ≅ sphereZero :=
  model.toSphereZero

/-- The based-space comparison carried by `SphereZeroModel` exists as explicit data. -/
theorem basedSpaceIso_nonempty (model : SphereZeroModel) :
    Nonempty (model.basedSpace ≅ sphereZero) :=
  ⟨model.basedSpaceIso⟩

end SphereZeroModel
