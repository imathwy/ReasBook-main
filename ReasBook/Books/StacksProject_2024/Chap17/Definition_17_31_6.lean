import Mathlib
import StacksProject_2024.Chap17.Definition_17_28_10
import StacksProject_2024.Chap17.Definition_17_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open TopCat.Sheaf
open scoped ZeroObject AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open RingedSpace.Hom

variable {X Y : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})]

private instance topCatSheaf_hasBinaryCoproducts :
    HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} X) := by
  simpa [TopCat.Sheaf] using
    (inferInstance :
      HasBinaryCoproducts
        (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}))

/- Domain-style sampling for Definition 17.31.6:
- primary domain: naive cotangent complexes of morphisms of ringed spaces;
- sampled owner declarations:
  `inverseImageStructureSheafHomComm`,
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent_X_negOne`,
  `SheafOfModules.RingedSite.naiveCotangent_X_zero`,
  `Algebra.naiveCotangent`;
- best owner abstraction: the source-facing ringed-space complex `NL_f`, obtained as the thin
  specialization of the site-level owner `SheafOfModules.RingedSite.naiveCotangent` to the opens
  site of `X`, along the inverse-image structure-sheaf morphism
  `inverseImageStructureSheafHomComm f`;
- primitive data: only the inverse-image structure sheaf `f⁻¹𝒪_Y` and the induced `Under` object
  `f⁻¹𝒪_Y ⟶ 𝒪_X`;
- derived API: the source-facing notation `NL[f]` for textbook `NL_f` and the degree `-1/0`
  identification lemmas obtained from the site-level owner.

Source/core/bridge triage:
- `source-facing`: the notation `NL[f]`, the Lean surface for textbook
  `NL_f = NL_{\mathcal O_X / f^{-1}\mathcal O_Y}`;
- `core/canonical`: the Chapter 18 site-level owner
  `SheafOfModules.RingedSite.naiveCotangent`;
- `bridge/view`: the specialization from an arbitrary sheaf of `\mathcal A`-algebras to the
  inverse-image structure-sheaf morphism of a ringed-space map.
-/

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

/- Definition 17.31.6: for a morphism of ringed spaces `f : X ⟶ Y`, the naive cotangent complex
`NL_f` is the opens-site specialization of the Chapter 18 site-level owner
`NL_{\mathcal O_X / f^{-1}\mathcal O_Y}` along the canonical inverse-image structure-sheaf
morphism `f^{-1}\mathcal O_Y ⟶ \mathcal O_X`. -/
scoped[AlgebraicGeometry] notation:max "NL[" f "]" =>
  SheafOfModules.RingedSite.naiveCotangent _ <|
    Under.mk (RingedSpace.Hom.inverseImageStructureSheafHomComm f)

end AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

open RingedSpace.Hom

variable {X Y : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})]

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `-1` term of `NL[f]` is the conormal sheaf `\mathcal I/\mathcal I^2` of the
canonical presentation of `\mathcal O_X` over `f^{-1}\mathcal O_Y`. -/
theorem naiveCotangent_X_negOne (f : X ⟶ Y) :
    (NL[f]).X (-1) =
      conormalSource
        (presentationMap _ (Under.mk (inverseImageStructureSheafHomComm f))) := by
  simpa using
    (SheafOfModules.RingedSite.naiveCotangent_X_negOne
      _ (Under.mk (inverseImageStructureSheafHomComm f)))

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `0` term of `NL[f]` is the canonical tensor term
`\mathcal O_X \otimes_{f^{-1}\mathcal O_Y[\mathcal O_X]}
  \Omega_{f^{-1}\mathcal O_Y[\mathcal O_X]/f^{-1}\mathcal O_Y}`. -/
theorem naiveCotangent_X_zero (f : X ⟶ Y) :
    (NL[f]).X 0 =
      conormalTensorTerm
        (presentationBase _ (Under.mk (inverseImageStructureSheafHomComm f)))
        (presentationMap _ (Under.mk (inverseImageStructureSheafHomComm f))) := by
  simpa using
    (SheafOfModules.RingedSite.naiveCotangent_X_zero
      _ (Under.mk (inverseImageStructureSheafHomComm f)))

end AlgebraicGeometry.RingedSpace
