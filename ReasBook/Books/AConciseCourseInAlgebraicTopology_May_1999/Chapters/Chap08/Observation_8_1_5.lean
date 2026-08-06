import Mathlib.Topology.Connected.PathConnected
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Adjunction_8_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1

open CategoryTheory
open scoped HomotopyClasses

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall: `lean_leansearch` surfaced `ZerothHomotopy` as the canonical owner for path
-- components. In this chapter the source-faithful owner for the based mapping space `F(X, Y)` is
-- the existing `underBasedMapSpace X Y`.

namespace underBasedMapSpace

variable {X Y : BasedSpace}

/-- A point of `underBasedMapSpace X Y` determines a morphism of based spaces `X ⟶ Y`. -/
theorem toBasedMap_w (f : underBasedMapSpace X Y) :
    X.hom ≫ TopCat.ofHom f.1 = Y.hom := sorry

/-- A point of `underBasedMapSpace X Y` determines a morphism of based spaces `X ⟶ Y`. -/
def toBasedMap (f : underBasedMapSpace X Y) : X ⟶ Y :=
  Under.homMk (TopCat.ofHom f.1) (toBasedMap_w f)

end underBasedMapSpace

/-- Forgetting the commuting-triangle proof identifies a morphism `X ⟶ Y` with the corresponding
point of `underBasedMapSpace X Y`. -/
def homToUnderBasedMapSpace (X Y : BasedSpace) :
    (X ⟶ Y) → underBasedMapSpace X Y :=
  fun f ↦ ⟨f.right.hom, fundamentalGroupFunctorMap_basepoint f⟩

/-- Converting a based map to a morphism of based spaces and back recovers the original point of
`underBasedMapSpace X Y`. -/
theorem homToUnderBasedMapSpace_leftInverse (X Y : BasedSpace) :
    Function.LeftInverse (underBasedMapSpace.toBasedMap) (homToUnderBasedMapSpace X Y) := sorry

/-- Forgetting the commuting-triangle proof after turning a point of `underBasedMapSpace X Y` into
a morphism recovers the original morphism. -/
theorem homToUnderBasedMapSpace_rightInverse (X Y : BasedSpace) :
    Function.RightInverse (underBasedMapSpace.toBasedMap) (homToUnderBasedMapSpace X Y) := sorry

/-- Morphisms `X ⟶ Y` in `Under (⊤_ TopCat)` are equivalent to points of `underBasedMapSpace X Y`.
-/
def homEquivUnderBasedMapSpace (X Y : BasedSpace) :
    (X ⟶ Y) ≃ underBasedMapSpace X Y where
  toFun := homToUnderBasedMapSpace X Y
  invFun := underBasedMapSpace.toBasedMap
  left_inv := homToUnderBasedMapSpace_leftInverse X Y
  right_inv := homToUnderBasedMapSpace_rightInverse X Y

/-- The path-component class of a point of `underBasedMapSpace X Y`. -/
def underBasedMapSpacePathClass (X Y : BasedSpace) :
    underBasedMapSpace X Y → ZerothHomotopy (underBasedMapSpace X Y) :=
  Quotient.mk (pathSetoid (underBasedMapSpace X Y))

/-- A based homotopy class determines a path component of `underBasedMapSpace X Y`. -/
theorem underBasedMapSpacePathClass_eq_of_basedHomotopy
    {X Y : BasedSpace} {f g : X ⟶ Y} (hfg : (basedHomotopySetoid X Y).r f g) :
    underBasedMapSpacePathClass X Y (homEquivUnderBasedMapSpace X Y f) =
      underBasedMapSpacePathClass X Y (homEquivUnderBasedMapSpace X Y g) := sorry

/-- A path in `underBasedMapSpace X Y` yields a single based homotopy class of representatives. -/
theorem basedHomotopyClass_eq_of_joined
    {X Y : BasedSpace} {f g : underBasedMapSpace X Y} (hfg : Joined f g) :
    (Quotient.mk (basedHomotopySetoid X Y) ((homEquivUnderBasedMapSpace X Y).symm f) :
      Ho*[X, Y]) =
      Quotient.mk (basedHomotopySetoid X Y) ((homEquivUnderBasedMapSpace X Y).symm g) := sorry

/-- The quotient map from based homotopy classes of based maps to path components of
`underBasedMapSpace X Y`. -/
def basedHomotopyClassToZerothHomotopyBasedMappingSpace (X Y : BasedSpace) :
    Ho*[X, Y] → ZerothHomotopy (underBasedMapSpace X Y) :=
  Quotient.lift
    (fun f : X ⟶ Y ↦ underBasedMapSpacePathClass X Y (homEquivUnderBasedMapSpace X Y f))
    (fun _ _ hfg ↦ underBasedMapSpacePathClass_eq_of_basedHomotopy hfg)

/-- The quotient map from path components of `underBasedMapSpace X Y` to based homotopy classes of
based maps. -/
def zerothHomotopyBasedMappingSpaceToBasedHomotopyClass (X Y : BasedSpace) :
    ZerothHomotopy (underBasedMapSpace X Y) → Ho*[X, Y] :=
  Quotient.lift
    (fun f : underBasedMapSpace X Y ↦
      (Quotient.mk (basedHomotopySetoid X Y) ((homEquivUnderBasedMapSpace X Y).symm f) :
        Ho*[X, Y]))
    (fun _ _ hfg ↦ basedHomotopyClass_eq_of_joined hfg)

/-- The path-component map and class map are inverse on based homotopy classes. -/
theorem basedHomotopyClassToZerothHomotopyBasedMappingSpace_left_inv (X Y : BasedSpace) :
    Function.LeftInverse
      (zerothHomotopyBasedMappingSpaceToBasedHomotopyClass X Y)
      (basedHomotopyClassToZerothHomotopyBasedMappingSpace X Y) := sorry

/-- The path-component map and class map are inverse on path components of
`underBasedMapSpace X Y`. -/
theorem basedHomotopyClassToZerothHomotopyBasedMappingSpace_right_inv (X Y : BasedSpace) :
    Function.RightInverse
      (zerothHomotopyBasedMappingSpaceToBasedHomotopyClass X Y)
      (basedHomotopyClassToZerothHomotopyBasedMappingSpace X Y) := sorry

/-- Observation 8.1.5: the set `[X,Y]` of based homotopy classes is naturally `π₀` of the based
mapping space, formalized here as the path-component quotient of `underBasedMapSpace X Y`. -/
def basedHomotopyClassesEquivPi0BasedMappingSpace (X Y : BasedSpace) :
    Ho*[X, Y] ≃ ZerothHomotopy (underBasedMapSpace X Y) where
  toFun := basedHomotopyClassToZerothHomotopyBasedMappingSpace X Y
  invFun := zerothHomotopyBasedMappingSpaceToBasedHomotopyClass X Y
  left_inv := basedHomotopyClassToZerothHomotopyBasedMappingSpace_left_inv X Y
  right_inv := basedHomotopyClassToZerothHomotopyBasedMappingSpace_right_inv X Y

/-- Applying `basedHomotopyClassesEquivPi0BasedMappingSpace` to the class of a based map returns
the path component of the corresponding point of `underBasedMapSpace X Y`. -/
theorem basedHomotopyClassesEquivPi0BasedMappingSpace_apply
    (X Y : BasedSpace) (f : X ⟶ Y) :
    basedHomotopyClassesEquivPi0BasedMappingSpace X Y
      ((Quotient.mk (basedHomotopySetoid X Y) f) : Ho*[X, Y]) =
        underBasedMapSpacePathClass X Y (homEquivUnderBasedMapSpace X Y f) := sorry
