import Books.AConciseCourseInAlgebraicTopology_May_1999.BasedCWComplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1

open CategoryTheory
open HomotopicalAlgebra

noncomputable section

universe u

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

namespace BasedHomotopyClasses

/-- Precomposition respects the based-homotopy relation on representatives. -/
theorem precomposeWellDefined {X Y Z : BasedSpace} (f : X ⟶ Y)
    {g₀ g₁ : Y ⟶ Z} (hg : (basedHomotopySetoid Y Z).r g₀ g₁) :
    (basedHomotopySetoid X Z).r (f ≫ g₀) (f ≫ g₁) := sorry

/-- Precomposition by a based map sends a based homotopy class `[Y, Z]` to the induced class
`[X, Z]`. -/
def precomposeFun {X Y Z : BasedSpace} (f : X ⟶ Y) :
    basedHomotopyClasses Y Z → basedHomotopyClasses X Z :=
  Quotient.map (fun g : Y ⟶ Z ↦ f ≫ g)
    (fun _ _ hg ↦ precomposeWellDefined f hg)

/-- Precomposition preserves the distinguished point given by the constant map. -/
theorem precomposeFun_point {X Y Z : BasedSpace} (f : X ⟶ Y) :
    precomposeFun f (basedHomotopyClasses Y Z).point =
      (basedHomotopyClasses X Z).point := sorry

/-- The pointed map on `[Y, Z]` induced by precomposition with `f : X ⟶ Y`. -/
def precompose {X Y Z : BasedSpace} (f : X ⟶ Y) :
    basedHomotopyClasses Y Z ⟶ basedHomotopyClasses X Z where
  toFun := precomposeFun f
  map_point := precomposeFun_point f

/-- Precomposition by the identity based map is the identity on based homotopy classes. -/
theorem precompose_id {X Z : BasedSpace} :
    ((precompose (𝟙 X) : basedHomotopyClasses X Z ⟶ basedHomotopyClasses X Z)).toFun = id := sorry

/-- Precomposition by a composite agrees with the composite of the induced pointed maps. -/
theorem precompose_comp {X Y W Z : BasedSpace} (f : X ⟶ Y) (g : Y ⟶ W) :
    ((precompose (f ≫ g) : basedHomotopyClasses W Z ⟶ basedHomotopyClasses X Z)).toFun =
      (((precompose g : basedHomotopyClasses W Z ⟶ basedHomotopyClasses Y Z) ≫
        (precompose f : basedHomotopyClasses Y Z ⟶ basedHomotopyClasses X Z))).toFun := sorry

/-- The contravariant pointed-set functor `X ↦ [X, Z]` on based spaces. -/
def functor (Z : BasedSpace) : BasedSpaceᵒᵖ ⥤ Pointed where
  obj X := basedHomotopyClasses X.unop Z
  map f := precompose f.unop
  map_id _ := Pointed.Hom.ext <| precompose_id
  map_comp f g := Pointed.Hom.ext <| precompose_comp g.unop f.unop

/-- The inclusion of based CW complexes into the ambient based-space category. -/
abbrev basedCWComplexInclusion : BasedCWComplex ⥤ BasedSpace :=
  CategoryTheory.ObjectProperty.ι IsBasedCWComplex

/-- The Chapter 22 functor `X ↦ [X, Z]`, restricted to based CW complexes. -/
abbrev onBasedCWComplexes (Z : BasedSpace) : BasedCWComplexᵒᵖ ⥤ Pointed :=
  basedCWComplexInclusion.op ⋙ functor Z

/-- Based-homotopic maps induce the same map on based homotopy classes. -/
theorem map_eq_of_basedHomotopy
    (Z : BasedSpace) {X Y : BasedSpace} {f g : X ⟶ Y} (hfg : basedHomotopyRel f g) :
    (functor Z).map f.op = (functor Z).map g.op := sorry

end BasedHomotopyClasses
