import Mathlib.Topology.Homotopy.HSpaces
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_4

open CategoryTheory
open scoped HomotopyClasses Topology.Homotopy

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

/-- Postcomposition respects the based-homotopy relation on representatives. -/
theorem basedHomotopyClassesPostcompose_wellDefined (Z : BasedSpace) {X Y : BasedSpace}
    (g : X ⟶ Y) {f₀ f₁ : Z ⟶ X} (hf : (basedHomotopySetoid Z X).r f₀ f₁) :
    (basedHomotopySetoid Z Y).r (f₀ ≫ g) (f₁ ≫ g) := sorry

/-- Postcomposition by a based map sends a based homotopy class `Ho*[Z, X]` to the induced class
`Ho*[Z, Y]`. -/
def basedHomotopyClassesPostcomposeFun (Z : BasedSpace) {X Y : BasedSpace} (g : X ⟶ Y) :
    Ho*[Z, X] → Ho*[Z, Y] :=
  Quotient.map (fun f : Z ⟶ X ↦ f ≫ g)
    (fun _ _ hf ↦ basedHomotopyClassesPostcompose_wellDefined Z g hf)

/-- Postcomposition preserves the distinguished point represented by the constant based map. -/
theorem basedHomotopyClassesPostcomposeFun_point (Z : BasedSpace) {X Y : BasedSpace}
    (g : X ⟶ Y) :
    basedHomotopyClassesPostcomposeFun Z g (Ho*[Z, X]).point = (Ho*[Z, Y]).point := sorry

/-- The pointed map on `Ho*[Z, X]` induced by postcomposition with `g : X ⟶ Y`. -/
def basedHomotopyClassesPostcompose (Z : BasedSpace) {X Y : BasedSpace} (g : X ⟶ Y) :
    Ho*[Z, X] ⟶ Ho*[Z, Y] where
  toFun := basedHomotopyClassesPostcomposeFun Z g
  map_point := basedHomotopyClassesPostcomposeFun_point Z g

/-- Pointwise loop multiplication of based maps `Z ⟶ Ωᵇ X`. -/
def loopBasedMapMul {Z X : BasedSpace} (f g : Z ⟶ Ωᵇ X) : Z ⟶ Ωᵇ X :=
  Under.homMk
    (TopCat.ofHom
      { toFun := fun z ↦ HSpace.hmul (f.right.hom z, g.right.hom z)
        continuous_toFun := sorry })
    sorry

/-- Pointwise loop inversion of a based map `Z ⟶ Ωᵇ X`. -/
def loopBasedMapInv {Z X : BasedSpace} (f : Z ⟶ Ωᵇ X) : Z ⟶ Ωᵇ X :=
  Under.homMk
    (TopCat.ofHom
      { toFun := fun z ↦ (f.right.hom z).symm
        continuous_toFun := sorry })
    sorry

/-- Pointwise loop multiplication descends to based homotopy classes. -/
theorem basedHomotopyClassesLoopMul_wellDefined {Z X : BasedSpace}
    {f₀ f₁ g₀ g₁ : Z ⟶ Ωᵇ X}
    (hf : (basedHomotopySetoid Z (Ωᵇ X)).r f₀ f₁)
    (hg : (basedHomotopySetoid Z (Ωᵇ X)).r g₀ g₁) :
    (basedHomotopySetoid Z (Ωᵇ X)).r (loopBasedMapMul f₀ g₀) (loopBasedMapMul f₁ g₁) := sorry

/-- Pointwise loop inversion descends to based homotopy classes. -/
theorem basedHomotopyClassesLoopInv_wellDefined {Z X : BasedSpace}
    {f₀ f₁ : Z ⟶ Ωᵇ X} (hf : (basedHomotopySetoid Z (Ωᵇ X)).r f₀ f₁) :
    (basedHomotopySetoid Z (Ωᵇ X)).r (loopBasedMapInv f₀) (loopBasedMapInv f₁) := sorry

/-- Multiplication on `Ho*[Z, Ωᵇ X]` induced by pointwise loop multiplication. -/
def basedHomotopyClassesLoopMul (Z X : BasedSpace) : Ho*[Z, Ωᵇ X] → Ho*[Z, Ωᵇ X] → Ho*[Z, Ωᵇ X] :=
  Quotient.map₂
    (fun f g : Z ⟶ Ωᵇ X ↦ loopBasedMapMul f g)
    (fun _ _ hf _ _ hg ↦ basedHomotopyClassesLoopMul_wellDefined hf hg)

/-- Inversion on `Ho*[Z, Ωᵇ X]` induced by pointwise path reversal. -/
def basedHomotopyClassesLoopInv (Z X : BasedSpace) : Ho*[Z, Ωᵇ X] → Ho*[Z, Ωᵇ X] :=
  Quotient.map
    (fun f : Z ⟶ Ωᵇ X ↦ loopBasedMapInv f)
    (fun _ _ hf ↦ basedHomotopyClassesLoopInv_wellDefined hf)

/-- The distinguished point is the unit of the loop-class group `Ho*[Z, Ωᵇ X]`. -/
noncomputable instance basedHomotopyClassesLoopOne (Z X : BasedSpace) : One (Ho*[Z, Ωᵇ X]) where
  one := (Ho*[Z, Ωᵇ X]).point

/-- Pointwise loop multiplication gives multiplication on `Ho*[Z, Ωᵇ X]`. -/
noncomputable instance basedHomotopyClassesLoopMulInst (Z X : BasedSpace) :
    Mul (Ho*[Z, Ωᵇ X]) where
  mul := basedHomotopyClassesLoopMul Z X

/-- Pointwise loop inversion gives inversion on `Ho*[Z, Ωᵇ X]`. -/
noncomputable instance basedHomotopyClassesLoopInvInst (Z X : BasedSpace) :
    Inv (Ho*[Z, Ωᵇ X]) where
  inv := basedHomotopyClassesLoopInv Z X

/-- The based homotopy classes `Ho*[Z, Ωᵇ X]` carry their canonical group structure. -/
noncomputable instance basedHomotopyClassesLoopGroup (Z X : BasedSpace) : Group (Ho*[Z, Ωᵇ X]) where
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  inv_mul_cancel := sorry

/-- The based homotopy classes `Ho*[Z, Ωᵇ Ωᵇ X]` carry their canonical commutative-group
structure. -/
noncomputable instance basedHomotopyClassesDoubleLoopCommGroup (Z X : BasedSpace) :
    CommGroup (Ho*[Z, Ωᵇ (Ωᵇ X)]) where
  mul := basedHomotopyClassesLoopMul Z (Ωᵇ X)
  one := (Ho*[Z, Ωᵇ (Ωᵇ X)]).point
  inv := basedHomotopyClassesLoopInv Z (Ωᵇ X)
  mul_comm := sorry
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  inv_mul_cancel := sorry

/-- Postcomposition by a based map between loop spaces induces a group homomorphism on
`Ho*[Z, -]`. -/
def basedHomotopyClassesPostcomposeLoopHom (Z : BasedSpace) {X Y : BasedSpace}
    (g : Ωᵇ X ⟶ Ωᵇ Y) : Ho*[Z, Ωᵇ X] →* Ho*[Z, Ωᵇ Y] where
  toFun := (basedHomotopyClassesPostcompose Z g).toFun
  map_one' := sorry
  map_mul' := sorry

/-- Postcomposition by a based map between double loop spaces induces a commutative-group
homomorphism on `Ho*[Z, -]`. -/
def basedHomotopyClassesPostcomposeDoubleLoopHom (Z : BasedSpace) {X Y : BasedSpace}
    (g : Ωᵇ (Ωᵇ X) ⟶ Ωᵇ (Ωᵇ Y)) : Ho*[Z, Ωᵇ (Ωᵇ X)] →* Ho*[Z, Ωᵇ (Ωᵇ Y)] where
  toFun := (basedHomotopyClassesPostcompose Z g).toFun
  map_one' := sorry
  map_mul' := sorry
