import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Adjunction_8_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.SuspensionSphere

open CategoryTheory
open scoped BasedSpace

noncomputable section

universe u

/-- The Chapter 11 two-point pointed space `sphereZeroPointedSpace`, viewed through the Chapter 8
based-space owner after lifting its carrier to universe `u`, so it can serve as the unit object
`S⁰` for smash-product constructions in any ambient universe. -/
abbrev sphereZero : BasedSpace.{u} :=
  (PointedCompactlyGenerated.of
      (CompactlyGenerated.of (ULift.{u} Bool))
      (ULift.up sphereZeroPointedSpace.point)).toBasedSpace

/-- The chosen basepoint of `sphereZero` is `false`. -/
@[simp] theorem underTopBasepoint_sphereZero :
    underTopBasepoint sphereZero = ULift.up false := by
  change ULift.up sphereZeroPointedSpace.point = ULift.up false
  simp

/-- The nonbasepoint of `sphereZero`, representing the second point of `S⁰`. -/
abbrev sphereZeroNonbasepoint : sphereZero.right := ULift.up true

/-- The raw triple-representative used to rebracket a smash product from the left-associated form
to the right-associated form. -/
def smashProductAssocRaw
    (X Y Z : BasedSpace) :
    (X.right × Y.right) × Z.right → (X ∧ (Y ∧ Z)).right
  | ((x, y), z) => smashProductMk X (Y ∧ Z) (x, smashProductMk Y Z (y, z))

/-- Rebracketing on a fixed outer coordinate respects the inner smash-product relation. -/
theorem smashProductAssocInner_respects
    (X Y Z : BasedSpace) (z : Z.right) :
    ∀ ⦃p q : X.right × Y.right⦄,
      smashProductRel X Y p q →
        smashProductAssocRaw X Y Z (p, z) =
          smashProductAssocRaw X Y Z (q, z) := sorry

/-- The intermediate map used to define the smash-product associator on quotient representatives. -/
def smashProductAssocInner
    (X Y Z : BasedSpace) :
    (X ∧ Y).right × Z.right → (X ∧ (Y ∧ Z)).right
  | (p, z) =>
      Quotient.lift
        (fun q : X.right × Y.right ↦ smashProductAssocRaw X Y Z (q, z))
        (smashProductAssocInner_respects X Y Z z)
        p

/-- The intermediate rebracketing map respects the outer smash-product relation. -/
theorem smashProductAssoc_respects
    (X Y Z : BasedSpace) :
    ∀ ⦃p q : (X ∧ Y).right × Z.right⦄,
      smashProductRel (X ∧ Y) Z p q →
        smashProductAssocInner X Y Z p = smashProductAssocInner X Y Z q := sorry

/-- Rebracketing a left-associated smash product to a right-associated smash product is
continuous. -/
theorem smashProductAssocContinuous
    (X Y Z : BasedSpace) :
    Continuous
      (Quotient.lift
        (smashProductAssocInner X Y Z)
        (smashProductAssoc_respects X Y Z) :
          ((X ∧ Y) ∧ Z).right → (X ∧ (Y ∧ Z)).right) := sorry

/-- The continuous map that rebrackets a left-associated smash product to the right-associated
smash product. -/
def smashProductAssocContinuousMap
    (X Y Z : BasedSpace) :
    C(((X ∧ Y) ∧ Z).right, (X ∧ (Y ∧ Z)).right) :=
  ⟨Quotient.lift
      (smashProductAssocInner X Y Z)
      (smashProductAssoc_respects X Y Z),
    smashProductAssocContinuous X Y Z⟩

/-- The smash-product associator preserves the chosen basepoint. -/
theorem smashProductAssoc_w
    (X Y Z : BasedSpace) :
    ((X ∧ Y) ∧ Z).hom ≫ TopCat.ofHom (smashProductAssocContinuousMap X Y Z) =
      (X ∧ (Y ∧ Z)).hom := sorry

/-- The based map rebracketing `(X ∧ Y) ∧ Z` to `X ∧ (Y ∧ Z)`. -/
def smashProductAssoc
    (X Y Z : BasedSpace) :
    (X ∧ Y) ∧ Z ⟶ X ∧ (Y ∧ Z) :=
  Under.homMk
    (TopCat.ofHom (smashProductAssocContinuousMap X Y Z))
    (smashProductAssoc_w X Y Z)

/-- The raw map from `sphereZero ∧ X` to `X` sending the nonbasepoint of `sphereZero` to the
identity on `X` and the basepoint of `sphereZero` to the basepoint of `X`. -/
def smashProductLeftUnitRaw
    (X : BasedSpace) :
    sphereZero.right × X.right → X.right
  | (b, x) => cond b.down x (underTopBasepoint X)

/-- The left-unit raw map respects the smash-product relation. -/
theorem smashProductLeftUnitRaw_respects
    (X : BasedSpace) :
    ∀ ⦃p q : sphereZero.right × X.right⦄,
      smashProductRel sphereZero X p q →
        smashProductLeftUnitRaw X p = smashProductLeftUnitRaw X q := sorry

/-- The left-unit map on `sphereZero ∧ X` is continuous. -/
theorem smashProductLeftUnitContinuous
    (X : BasedSpace) :
    Continuous
      (Quotient.lift
        (smashProductLeftUnitRaw X)
        (smashProductLeftUnitRaw_respects X) :
          (sphereZero ∧ X).right → X.right) := sorry

/-- The continuous map on `sphereZero ∧ X` realizing the left unit. -/
def smashProductLeftUnitContinuousMap
    (X : BasedSpace) :
    C((sphereZero ∧ X).right, X.right) :=
  ⟨Quotient.lift
      (smashProductLeftUnitRaw X)
      (smashProductLeftUnitRaw_respects X),
    smashProductLeftUnitContinuous X⟩

/-- The left-unit map on `sphereZero ∧ X` preserves the chosen basepoint. -/
theorem smashProductLeftUnit_w
    (X : BasedSpace) :
    (sphereZero ∧ X).hom ≫ TopCat.ofHom (smashProductLeftUnitContinuousMap X) = X.hom := sorry

/-- The based map `sphereZero ∧ X ⟶ X` implementing the left unit for the smash product. -/
def smashProductLeftUnit
    (X : BasedSpace) :
    sphereZero ∧ X ⟶ X :=
  Under.homMk
    (TopCat.ofHom (smashProductLeftUnitContinuousMap X))
    (smashProductLeftUnit_w X)

/-- The raw map from `X ∧ sphereZero` to `X` sending the nonbasepoint of `sphereZero` to the
identity on `X` and the basepoint of `sphereZero` to the basepoint of `X`. -/
def smashProductRightUnitRaw
    (X : BasedSpace) :
    X.right × sphereZero.right → X.right
  | (x, b) => cond b.down x (underTopBasepoint X)

/-- The right-unit raw map respects the smash-product relation. -/
theorem smashProductRightUnitRaw_respects
    (X : BasedSpace) :
    ∀ ⦃p q : X.right × sphereZero.right⦄,
      smashProductRel X sphereZero p q →
        smashProductRightUnitRaw X p = smashProductRightUnitRaw X q := sorry

/-- The right-unit map on `X ∧ sphereZero` is continuous. -/
theorem smashProductRightUnitContinuous
    (X : BasedSpace) :
    Continuous
      (Quotient.lift
        (smashProductRightUnitRaw X)
        (smashProductRightUnitRaw_respects X) :
          (X ∧ sphereZero).right → X.right) := sorry

/-- The continuous map on `X ∧ sphereZero` realizing the right unit. -/
def smashProductRightUnitContinuousMap
    (X : BasedSpace) :
    C((X ∧ sphereZero).right, X.right) :=
  ⟨Quotient.lift
      (smashProductRightUnitRaw X)
      (smashProductRightUnitRaw_respects X),
    smashProductRightUnitContinuous X⟩

/-- The right-unit map on `X ∧ sphereZero` preserves the chosen basepoint. -/
theorem smashProductRightUnit_w
    (X : BasedSpace) :
    (X ∧ sphereZero).hom ≫ TopCat.ofHom (smashProductRightUnitContinuousMap X) = X.hom := sorry

/-- The based map `X ∧ sphereZero ⟶ X` implementing the right unit for the smash product. -/
def smashProductRightUnit
    (X : BasedSpace) :
    X ∧ sphereZero ⟶ X :=
  Under.homMk
    (TopCat.ofHom (smashProductRightUnitContinuousMap X))
    (smashProductRightUnit_w X)
