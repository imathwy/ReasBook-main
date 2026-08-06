import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.MappingCylinderCofiber
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_2_1

open CategoryTheory

noncomputable section

universe u

-- Semantic recall: `lean_leansearch` again surfaced only model-categorical cofibration/cofiber
-- APIs. The verified local owners for the source are `ReducedQuotientMap` for based quotient
-- models of `X/A`, the mapping-cylinder factorization of `subsetInclusion A`, and
-- `IsCofiberHomotopyEquivalence` for based homotopy equivalences under the chosen basepoint.

/-- The projection `M_(A ↪ X) ⟶ X` descends to a continuous map from the canonical quotient model
of `C_i` to the canonical quotient model of `X/A`. -/
theorem mappingCylinderCofiberToQuotient_respects
    {X : TopCat.{u}} (A : Set X)
    {z w : (subsetInclusion A).mappingCylinder}
    (hzw : collapseSubsetSetoid (mappingCylinderCofiberSubspace A) z w) :
    collapseSubsetQuotientMap A (mappingCylinderProjection (subsetInclusion A) z) =
      collapseSubsetQuotientMap A (mappingCylinderProjection (subsetInclusion A) w) :=
  sorry

variable {X : TopCat.{u}} {A : Set X} {XA Ci : BasedSpace}

variable (QX : ReducedQuotientMap X A XA)
variable
  (QC :
    ReducedQuotientMap
      (subsetInclusion A).mappingCylinder
      (mappingCylinderCofiberSubspace A)
      Ci)

/-- The canonical quotient comparison from the mapping-cylinder cofiber model of `A ↪ X` to the
canonical quotient model `X/A`. -/
def mappingCylinderCofiberToQuotientCanonical (A : Set X) :
    C(
      collapseSubsetType (subsetInclusion A).mappingCylinder
        (mappingCylinderCofiberSubspace A),
      collapseSubsetType X A
    ) where
  toFun :=
    Quotient.lift
      (fun z : (subsetInclusion A).mappingCylinder ↦
        collapseSubsetQuotientMap A (mappingCylinderProjection (subsetInclusion A) z))
      (fun z w hzw ↦ mappingCylinderCofiberToQuotient_respects A hzw)
  continuous_toFun := sorry

/-- Transporting the canonical quotient comparison through chosen quotient models for `C_i` and
`X/A` gives the source-facing map `ψ : C_i ⟶ X/A`. -/
def cofiberToQuotientContinuousMap :
    C(Ci.right, XA.right) :=
  let eX := QX.quotientHomeomorph
  let eC := QC.quotientHomeomorph
  let fromQuotient : C(collapseSubsetType X A, XA.right) :=
    ⟨eX.symm, eX.symm.continuous_toFun⟩
  let toCofiber :
      C(
        Ci.right,
        collapseSubsetType (subsetInclusion A).mappingCylinder
          (mappingCylinderCofiberSubspace A)
      ) :=
    ⟨eC, eC.continuous_toFun⟩
  fromQuotient.comp ((mappingCylinderCofiberToQuotientCanonical A).comp toCofiber)

/-- The transported quotient comparison preserves the distinguished basepoints of the chosen
cofiber and quotient models. -/
theorem cofiberToQuotientContinuousMap_w :
    Ci.hom ≫ TopCat.ofHom (cofiberToQuotientContinuousMap QX QC) = XA.hom := sorry

/-- The quotient comparison `ψ : C_i ⟶ X/A` between chosen based models of the cofiber and the
quotient. -/
def cofiberToQuotient :
    Ci ⟶ XA :=
  Under.homMk
    (TopCat.ofHom (cofiberToQuotientContinuousMap QX QC))
    (cofiberToQuotientContinuousMap_w QX QC)

/-- The underlying map of `cofiberToQuotient QX QC` is `cofiberToQuotientContinuousMap QX QC`. -/
@[simp] theorem cofiberToQuotient_right :
    (cofiberToQuotient QX QC).right = TopCat.ofHom (cofiberToQuotientContinuousMap QX QC) :=
  rfl

/-- Lemma 8.4.9. If the inclusion `subsetInclusion A : A ↪ X` is a cofibration, then the quotient
map `ψ : C_i ⟶ X/A`, formalized as `cofiberToQuotient QX QC` between a chosen based cofiber model
`Ci` of the mapping-cylinder replacement and a chosen based quotient model `XA` of `X/A`, is a
based homotopy equivalence. -/
theorem cofiberToQuotient_isBasedHomotopyEquivalence
    (hi : IsCofibration (subsetInclusion A)) :
    IsCofiberHomotopyEquivalence (cofiberToQuotient QX QC) := sorry

/-- For a cofibration `subsetInclusion A : A ↪ X`, the quotient comparison
`cofiberToQuotient QX QC : C_i ⟶ X/A` is available to typeclass search as a based homotopy
equivalence. -/
instance cofiberToQuotient.instIsCofiberHomotopyEquivalence
    (hi : IsCofibration (subsetInclusion A)) :
    IsCofiberHomotopyEquivalence (cofiberToQuotient QX QC) :=
  cofiberToQuotient_isBasedHomotopyEquivalence QX QC hi
