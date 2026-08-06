import Mathlib.Topology.Homotopy.Contractible
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_4_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.MappingCylinderCofiber
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_2_1

open CategoryTheory
open ContinuousMap

noncomputable section

universe u

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch`: the local owner for a homotopy inverse under the chosen
-- basepoint is `IsCofiberHomotopyEquivalence`. Construction 14.2.2 is therefore formalized by
-- explicit quotient/cofiber/suspension comparison data, with the boundary map given by
-- composition.

/-- A chosen reduced-suspension model for the subspace `A`, consisting of a contractible cone on
`A`, an explicit identification of `A` with the base of that cone, and a quotient model of the
cone by its base realizing the based space `SigmaA`. -/
structure CofibrationBoundarySuspensionModel
    {X : TopCat.{u}} (A : Set X) (SigmaA : BasedSpace) where
  /-- The chosen cone on `A`. -/
  suspensionCone : TopCat.{u}
  /-- The inclusion of `A` as the base of the chosen cone. -/
  suspensionBaseInclusion : C(A, suspensionCone)
  /-- The chosen base inclusion identifies `A` with the corresponding subspace of the cone. -/
  suspensionBaseHomeomorph : A ≃ₜ Set.range suspensionBaseInclusion
  /-- The chosen cone is contractible. -/
  coneContractible : ContractibleSpace suspensionCone
  /-- The quotient of the chosen cone by its base realizes the suspension model `SigmaA`. -/
  suspensionModel :
    ReducedQuotientMap
      suspensionCone
      (Set.range suspensionBaseInclusion)
      SigmaA

instance {X : TopCat.{u}} {A : Set X} {SigmaA : BasedSpace}
    (data : CofibrationBoundarySuspensionModel A SigmaA) :
    ContractibleSpace data.suspensionCone :=
  data.coneContractible

/-- A chosen quotient/cofiber/suspension comparison for the boundary construction attached to a
subset `A ⊆ X`. Besides the quotient model `XA` of `X/A`, the structure explicitly records a
chosen cofiber model `Ci` for the mapping-cylinder cofibration replacing `A ↪ X` and a chosen
reduced-suspension model for `A` whose quotient realizes `SigmaA`. The comparison
`Ci ⟶ XA` is the canonical Chapter 8 map determined by `quotientModel` and `cofiberModel`; the
extra data here is the chosen homotopy inverse and the cofiber-to-suspension projection. -/
structure CofibrationBoundaryFactorization
    (X : TopCat.{u}) (A : Set X) (XA SigmaA Ci : BasedSpace) where
  /-- The chosen quotient model identifying `XA` with the collapse quotient `X/A`. -/
  quotientModel : ReducedQuotientMap X A XA
  /-- The chosen cofiber model `Ci`, realized as a quotient model of the mapping-cylinder
  cofibration replacing `A ↪ X`. -/
  cofiberModel :
    ReducedQuotientMap
      (subsetInclusion A).mappingCylinder
      (mappingCylinderCofiberSubspace A)
      Ci
  /-- The chosen reduced-suspension model on `A` whose quotient realizes `SigmaA`. -/
  suspensionData : CofibrationBoundarySuspensionModel A SigmaA
  /-- A chosen homotopy inverse from the quotient model `XA` back to the cofiber model `Ci`. -/
  quotientToCofiber : XA ⟶ Ci
  /-- The chosen map `XA ⟶ Ci` is a right homotopy inverse to the canonical comparison
  `Ci ⟶ XA`. -/
  quotientToCofiber_right :
    HomotopicUnder
      (quotientToCofiber ≫ _root_.cofiberToQuotient quotientModel cofiberModel)
      (𝟙 XA)
  /-- The chosen map `XA ⟶ Ci` is a left homotopy inverse to the canonical comparison
  `Ci ⟶ XA`. -/
  quotientToCofiber_left :
    HomotopicUnder
      (_root_.cofiberToQuotient quotientModel cofiberModel ≫ quotientToCofiber)
      (𝟙 Ci)
  /-- A chosen map from the mapping-cylinder replacement to the chosen suspension cone whose
  quotient descends to the cofiber projection `Ci ⟶ SigmaA`. -/
  cofiberProjectionLift :
    C((subsetInclusion A).mappingCylinder, suspensionData.suspensionCone)
  /-- The map `cofiberProjectionLift` sends the mapping-cylinder cofibration image into the base
  of the chosen suspension cone. -/
  cofiberProjectionLift_mapsSubspace :
    ∀ ⦃x : (subsetInclusion A).mappingCylinder⦄,
      x ∈ mappingCylinderCofiberSubspace A →
        cofiberProjectionLift x ∈ Set.range suspensionData.suspensionBaseInclusion
  /-- The chosen cofiber projection from the cofiber model `Ci` to the suspension model `SigmaA`
  induced by `cofiberProjectionLift` through `cofiberModel` and the chosen suspension quotient.
  -/
  cofiberProjection : Ci ⟶ SigmaA
  /-- The chosen cofiber projection is induced from `cofiberProjectionLift` after passing to the
  chosen cofiber and suspension quotient models. -/
  cofiberProjection_spec :
    let qCi := cofiberModel.quotientMap
    let qSigma := suspensionData.suspensionModel.quotientMap
    ∀ x : (subsetInclusion A).mappingCylinder,
      cofiberProjection.right.hom (qCi.hom x) =
        qSigma.hom (cofiberProjectionLift x)

namespace CofibrationBoundaryFactorization

/-- The canonical cofiber-to-quotient comparison attached to the chosen quotient and cofiber
models in `CofibrationBoundaryFactorization`. -/
abbrev cofiberToQuotient
    {X : TopCat.{u}} {A : Set X} {XA SigmaA Ci : BasedSpace}
    (data : CofibrationBoundaryFactorization X A XA SigmaA Ci) :
    Ci ⟶ XA :=
  _root_.cofiberToQuotient data.quotientModel data.cofiberModel

/-- The quotient map from the chosen cofiber model of `A ↪ X`. -/
abbrev cofiberQuotientMap
    {X : TopCat.{u}} {A : Set X} {XA SigmaA Ci : BasedSpace}
    (data : CofibrationBoundaryFactorization X A XA SigmaA Ci) :
    (subsetInclusion A).mappingCylinder ⟶ Ci.right :=
  data.cofiberModel.quotientMap

/-- The quotient map realizing the chosen reduced-suspension model `SigmaA`. -/
abbrev suspensionQuotientMap
    {X : TopCat.{u}} {A : Set X} {XA SigmaA Ci : BasedSpace}
    (data : CofibrationBoundaryFactorization X A XA SigmaA Ci) :
    data.suspensionData.suspensionCone ⟶ SigmaA.right :=
  let suspensionModel := data.suspensionData.suspensionModel
  suspensionModel.quotientMap

/-- The underlying continuous map of the chosen cofiber projection `Ci ⟶ SigmaA`. -/
abbrev cofiberProjectionMap
    {X : TopCat.{u}} {A : Set X} {XA SigmaA Ci : BasedSpace}
    (data : CofibrationBoundaryFactorization X A XA SigmaA Ci) :
    Ci.right ⟶ SigmaA.right :=
  data.cofiberProjection.right

/-- The suspension quotient map sends the chosen suspension base to the basepoint of `SigmaA`. -/
@[simp] theorem suspensionQuotientMap_mapsSubspace
    {X : TopCat.{u}} {A : Set X} {XA SigmaA Ci : BasedSpace}
    (data : CofibrationBoundaryFactorization X A XA SigmaA Ci)
    {x : data.suspensionData.suspensionCone}
    (hx : x ∈ Set.range data.suspensionData.suspensionBaseInclusion) :
    data.suspensionQuotientMap.hom x ∈ ({underTopBasepoint SigmaA} : Set SigmaA.right) := by
  let suspensionModel := data.suspensionData.suspensionModel
  exact suspensionModel.mapsSubspace hx

@[simp] theorem cofiberProjection_spec_apply
    {X : TopCat.{u}} {A : Set X} {XA SigmaA Ci : BasedSpace}
    (data : CofibrationBoundaryFactorization X A XA SigmaA Ci)
    (x : (subsetInclusion A).mappingCylinder) :
    data.cofiberProjectionMap.hom (data.cofiberQuotientMap.hom x) =
      data.suspensionQuotientMap.hom (data.cofiberProjectionLift x) := by
  simpa using data.cofiberProjection_spec x

/-- The explicit pair map from the mapping-cylinder replacement pair to the chosen suspension
pair whose quotient descends to `cofiberProjection`. -/
noncomputable def cofiberProjectionPairMap
    {X : TopCat.{u}} {A : Set X} {XA SigmaA Ci : BasedSpace}
    (data : CofibrationBoundaryFactorization X A XA SigmaA Ci) :
    subsetPair
        (subsetInclusion A).mappingCylinder
        (mappingCylinderCofiberSubspace A) ⟶
      basedReducedPair SigmaA where
  hom :=
    TopCat.ofHom data.cofiberProjectionLift ≫ data.suspensionQuotientMap
  map_subspace' := by
    intro x hx
    change
      data.suspensionQuotientMap.hom (data.cofiberProjectionLift x) ∈
        ({underTopBasepoint SigmaA} : Set SigmaA.right)
    exact data.suspensionQuotientMap_mapsSubspace (data.cofiberProjectionLift_mapsSubspace hx)

/-- The cofiber comparison in `CofibrationBoundaryFactorization` is a cofiber homotopy
equivalence. -/
theorem cofiberToQuotient_isCofiberHomotopyEquivalence
    {X : TopCat.{u}} {A : Set X} {XA SigmaA Ci : BasedSpace}
    (data : CofibrationBoundaryFactorization X A XA SigmaA Ci) :
    IsCofiberHomotopyEquivalence data.cofiberToQuotient :=
  isCofiberHomotopyEquivalence_iff.2
    ⟨data.quotientToCofiber, data.quotientToCofiber_right, data.quotientToCofiber_left⟩

/-- The cofiber comparison in `CofibrationBoundaryFactorization` is available as instance API. -/
instance instIsCofiberHomotopyEquivalenceCofiberToQuotient
    {X : TopCat.{u}} {A : Set X} {XA SigmaA Ci : BasedSpace}
    (data : CofibrationBoundaryFactorization X A XA SigmaA Ci) :
    IsCofiberHomotopyEquivalence data.cofiberToQuotient :=
  data.cofiberToQuotient_isCofiberHomotopyEquivalence

end CofibrationBoundaryFactorization

/-- Construction 14.2.2. If `A` is nonempty so that `X/A` carries the canonical based-space owner
`collapseSubsetBasedSpace X A hA`, and if `SigmaA` is realized by chosen reduced-suspension data
for `A`, then the topological boundary map
`∂ : collapseSubsetBasedSpace X A hA ⟶ SigmaA` is obtained by composing a chosen homotopy
inverse `X/A ⟶ Ci` with the cofiber projection `Ci ⟶ ΣA` induced by that suspension data. -/
noncomputable def cofibrationTopologicalBoundaryMap
    {X : TopCat.{u}} {A : Set X} (hA : A.Nonempty) {SigmaA Ci : BasedSpace}
    (data :
      CofibrationBoundaryFactorization X A (collapseSubsetBasedSpace X A hA) SigmaA Ci) :
    collapseSubsetBasedSpace X A hA ⟶ SigmaA :=
  data.quotientToCofiber ≫ data.cofiberProjection
