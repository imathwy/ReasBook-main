import Mathlib
import StacksProject_2024.Chap20.Lemma_20_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {ι : Type u}
variable [EnoughInjectives (RingedSpace.Modules X)]
variable [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]

variable (𝒰 : ι → Opens X.carrier)
variable
  (sourceComplexToDerived :
    CochainComplex.Plus (RingedSpace.Modules X) → DerivedCategory (RingedSpace.Modules X))
variable
  (derivedGlobalSections :
    DerivedCategory (RingedSpace.Modules X) ⥤
      CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat)
variable
  (derivedTensorΓ :
    CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat ⥤
      CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat ⥤
        CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat)
variable
  (sourceDerivedTensor :
    CochainComplex.Plus (RingedSpace.Modules X) →
      CochainComplex.Plus (RingedSpace.Modules X) →
        DerivedCategory (RingedSpace.Modules X))
variable
  (tensorComplex :
    CochainComplex.Plus (RingedSpace.Modules X) →
      CochainComplex.Plus (RingedSpace.Modules X) →
        CochainComplex.Plus (RingedSpace.Modules X))
variable
  (cechTensorTotalComplex :
    CochainComplex.Plus (RingedSpace.Modules X) →
      CochainComplex.Plus (RingedSpace.Modules X) →
        CochainComplex.Plus AddCommGrpCat)
variable
  (cechComparison :
    ∀ K : CochainComplex.Plus (RingedSpace.Modules X),
      (moduleCechDerivedFunctor X 𝒰).obj K ⟶
        derivedGlobalSections.obj (sourceComplexToDerived K))
variable
  (derivedCupProduct :
    ∀ K M : CochainComplex.Plus (RingedSpace.Modules X),
      ((derivedTensorΓ.obj
          (derivedGlobalSections.obj (sourceComplexToDerived M))).obj
        (derivedGlobalSections.obj (sourceComplexToDerived K))) ⟶
        derivedGlobalSections.obj (sourceDerivedTensor K M))
variable
  (sourceTensorCounit :
    ∀ K M : CochainComplex.Plus (RingedSpace.Modules X),
      sourceDerivedTensor K M ⟶ sourceComplexToDerived (tensorComplex K M))
variable
  (cechTensorCounit :
    ∀ K M : CochainComplex.Plus (RingedSpace.Modules X),
      ((derivedTensorΓ.obj ((moduleCechDerivedFunctor X 𝒰).obj M)).obj
        ((moduleCechDerivedFunctor X 𝒰).obj K)) ⟶
        (CategoryTheory.boundedBelowCochainComplexToDerivedBelow
          (𝟭 AddCommGrpCat)).obj (cechTensorTotalComplex K M))
variable
  (cechCupProduct :
    ∀ K M : CochainComplex.Plus (RingedSpace.Modules X),
      ((CategoryTheory.boundedBelowCochainComplexToDerivedBelow
          (𝟭 AddCommGrpCat)).obj (cechTensorTotalComplex K M)) ⟶
        (moduleCechDerivedFunctor X 𝒰).obj (tensorComplex K M))

-- Proof sketch: this is the morphism-to-a-point specialization of Lemma `20.31.3`. Replace the
-- two bounded-below complexes by flasque resolutions as in Lemma `20.30.2`, so that both the
-- Čech representatives and the derived global sections are computed by ordinary global sections.
-- The resulting diagram is then the Čech cup-product compatibility square, whose commutativity
-- reduces to Lemma `20.31.3` together with the comparison map of Lemma `20.25.1`.
/-- Lemma 20.31.4: for a ringed space `(X, \mathcal O_X)`, an open covering `\mathcal U`, and
bounded-below complexes `\mathcal K^\bullet` and `\mathcal M^\bullet`, the cup product on derived
global sections is compatible with the Čech cup product. Concretely, if `cechComparison` denotes
the comparison morphism of Lemma 20.25.1 from the total Čech complex to derived global sections,
then the square from
`Tot(\check{\mathcal C}^\bullet(\mathcal U, \mathcal K^\bullet)) \otimes^{\mathbf L}
  Tot(\check{\mathcal C}^\bullet(\mathcal U, \mathcal M^\bullet))`
to
`R\Gamma(X, \mathcal K^\bullet) \otimes^{\mathbf L} R\Gamma(X, \mathcal M^\bullet)`,
down to the Čech cup product and to
`R\Gamma(X, \mathrm{Tot}(\mathcal K^\bullet \otimes_{\mathcal O_X} \mathcal M^\bullet))`,
commutes in the target derived category. -/
theorem cech_tensor_derivedGlobalSections_square_commutes
    (K M : CochainComplex.Plus (RingedSpace.Modules X)) :
    ((derivedTensorΓ.map (cechComparison M)).app
        ((moduleCechDerivedFunctor X 𝒰).obj K)) ≫
      ((derivedTensorΓ.obj
          (derivedGlobalSections.obj (sourceComplexToDerived M))).map
        (cechComparison K)) ≫
      derivedCupProduct K M ≫
      derivedGlobalSections.map (sourceTensorCounit K M) =
    cechTensorCounit K M ≫
      cechCupProduct K M ≫
      cechComparison (tensorComplex K M) := sorry

end

end AlgebraicGeometry.RingedSpace
