import Mathlib
import StacksProject_2024.Chap20.«20_55_7_2»
import StacksProject_2024.Chap20.Lemma_20_55_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)] [BraidedCategory (RingedSpace.Modules X)] [Abelian (RingedSpace.Modules X)]
variable {ℐ : (RingedSpace.Modules X)}

local instance instPreadditiveSheafModules : Preadditive (RingedSpace.Modules X) :=
  SheafOfModules.instPreadditive (RingedSpace.ringCatSheaf X)

/-- The complex representing the tensor product of the Berthelot-Ogus complex `\eta_\mathcal I
K^\bullet` with the quotient module `\mathcal O_X / \mathcal I`. -/
abbrev idealEtaQuotientTensorRepresentative
    (ι : ℐ ⟶ CategoryTheory.MonoidalCategoryStruct.tensorUnit (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) :
    CochainComplex (RingedSpace.Modules X) ℤ :=
  tensorRightCochainComplex (cokernel ι) (idealEtaComplex ι K hK)

-- Proof sketch: this is the defining abbreviation for the complex-level representative of the
-- left-hand side.
/-- The representative of the left-hand side is obtained by tensoring the Berthelot-Ogus complex
with the quotient module `\mathcal O_X / \mathcal I` termwise. -/
theorem idealEtaQuotientTensorRepresentative_def
    (ι : ℐ ⟶ CategoryTheory.MonoidalCategoryStruct.tensorUnit (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K) :
    idealEtaQuotientTensorRepresentative ι K hK =
      tensorRightCochainComplex (cokernel ι) (idealEtaComplex ι K hK) := sorry

-- Proof sketch: represent `Lη_\mathcal I M` by the Berthelot-Ogus complex `η_\mathcal I K^\bullet`
-- of a chosen `\mathcal I`-torsion free model `K^\bullet`, replace the derived tensor with
-- `\mathcal O_X / \mathcal I` by the termwise quotient tensor representative used in the source
-- proof, represent `H^\bullet(M / \mathcal I)` by the Bockstein cohomology complex built from the
-- successive quotient complexes, and then use the stalkwise comparison from More on Algebra
-- `15.96.6` to identify the two derived objects.
/-- Lemma 20.55.8: for a chosen `\mathcal I`-torsion free complex model `K^\bullet`, the derived
tensor product of the Berthelot-Ogus complex `\eta_\mathcal I K^\bullet` with
`\mathcal O_X / \mathcal I` is isomorphic in `D(\mathcal O_X)` to the Bockstein cohomology
complex modeling `H^\bullet(M / \mathcal I)`. Lean records this by asserting the existence of a
quasi-isomorphism between the chosen complex representatives of the two derived objects. -/
theorem idealEtaQuotientTensorRepresentative_exists_quasiIso_to_bocksteinCohomology
    (ι : ℐ ⟶ CategoryTheory.MonoidalCategoryStruct.tensorUnit (RingedSpace.Modules X))
    [locally_principal_regular_ideal_situation ℐ ι]
    (K : CochainComplexModules X) (hK : IsIdealTorsionFreeComplex ι K)
    [∀ i : ℤ, (idealEtaQuotientTensorRepresentative ι K hK).HasHomology i]
    (tensorWithIdealPowerQuotient : ℤ → CochainComplex (RingedSpace.Modules X) ℤ)
    [∀ i : ℤ, (tensorWithIdealPowerQuotient i).HasHomology i]
    (β : ∀ i : ℤ,
      (tensorWithIdealPowerQuotient i).homology i ⟶
        (tensorWithIdealPowerQuotient (i + 1)).homology (i + 1))
    (hβ : ∀ i : ℤ, β i ≫ β (i + 1) = 0)
    [∀ i : ℤ,
      (idealQuotientBocksteinCohomologyComplex tensorWithIdealPowerQuotient β hβ).HasHomology i] :
    ∃ φ : idealEtaQuotientTensorRepresentative ι K hK ⟶
        idealQuotientBocksteinCohomologyComplex tensorWithIdealPowerQuotient β hβ,
      QuasiIso φ := sorry

end AlgebraicGeometry.RingedSpace
