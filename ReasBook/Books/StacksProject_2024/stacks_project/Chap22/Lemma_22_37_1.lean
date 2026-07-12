import StacksProject_2024.Chap13.Lemma_13_7_2
import StacksProject_2024.Chap22.Lemma_22_26_9
import StacksProject_2024.Chap22.Lemma_22_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "DGA" => CochainDGAlgebra R
local notation "Mod_(" A ")" => DifferentialGradedModule A
local notation:25 A " ⟶dga " B => CochainDGAlgebra.Hom A B

section DerivedTensorAlongDGAHom

variable {A B : CochainDGAlgebra R}
variable (φ : CochainDGAlgebra.Hom A B)
variable (QisA : MorphismProperty (K R (Mod_(A))))
  [QisA.IsSaturatedMultiplicativeSystem]
variable (QisB : MorphismProperty (K R (Mod_(B))))
  [QisB.IsSaturatedMultiplicativeSystem]
variable (tensorWithB : DgFunctor R (Mod_(A)) (Mod_(B)))
variable [(tensorWithB.mapK ⋙ QisB.Q).HasLeftDerivedFunctor QisA]
variable [HasZeroObject QisA.Localization] [HasZeroObject QisB.Localization]
variable [HasShift QisA.Localization ℤ] [HasShift QisB.Localization ℤ]
variable [Preadditive QisA.Localization] [Preadditive QisB.Localization]
variable [∀ n : ℤ, (shiftFunctor QisA.Localization n).Additive]
variable [∀ n : ℤ, (shiftFunctor QisB.Localization n).Additive]
variable [Pretriangulated QisA.Localization] [Pretriangulated QisB.Localization]
variable [LTensor[QisA, QisB](tensorWithB).CommShift ℤ]
variable [LTensor[QisA, QisB](tensorWithB).IsTriangulated]
variable [Functor.Full (LTensor[QisA, QisB](tensorWithB))]
variable [Functor.Faithful (LTensor[QisA, QisB](tensorWithB))]

local notation "LT" => LTensor[QisA, QisB](tensorWithB)

set_option linter.unusedVariables false in
/-- In the Chapter `22` DG-algebra-map setting of Lemma `22.37.1`, once the preceding
quasi-isomorphism arguments have supplied full faithfulness of the derived tensor functor
`LTensor[QisA, QisB](tensorWithB)`, an adjunction with the derived restriction-of-scalars functor
`φ.restrictionDerived QisA QisB hRestrictionInverts`, and the zero-kernel property for that
restriction functor, the derived tensor functor is essentially surjective. -/
theorem derivedTensorAlongDGAHom_essSurj
    (hRestrictionInverts : QisB.IsInvertedBy (((φ.restrictDgFunctor).mapK) ⋙ QisA.Q))
    (hAdj : LT ⊣ φ.restrictionDerived QisA QisB hRestrictionInverts)
    (hKernel : (φ.restrictionDerived QisA QisB hRestrictionInverts).kernel ≤ IsZero) :
    Functor.EssSurj LT :=
  Adjunction.essSurj_of_kernel_le_isZero hAdj hKernel

set_option linter.unusedVariables false in
/-- Lemma `22.37.1`: let `φ : (A, d) ⟶ (B, d)` be a homomorphism of differential graded
`R`-algebras. If the Chapter `22` derived tensor functor `LTensor[QisA, QisB](tensorWithB)`,
attached to tensoring with `B`, is fully faithful, left adjoint to the derived
restriction-of-scalars functor `φ.restrictionDerived QisA QisB hRestrictionInverts`, and that
derived restriction functor has
zero kernel, then the derived tensor functor is an equivalence of categories.

This keeps the tagged main statement on the source-facing Chapter `22` DG-algebra owners, while
the proof reuses the canonical adjunction criterion from Chapter `13`. -/
@[stacks 09S6]
theorem derivedTensorAlongDGAHom_isEquivalence
    (hRestrictionInverts : QisB.IsInvertedBy (((φ.restrictDgFunctor).mapK) ⋙ QisA.Q))
    (hAdj : LT ⊣ φ.restrictionDerived QisA QisB hRestrictionInverts)
    (hKernel : (φ.restrictionDerived QisA QisB hRestrictionInverts).kernel ≤ IsZero) :
    Functor.IsEquivalence LT :=
  Adjunction.isEquivalence_of_fullyFaithful_of_kernel_le_isZero hAdj hKernel

end DerivedTensorAlongDGAHom

end
