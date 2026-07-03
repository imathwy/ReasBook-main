import Mathlib
import StacksProject_2024.Chap15.Lemma_15_92_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
private abbrev derivedCompleteInclusion (I : Ideal A) :=
  (DerivedCategory.derivedCompleteObjectProperty I).ι
private abbrev derivedCompleteLeftAdjoint (I : Ideal A) (hI : I.FG) :
    DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory :=
  @Functor.leftAdjoint _ _ _ _ (derivedCompleteInclusion I)
    (derivedCompleteInclusion_isRightAdjoint_of_fg I hI)

private abbrev derivedCompleteAdjunction (I : Ideal A) (hI : I.FG) :
    derivedCompleteLeftAdjoint I hI ⊣ derivedCompleteInclusion I :=
  @Adjunction.ofIsRightAdjoint _ _ _ _ (derivedCompleteInclusion I)
    (derivedCompleteInclusion_isRightAdjoint_of_fg I hI)

/-- Remark 15.92.11: the derived completion endofunctor on `D(A)` is the composite of the chosen
left adjoint to the inclusion `D_comp(A, I) ⥤ D(A)` with that inclusion, for a finitely generated
ideal `I ⊆ A`. Its value on `K` is the textbook object denoted `K^∧`. -/
abbrev derivedCompletion (I : Ideal A) (hI : I.FG) : DMod ⥤ DMod :=
  derivedCompleteLeftAdjoint I hI ⋙ derivedCompleteInclusion I

/-- The derived completion `K^∧` of an object `K` of `D(A)`. -/
abbrev derivedCompletionOf (I : Ideal A) (hI : I.FG) (K : DMod) : DMod :=
  (derivedCompletion I hI).obj K

notation:max K:max "^∧[" I:max ", " hI:max "]" => derivedCompletionOf I hI K

/-- The canonical map from `K` to its derived completion `K^∧`. -/
abbrev toDerivedCompletion (I : Ideal A) (hI : I.FG) (K : DMod) :
    K ⟶ K^∧[I, hI] :=
  (derivedCompleteAdjunction I hI).unit.app K

/-- The derived completion of `K` is derived complete with respect to `I`. -/
theorem derivedCompletionOf_isDerivedComplete
    (I : Ideal A) (hI : I.FG) (K : DMod) :
    (K^∧[I, hI]).IsDerivedCompleteWithRespectTo I :=
  ((derivedCompleteLeftAdjoint I hI).obj K).property

end

end DerivedCategory
