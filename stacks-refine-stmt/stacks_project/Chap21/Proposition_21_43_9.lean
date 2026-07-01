import Mathlib
import stacks_project.Chap21.Definition_21_43_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe w uC vC uD vD uD' vD'

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{uD} D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{uC})
variable
  (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

local notation "QCP" => isQuasiCoherent 𝒪 RGamma derivedRestrict comparison
local notation "QCoh" => QC 𝒪 RGamma derivedRestrict comparison

-- Proof sketch: this is the strict-fullness assertion in the proposition. In the intended
-- site-theoretic situation it comes from the triangulated-object-property description of
-- `QC(\mathcal O)` and the fact that the defining comparison maps are invariant under
-- isomorphism.
/-- Proposition 21.43.9 (1): the quasi-coherent subcategory `QC(\mathcal O)` is strictly full,
equivalently the defining object property is closed under isomorphisms in `D(\mathcal O)`. -/
instance qc_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms QCP := sorry

-- Proof sketch: the proposition asserts that `QC(\mathcal O)` is saturated. In the intended
-- proof, one combines the triangulated description of `QC(\mathcal O)` with the closure under
-- retracts coming from the quasi-coherent cohomology criterion.
/-- Proposition 21.43.9 (2): the quasi-coherent subcategory `QC(\mathcal O)` is saturated, i.e.
stable under retracts in `D(\mathcal O)`. -/
instance qc_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts QCP := sorry

-- Proof sketch: the proposition identifies `QC(\mathcal O)` as a triangulated subcategory. In the
-- intended site-theoretic proof, this follows from the quasi-coherent cohomology characterization
-- and the weak-Serre stability of quasi-coherent modules.
/-- Proposition 21.43.9 (3): the quasi-coherent subcategory `QC(\mathcal O)` is triangulated. -/
instance qc_isTriangulated :
    ObjectProperty.IsTriangulated QCP := sorry

-- Proof sketch: the proposition states that `QC(\mathcal O)` is preserved by arbitrary direct
-- sums. In the intended proof, one uses the quasi-coherent cohomology description together with
-- direct-sum closure of quasi-coherent modules and commutation of cohomology with coproducts.
/-- Proposition 21.43.9 (4): the quasi-coherent subcategory `QC(\mathcal O)` is closed under
arbitrary `ι`-indexed direct sums. -/
instance qc_isClosedUnderDirectSums (ι : Type w) :
    ObjectProperty.IsClosedUnderColimitsOfShape QCP (Discrete ι) := sorry

-- Proof sketch: apply Brown representability, in the form of Lemma `13.39.1`, to the Brown set
-- constructed in the preceding lemmas for `QC(\mathcal O)`.
/-- Proposition 21.43.9 (5): every contravariant cohomological functor on `QC(\mathcal O)` that
turns arbitrary direct sums into products is representable. -/
theorem qc_contravariantCohomologicalFunctor_isRepresentable
    (H : QCohᵒᵖ ⥤ AddCommGrpCat.{vD})
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type uD, PreservesLimitsOfShape (Discrete J) H) :
    ∃ X : QCoh, Nonempty (preadditiveYoneda.obj X ≅ H) := sorry

section RightAdjoints

variable {D' : Type uD'} [Category.{vD'} D']
variable [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
variable [∀ n : ℤ, (shiftFunctor D' n).Additive]
variable [Pretriangulated D'] [IsTriangulated D']

-- Proof sketch: use the Brown representability set for `QC(\mathcal O)` and apply Proposition
-- `13.39.2` to the exact coproduct-preserving functor `F`, then package the resulting right
-- adjoint together with its inherited shift compatibility and triangulated structure.
/-- Proposition 21.43.9 (6): every exact functor from `QC(\mathcal O)` to a triangulated category
that preserves arbitrary direct sums has an exact right adjoint. -/
theorem qc_exactFunctor_hasExactRightAdjoint
    (F : QCoh ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type uD, PreservesColimitsOfShape (Discrete J) F] :
    ∃ (G : D' ⥤ QCoh) (_ : G.CommShift ℤ),
      Nonempty (F ⊣ G) ∧ G.IsTriangulated := sorry

end RightAdjoints

-- Proof sketch: specialize the previous exact-right-adjoint statement to the inclusion functor
-- `QC(\mathcal O) ↪ D(\mathcal O)`, using the direct-sum closure of `QC(\mathcal O)` to see that
-- the inclusion preserves arbitrary direct sums.
/-- Proposition 21.43.9 (7): the inclusion functor `QC(\mathcal O) \to D(\mathcal O)` has an exact
right adjoint. -/
theorem qc_inclusion_hasExactRightAdjoint
    [∀ J : Type uD, PreservesColimitsOfShape (Discrete J) (ObjectProperty.ι QCP : QCoh ⥤ D)] :
    ∃ (G : D ⥤ QCoh) (_ : G.CommShift ℤ),
      Nonempty ((ObjectProperty.ι QCP : QCoh ⥤ D) ⊣ G) ∧ G.IsTriangulated := sorry

end

end CategoryTheory.ModulesOnCategory
