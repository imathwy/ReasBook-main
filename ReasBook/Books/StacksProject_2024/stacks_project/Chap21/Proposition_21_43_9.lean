import StacksProject_2024.Chap13.Proposition_13_39_2
import StacksProject_2024.Chap21.Lemma_21_43_2
import StacksProject_2024.Chap21.Lemma_21_43_8

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe uC vC uD vD uD' vD'

attribute [local instance] HasDerivedCategory.standard

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
variable [∀ U : C, (RGamma U).CommShift ℤ]
variable [∀ U : C, (RGamma U).IsTriangulated]
variable [∀ {U V : C} (f : U ⟶ V), (derivedRestrict f).CommShift ℤ]
variable [∀ {U V : C} (f : U ⟶ V), (derivedRestrict f).IsTriangulated]
variable [∀ {U V : C} (f : U ⟶ V), NatTrans.CommShift (comparison f) ℤ]

local notation "QCP" => isQuasiCoherent 𝒪 RGamma derivedRestrict comparison
local notation "QCoh" => QC 𝒪 RGamma derivedRestrict comparison

/-
Domain-style sampling:
- primary domain: full subcategories cut out by an `ObjectProperty` on a triangulated category,
  together with Brown representability and adjunction criteria for exact functors out of that full
  subcategory;
- sampled owner declarations:
  `CategoryTheory.ObjectProperty`,
  `CategoryTheory.ObjectProperty.FullSubcategory`,
  `CategoryTheory.brown_representability_of_detecting_factorization_set`,
  `CategoryTheory.exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet`;
- best owner abstraction:
  `source-facing`: the Section `21.43` object property `QCP` and its full subcategory `QCoh`;
  `core/canonical`: `ObjectProperty.IsClosedUnderIsomorphisms`,
    `ObjectProperty.IsStableUnderRetracts`, `ObjectProperty.IsTriangulated`,
    `Functor.IsLeftAdjoint`, together with `Adjunction.isTriangulated_rightAdjoint`;
  `bridge/view`: the source-facing representability and exact-right-adjoint existence statements
    below, phrased directly for `QC(𝒪)` while keeping the choice of a right adjoint internal to
    the proofs.
- primitive-vs-derived split:
  primitive data: the comparison object property `QCP`;
  derived API: the full subcategory `QCoh`, its structural closure properties, Brown
    representability for contravariant cohomological functors on `QCoh`, and exact-right-adjoint
    existence statements for exact coproduct-preserving functors out of `QCoh`.
-/

/- Proposition 21.43.9 (1): the strict-fullness statement for `QC(𝒪)` is exactly the
source-facing owner instance from Lemma `21.43.2`. -/
#check qc_isClosedUnderIsomorphisms 𝒪 RGamma derivedRestrict comparison

/- Proposition 21.43.9 (2): saturation of `QC(𝒪)` is already recorded by the owner
instance from Lemma `21.43.2`. -/
#check qc_isStableUnderRetracts 𝒪 RGamma derivedRestrict comparison

/- Proposition 21.43.9 (3): triangulatedity of `QC(𝒪)` is already recorded by the owner
instance from Lemma `21.43.2`. -/
#check qc_isTriangulated 𝒪 RGamma derivedRestrict comparison

/- Proposition 21.43.9 (4): closure of `QC(𝒪)` under arbitrary direct sums is already
recorded by the owner instance from Lemma `21.43.2`. -/
#check qc_isClosedUnderDirectSums 𝒪 RGamma derivedRestrict comparison

end

section

variable {C : Type uC} [Category.{vC} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{uC})

local notation "Ring𝒪" => 𝒪 ⋙ forget₂ CommRingCat RingCat
local notation "DModO" => DerivedCategory (PresheafOfModules Ring𝒪)

variable [HasZeroObject DModO] [HasShift DModO ℤ] [Preadditive DModO]
variable [∀ n : ℤ, (shiftFunctor DModO n).Additive]
variable [Pretriangulated DModO] [IsTriangulated DModO] [HasCoproducts.{uC} DModO]
variable
  (RGamma :
    ∀ U : C,
      DModO ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
variable [∀ U : C, (RGamma U).CommShift ℤ]
variable [∀ U : C, (RGamma U).IsTriangulated]
variable [∀ {U V : C} (f : U ⟶ V), (derivedRestrict f).CommShift ℤ]
variable [∀ {U V : C} (f : U ⟶ V), (derivedRestrict f).IsTriangulated]
variable [∀ {U V : C} (f : U ⟶ V), NatTrans.CommShift (comparison f) ℤ]

local notation "QCP" => isQuasiCoherent 𝒪 RGamma derivedRestrict comparison
local notation "QCoh" => QC 𝒪 RGamma derivedRestrict comparison
local notation "ιQC" => ObjectProperty.ι QCP
local notation "brownSetQC" =>
  qc_exists_brownRepresentabilitySet 𝒪 RGamma derivedRestrict comparison

variable [HasZeroObject QCoh] [HasShift QCoh ℤ] [Preadditive QCoh]
variable [∀ n : ℤ, (shiftFunctor QCoh n).Additive]
variable [Pretriangulated QCoh] [IsTriangulated QCoh] [HasCoproducts.{max uC vC} QCoh]

/-- Proposition 21.43.9 (5): every contravariant cohomological functor on `QC(𝒪)` that sends
arbitrary direct sums to products is representable. -/
@[stacks 0GZ0]
theorem qc_brown_representability
    (H : QCohᵒᵖ ⥤ AddCommGrpCat.{max uC vC})
    [H.rightOp.IsHomological]
    [∀ J : Type (max uC vC), PreservesLimitsOfShape (Discrete J) H] :
    ∃ X : QCoh, Nonempty (preadditiveYoneda.obj X ≅ H) := by
  sorry

/-- Canonical companion to Proposition `21.43.9` (5): the underlying `Type`-valued functor of a
contravariant cohomological functor on `QC(𝒪)` that sends arbitrary direct sums to products is
representable after the standard universe lift. -/
theorem qc_brown_representability_isRepresentable
    (H : QCohᵒᵖ ⥤ AddCommGrpCat.{max uC vC})
    [H.rightOp.IsHomological]
    [∀ J : Type (max uC vC), PreservesLimitsOfShape (Discrete J) H] :
    ((H ⋙ forget AddCommGrpCat) ⋙ uliftFunctor.{max uC vC}).IsRepresentable := by
  sorry

section RightAdjoints

variable {D' : Type uD'} [Category.{vD'} D']
variable [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
variable [∀ n : ℤ, (shiftFunctor D' n).Additive]
variable [Pretriangulated D'] [IsTriangulated D']

-- Proof sketch: use the Brown representability set for `QC(𝒪)` and apply Proposition
-- `13.39.2` to the exact coproduct-preserving functor `F`.
/-- Canonical companion to Proposition 21.43.9 (6): every exact functor from `QC(𝒪)` to a
triangulated category that preserves arbitrary direct sums is a left adjoint. -/
@[instance 100] instance qc_exactFunctor_isLeftAdjoint
    (F : QCoh ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max uC vC), PreservesColimitsOfShape (Discrete J) F] :
    F.IsLeftAdjoint :=
  exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet F brownSetQC

-- Proof sketch: once the Brown witness construction is completed upstream, use the left-adjoint
-- instance above, choose a right adjoint only inside the proof, and then apply
-- `Adjunction.isTriangulated_rightAdjoint`.
/-- Proposition 21.43.9 (6): every exact functor from `QC(𝒪)` to a triangulated category that
preserves arbitrary direct sums has a right adjoint which is again exact. -/
@[stacks 0GZ0]
theorem qc_exactFunctor_hasExactRightAdjoint
    (F : QCoh ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max uC vC), PreservesColimitsOfShape (Discrete J) F] :
    ∃ G : D' ⥤ QCoh, Nonempty (F ⊣ G) ∧ G.IsTriangulated := by
  sorry

end RightAdjoints

-- Proof sketch: apply the Chapter `13` left-adjoint criterion to the inclusion functor
-- `QC(𝒪) ↪ D(𝒪)`, using the direct-sum closure of `QC(𝒪)` to see that
-- the inclusion preserves arbitrary direct sums.
/-- Canonical companion to Proposition 21.43.9 (7): the inclusion functor `QC(𝒪) ↪ D(𝒪)` is a
left adjoint. -/
@[instance 100] instance qc_inclusion_isLeftAdjoint
    [∀ J : Type (max uC vC), ∀ U : C, PreservesColimitsOfShape (Discrete J) (RGamma U)]
    [∀ J : Type (max uC vC),
      ∀ {U V : C} (f : U ⟶ V), PreservesColimitsOfShape (Discrete J) (derivedRestrict f)] :
    (ιQC).IsLeftAdjoint :=
  exactFunctor_isLeftAdjoint_of_exists_brownRepresentabilitySet ιQC brownSetQC

-- Proof sketch: apply the same argument to the inclusion functor once the upstream Brown witness
-- construction is available, keeping the right adjoint existential in the public statement.
/-- Proposition 21.43.9 (7): the inclusion functor `QC(𝒪) ↪ D(𝒪)` has a right adjoint which is
again exact. -/
@[stacks 0GZ0]
theorem qc_inclusion_hasExactRightAdjoint
    [∀ J : Type (max uC vC), ∀ U : C, PreservesColimitsOfShape (Discrete J) (RGamma U)]
    [∀ J : Type (max uC vC),
      ∀ {U V : C} (f : U ⟶ V), PreservesColimitsOfShape (Discrete J) (derivedRestrict f)] :
    ∃ G : DModO ⥤ QCoh, Nonempty ((ιQC) ⊣ G) ∧ G.IsTriangulated := by
  sorry

end

end CategoryTheory.ModulesOnCategory
