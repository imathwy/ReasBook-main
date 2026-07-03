import StacksProject_2024.Chap08.Lemma_8_3_7.LocalPreimage

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)

open SemiRepresentableFamily.Over

/-- Helper for Lemma 8.3.7: the refinement pullback functor is full once the local fully faithful
descent functors on `𝒱_i` and the overlap faithful descent functors on `𝒱_{ii'}` are glued along
the source proof's comparison route. -/
theorem pullbackFamilyDescentFunctor_full_of_refinement
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)]
    [∀ i : 𝒰.index,
      HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    [∀ i i' : 𝒰.index,
      HasDescentPullbacks (𝒱.overlapBaseChange 𝒰 i i')]
    [∀ i : 𝒰.index,
      Functor.Full (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    [∀ i i' : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.overlapBaseChange 𝒰 i i'))]
    (φ : 𝒱 ⟶ 𝒰) :
    Functor.Full
      (pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)) := by
  -- Route correction: the faithful half is already separated, so the remaining source-faithful
  -- work is exactly the local-preimage gluing argument from the textbook proof.
  refine ⟨?_⟩
  intro D₁ D₂ θ
  -- Glue the local fully faithful preimages into the unique global candidate in `DD(𝒰)`.
  refine ⟨glued_local_member_base_change_preimage
      hc 𝒰 𝒱 φ θ, ?_⟩
  -- The split LocalPreimage layer already isolates the map-back verification.
  exact glued_local_member_base_change_preimage_maps_to_theta
    hc 𝒰 𝒱 φ θ

end CategoryTheory
