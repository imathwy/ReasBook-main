import StacksProject_2024.Chap08.Lemma_8_3_7.Comparison
import StacksProject_2024.Chap08.Lemma_8_3_7.Faithful
import StacksProject_2024.Chap08.Lemma_8_3_7.Full

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)

open SemiRepresentableFamily.Over

/-- Helper for Lemma 8.3.7: once the local faithful and full halves of the identity-refinement
comparison functor are available, the main equivalence-transfer theorem can use that comparison as
its fully faithful bridge. -/
private noncomputable def pullbackFamilyDescentFunctor_fullyFaithful_of_refinement_local
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
    (pullbackFamilyDescentFunctor hc (𝟙 U)
      (identity_refinement_adapter φ)).FullyFaithful :=
  letI := pullbackFamilyDescentFunctor_faithful_of_refinement
    hc 𝒰 𝒱 φ
  letI := pullbackFamilyDescentFunctor_full_of_refinement
    hc 𝒰 𝒱 φ
  Functor.FullyFaithful.ofFullyFaithful _

/-- Lemma 8.3.7: let `φ : 𝒱 ⟶ 𝒰` be a refinement of fixed-target families over `U`, and for each
`i` and `(i,i')` write `𝒱_i = baseChange 𝒱 (𝒰.obj i).hom` and
`𝒱_{ii'} = baseChange 𝒱 (𝒰.pr0 i i' ≫ (𝒰.obj i).hom)`. Assume descent data
are defined for `𝒰`, `𝒱`, every `𝒱_i`, and every `𝒱_{ii'}`. If `𝒮_U ⥤ DD(𝒱)` is an equivalence,
if each `𝒮_{U_i} ⥤ DD(𝒱_i)` is fully faithful, and if each
`𝒮_{U_i ×[U] U_{i'}} ⥤ DD(𝒱_{ii'})` is faithful, then `𝒮_U ⥤ DD(𝒰)` is an equivalence. -/
theorem familyDescentFunctor_isEquivalence_of_refinement
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
    (φ : 𝒱 ⟶ 𝒰) [Functor.IsEquivalence (familyDescentFunctor hc 𝒱)] :
    Functor.IsEquivalence (familyDescentFunctor hc 𝒰) := by
  -- Package the local faithful and full comparison into the fully faithful bridge used by the
  -- equivalence-transfer theorem.
  have hPullback :
      (pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).FullyFaithful :=
    -- The identity-target refinement comparison is fully faithful because its faithful and full
    -- halves were established in the imported local descent files.
    pullbackFamilyDescentFunctor_fullyFaithful_of_refinement_local
      hc 𝒰 𝒱 φ
  -- With that bridge named, the source-proof route is just the imported comparison theorem.
  exact familyDescentFunctor_isEquivalence_of_refinement_of_pullbackFullyFaithful
    hc 𝒰 𝒱 φ hPullback

end CategoryTheory
