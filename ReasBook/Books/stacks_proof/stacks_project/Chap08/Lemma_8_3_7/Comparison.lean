import StacksProject_2024.Chap08.Lemma_8_3_7.Base

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory
namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)


/-- Helper for Lemma 8.3.7: pulling back the canonical descent datum along a refinement
`φ : 𝒱 ⟶ 𝒰` agrees with the canonical descent datum on the refined family `𝒱`. -/
noncomputable def familyDescentFunctor_comp_refinement_pullback_iso
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    (φ : 𝒱 ⟶ 𝒰) :
    familyDescentFunctor hc 𝒰 ⋙
      pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ) ≅
        familyDescentFunctor hc 𝒱 := by
  let e𝒰 := Pseudofunctor.DescentData'.descentDataEquivalence
    hc.fiberPseudofunctor 𝒰.pairwisePullback 𝒰.triplePullback
  let e𝒱 := Pseudofunctor.DescentData'.descentDataEquivalence
    hc.fiberPseudofunctor 𝒱.pairwisePullback 𝒱.triplePullback
  let compIso :=
    Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso hc.fiberPseudofunctor
      (p := 𝟙 U) (f := fun i : 𝒰.index ↦ (𝒰.obj i).hom)
      (f' := fun j : 𝒱.index ↦ (𝒱.obj j).hom)
      (α := φ.α) (p' := fun j ↦ (φ.f j).left)
      (w := by
        intro j
        simpa using Over.w (φ.f j))
  let pullFunctor :=
    Pseudofunctor.DescentData.pullFunctor hc.fiberPseudofunctor
      (p := 𝟙 U) (f := fun i : 𝒰.index ↦ (𝒰.obj i).hom)
      (f' := fun j : 𝒱.index ↦ (𝒱.obj j).hom)
      (α := φ.α) (p' := fun j ↦ (φ.f j).left)
      (w := by
        intro j
        simpa using Over.w (φ.f j))
  -- Reassociate through the owner-level descent-data equivalences, identify the middle bridge with
  -- the refinement pullback functor from Lemma 8.3.3, and then cancel pullback along `𝟙 U`.
  calc
    familyDescentFunctor hc 𝒰 ⋙
        pullbackFamilyDescentFunctor hc (𝟙 U)
          (identity_refinement_adapter φ) ≅
      (((hc.fiberPseudofunctor).toDescentData (fun i : 𝒰.index ↦ (𝒰.obj i).hom)) ⋙
        (e𝒰.inverse ⋙ e𝒰.functor ⋙ pullFunctor)) ⋙ e𝒱.inverse := by
          -- Reassociate the owner-level composition to isolate the middle
          -- `e𝒰.inverse ⋙ e𝒰.functor`.
          simpa [familyDescentFunctor, pullbackFamilyDescentFunctor, pullFunctor] using
            (Functor.associator
              (((hc.fiberPseudofunctor).toDescentData (fun i : 𝒰.index ↦ (𝒰.obj i).hom)) ⋙
                e𝒰.inverse)
              (e𝒰.functor ⋙ pullFunctor)
              e𝒱.inverse).symm ≪≫
              Functor.isoWhiskerRight
                (Functor.associator
                  ((hc.fiberPseudofunctor).toDescentData
                    (fun i : 𝒰.index ↦ (𝒰.obj i).hom))
                  e𝒰.inverse
                  (e𝒰.functor ⋙ pullFunctor))
                e𝒱.inverse
    _ ≅
      (((hc.fiberPseudofunctor).toDescentData (fun i : 𝒰.index ↦ (𝒰.obj i).hom)) ⋙
        pullFunctor) ⋙ e𝒱.inverse := by
          -- Cancel the middle descent-data equivalence for `𝒰`.
          exact Functor.isoWhiskerRight
            (Functor.isoWhiskerLeft
              ((hc.fiberPseudofunctor).toDescentData (fun i : 𝒰.index ↦ (𝒰.obj i).hom))
              (e𝒰.invFunIdAssoc pullFunctor))
            e𝒱.inverse
    _ ≅ ((hc.pullbackFunctor (𝟙 U)) ⋙ familyDescentFunctor hc 𝒱) := by
          -- The canonical pullback comparison on descent data is the textbook refinement bridge.
          simpa [familyDescentFunctor, pullFunctor] using
            Functor.isoWhiskerRight compIso e𝒱.inverse
    _ ≅ familyDescentFunctor hc 𝒱 := by
          -- Pullback along the identity is canonically isomorphic to the identity on the fiber.
          exact Functor.isoWhiskerRight (hc.pullbackIdIso U).symm (familyDescentFunctor hc 𝒱) ≪≫
            Functor.leftUnitor (familyDescentFunctor hc 𝒱)

/-- Helper for Lemma 8.3.7: once the refinement pullback functor on descent data is fully
faithful, the comparison with `𝒱` transfers the equivalence back to `𝒰`. -/
theorem familyDescentFunctor_isEquivalence_of_refinement_of_pullbackFullyFaithful
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    (φ : 𝒱 ⟶ 𝒰) [Functor.IsEquivalence (familyDescentFunctor hc 𝒱)]
    (hPullback :
      (pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)).FullyFaithful) :
    Functor.IsEquivalence (familyDescentFunctor hc 𝒰) := by
  let pullbackFunctor :=
    pullbackFamilyDescentFunctor hc (𝟙 U)
      (identity_refinement_adapter φ)
  let compIso := familyDescentFunctor_comp_refinement_pullback_iso hc 𝒰 𝒱 φ
  letI : pullbackFunctor.Faithful := hPullback.faithful
  letI : pullbackFunctor.Full := hPullback.full
  letI : Functor.IsEquivalence (familyDescentFunctor hc 𝒰 ⋙ pullbackFunctor) :=
    Functor.isEquivalence_of_iso compIso.symm
  -- Full faithfulness of the pullback functor lets us cancel it from the comparison with `𝒱`.
  letI : Functor.Faithful (familyDescentFunctor hc 𝒰) :=
    Functor.Faithful.of_comp_iso compIso
  letI : Functor.Full (familyDescentFunctor hc 𝒰) :=
    Functor.Full.of_comp_faithful_iso compIso
  -- Essential surjectivity also cancels through a fully faithful target functor.
  letI : Functor.EssSurj (familyDescentFunctor hc 𝒰) :=
    Functor.essSurj_of_comp_fully_faithful (familyDescentFunctor hc 𝒰) pullbackFunctor
  exact { }

end CategoryTheory
