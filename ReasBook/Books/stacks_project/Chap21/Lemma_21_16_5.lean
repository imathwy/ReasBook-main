import Mathlib
import stacks_project.Chap07.Lemma_7_18_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe uI uC vC

namespace CategoryTheory

open CofilteredSiteDiagram

/-- A compatible inverse system of abelian sheaves on the stage sites of `S`, with transition maps
`f_a^{-1} \mathcal F_i ⟶ \mathcal F_j` for arrows `a : j ⟶ i`. -/
structure InverseSystemOfAbelianSheaves
    (S : CofilteredSiteDiagram.{uI, uC, vC}) where
  /-- The abelian sheaf on the stage site `i`. -/
  obj : ∀ i : S.I, Sheaf (S.stageTopology i) AddCommGrpCat.{max uC vC}
  /-- The transition morphism `f_a^{-1} \mathcal F_i ⟶ \mathcal F_j` for `a : j ⟶ i`. -/
  transition : ∀ {i j : S.I} (a : j ⟶ i),
    ((S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j)).obj (obj i) ⟶
      obj j
  /-- The transition morphism for the identity arrow is the canonical identity pullback map. -/
  transition_id : ∀ i : S.I,
    transition (𝟙 i) = (S.stageSheafPullbackIdIso AddCommGrpCat.{max uC vC} i).hom.app (obj i)
  /-- The transition morphisms satisfy the cocycle condition. -/
  transition_comp : ∀ {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j),
    (S.stageSheafPullbackCompIso AddCommGrpCat.{max uC vC} a b).hom.app (obj i) ≫
        transition (b ≫ a) =
      ((S.stageFunctor b).sheafPullback AddCommGrpCat.{max uC vC}
        (S.stageTopology j) (S.stageTopology k)).map (transition a) ≫
        transition b

/-- A morphism of inverse systems of abelian sheaves is a componentwise morphism commuting with
all transition maps. -/
structure InverseSystemOfAbelianSheavesHom
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F G : InverseSystemOfAbelianSheaves S) where
  /-- The morphism on the stage `i`. -/
  app : ∀ i : S.I, F.obj i ⟶ G.obj i
  /-- Compatibility of the component maps with the transition morphisms. -/
  comm : ∀ {i j : S.I} (a : j ⟶ i),
    ((S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j)).map (app i) ≫
        G.transition a =
      F.transition a ≫
        app j

-- Proof sketch: choose for each stage an injective embedding `F.obj i ⟶ A_i`, then form the
-- product over all arrows `b : k ⟶ i` of the pushforwards `f_{b,*} A_k`. The adjoints of the
-- composites `f_b^{-1} F_i ⟶ F_k ⟶ A_k` give a componentwise monomorphism into this product, and
-- the canonical pullback-pushforward comparison maps make the targets into a compatible inverse
-- system. Exactness of stage pushforwards preserves injectives, so each stage of the target system
-- is injective.
/-- Lemma 21.16.5: every inverse system of abelian sheaves on a cofiltered inverse system of sites
admits a morphism into another inverse system whose stagewise maps are monomorphisms and whose
stagewise targets are injective abelian sheaves. -/
theorem exists_mono_to_injective_inverse_system_of_abelian_sheaves
    (S : CofilteredSiteDiagram.{uI, uC, vC})
    (F : InverseSystemOfAbelianSheaves S) :
    ∃ (G : InverseSystemOfAbelianSheaves S) (ι : InverseSystemOfAbelianSheavesHom F G),
      (∀ i : S.I, Mono (ι.app i)) ∧ ∀ i : S.I, Injective (G.obj i) := sorry

end CategoryTheory
