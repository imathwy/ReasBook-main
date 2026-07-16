import Mathlib
import StacksProject_2024.stacks_project.Chap07.Lemma_7_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite

noncomputable section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/- Domain-style sampling for Lemma 7.20.4:
- primary domain: sheafification and cocontinuous pushforward/pullback on sites;
- sampled owner API:
  `GrothendieckTopology.sheafifyMap`,
  `GrothendieckTopology.toSheafify`,
  `Adjunction.leftAdjointUniq`,
  `Functor.ranAdjunction`,
  `Functor.sheafPullbackCocontinuousAdjunction`,
  `sheafificationAdjunction`,
  `presheafToSheaf`;
- source/core/bridge triage:
  `source-facing`: the canonical comparison map `(u^p ℱ)^# ⟶ (u^p (ℱ^#))^#`;
  `core/canonical`: the natural isomorphism between the two left adjoints from presheaves on `D`
  to sheaves on `C`, namely
  `((Functor.whiskeringLeft _ _ _).obj G.op) ⋙ presheafToSheaf J _` and
  `presheafToSheaf K _ ⋙ G.sheafPullbackCocontinuous _ J K`, obtained from
  `Adjunction.leftAdjointUniq` applied to `(G.op.ranAdjunction _).comp
  (sheafificationAdjunction J _)` and
  `(sheafificationAdjunction K _).comp (G.sheafPullbackCocontinuousAdjunction J K)`;
  `bridge/view`: the textbook comparison is the component morphism
  `J.sheafifyMap (whiskerLeft G.op (K.toSheafify F))` of that owner-level natural isomorphism.

Primitive data are the cocontinuous functor `G`, the two sheafification adjunctions, and the
right Kan extension hypotheses. The comparison map is derived API from the owner functors
`presheafToSheaf` and `sheafificationAdjunction`; the public statement should therefore use the
canonical owner natural isomorphism first, with `J.sheafifyMap` and `K.toSheafify` retained as
the source-facing bridge surface for the component formula.
-/

-- Proof sketch: the main owner is the left-adjoint-uniqueness isomorphism comparing sheafify
-- after presheaf pullback with cocontinuous pullback after sheafify. The textbook morphism
-- `J.sheafifyMap (whiskerLeft G.op (K.toSheafify F))` is the component of that owner isomorphism
-- at `F`; the source-facing `IsIso` statement is then a direct consequence.
/-- Lemma 7.20.4, owner level: the two canonical left adjoints from presheaves on `D` to sheaves
on `C` are naturally isomorphic. -/
noncomputable def pullbackCocontinuousSheafificationCompatibility
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F'] :
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op) ⋙
        presheafToSheaf J (Type (max u₁ u₂ v₁ v₂)) ≅
      presheafToSheaf K (Type (max u₁ u₂ v₁ v₂)) ⋙
        G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K :=
  Adjunction.leftAdjointUniq
    ((G.op.ranAdjunction (Type (max u₁ u₂ v₁ v₂))).comp
      (sheafificationAdjunction J (Type (max u₁ u₂ v₁ v₂))))
    ((sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))).comp
      (G.sheafPullbackCocontinuousAdjunction J K))

/-- Lemma 7.20.4, source-facing bridge: for a cocontinuous functor in the setup of Lemma 7.20.3,
the canonical map `(u^p ℱ)^# ⟶ (u^p (ℱ^#))^#` is an isomorphism. -/
theorem pullbackCocontinuousSheafificationComparison_isIso
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F']
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    IsIso (J.sheafifyMap (whiskerLeft G.op (K.toSheafify F))) := sorry

end CategoryTheory.Functor
