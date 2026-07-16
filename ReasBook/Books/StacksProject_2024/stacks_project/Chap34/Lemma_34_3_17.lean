import Mathlib
import StacksProject_2024.stacks_project.Chap34.Lemma_34_3_12
import StacksProject_2024.stacks_project.Chap34.Lemma_34_3_14

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}} (f : T ⟶ S)

local notation "J_small_T" => T.smallZariskiTopology
local notation "J_small_S" => S.smallZariskiTopology
local notation "J_big_T" => T.bigZariskiTopology
local notation "J_big_S" => S.bigZariskiTopology

-- Semantic recall: `lean_leansearch` surfaced the canonical open-immersion pullback API and
-- site-theoretic owners `Functor.morphismOfTopoiInOfContinuous` and
-- `Functor.morphismOfTopoiInOfCocontinuous`. Local Chapter 34 precedent in
-- `Lemma_34_3_13`, `Lemma_34_3_14`, and `Lemma_34_3_16` fixes the relevant source-facing owners
-- as `smallZariskiToBigZariskiMorphismOfTopoi`, `smallZariskiToBigZariskiSiteMorphismOfTopoi`,
-- and the cocontinuous big Zariski morphism attached to `bigZariskiMapFunctor f`.

/-- Helper: pulling back an open immersion along `f` is again an open immersion. -/
theorem smallZariskiPullbackObj_isOpenImmersion
    (f : T ⟶ S) (U : S.smallZariskiSite) :
    IsOpenImmersion (((Over.pullback f).obj U.toComma).hom) := sorry

/-- The pullback of a small Zariski object along `f`, viewed again in the small Zariski site
of `T`. -/
abbrev smallZariskiPullbackObj (f : T ⟶ S) (U : S.smallZariskiSite) :
    T.smallZariskiSite :=
  MorphismProperty.Over.mk ⊤
    (((Over.pullback f).obj U.toComma).hom)
    (smallZariskiPullbackObj_isOpenImmersion f U)

/-- Helper: the underlying pullback map between over-objects commutes with the structure maps to
`T`, so it defines a morphism in the small Zariski site. -/
theorem smallZariskiPullbackMap_w
    (f : T ⟶ S) {X Y : S.smallZariskiSite} (g : X ⟶ Y) :
    ((Over.pullback f).map g.toCommaMorphism).left ≫ (smallZariskiPullbackObj f Y).hom =
      (smallZariskiPullbackObj f X).hom := sorry

/-- The map on pullback objects induced by a morphism in the small Zariski site over `S`. -/
abbrev smallZariskiPullbackMap
    (f : T ⟶ S) {X Y : S.smallZariskiSite} (g : X ⟶ Y) :
    smallZariskiPullbackObj f X ⟶ smallZariskiPullbackObj f Y :=
  MorphismProperty.Over.homMk
    (((Over.pullback f).map g.toCommaMorphism).left)
    (smallZariskiPullbackMap_w f g)

/-- Helper: pullback along `f` preserves identity morphisms on the small Zariski site. -/
theorem smallZariskiPullbackMap_id (f : T ⟶ S) (X : S.smallZariskiSite) :
    smallZariskiPullbackMap f (𝟙 X) = 𝟙 (smallZariskiPullbackObj f X) := sorry

/-- Helper: pullback along `f` preserves composition of morphisms on the small Zariski site. -/
theorem smallZariskiPullbackMap_comp
    (f : T ⟶ S) {X Y Z : S.smallZariskiSite} (g : X ⟶ Y) (h : Y ⟶ Z) :
    smallZariskiPullbackMap f (g ≫ h) =
      smallZariskiPullbackMap f g ≫ smallZariskiPullbackMap f h := sorry

/-- The small Zariski base-change functor induced by `f : T ⟶ S`. -/
@[stacks 0211]
abbrev smallZariskiPullbackFunctor (f : T ⟶ S) :
    S.smallZariskiSite ⥤ T.smallZariskiSite where
  obj U := smallZariskiPullbackObj f U
  map g := smallZariskiPullbackMap f g
  map_id X := smallZariskiPullbackMap_id f X
  map_comp g h := smallZariskiPullbackMap_comp f g h

/-- The postcomposition functor on big Zariski over-categories induced by `f`. -/
abbrev bigZariskiMapFunctor : Over T ⥤ Over S :=
  Over.map f

/-- Helper: the postcomposition functor on big Zariski sites is cocontinuous. -/
instance bigZariskiMapFunctor_isCocontinuous :
    Functor.IsCocontinuous (bigZariskiMapFunctor f) J_big_T J_big_S := sorry

/-- Helper: the cocontinuous big Zariski presentation has the pointwise right-Kan-extension
hypotheses needed to package the associated morphism of topoi. -/
instance bigZariskiMapFunctor_op_hasPointwiseRightKanExtension
    (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (bigZariskiMapFunctor f).op.HasPointwiseRightKanExtension P := sorry

/-- The big Zariski morphism of topoi attached to `f`, presented cocontinuously by
postcomposition on over-categories. -/
@[stacks 0211]
abbrev bigZariskiMorphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn J_big_S J_big_T :=
  (bigZariskiMapFunctor f).morphismOfTopoiInOfCocontinuous J_big_T J_big_S

/-- Lemma 34.3.17 (1): the relocalization morphism `i_f` from Lemma 34.3.13 factors as
`f_{big} \circ i_T`, where `f_{big}` is the big Zariski morphism of topoi attached to `f`. -/
@[stacks 0211]
theorem smallZariskiToBigZariskiMorphismOfTopoi_eq_comp_bigZariski :
    smallZariskiToBigZariskiMorphismOfTopoi f =
      MorphismOfTopoiIn.comp
        (bigZariskiMorphismOfTopoi f)
        (smallZariskiToBigZariskiMorphismOfTopoi (𝟙 T)) := sorry

/-- Lemma 34.3.17 (2): the small Zariski base-change functor
`S_{Zar} ⥤ T_{Zar}`, `(U \to S) \mapsto (U \times_S T \to T)`, is continuous. -/
@[stacks 0211]
instance smallZariskiPullbackFunctor_isContinuous :
    Functor.IsContinuous (smallZariskiPullbackFunctor f) J_small_S J_small_T := sorry

/-- Lemma 34.3.17 (3): the continuous small Zariski base-change functor induces a morphism of
sites `T_{Zar} \to S_{Zar}`. -/
@[stacks 0211]
instance smallZariskiPullbackFunctor_isMorphismOfSites :
    IsMorphismOfSites J_small_S J_small_T (smallZariskiPullbackFunctor f) := sorry

/-- Helper: the inverse-image functor on open subsets attached to the underlying continuous map
of schemes is continuous for the usual open-cover topologies. -/
instance underlyingOpensMap_isContinuous :
    Functor.IsContinuous (TopologicalSpace.Opens.map f.base)
      (Opens.grothendieckTopology S.toTopCat) (Opens.grothendieckTopology T.toTopCat) := sorry

/-- Lemma 34.3.17 (4): the induced morphism of sites defines the morphism of topoi
`f_{small} : \mathit{Sh}(T_{Zar}) \to \mathit{Sh}(S_{Zar})`, represented here by the composite
`\pi_S \circ i_f`. -/
@[stacks 0211]
abbrev smallZariskiMorphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn J_small_S J_small_T :=
  MorphismOfTopoiIn.comp
    (smallZariskiToBigZariskiSiteMorphismOfTopoi S)
    (smallZariskiToBigZariskiMorphismOfTopoi f)

/-- Lemma 34.3.17 (5): for a sheaf `\mathcal{F}` on `T_{Zar}` and an object `U/S` of
`S_{Zar}`, the inverse image functor of `f_{small}` agrees, after the identification of
Lemma 34.3.12, with the usual inverse image of sheaves on topological spaces. -/
@[stacks 0211]
theorem smallZariskiMorphismOfTopoi_inverseImage_eq_usual :
    (smallZariskiMorphismOfTopoi f)⁻¹ ⋙ (smallZariskiTypeSheafEquiv T).functor =
      (smallZariskiTypeSheafEquiv S).functor ⋙
        (TopologicalSpace.Opens.map f.base).sheafPullback (Type (u + 1))
          (Opens.grothendieckTopology S.toTopCat)
          (Opens.grothendieckTopology T.toTopCat) := sorry

/-- Lemma 34.3.17 (6): the direct image functor of `f_{small}` agrees, after the identification of
Lemma 34.3.12, with the usual direct image of sheaves on topological spaces. -/
@[stacks 0211]
theorem smallZariskiMorphismOfTopoi_pushforward_eq_usual :
    (smallZariskiMorphismOfTopoi f) _* ⋙ (smallZariskiTypeSheafEquiv S).functor =
      (smallZariskiTypeSheafEquiv T).functor ⋙
        TopCat.Sheaf.pushforward (Type (u + 1)) f.base := sorry

/-- Lemma 34.3.17 (7): for a sheaf `\mathcal{F}` on `T_{Zar}` and an object `U/S` of
`S_{Zar}`, the direct image `f_{small,*}(\mathcal{F})` is computed by evaluation on
`(U \times_S T)/T`. -/
@[stacks 0211]
theorem smallZariskiMorphismOfTopoi_pushforward_obj_obj
    (ℱ : Sheaf J_small_T (Type (u + 1))) (U : S.smallZariskiSite) :
    (((smallZariskiMorphismOfTopoi f) _*).obj ℱ).1.obj (op U) =
      ℱ.1.obj (op ((smallZariskiPullbackFunctor f).obj U)) := sorry

/-- Lemma 34.3.17 (8): the square relating the small and big Zariski morphisms of topoi commutes:
`f_{small} \circ \pi_T = \pi_S \circ f_{big}`. -/
@[stacks 0211]
theorem smallZariskiMorphismOfTopoi_comp_smallZariskiToBigZariskiSiteMorphism :
    MorphismOfTopoiIn.comp
        (smallZariskiMorphismOfTopoi f)
        (smallZariskiToBigZariskiSiteMorphismOfTopoi T) =
      MorphismOfTopoiIn.comp
        (smallZariskiToBigZariskiSiteMorphismOfTopoi S)
        (bigZariskiMorphismOfTopoi f) := sorry

/-- Lemma 34.3.17 (9): the small Zariski morphism is the composite
`\pi_S \circ f_{big} \circ i_T : \mathit{Sh}(T_{Zar}) \to \mathit{Sh}(S_{Zar})`. -/
@[stacks 0211]
theorem smallZariskiMorphismOfTopoi_eq_comp_bigZariski_comp_iT :
    smallZariskiMorphismOfTopoi f =
      MorphismOfTopoiIn.comp
        (MorphismOfTopoiIn.comp
          (smallZariskiToBigZariskiSiteMorphismOfTopoi S)
          (bigZariskiMorphismOfTopoi f))
        (smallZariskiToBigZariskiMorphismOfTopoi (𝟙 T)) := sorry

/-- Lemma 34.3.17 (10): the small Zariski morphism is the composite
`\pi_S \circ i_f : \mathit{Sh}(T_{Zar}) \to \mathit{Sh}(S_{Zar})`. -/
@[stacks 0211]
theorem smallZariskiMorphismOfTopoi_eq_comp_smallZariskiToBigZariski :
    smallZariskiMorphismOfTopoi f =
      MorphismOfTopoiIn.comp
        (smallZariskiToBigZariskiSiteMorphismOfTopoi S)
        (smallZariskiToBigZariskiMorphismOfTopoi f) := sorry

end AlgebraicGeometry.Scheme
