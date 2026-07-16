import Mathlib
import StacksProject_2024.stacks_project.Chap07.Lemma_7_21_1
import StacksProject_2024.stacks_project.Chap34.Lemma_34_4_14

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}} (f : T ⟶ S)

local notation "J_small_T" => T.smallEtaleTopology
local notation "J_small_S" => S.smallEtaleTopology
local notation "J_big_T" => T.overGrothendieckTopology @Etale
local notation "J_big_S" => S.overGrothendieckTopology @Etale

-- Semantic recall: `lean_leansearch` surfaced the canonical site-theoretic owners
-- `Functor.sheafPushforwardContinuous`, `Functor.morphismOfTopoiInOfContinuous`,
-- and `Functor.morphismOfTopoiInOfCocontinuous`. Local Chapter 34 precedent in
-- `Lemma_34_4_13`, `Lemma_34_4_14`, and `Lemma_34_4_16` fixes the relevant source-facing owners
-- as `smallEtaleToBigEtaleMorphismOfTopoi`, `smallEtaleToBigEtaleSiteMorphismOfTopoi`, and the
-- cocontinuous big étale morphism attached to `bigEtaleMapFunctor f`.

/-- Helper: pulling back an étale morphism along `f` is again étale. -/
theorem smallEtalePullbackObj_isEtale (f : T ⟶ S) (U : S.Etale) :
    Etale (((Over.pullback f).obj U.toComma).hom) := sorry

/-- The pullback of a small étale object along `f`, viewed again in the small étale site of `T`. -/
abbrev smallEtalePullbackObj (f : T ⟶ S) (U : S.Etale) : T.Etale :=
  MorphismProperty.Over.mk ⊤
    (((Over.pullback f).obj U.toComma).hom)
    (smallEtalePullbackObj_isEtale f U)

/-- Helper: the underlying pullback map between over-objects commutes with the structure maps to
`T`, so it defines a morphism in the small étale site. -/
theorem smallEtalePullbackMap_w (f : T ⟶ S) {X Y : S.Etale} (g : X ⟶ Y) :
    ((Over.pullback f).map g.toCommaMorphism).left ≫ (smallEtalePullbackObj f Y).hom =
      (smallEtalePullbackObj f X).hom := sorry

/-- The map on pullback objects induced by a morphism in the small étale site over `S`. -/
abbrev smallEtalePullbackMap (f : T ⟶ S) {X Y : S.Etale} (g : X ⟶ Y) :
    smallEtalePullbackObj f X ⟶ smallEtalePullbackObj f Y :=
  MorphismProperty.Over.homMk
    (((Over.pullback f).map g.toCommaMorphism).left)
    (smallEtalePullbackMap_w f g)

/-- Helper: pullback along `f` preserves identity morphisms on the small étale site. -/
theorem smallEtalePullbackMap_id (f : T ⟶ S) (X : S.Etale) :
    smallEtalePullbackMap f (𝟙 X) = 𝟙 (smallEtalePullbackObj f X) := sorry

/-- Helper: pullback along `f` preserves composition of morphisms on the small étale site. -/
theorem smallEtalePullbackMap_comp (f : T ⟶ S) {X Y Z : S.Etale}
    (g : X ⟶ Y) (h : Y ⟶ Z) :
    smallEtalePullbackMap f (g ≫ h) =
      smallEtalePullbackMap f g ≫ smallEtalePullbackMap f h := sorry

/-- The small étale base-change functor induced by `f : T ⟶ S`. -/
abbrev smallEtalePullbackFunctor (f : T ⟶ S) : S.Etale ⥤ T.Etale where
  obj U := smallEtalePullbackObj f U
  map g := smallEtalePullbackMap f g
  map_id X := smallEtalePullbackMap_id f X
  map_comp g h := smallEtalePullbackMap_comp f g h

/-- The postcomposition functor on big étale over-categories induced by `f`. -/
abbrev bigEtaleMapFunctor (f : T ⟶ S) : Over T ⥤ Over S :=
  Over.map f

/-- Helper: the postcomposition functor on big étale sites is cocontinuous. -/
instance bigEtaleMapFunctor_isCocontinuous :
    Functor.IsCocontinuous (bigEtaleMapFunctor f) J_big_T J_big_S := sorry

/-- Helper: the cocontinuous big étale presentation has the pointwise right-Kan-extension
hypotheses needed to package the associated morphism of topoi. -/
instance bigEtaleMapFunctor_op_hasPointwiseRightKanExtension
    (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (bigEtaleMapFunctor f).op.HasPointwiseRightKanExtension P := sorry

/-- The big étale morphism of topoi attached to `f`, presented cocontinuously by `Over.map f`. -/
abbrev bigEtaleMorphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn J_big_S J_big_T :=
  (bigEtaleMapFunctor f).morphismOfTopoiInOfCocontinuous J_big_T J_big_S

/-- Lemma 34.4.17 (1): the relocalization morphism `i_f` from Lemma 34.4.13 factors as
`f_{big} \circ i_T`, where `f_{big}` is the big étale morphism of topoi attached to `f`. -/
@[stacks 021I]
theorem smallEtaleToBigEtaleMorphismOfTopoi_eq_comp_bigEtale :
    smallEtaleToBigEtaleMorphismOfTopoi f =
      MorphismOfTopoiIn.comp
        (bigEtaleMorphismOfTopoi f)
        (smallEtaleToBigEtaleMorphismOfTopoi (𝟙 T)) := sorry

/-- Lemma 34.4.17 (2): the small étale base-change functor
`S_{\acute{e}tale} ⥤ T_{\acute{e}tale}`, `(U \to S) \mapsto (U \times_S T \to T)`, is
continuous. -/
@[stacks 021I]
instance smallEtalePullbackFunctor_isContinuous :
    Functor.IsContinuous (smallEtalePullbackFunctor f) J_small_S J_small_T := sorry

/-- Lemma 34.4.17 (3): the continuous small étale base-change functor induces a morphism of
sites `T_{\acute{e}tale} \to S_{\acute{e}tale}`. -/
@[stacks 021I]
instance smallEtalePullbackFunctor_isMorphismOfSites :
    IsMorphismOfSites J_small_S J_small_T (smallEtalePullbackFunctor f) := sorry

/-- Lemma 34.4.17 (4): the induced morphism of sites defines the morphism of topoi
`f_{small} : \mathit{Sh}(T_{\acute{e}tale}) \to \mathit{Sh}(S_{\acute{e}tale})`, represented
here by the composite `\pi_S \circ i_f`. -/
@[stacks 021I]
abbrev smallEtaleMorphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn J_small_S J_small_T :=
  MorphismOfTopoiIn.comp
    (smallEtaleToBigEtaleSiteMorphismOfTopoi S)
    (smallEtaleToBigEtaleMorphismOfTopoi f)

/-- Lemma 34.4.17 (5): for a sheaf `\mathcal{F}` on `T_{\acute{e}tale}` and an object `U/S` of
`S_{\acute{e}tale}`, the direct image `f_{small,*}(\mathcal{F})` is computed by evaluation on
`(U \times_S T)/T`. -/
@[stacks 021I]
theorem smallEtaleMorphismOfTopoi_pushforward_obj_obj
    (ℱ : Sheaf J_small_T (Type (u + 1))) (U : S.Etale) :
    (((smallEtaleMorphismOfTopoi f) _*).obj ℱ).1.obj (op U) =
      ℱ.1.obj (op ((smallEtalePullbackFunctor f).obj U)) := sorry

/-- Lemma 34.4.17 (6): the square relating the small and big étale morphisms of topoi commutes:
`f_{small} \circ \pi_T = \pi_S \circ f_{big}`. -/
@[stacks 021I]
theorem smallEtaleMorphismOfTopoi_comp_smallEtaleToBigEtaleSiteMorphism :
    MorphismOfTopoiIn.comp
        (smallEtaleMorphismOfTopoi f)
        (smallEtaleToBigEtaleSiteMorphismOfTopoi T) =
      MorphismOfTopoiIn.comp
        (smallEtaleToBigEtaleSiteMorphismOfTopoi S)
        (bigEtaleMorphismOfTopoi f) := sorry

/-- Lemma 34.4.17 (7): the small étale morphism is the composite
`\pi_S \circ i_f : \mathit{Sh}(T_{\acute{e}tale}) \to \mathit{Sh}(S_{\acute{e}tale})`. -/
@[stacks 021I]
theorem smallEtaleMorphismOfTopoi_eq_comp_smallEtaleToBigEtale :
    smallEtaleMorphismOfTopoi f =
      MorphismOfTopoiIn.comp
        (smallEtaleToBigEtaleSiteMorphismOfTopoi S)
        (smallEtaleToBigEtaleMorphismOfTopoi f) := sorry

end AlgebraicGeometry.Scheme
