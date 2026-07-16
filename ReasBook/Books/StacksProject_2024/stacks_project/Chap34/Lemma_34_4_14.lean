import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_14_1
import StacksProject_2024.stacks_project.Chap34.Lemma_34_4_13

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

local notation "J_small" => S.smallEtaleTopology
local notation "J_big" => S.overGrothendieckTopology @Etale

-- Semantic recall: `lean_leansearch` only surfaced generic fully faithful/final-functor API, while
-- the verified local Chapter 7 owners for this item are `IsMorphismOfSites`,
-- `Functor.morphismOfTopoiInOfContinuous`, and the fully-faithful continuous-adjunction retraction
-- surface from `Lemma_7_21_8`. For the source-facing morphism `i_S`, the correct Chapter 34 owner
-- is already `smallEtaleToBigEtaleMorphismOfTopoi (𝟙 S)` from `Lemma_34_4_13`.

/-- Lemma 34.4.14 (1): the inclusion functor
`S_{\acute{e}tale} ⥤ (\mathit{Sch}/S)_{\acute{e}tale}` defines a morphism of sites
`(\mathit{Sch}/S)_{\acute{e}tale} \to S_{\acute{e}tale}`. -/
@[stacks 021G]
instance smallEtaleToBigEtaleFunctor_id_isMorphismOfSites :
    IsMorphismOfSites J_small J_big (smallEtaleToBigEtaleFunctor (𝟙 S)) := sorry

/-- Helper: the inverse-image functor on sheaves attached to the small-to-big étale site morphism
preserves finite limits, so it packages into a morphism of topoi. -/
instance smallEtaleToBigEtaleFunctor_id_sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits
      ((smallEtaleToBigEtaleFunctor (𝟙 S)).sheafPullback (Type (u + 1)) J_small J_big) := sorry

/-- Lemma 34.4.14 (2): the site morphism from (1) induces a morphism of topoi
`\pi_S : \mathit{Sh}((\mathit{Sch}/S)_{\acute{e}tale}) \to \mathit{Sh}(S_{\acute{e}tale})`. -/
@[stacks 021G]
abbrev smallEtaleToBigEtaleSiteMorphismOfTopoi :
    MorphismOfTopoiIn J_small J_big :=
  (smallEtaleToBigEtaleFunctor (𝟙 S)).morphismOfTopoiInOfContinuous J_small J_big

/-- Lemma 34.4.14 (3): composing the site-induced morphism of topoi with the Chapter 34 morphism
`i_{\mathrm{id}_S}` from Lemma 34.4.13 gives the identity on `\mathit{Sh}(S_{\acute{e}tale})`.
This is the Lean owner-level form of the source statement `\pi_S \circ i_S = \mathrm{id}`, with
`i_S` identified with `i_{\mathrm{id}_S}`. -/
@[stacks 021G]
theorem smallEtaleToBigEtaleSiteMorphism_comp_id :
    MorphismOfTopoiIn.comp
        (smallEtaleToBigEtaleSiteMorphismOfTopoi S)
        (smallEtaleToBigEtaleMorphismOfTopoi (𝟙 S)) =
      MorphismOfTopoiIn.id J_small := sorry

/-- Lemma 34.4.14 (4): for a sheaf `\mathcal{G}` on `(\mathit{Sch}/S)_{\acute{e}tale}` and an
object `U/S` of `S_{\acute{e}tale}`, the inverse image `i_S^{-1}(\mathcal{G}) = \pi_{S,*}
(\mathcal{G})` is computed by evaluation on the same scheme viewed over `S`. -/
@[stacks 021G]
theorem smallEtaleToBigEtaleSiteMorphism_pushforward_obj_obj
    (𝒢 : Sheaf J_big (Type (u + 1))) (U : S.Etale) :
    (((smallEtaleToBigEtaleSiteMorphismOfTopoi S) _*).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((smallEtaleToBigEtaleFunctor (𝟙 S)).obj U)) := sorry

end AlgebraicGeometry.Scheme
