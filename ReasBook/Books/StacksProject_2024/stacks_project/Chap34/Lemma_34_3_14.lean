import Mathlib
import StacksProject_2024.Chap07.Definition_7_14_1
import StacksProject_2024.Chap34.Lemma_34_3_13

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

local notation "J_small" => S.smallZariskiTopology
local notation "J_big" => S.bigZariskiTopology

-- Semantic recall: `lean_leansearch` surfaced generic sheaf/site owners, and the verified local
-- Chapter 34 source-facing owner for `i_{\mathrm{id}_S}` is
-- `smallZariskiToBigZariskiMorphismOfTopoi (𝟙 S)` from `Lemma_34_3_13`.

/-- Lemma 34.3.14 (1): the inclusion functor
`S_{Zar} ⥤ (\mathit{Sch}/S)_{Zar}` defines a morphism of sites
`(\mathit{Sch}/S)_{Zar} \to S_{Zar}`. -/
@[stacks 020Z]
instance smallZariskiToBigZariskiFunctor_id_isMorphismOfSites :
    IsMorphismOfSites J_small J_big (smallZariskiToBigZariskiFunctor (𝟙 S)) := sorry

/-- Helper: the inverse-image functor on sheaves attached to the small-to-big Zariski site morphism
preserves finite limits, so it packages into a morphism of topoi. -/
instance smallZariskiToBigZariskiFunctor_id_sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits
      ((smallZariskiToBigZariskiFunctor (𝟙 S)).sheafPullback (Type (u + 1)) J_small J_big) :=
  sorry

/-- Lemma 34.3.14 (2): the site morphism from (1) induces a morphism of topoi
`\pi_S : \mathit{Sh}((\mathit{Sch}/S)_{Zar}) \to \mathit{Sh}(S_{Zar})`. -/
@[stacks 020Z]
abbrev smallZariskiToBigZariskiSiteMorphismOfTopoi :
    MorphismOfTopoiIn J_small J_big :=
  (smallZariskiToBigZariskiFunctor (𝟙 S)).morphismOfTopoiInOfContinuous J_small J_big

/-- Lemma 34.3.14 (3): composing the site-induced morphism of topoi with the Chapter 34 morphism
`i_{\mathrm{id}_S}` from Lemma 34.3.13 gives the identity on `\mathit{Sh}(S_{Zar})`.
This is the Lean owner-level form of the source statement `\pi_S \circ i_S = \mathrm{id}`, with
`i_S` identified with `i_{\mathrm{id}_S}`. -/
@[stacks 020Z]
theorem smallZariskiToBigZariskiSiteMorphism_comp_id :
    MorphismOfTopoiIn.comp
        (smallZariskiToBigZariskiSiteMorphismOfTopoi S)
        (smallZariskiToBigZariskiMorphismOfTopoi (𝟙 S)) =
      MorphismOfTopoiIn.id J_small := sorry

/-- Lemma 34.3.14 (4): for a sheaf `\mathcal{G}` on `(\mathit{Sch}/S)_{Zar}` and an object
`U/S` of `S_{Zar}`, the inverse image `i_S^{-1}(\mathcal{G}) = \pi_{S,*}(\mathcal{G})`
is computed by evaluation on the same scheme viewed over `S`. -/
@[stacks 020Z]
theorem smallZariskiToBigZariskiSiteMorphism_pushforward_obj_obj
    (𝒢 : Sheaf J_big (Type (u + 1))) (U : S.smallZariskiSite) :
    (((smallZariskiToBigZariskiSiteMorphismOfTopoi S) _*).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((smallZariskiToBigZariskiFunctor (𝟙 S)).obj U)) := sorry

end AlgebraicGeometry.Scheme
