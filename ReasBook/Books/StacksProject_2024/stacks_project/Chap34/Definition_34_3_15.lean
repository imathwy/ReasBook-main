import Mathlib
import StacksProject_2024.Chap34.Lemma_34_3_14

open CategoryTheory
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

local notation "J_small" => S.smallZariskiTopology
local notation "J_big" => S.bigZariskiTopology

-- Semantic recall: `lean_leansearch` found the generic sheaf pushforward owner
-- `Functor.sheafPushforwardContinuous`; the local Chapter 34 owner is the direct-image functor
-- of `smallZariskiToBigZariskiSiteMorphismOfTopoi S` from Lemma 34.3.14.

/-- Definition 34.3.15: in the situation of Lemma 34.3.14, the direct image
`π_{S,*}` is the restriction functor from sheaves on the big Zariski site of `S` to sheaves on the
small Zariski site of `S`. For a big-site sheaf `𝓕`, `(smallZariskiSiteRestriction S).obj 𝓕`
formalizes `𝓕|_{S_Zar}`. -/
@[stacks 04BS]
abbrev smallZariskiSiteRestriction :
    Sheaf J_big (Type (u + 1)) ⥤ Sheaf J_small (Type (u + 1)) :=
  (smallZariskiToBigZariskiSiteMorphismOfTopoi S) _*

/-- Evaluating the restriction functor on a big Zariski sheaf is the direct image along `π_S`. -/
@[stacks 04BS]
theorem smallZariskiSiteRestriction_obj (𝓕 : Sheaf J_big (Type (u + 1))) :
    (smallZariskiSiteRestriction S).obj 𝓕 =
      ((smallZariskiToBigZariskiSiteMorphismOfTopoi S) _*).obj 𝓕 := sorry

end AlgebraicGeometry.Scheme
