import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap34.Lemma_34_4_14

open CategoryTheory
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

-- Semantic recall: `lean_leansearch` surfaced the canonical sheaf pushforward owner
-- `Functor.sheafPushforwardContinuous` and its objectwise formulas; the verified Chapter 34
-- specialization for this item is the source-facing morphism of topoi
-- `smallEtaleToBigEtaleSiteMorphismOfTopoi S` from `Lemma 34.4.14`, whose direct image is the
-- restriction functor denoted `\mathcal{F}|_{S_{\acute{e}tale}}` in the Stacks Project.

/- Definition 34.4.15: in the situation of Lemma 34.4.14, restriction from the big étale site of
`S` to the small étale site is the canonical direct-image functor of the morphism of topoi
`\pi_S : Sh((\mathrm{Sch}/S)_{\acute{e}tale}) ⥤ Sh(S_{\acute{e}tale})`, i.e.
`(smallEtaleToBigEtaleSiteMorphismOfTopoi S) _*`. -/
recall smallEtaleToBigEtaleSiteMorphismOfTopoi

/- Companion check: for a sheaf `\mathcal{F}` on the big étale site, its restriction
`\mathcal{F}|_{S_{\acute{e}tale}}` is the object
`(((smallEtaleToBigEtaleSiteMorphismOfTopoi S) _*).obj \mathcal{F})`
of `Sheaf S.smallEtaleTopology (Type (u + 1))`. -/
variable (𝒜 : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)))

#check (((smallEtaleToBigEtaleSiteMorphismOfTopoi S) _*).obj 𝒜)

end AlgebraicGeometry.Scheme
