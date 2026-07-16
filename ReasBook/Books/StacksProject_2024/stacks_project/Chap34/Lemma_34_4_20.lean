import Mathlib
import StacksProject_2024.stacks_project.Chap07.Remark_7_26_7

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

section

variable (S : Scheme.{u})

local notation "J_big" => S.overGrothendieckTopology @Etale

-- Semantic recall: `lean_leansearch` surfaced the generic sheaf-pullback owners on sites, and
-- local Chapter 7 precedent identifies Remark 7.26.7 as the exact source-faithful owner for
-- "a sheaf is given by local sheaves plus transition maps"; here the localized slice over
-- `T/S ∈ Over S` with étale arrows is the canonical owner corresponding to `T_{\acute{e}tale}`.

/-- The localized slice family over `(\mathit{Sch}/S)_{\acute{e}tale}` whose objects over `T/S`
are morphisms `U \to T` that are étale on underlying schemes. -/
instance smallEtaleLocalizedSliceFamily :
    CategoryTheory.GrothendieckTopology.LocalizedSliceFamily J_big
      (fun X : Over S ↦ fun Y : Over X ↦ Etale Y.hom.left) := sorry

/-- Lemma 34.4.20: the canonical functor from sheaves on the big étale site
`(\mathit{Sch}/S)_{\acute{e}tale}` to localized glueing data for the étale localized slices is an
equivalence. Equivalently, a sheaf on `(\mathit{Sch}/S)_{\acute{e}tale}` is given by sheaves
`\mathcal F_T` on the small étale sites `T_{\acute{e}tale}` together with comparison maps
`c_f : f_{small}^{-1}\mathcal F_T \to \mathcal F_{T'}` that are compatible with composition and
are isomorphisms when `f` is étale. -/
@[stacks 021K]
theorem sheafToSmallEtaleGlueingFunctor_isEquivalence :
    Functor.IsEquivalence
      (CategoryTheory.GrothendieckTopology.sheafToLocalizedSliceGlueingFunctor J_big
        (fun X : Over S ↦ fun Y : Over X ↦ Etale Y.hom.left)) := sorry

end

end AlgebraicGeometry.Scheme
