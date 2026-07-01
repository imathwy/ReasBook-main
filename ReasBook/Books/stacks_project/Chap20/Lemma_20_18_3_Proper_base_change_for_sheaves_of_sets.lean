import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open TopCat

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X Y Y' : TopCat.{u}}

/-- The source sheaf `g^{-1} f_* \mathcal F` in the proper base change comparison for sheaves of
sets. -/
abbrev properBaseChangeSetSheafSource (f : X ⟶ Y) (g : Y' ⟶ Y) (ℱ : X.Sheaf (Type u)) :
    Y'.Sheaf (Type u) :=
  (TopCat.Sheaf.pullback (Type u) g).obj ((TopCat.Sheaf.pushforward (Type u) f).obj ℱ)

/-- The target sheaf `f'_* (g')^{-1} \mathcal F` in the proper base change comparison for sheaves
of sets. -/
abbrev properBaseChangeSetSheafTarget (f : X ⟶ Y) (g : Y' ⟶ Y) (ℱ : X.Sheaf (Type u)) :
    Y'.Sheaf (Type u) :=
  (TopCat.Sheaf.pushforward (Type u) (pullback.snd f g)).obj
    ((TopCat.Sheaf.pullback (Type u) (pullback.fst f g)).obj ℱ)

section ProperBaseChangeForSheavesOfSets

variable (f : X ⟶ Y) (g : Y' ⟶ Y)

-- Proof sketch: reduce to stalks at points of `Y'`, as in the abelian proper base change theorem.
-- Identify both stalks with sections of the restriction of `\mathcal F` to the fiber over the
-- image point, then apply the set-valued version of the fiberwise description from
-- Lemmas `20.18.1` and `20.16.3`.
/-- Lemma 20.18.3 (Proper base change for sheaves of sets): for a cartesian square of topological
spaces with `X' = Y' ×[Y] X`, a proper map `f : X ⟶ Y`, and a sheaf of sets `\mathcal F` on `X`,
the inverse image `g^{-1} f_* \mathcal F` is canonically isomorphic to
`f'_* (g')^{-1} \mathcal F`, where `g' : X' ⟶ X` and `f' : X' ⟶ Y'` are the pullback
projections. -/
theorem proper_base_change_set_sheaf_isomorphic
    (hf : IsProperMap f) (ℱ : X.Sheaf (Type u)) :
    IsIsomorphic (properBaseChangeSetSheafSource f g ℱ) (properBaseChangeSetSheafTarget f g ℱ) :=
  sorry

end ProperBaseChangeForSheavesOfSets

end TopCat.Sheaf
