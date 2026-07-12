import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap04.Definition_4_35_1
import StacksProject_2024.Chap07.Lemma_7_28_1
import StacksProject_2024.Chap07.Lemma_7_28_4
import StacksProject_2024.Chap08.Lemma_8_10_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

namespace FibredCategoryOver

variable {C : Type u} [Category.{v} C]

section

variable (J : GrothendieckTopology C) (X : FibredCategoryOver C)

/-
Domain-style sampling for Lemma 8.10.4:
- primary domain: categories fibred in groupoids over a site and the induced localized functors on
  slice categories.
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `Over.post`,
  `CategoryTheory.overPost_isContinuous`,
  `CategoryTheory.overPost_isCocontinuous`.
- best owner abstraction: the site-theoretic owner is the projection functor `X.p` equipped with
  continuity and cocontinuity from the inherited topology to the base topology; the localized
  statements for `Over.post X.p` are then derived slice specializations of the Chapter 7 owner
  theorems.
- primitive data: the fibred-in-groupoids projection `X.p`, the inherited topology
  `inheritedTopology J X`, and the chosen object `x : X.S`.
- derived API: the localized continuity and cocontinuity of `Over.post X.p`, obtained by
  synthesizing the Chapter 7 slice-site owners from the owner instances on `X.p`.

Source/core/bridge triage:
- `source-facing`: the equivalence statement
  `overPost_isEquivalence_of_isFibredInGroupoids`;
- `core/canonical`: the owner classes `Functor.IsContinuous`, `Functor.IsCocontinuous`, and the
  slice functor `Over.post`;
- `bridge/view`: the localized slice-site syntheses below, which specialize the Chapter 7
  `Over.post` owners to the inherited topology of a fibred category in groupoids.
-/

-- Proof sketch: the induced functor on slices sends `y ⟶ x` to `p.map (y ⟶ x) : p(y) ⟶ p(x)`.
-- Essential surjectivity comes from choosing a cartesian lift of any arrow into `p(x)`, and full
-- faithfulness comes from the uniqueness of lifts in a category fibred in groupoids.
/-- Lemma 8.10.4: if `X` is a category fibred in groupoids over the site `(C, J)` and `x : X.S`
lies over `U = X.p.obj x`, then the induced slice functor `X/x ⥤ C/U` is an equivalence of
categories. Together with the projection continuity and cocontinuity instances below, and the
canonical localized slice-site syntheses, this is the textbook equivalence of sites. -/
theorem overPost_isEquivalence_of_isFibredInGroupoids
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] (x : X.S) :
    (Over.post X.p : Over x ⥤ Over (X.p.obj x)).IsEquivalence := sorry

/-- The projection of a category fibred in groupoids is continuous from the inherited topology on
the total category to the base topology. -/
instance isContinuous_of_isFibredInGroupoids
    (J : GrothendieckTopology C) (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] :
    X.p.IsContinuous (inheritedTopology J X) J := sorry

/-- The projection of a category fibred in groupoids is cocontinuous from the inherited topology
on the total category to the base topology. -/
instance isCocontinuous_of_isFibredInGroupoids
    (J : GrothendieckTopology C) (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] :
    X.p.IsCocontinuous (inheritedTopology J X) J := sorry

variable [IsFibredInGroupoids X.p] (x : X.S)

/- Companion recall: once `X.p` carries the owner continuity/cocontinuity instances above, the
localized slice functor `Over.post X.p` is exactly the Chapter 7 owner specialization. -/
#check overPost_isContinuous X.p x

#check overPost_isCocontinuous (inheritedTopology J X) J X.p x

end

end FibredCategoryOver

end CategoryTheory
