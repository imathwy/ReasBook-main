import Mathlib
import StacksProject_2024.Chap07.Lemma_7_21_1
import StacksProject_2024.Chap07.Lemma_7_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe w vC vD uC uD

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the generic continuous and cocontinuous sheaf
-- pushforward owners; the local Chapter 7 owner for the retraction statement is
-- `u.sheafAdjunctionContinuous` from Sites, Lemma 7.21.8, packaged here through
-- `Functor.morphismOfTopoiInOfContinuous` and `Functor.morphismOfTopoiInOfCocontinuous`.

/-- The five big scheme topologies used in change-of-big-site statements. -/
inductive BigSchemeTopologyKind where
  /-- The Zariski topology. -/
  | zariski
  /-- The etale topology. -/
  | etale
  /-- The smooth topology. -/
  | smooth
  /-- The syntomic topology. -/
  | syntomic
  /-- The fppf topology. -/
  | fppf

/-- Helper: the functor induced on over-categories by a big-site inclusion. -/
abbrev bigSiteInclusionOverFunctor
    {Sch : Type uC} {Sch' : Type uD}
    [Category.{vC} Sch] [Category.{vD} Sch']
    (inclusion : Sch ⥤ Sch') (S : Sch) :
    Over S ⥤ Over (inclusion.obj S) :=
  Over.post inclusion

/-- Lemma 34.12.2 (1): for one of the five big scheme topologies, if an inclusion functor
`Sch_tau -> Sch'_tau` satisfies the hypotheses of Sites, Lemma 7.21.8, then the continuous and
cocontinuous morphisms of topoi attached to this inclusion compose to the identity on
`Sh(Sch_tau)`. -/
@[stacks 022K]
theorem bigSiteInclusion_morphismOfTopoiIn_comp_id
    (tau : BigSchemeTopologyKind)
    {Sch : Type uC} {Sch' : Type uD}
    [Category.{vC} Sch] [Category.{vD} Sch']
    (J : GrothendieckTopology Sch) (K : GrothendieckTopology Sch')
    (inclusion : Sch ⥤ Sch')
    [inclusion.Full] [inclusion.Faithful]
    [inclusion.IsContinuous J K] [inclusion.IsCocontinuous J K]
    [HasWeakSheafify K (Type w)]
    [∀ P : Schᵒᵖ ⥤ Type w, inclusion.op.HasLeftKanExtension P]
    [PreservesFiniteLimits (inclusion.sheafPullback (Type w) J K)]
    [HasSheafify J (Type w)]
    [∀ P : Schᵒᵖ ⥤ Type w, inclusion.op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn.comp
        (inclusion.morphismOfTopoiInOfContinuous J K)
        (inclusion.morphismOfTopoiInOfCocontinuous J K) =
      MorphismOfTopoiIn.id J := sorry

/-- Lemma 34.12.2 (2): with the same topology and big-site inclusion, for every object `S` of
`Sch_tau`, the induced inclusion of localized sites `(Sch/S)_tau -> (Sch'/S)_tau` satisfies the
same conclusion: the associated morphisms of topoi compose to the identity on
`Sh((Sch/S)_tau)`. -/
@[stacks 022K]
theorem bigSiteInclusion_over_morphismOfTopoiIn_comp_id
    (tau : BigSchemeTopologyKind)
    {Sch : Type uC} {Sch' : Type uD}
    [Category.{vC} Sch] [Category.{vD} Sch']
    (J : GrothendieckTopology Sch) (K : GrothendieckTopology Sch')
    (inclusion : Sch ⥤ Sch') (S : Sch)
    [(bigSiteInclusionOverFunctor inclusion S).Full]
    [(bigSiteInclusionOverFunctor inclusion S).Faithful]
    [(bigSiteInclusionOverFunctor inclusion S).IsContinuous (J.over S) (K.over (inclusion.obj S))]
    [(bigSiteInclusionOverFunctor inclusion S).IsCocontinuous (J.over S) (K.over (inclusion.obj S))]
    [HasWeakSheafify (K.over (inclusion.obj S)) (Type w)]
    [∀ P : (Over S)ᵒᵖ ⥤ Type w,
      (bigSiteInclusionOverFunctor inclusion S).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((bigSiteInclusionOverFunctor inclusion S).sheafPullback
        (Type w) (J.over S) (K.over (inclusion.obj S)))]
    [HasSheafify (J.over S) (Type w)]
    [∀ P : (Over S)ᵒᵖ ⥤ Type w,
      (bigSiteInclusionOverFunctor inclusion S).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn.comp
        ((bigSiteInclusionOverFunctor inclusion S).morphismOfTopoiInOfContinuous
          (J.over S) (K.over (inclusion.obj S)))
        ((bigSiteInclusionOverFunctor inclusion S).morphismOfTopoiInOfCocontinuous
          (J.over S) (K.over (inclusion.obj S))) =
      MorphismOfTopoiIn.id (J.over S) := sorry

end AlgebraicGeometry
