import stacks_project.Chap04.Definition_4_35_1
import stacks_project.Chap04.Definition_4_33_9
import stacks_project.Chap04.Lemma_4_33_7
import stacks_project.Chap07.Definition_7_13_1
import stacks_project.Chap08.Definition_8_3_5
import stacks_project.Chap08.Lemma_8_10_1

noncomputable section

universe u v w

namespace CategoryTheory

namespace FibredCategoryOver

variable {C : Type u} [Category.{v} C]

/-- Helper for Lemma 8.10.5: the componentwise image of a fixed-target family under the
projection functor. -/
def projectionImageFamily
    (X : FibredCategoryOver C) {y : X.S} (S : SemiRepresentableFamily.Over.{w} y) :
    SemiRepresentableFamily.Over (X.p.obj y) where
  index := S.index
  obj := fun i ↦ (Over.post X.p).obj (S.obj i)

/-- Helper for Lemma 8.10.5: an inherited covering family maps to a covering family downstairs.
The source proof first refines the inherited cover by a generating strongly cartesian family, then
enlarges that downstairs generator to the actual image family. -/
theorem image_family_isCovering_of_inherited_family_covering
    (J : GrothendieckTopology C) (X : FibredCategoryOver C) [IsFibredInGroupoids X.p]
    {y : X.S} (S : SemiRepresentableFamily.Over.{w} y)
    (hS :
      Presieve.ofArrows (fun i ↦ (S.obj i).left) (fun i ↦ (S.obj i).hom) ∈
        ((stronglyCartesianLiftPrecoverage J.toPrecoverage X.p).toGrothendieck.toPrecoverage) y) :
    Presieve.ofArrows (fun i ↦ X.p.obj ((S.obj i).left)) (fun i ↦ X.p.map ((S.obj i).hom)) ∈
      J.toPrecoverage (X.p.obj y) := by
  -- TODO: extract the exact `ProjectionSite` argument once the inherited precoverage exposes a
  -- public `HasPullbacks`/stability bridge for
  -- `Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition`.
  -- The intended proof is still the source-faithful refinement to a strongly cartesian generating
  -- family followed by enlargement to the full projected image family.
  sorry

end FibredCategoryOver

end CategoryTheory
