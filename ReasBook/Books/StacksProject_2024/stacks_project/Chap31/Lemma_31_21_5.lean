import Mathlib
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap29.Lemma_29_31_3
import StacksProject_2024.Chap31.Definition_31_21_1
import StacksProject_2024.Chap31.Lemma_31_20_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced only the ambient immersion and finite-presentation
-- owners, not a global owner for the canonical map `(31.19.1.2)`. Local Chapter 29/31 precedent
-- therefore fixes the conormal sheaf owner `immersionConormalSheaf`, the closed-immersion ideal
-- owner `closedImmersionIdealSubobject`, and the two source-facing ideal-sheaf criteria from
-- Lemma 31.20.4.

section

variable {X Z : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]

/-- A closed-immersion presentation of `i` satisfying the conormal criterion from
Lemma 31.21.5: the local conormal sheaf is finite locally free, and the affine-local
associated-graded criterion from Lemma 31.20.4 holds. This is the source-faithful form currently
available in the project for the source conditions that `\mathcal C_{Z/X}` is finite locally free
and that the canonical map `(31.19.1.2)` is an isomorphism. -/
@[stacks 063M]
def immersionFiniteLocallyFreeConormalAndAssociatedGradedCriterion
    (i : Z ⟶ X) [IsImmersion i] : Prop :=
  ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme, ∃ hclosed : IsClosedImmersion j,
    j ≫ U.ι = i ∧
      (letI : IsClosedImmersion j := hclosed
       SheafOfModules.IsFiniteLocallyFree (immersionConormalSheaf j) ∧
         AlgebraicGeometry.RingedSpace.idealSheafConormalFiniteLocallyFreeCriterion
           (closedImmersionIdealSubobject j) ∧
           AlgebraicGeometry.RingedSpace.idealSheafAssociatedGradedPolynomialCriterion
             (closedImmersionIdealSubobject j))

/-- Lemma 31.21.5: an immersion `i : Z ⟶ X` is quasi-regular if and only if it is locally of
finite presentation and admits a closed-immersion presentation satisfying the finite-locally-free
conormal and associated-graded criterion above. In the current project, this criterion is the
source-faithful replacement for the source clauses that `\mathcal C_{Z/X}` is finite locally free
and that the canonical map `(31.19.1.2)` is an isomorphism. -/
@[stacks 063M]
theorem isQuasiRegularImmersion_iff_locallyOfFinitePresentation_and_conormalCriterion
    (i : Z ⟶ X) [IsImmersion i] :
    IsQuasiRegularImmersion i ↔
      LocallyOfFinitePresentation i ∧
        immersionFiniteLocallyFreeConormalAndAssociatedGradedCriterion i := sorry

end

end AlgebraicGeometry
