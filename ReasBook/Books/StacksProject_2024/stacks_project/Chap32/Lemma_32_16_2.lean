import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `IsSeparated`,
-- `ValuativeCriterion.Uniqueness`, and `CommSq.LiftStruct`; nearby Chapter 32 files encode
-- finite type morphisms as `Scheme.Hom.FiniteType` and DVR-valuative uniqueness as
-- `Subsingleton sq.LiftStruct`.

/-- Lemma 32.16.2: let `f : X ⟶ S` and `h : U ⟶ X` be morphisms of schemes. Assume that `S` is
locally Noetherian, that `f` is locally of finite type, that `h` is of finite type, and that
`h(U)` is dense in `X`. If every commutative DVR-valuative square whose generic arrow factors
through `h` admits at most one dotted arrow to `X`, then `f` is separated. -/
@[stacks 0CM4]
theorem isSeparated_of_dvrValuativeCriterionUniqueness_from_denseRange
    {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [Scheme.Hom.FiniteType h]
    (h_dense : DenseRange h)
    (h_valuative :
      ∀ (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
        [Field K] [Algebra A K] [IsFractionRing A K]
        (uK : Spec (CommRingCat.of K) ⟶ U)
        (sA : Spec (CommRingCat.of A) ⟶ S)
        (sq : CommSq (uK ≫ h)
          (Spec.map (CommRingCat.ofHom (algebraMap A K))) f sA),
          Subsingleton sq.LiftStruct) :
    IsSeparated f := sorry

end AlgebraicGeometry
