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

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `IsProper`, `IsSeparated`, and `ValuativeCriterion`; nearby Chapter 32 files spell finite type
-- as `Scheme.Hom.FiniteType` and represent displayed valuative squares by `CommSq.HasLift`.

/-- Lemma 32.16.1: let `f : X ⟶ S` and `h : U ⟶ X` be morphisms of schemes. Assume that
`S` is locally Noetherian, that `f` and `h` are of finite type, that `f` is separated, and that
the image of `h` is dense in `X`. If every commutative DVR-valuative square whose generic arrow
factors through `h` admits a dotted arrow to `X`, then `f` is proper. -/
@[stacks 0CM3]
theorem isProper_of_dvrValuativeCriterion_from_denseRange
    {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
    [IsLocallyNoetherian S] [Scheme.Hom.FiniteType f] [Scheme.Hom.FiniteType h]
    [IsSeparated f] (h_dense : DenseRange h)
    (h_valuative :
      ∀ (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
        [Field K] [Algebra A K] [IsFractionRing A K]
        (uK : Spec (CommRingCat.of K) ⟶ U)
        (sA : Spec (CommRingCat.of A) ⟶ S)
        (sq : CommSq (uK ≫ h)
          (Spec.map (CommRingCat.ofHom (algebraMap A K))) f sA),
          sq.HasLift) :
    IsProper f := sorry

end AlgebraicGeometry
