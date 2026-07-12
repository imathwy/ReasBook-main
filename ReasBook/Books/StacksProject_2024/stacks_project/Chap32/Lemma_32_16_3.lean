import StacksProject_2024.Chap32.Lemma_32_16_1
import StacksProject_2024.Chap32.Lemma_32_16_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `IsProper.of_valuativeCriterion`,
-- `ValuativeCriterion.Uniqueness`, and the canonical `LiftStruct`/`HasLift` API; nearby
-- Lemmas 32.16.1 and 32.16.2 encode the dense-image DVR tests in these terms.

/-- Lemma 32.16.3: let `f : X ⟶ S` and `h : U ⟶ X` be morphisms of schemes. Assume that `S` is
locally Noetherian, that `f` and `h` are of finite type, and that `h(U)` is dense in `X`. If
every commutative DVR-valuative square whose generic arrow factors through `h` admits a unique
dotted arrow to `X`, then `f` is proper. -/
@[stacks 0CM5]
theorem isProper_of_dvrValuativeCriterionExistsUnique_from_denseRange
    {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
    [IsLocallyNoetherian S] [Scheme.Hom.FiniteType f] [Scheme.Hom.FiniteType h]
    (h_dense : DenseRange h)
    (h_valuative :
      ∀ (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
        [Field K] [Algebra A K] [IsFractionRing A K]
        (uK : Spec (CommRingCat.of K) ⟶ U)
        (sA : Spec (CommRingCat.of A) ⟶ S)
        (sq : CommSq (uK ≫ h)
          (Spec.map (CommRingCat.ofHom (algebraMap A K))) f sA),
          sq.HasLift ∧ Subsingleton sq.LiftStruct) :
    IsProper f := sorry

end AlgebraicGeometry
