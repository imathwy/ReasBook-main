import Mathlib
import StacksProject_2024.Chap29.Definition_29_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical separatedness/valuative owners
-- `IsSeparated.valuativeCriterion`, `IsSeparated.of_valuativeCriterion`, and
-- `ValuativeCriterion.Uniqueness`; local Chapter 29 precedent provides
-- `genericPointsOfIrreducibleComponents` and `Scheme.fromSpecResidueField` for the generic-point
-- specialization appearing in the source.

/-- A DVR-restricted uniqueness condition for valuative squares over a scheme morphism `f`. -/
@[stacks 0207]
def DvrValuativeCriterionUniqueness {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (i₁ : Spec (CommRingCat.of K) ⟶ X)
    (i₂ : Spec (CommRingCat.of R) ⟶ S)
    (sq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) f i₂),
      Subsingleton sq.LiftStruct

/-- A DVR-restricted uniqueness condition on the canonical generic-point valuative squares of the
irreducible components of the source. -/
@[stacks 0207]
def GenericPointDvrValuativeCriterionUniqueness {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ ⦃η : X⦄, η ∈ genericPointsOfIrreducibleComponents X →
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Algebra R (X.residueField η)] [IsFractionRing R (X.residueField η)]
      (i₂ : Spec (CommRingCat.of R) ⟶ S)
      (sq : CommSq (X.fromSpecResidueField η)
        (Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField η)))) f i₂),
        Subsingleton sq.LiftStruct

/-- Under the locally Noetherian and locally finite type hypotheses, separatedness is equivalent to
the full valuative uniqueness condition. -/
@[stacks 0207]
theorem isSeparated_iff_valuativeCriterionUniqueness
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] :
    IsSeparated f ↔ ValuativeCriterion.Uniqueness f := sorry

/-- Restricting the valuative uniqueness condition to discrete valuation rings does not change the
criterion. -/
@[stacks 0207]
theorem valuativeCriterionUniqueness_iff_dvrValuativeCriterionUniqueness
    {X S : Scheme.{u}} (f : X ⟶ S) :
    ValuativeCriterion.Uniqueness f ↔ DvrValuativeCriterionUniqueness f := sorry

/-- Under the locally Noetherian and locally finite type hypotheses, it is enough to test
DVR-valuative uniqueness on the canonical generic-point maps of the irreducible components of the
source. -/
@[stacks 0207]
theorem dvrValuativeCriterionUniqueness_iff_genericPointDvrValuativeCriterionUniqueness
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] :
    DvrValuativeCriterionUniqueness f ↔ GenericPointDvrValuativeCriterionUniqueness f := sorry

/-- Lemma 32.15.2: let `S` be a locally Noetherian scheme and let `f : X ⟶ S` be locally of
finite type. Then `f` is separated if and only if for every generic point `η` of an irreducible
component of `X`, every discrete valuation ring with fraction field `κ(η)` admits at most one
valuative lift of the canonical map `Spec(κ(η)) ⟶ X` over `f`. -/
@[stacks 0207]
theorem isSeparated_iff_genericPointDvrValuativeCriterionUniqueness
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] :
    IsSeparated f ↔ GenericPointDvrValuativeCriterionUniqueness f := sorry

end AlgebraicGeometry
