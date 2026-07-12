import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import StacksProject_2024.Chap29.Definition_29_15_1
import StacksProject_2024.Chap29.Definition_29_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `ValuativeCriterion`,
-- `ValuativeCriterion.Existence`, `ValuativeCriterion.Uniqueness`, and
-- `IsProper.of_valuativeCriterion`; nearby Chapter 32 precedent represents the displayed
-- valuative squares by `CommSq`, with dotted arrows as `HasLift`/`LiftStruct`, and uses
-- `genericPointsOfIrreducibleComponents` plus `Scheme.fromSpecResidueField` for the generic-point
-- specialization.

/-- A DVR-restricted valuative criterion with exactly one dotted arrow in every square over `f`. -/
@[stacks 0208]
def DvrValuativeCriterionExistsUnique {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (i₁ : Spec (CommRingCat.of K) ⟶ X)
    (i₂ : Spec (CommRingCat.of R) ⟶ S)
    (sq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) f i₂),
      sq.HasLift ∧ Subsingleton sq.LiftStruct

/-- The generic-point DVR-valuative existence condition: for every generic point of an irreducible
component of `X`, every DVR whose fraction field is the residue field at that point admits a dotted
arrow for the canonical map `Spec(κ(η)) ⟶ X`. -/
@[stacks 0208]
def GenericPointDvrValuativeCriterionExistence {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ ⦃η : X⦄, η ∈ genericPointsOfIrreducibleComponents X →
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Algebra R (X.residueField η)] [IsFractionRing R (X.residueField η)]
      (i₂ : Spec (CommRingCat.of R) ⟶ S)
      (sq : CommSq (X.fromSpecResidueField η)
        (Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField η)))) f i₂),
        sq.HasLift

/-- The generic-point DVR-valuative criterion with exactly one dotted arrow for every canonical
generic-point square over `f`. -/
@[stacks 0208]
def GenericPointDvrValuativeCriterionExistsUnique {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ ⦃η : X⦄, η ∈ genericPointsOfIrreducibleComponents X →
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Algebra R (X.residueField η)] [IsFractionRing R (X.residueField η)]
      (i₂ : Spec (CommRingCat.of R) ⟶ S)
      (sq : CommSq (X.fromSpecResidueField η)
        (Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField η)))) f i₂),
        sq.HasLift ∧ Subsingleton sq.LiftStruct

/-- The DVR exists-unique predicate splits into existence of a lift for every DVR-valuative square
and uniqueness of such lifts. -/
@[stacks 0208]
theorem dvrValuativeCriterionExistsUnique_iff_hasLift_and_uniqueness
    {X S : Scheme.{u}} (f : X ⟶ S) :
    DvrValuativeCriterionExistsUnique f ↔
      (∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        [Field K] [Algebra R K] [IsFractionRing R K]
        (i₁ : Spec (CommRingCat.of K) ⟶ X)
        (i₂ : Spec (CommRingCat.of R) ⟶ S)
        (sq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) f i₂),
          sq.HasLift) ∧
      (∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        [Field K] [Algebra R K] [IsFractionRing R K]
        (i₁ : Spec (CommRingCat.of K) ⟶ X)
        (i₂ : Spec (CommRingCat.of R) ⟶ S)
        (sq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) f i₂),
          Subsingleton sq.LiftStruct) := sorry

/-- The generic-point DVR exists-unique predicate is the conjunction of generic-point DVR
existence and uniqueness. -/
@[stacks 0208]
theorem genericPointDvrValuativeCriterionExistsUnique_iff_existence_and_uniqueness
    {X S : Scheme.{u}} (f : X ⟶ S) :
    GenericPointDvrValuativeCriterionExistsUnique f ↔
      GenericPointDvrValuativeCriterionExistence f ∧
        (∀ ⦃η : X⦄, η ∈ genericPointsOfIrreducibleComponents X →
          ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
            [Algebra R (X.residueField η)] [IsFractionRing R (X.residueField η)]
            (i₂ : Spec (CommRingCat.of R) ⟶ S)
            (sq : CommSq (X.fromSpecResidueField η)
              (Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField η)))) f i₂),
              Subsingleton sq.LiftStruct) := sorry

/-- Lemma 32.15.3: for a finite type morphism `f : X ⟶ S` over a locally Noetherian scheme,
properness is equivalent to the full valuative criterion, to the same exists-unique condition
tested only on discrete valuation rings, and to testing the DVR exists-unique condition only on
the canonical generic-point maps of the irreducible components of `X`. -/
@[stacks 0208]
theorem isProper_tfae_valuativeCriterion_dvr_genericPoint
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f] [IsLocallyNoetherian S] :
    List.TFAE
      [ IsProper f
      , ValuativeCriterion f
      , DvrValuativeCriterionExistsUnique f
      , GenericPointDvrValuativeCriterionExistsUnique f
      ] := sorry

end AlgebraicGeometry
