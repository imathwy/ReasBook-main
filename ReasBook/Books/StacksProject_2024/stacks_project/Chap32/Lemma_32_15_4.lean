import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical owners
-- `UniversallyClosed`, `ValuativeCriterion.Existence`, and
-- `UniversallyClosed.of_valuativeCriterion`; local Chapter 32 precedent records affine-space
-- testing as `pullback.snd f (AffineSpace (Fin n) S ↘ S)` and displayed valuative squares as
-- `ValuativeCommSq` / `CommSq.HasLift`.

/-- A DVR-restricted existence condition for valuative squares over a morphism `f`.
It says that every square of the form `Spec(K) ⟶ X` over `Spec(R) ⟶ S`, where `R` is a
discrete valuation ring with fraction field `K`, admits a dotted lift `Spec(R) ⟶ X`. -/
@[stacks 05JY]
def DvrValuativeCriterionExistence {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (i₁ : Spec (CommRingCat.of K) ⟶ X)
    (i₂ : Spec (CommRingCat.of R) ⟶ S)
    (sq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) f i₂),
      sq.HasLift

/-- The DVR-restricted valuative existence predicate is exactly the explicit dotted-arrow
condition for all discrete-valuation-ring valuative squares. -/
@[stacks 05JY]
theorem dvrValuativeCriterionExistence_iff_hasLift {X S : Scheme.{u}} (f : X ⟶ S) :
    DvrValuativeCriterionExistence f ↔
      ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        [Field K] [Algebra R K] [IsFractionRing R K]
        (i₁ : Spec (CommRingCat.of K) ⟶ X)
        (i₂ : Spec (CommRingCat.of R) ⟶ S)
        (sq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) f i₂),
          sq.HasLift := sorry

/-- Lemma 32.15.4: let `f : X ⟶ S` be a finite type morphism of schemes and assume `S` is
locally Noetherian. Then the following are equivalent: `f` is universally closed; for every `n`,
the morphism `\mathbf A^n × X ⟶ \mathbf A^n × S` obtained by base change along
`\mathbf A^n_S ⟶ S` is closed; every valuative square of the form `32.15.1.1` admits a dotted
arrow; and the same dotted-arrow existence condition holds for all such squares with the base ring
a discrete valuation ring. -/
@[stacks 05JY]
theorem universallyClosed_tfae_affineSpace_closed_valuativeCriterionExistence_dvr
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f] [IsLocallyNoetherian S] :
    List.TFAE
      [ UniversallyClosed f
      , ∀ n : ℕ, IsClosedMap (pullback.snd f (AffineSpace (Fin n) S ↘ S)).base
      , ValuativeCriterion.Existence f
      , DvrValuativeCriterionExistence f
      ] := sorry

end AlgebraicGeometry
