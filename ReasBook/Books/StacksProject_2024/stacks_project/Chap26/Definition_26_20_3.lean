import Mathlib.AlgebraicGeometry.ValuativeCriterion

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

-- Semantic recall: mathlib already packages the existence and uniqueness parts of the valuative
-- criterion for scheme morphisms as `ValuativeCriterion.Existence` and
-- `ValuativeCriterion.Uniqueness`. The full valuative criterion itself is the canonical
-- property `ValuativeCriterion`, with its source-facing conjunction packaged by
-- `ValuativeCriterion.iff`.

/- Definition 26.20.3 (1): the existence part of the valuative criterion for a morphism of schemes
is the canonical morphism property `ValuativeCriterion.Existence`. -/
#check ValuativeCriterion.Existence

/- Definition 26.20.3 (2): the uniqueness part of the valuative criterion for a morphism of
schemes is the canonical morphism property `ValuativeCriterion.Uniqueness`. -/
#check ValuativeCriterion.Uniqueness

/- Companion recall: satisfying the full valuative criterion is the canonical property
`ValuativeCriterion`. -/
#check ValuativeCriterion

/- Companion recall: the full valuative criterion is the conjunction of its existence and
uniqueness parts via the canonical characterization `ValuativeCriterion.iff`. -/
#check ValuativeCriterion.iff
