import Mathlib.Algebra.Group.Conj
import Mathlib.RepresentationTheory.Irreducible
import LinearRepresentations_Serre_1977.Chap04.ContinuousIrreducibleFamily

noncomputable section

-- Semantic recall: Chapter 3 already uses the canonical `FDRep` owner together with
-- `PairwiseNonisomorphic`, while Chapter 4 records continuity directly on representations through
-- `Representation.IsContinuous`. The compact-group theorem is therefore stated on `FDRep ℂ G`
-- families plus direct continuous-realizability and completeness hypotheses, rather than through
-- package-style continuity owners.

namespace Representation

open CategoryTheory

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- Theorem 4-30 (1) — Infinitude of Conjugacy Classes and Irreducibles: if a compact group `G`
is not finite, then `G` has infinitely many conjugacy classes. -/
theorem infinite_conjClasses_of_not_finite (hG : ¬ Finite G) :
    Infinite (ConjClasses G) := sorry

/-- Theorem 4-30 (2) — Infinitude of Conjugacy Classes and Irreducibles: if a compact group `G`
is not finite, then there is no finite family of pairwise nonisomorphic irreducible objects of
`FDRep ℂ G` whose members all admit continuous realizations and which is complete for continuous
irreducible finite-dimensional complex representations of `G`. The public statement uses the
source-facing owners `FDRep.HasContinuousRealization` and
`IsCompleteContinuousIrreducibleFamily` instead of an existential/typeclass tower. -/
theorem not_exists_finite_complete_irreducible_family_of_not_finite
    (hG : ¬ Finite G) :
    ¬ ∃ (ι : Type) (π : ι → FDRep ℂ G),
      Finite ι ∧
        PairwiseNonisomorphic π ∧
        (∀ i, FDRep.HasContinuousRealization (π i)) ∧
        IsCompleteContinuousIrreducibleFamily π := sorry

end

end Representation
