import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_1

open CategoryTheory
open CategoryTheory.Limits

universe u

-- Semantic recall via `lean_leansearch` surfaced only the general discrete-limit/product API for
-- `AddCommGrpCat`, not a standalone Chapter 18 additivity theorem. Local precedent from
-- `Theorem_18_1_1` already packages the source axiom on the canonical owner
-- `PairCohomologyTheory`.

/- Axiom 18.1.4. Cohomology additivity sends disjoint unions of pairs to products of cohomology
groups. Because `PairCohomologyTheory.cohomology q` is contravariant, this is formalized as the
field `PairCohomologyTheory.additivity`, asserting preservation of limits of discrete diagrams. -/
recall PairCohomologyTheory.additivity {π : Type u} [AddCommGroup π]
    (H : PairCohomologyTheory π) (q : ℤ) {ι : Type u} :
    PreservesLimitsOfShape (Discrete ι) (H q)

recall SpacePair.sigmaPair {ι : Type u} (P : ι → SpacePair.{u}) : SpacePair
