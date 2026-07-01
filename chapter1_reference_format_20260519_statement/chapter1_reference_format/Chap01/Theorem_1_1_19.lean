import Mathlib
import chapter1_reference_format.Chap01.Theorem_1_7_19

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Theorem 1.1.19: transfinite induction says that if a subset `A` contains every element `a`
whose strict initial segment `Set.Iio a` is already contained in `A`, then `A` is all of the
ambient ordered type. The chapter's canonical owner for this statement is the set-level
well-founded induction theorem `Set.eq_univ_of_Iio_subset`, which specializes to well-ordered
sets. -/
recall Set.eq_univ_of_Iio_subset {S : Type u} [Preorder S] [WellFoundedLT S]
    (A : Set S) (hA : ∀ a : S, Set.Iio a ⊆ A → a ∈ A) :
    A = Set.univ
