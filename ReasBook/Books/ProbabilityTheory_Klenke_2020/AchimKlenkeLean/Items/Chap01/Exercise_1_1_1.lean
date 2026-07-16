import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap01.Theorem_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped MeasureTheory

universe u v

variable {Ω : Type u}

-- Proof sketch: disjointify the countable family by recursively removing the previously covered
-- part; each difference of one semiring set with a finite union of previous semiring sets can be
-- refined into a finite disjoint family in the semiring, and then these finite refinements are
-- reindexed by `ℕ`.
/-- Exercise 1.1.1: A countable union of members of a semiring of sets can be rewritten as a
countable pairwise disjoint union of members of the same semiring. -/
theorem exists_disjoint_iUnion_eq_iUnion_of_isSetSemiring {A : Set (Set Ω)}
    (hA : IsSetSemiring A) (s : ℕ → Set Ω) (hs : ∀ n, s n ∈ A) :
    ∃ d : ℕ → Set Ω, IsDisjointUnionDecomposition A s d := sorry

-- Proof sketch: enumerate the finite family by its index type, apply the same finite-step
-- disjointification argument, and keep only the pieces indexed by the original `Finset`.
/-- A finite union of members of a semiring of sets can be rewritten as a finite pairwise disjoint
union of members of the same semiring. -/
theorem exists_disjoint_biUnion_eq_biUnion_of_isSetSemiring {A : Set (Set Ω)} {ι : Type v}
    (hA : IsSetSemiring A) (t : Finset ι) (s : ι → Set Ω) (hs : ∀ i ∈ t, s i ∈ A) :
    ∃ d : ↑t → Set Ω, IsDisjointUnionDecomposition A (fun i : ↑t ↦ s i) d := sorry
