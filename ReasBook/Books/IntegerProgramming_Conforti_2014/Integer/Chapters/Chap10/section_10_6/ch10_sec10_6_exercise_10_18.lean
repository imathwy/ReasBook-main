import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_25
import Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_1
import Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open Function

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling note:
-- * primary domain: mixed 0,1 lift-and-project statements on `MixedRealPoint n n`
-- * core owners inspected before refinement:
--   `MixedRealPoint`, `binary_prefix_points_on_subset`, `Set.IsPolytope`,
--   `lovasz_schrijver_N`, and `Fin.appendEquiv`
-- * source-facing refinement choice: keep the mixed-product theorem, but bridge the first-block
--   binary condition through the Chapter 5 owner `binary_prefix_points_on_subset`
--   on `Prod.fst '' P`, while transporting the Chapter 10 operator through the canonical
--   flattening `Fin.appendEquiv n n : MixedRealPoint n n ≃ (Fin (n + n) → ℝ)`.

section Exercise1018

variable {n : ℕ}

/-- The points of `P ⊆ ℝ^n × ℝ^n` whose first-block coordinates indexed by `I` are binary. -/
def mixed_binary_first_block_points_on
    (P : Set (MixedRealPoint n n))
    (I : Finset (Fin n)) : Set (MixedRealPoint n n) :=
  {x | x ∈ P ∧ ∀ i ∈ I, x.1 i = 0 ∨ x.1 i = 1}

/-- Membership in `mixed_binary_first_block_points_on P I` means belonging to `P` and having
binary first-block coordinates on the index set `I`. -/
theorem mem_mixed_binary_first_block_points_on_iff
    (P : Set (MixedRealPoint n n))
    (I : Finset (Fin n))
    (x : MixedRealPoint n n) :
    x ∈ mixed_binary_first_block_points_on P I ↔
      x ∈ P ∧ ∀ i ∈ I, x.1 i = 0 ∨ x.1 i = 1 :=
  Iff.rfl

/-- Bridge to the Chapter 5 owner `binary_prefix_points_on_subset` on the first-block projection
`Prod.fst '' P`. -/
theorem mem_mixed_binary_first_block_points_on_iff_mem_binary_prefix_points_on_subset
    (P : Set (MixedRealPoint n n))
    (I : Finset (Fin n))
    (x : MixedRealPoint n n) :
    x ∈ mixed_binary_first_block_points_on P I ↔
      x ∈ P ∧
        x.1 ∈ binary_prefix_points_on_subset (Nat.le_refl n) (Prod.fst '' P) I := by
  constructor
  · rintro ⟨hxP, hxI⟩
    refine ⟨hxP, ?_⟩
    refine ⟨⟨x, hxP, rfl⟩, ?_⟩
    simpa using hxI
  · rintro ⟨hxP, hxI⟩
    refine ⟨hxP, ?_⟩
    simpa using hxI.2

/-- Exercise 10.18. If `P` is a polytope contained in `[0,1]^n × ℝ^n`, then for every natural
number `t` and every index set `I ⊆ {1, …, n}` with `|I| ≤ t`, the `t`th Lovász-Schrijver
iterate of the canonical Chapter 10 operator, transported back from the flattening
`Fin.appendEquiv n n '' P ⊆ ℝ^(n+n)`, is contained in the convex hull of the points of `P`
whose first-block coordinates indexed by `I` are binary. -/
theorem lovasz_schrijver_iterate_subset_convexHull_binary_first_block_points_on
    (P : Set (MixedRealPoint n n))
    (hP_polytope : P.IsPolytope ℝ)
    (hP_subset :
      P ⊆ (Set.Icc (0 : Fin n → ℝ) 1) ×ˢ (Set.univ : Set (Fin n → ℝ)))
    (t : ℕ)
    (I : Finset (Fin n))
    (hI : I.card ≤ t) :
    (Fin.appendEquiv n n).symm '' ((lovasz_schrijver_N^[t]) ((Fin.appendEquiv n n) '' P)) ⊆
      convexHull ℝ (mixed_binary_first_block_points_on P I) := sorry

end Exercise1018
