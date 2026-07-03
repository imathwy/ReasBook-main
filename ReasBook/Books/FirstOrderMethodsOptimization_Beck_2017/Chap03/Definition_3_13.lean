import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

/- Definition 3.13 is `source-facing` at the finite-set median set itself. There is no earlier
chapter owner or mathlib owner for this exact notion, so the public root stays `median_set A :
Set ℝ`. The pointwise notion of being a median is expressed directly by membership
`β ∈ median_set A`, and the middle tuple indices below are represented by canonical `Fin.ofNat`
terms rather than local wrapper definitions. -/

/-- Definition 3.13: `median_set A` is the set of real numbers `β` such that at least half of the
elements of the finite nonempty set `A` lie below `β` and at least half lie above `β`. -/
def median_set (A : Finset ℝ) : Set ℝ :=
  {β |
    A.Nonempty ∧
      A.card ≤ 2 * (A.filter (fun a ↦ a ≤ β)).card ∧
        A.card ≤ 2 * (A.filter (fun a ↦ β ≤ a)).card}

/-- Membership in `median_set A` is equivalent to satisfying the two median-count inequalities. -/
@[simp] lemma mem_median_set_iff {A : Finset ℝ} {β : ℝ} :
    β ∈ median_set A ↔
      A.Nonempty ∧
        A.card ≤ 2 * (A.filter (fun a ↦ a ≤ β)).card ∧
          A.card ≤ 2 * (A.filter (fun a ↦ β ≤ a)).card :=
  Iff.rfl

-- Proof sketch: for a strictly increasing tuple of odd length, exactly `m + 1` entries lie below
-- the middle element and exactly `m + 1` entries lie above it, while any other candidate fails
-- one of the two counting inequalities.
/-- For a strictly increasing odd tuple, the median set is the singleton containing the middle
entry. -/
theorem median_set_eq_singleton_of_strictMono_odd (m : ℕ) (a : Fin (2 * m + 1) → ℝ)
    (ha : StrictMono a) :
    median_set (Finset.univ.image a) = ({a (Fin.ofNat (2 * m + 1) m)} : Set ℝ) := sorry

-- Proof sketch: for a strictly increasing tuple of even length `2 * (m + 1)`, the two counting
-- inequalities hold exactly for those `β` between the two middle entries `a_m` and `a_{m+1}`.
/-- For a strictly increasing even tuple, the median set is the closed interval between the two
middle entries. -/
theorem median_set_eq_Icc_of_strictMono_even (m : ℕ) (a : Fin (2 * (m + 1)) → ℝ)
    (ha : StrictMono a) :
    median_set (Finset.univ.image a) =
      Set.Icc (a (Fin.ofNat (2 * (m + 1)) m)) (a (Fin.ofNat (2 * (m + 1)) (m + 1))) := sorry

end
