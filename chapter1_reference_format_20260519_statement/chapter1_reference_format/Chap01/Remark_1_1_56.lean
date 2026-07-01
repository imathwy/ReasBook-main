import Mathlib
import chapter1_reference_format.Chap01.Definition_1_1_55

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Remark 1.1.56: a pairwise coprime integer family with at least two entries has
unit gcd. -/
lemma gcd_isUnit_of_pairwise_two_or_more {s : Multiset ℤ}
    (hs : 2 ≤ s.card) (hpair : s.Pairwise IsCoprime) :
    IsUnit s.gcd := by
  rcases hpair with ⟨l, rfl, hpair⟩
  -- A pairwise witness with at least two entries exposes two concrete coprime members.
  cases l with
  | nil =>
      simp at hs
  | cons a t =>
      cases t with
      | nil =>
          simp at hs
      | cons b t =>
          -- The multiset gcd divides every entry, so it divides the chosen coprime pair.
          have hab : IsCoprime a b := by
            exact List.rel_of_pairwise_cons hpair (by simp)
          have hga : (((a :: b :: t : List ℤ) : Multiset ℤ).gcd) ∣ a := by
            exact Multiset.gcd_dvd (by simp)
          have hgb : (((a :: b :: t : List ℤ) : Multiset ℤ).gcd) ∣ b := by
            exact Multiset.gcd_dvd (by simp)
          exact hab.isUnit_of_dvd' hga hgb

-- Proof sketch: if a positive integer divides the canonical multiset gcd, then it divides every
-- entry. When the multiset has at least two members, it divides some pair of distinct entries;
-- pairwise coprimality forces every such common divisor to be `1`, so the family gcd is `1`.
/-- Remark 1.1.56 (1): a pairwise coprime family of at least two integers is mutually coprime. -/
theorem pairwise_isCoprime_implies_gcd_eq_one {s : Multiset ℤ}
    (hs : 2 ≤ s.card) (hpair : s.Pairwise IsCoprime) :
    s.gcd = 1 := by
  -- Normalize the gcd first, then identify the goal with the unit statement from the helper.
  rw [← Multiset.normalize_gcd s, normalize_eq_one]
  exact gcd_isUnit_of_pairwise_two_or_more hs hpair

-- Proof sketch: the triple `(6, 10, 15)` has gcd `1`, but each pair shares a nontrivial common
-- divisor, so global coprimality does not imply pairwise coprimality.
/-- Remark 1.1.56 (2): the converse fails; some triple of integers is mutually coprime without
being pairwise coprime. -/
theorem exists_triple_gcd_eq_one_not_pairwise_isCoprime :
    ∃ s : Multiset ℤ, s.card = 3 ∧ s.gcd = 1 ∧ ¬ s.Pairwise IsCoprime := by
  refine ⟨(([6, 10, 15] : List ℤ) : Multiset ℤ), ?_, ?_, ?_⟩
  · decide
  · decide
  · -- The explicit pair `(6, 10)` already violates pairwise coprimality.
    rw [Multiset.pairwise_coe_iff_pairwise (hr := fun a b hab => hab.symm)]
    simp [Int.isCoprime_iff_gcd_eq_one]
    norm_num

/- Remark 1.1.56 (3): for a finite family `s : Multiset ℤ`, multiplying every entry by `a`
multiplies the family gcd by the normalized absolute value of `a`; this is the canonical owner
theorem `Multiset.gcd_map_mul`. -/
#check (Multiset.gcd_map_mul : ∀ a : ℤ, ∀ s : Multiset ℤ,
  (s.map (a * ·)).gcd = normalize a * s.gcd)
