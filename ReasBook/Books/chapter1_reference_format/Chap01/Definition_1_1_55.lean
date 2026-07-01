import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace Multiset

/- Definition 1.1.55 (1): for a finite family of integers, represented as a multiset `s`, the
canonical gcd owner is `Multiset.gcd : Multiset ℤ → ℤ`. On integers this is the normalized,
nonnegative gcd, whose absolute value is the natural-number gcd of the absolute values of the
entries. -/
#check (Multiset.gcd : Multiset ℤ → ℤ)

/-- The multiset gcd of integers has natural absolute value equal to the gcd of the absolute
values of the entries. -/
theorem natAbs_gcd_eq_map_natAbs_gcd (s : Multiset ℤ) :
    s.gcd.natAbs = (s.map Int.natAbs).gcd := by
  refine s.induction_on ?_ ?_
  · simp
  · intro a s ih
    rw [Multiset.gcd_cons, Multiset.map_cons, Multiset.gcd_cons, Int.natAbs_gcd, Int.gcd_eq_natAbs,
      ih]
    rfl

/- The divisibility universal property for the gcd of a finite integer family is the canonical
theorem `Multiset.dvd_gcd`; the textbook formulation for a natural number `d` is obtained by
specializing this recalled statement to the integer cast `a := (d : ℤ)`. -/
#check (Multiset.dvd_gcd : ∀ {s : Multiset ℤ} {a : ℤ}, a ∣ s.gcd ↔ ∀ b ∈ s, a ∣ b)

/- Definition 1.1.55 (2): a finite family of integers is mutually coprime exactly when its
canonical multiset gcd is `1`. -/
#check (fun s : Multiset ℤ ↦ s.gcd = 1)

/- Definition 1.1.55 (3): a finite family of integers is pairwise coprime exactly when it
satisfies the canonical multiset pairwise relation `s.Pairwise IsCoprime`. -/
#check (fun s : Multiset ℤ ↦ s.Pairwise IsCoprime)

-- Proof sketch: unfold `IsCoprime` using `Int.isCoprime_iff_gcd_eq_one` and transport the
-- relation through the multiset pairwise witness list.
/-- Pairwise coprimality of a finite family of integers is equivalent to requiring the gcd of each
pair of distinct members to be `1`. -/
theorem pairwise_isCoprime_iff_pairwise_gcd_eq_one (s : Multiset ℤ) :
    s.Pairwise IsCoprime ↔ s.Pairwise (fun a b ↦ Int.gcd a b = 1) := by
  constructor
  · rintro ⟨l, rfl, hl⟩
    refine ⟨l, rfl, hl.imp fun hab ↦ ?_⟩
    simpa [Int.isCoprime_iff_gcd_eq_one] using hab
  · rintro ⟨l, rfl, hl⟩
    refine ⟨l, rfl, hl.imp fun hab ↦ ?_⟩
    simpa [Int.isCoprime_iff_gcd_eq_one] using hab

end Multiset
