import Mathlib.FieldTheory.IsAlgClosed.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

/-
Definition 15.14.1 is `source-facing`: mathlib does not already provide an owner predicate for an
absolutely integrally closed commutative ring. The primitive data are exactly the canonical
polynomial splitting predicate on monic polynomials. The sampled canonical declarations in the same
domain are `Polynomial.Splits`, `IsAlgClosed`, and `IsAlgClosed.exists_root`; the owner here keeps
the ring-level source notion primitive, with root-existence API derived below.
-/
/-- Definition 15.14.1: a commutative ring `A` is absolutely integrally closed if every monic
polynomial over `A` splits, equivalently if every monic polynomial is a product of linear
factors. -/
class IsAbsolutelyIntegrallyClosed (A : Type u) [CommRing A] : Prop where
  splits (f : A[X]) (_ : f.Monic) : f.Splits

/-- An algebraically closed field is absolutely integrally closed. -/
instance {A : Type u} [Field A] [IsAlgClosed A] : IsAbsolutelyIntegrallyClosed A where
  splits f _ := IsAlgClosed.splits f

section

variable {A : Type u} [CommRing A]

/-- A monic polynomial over `A` splits if every monic polynomial of nonzero degree has a root. -/
private theorem splits_of_forall_monic_nonzero_degree_has_root
    (hroot : ∀ (f : A[X]) (_ : f.Monic) (_ : f.degree ≠ 0), ∃ a : A, f.IsRoot a) :
    ∀ f : A[X], f.Monic → f.Splits := by
  let P : ℕ → Prop := fun n ↦ ∀ f : A[X], f.natDegree = n → f.Monic → f.Splits
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strong_induction_on n fun n ih f hdeg hf ↦ by
      by_cases hn : n = 0
      · exact Polynomial.splits_of_natDegree_eq_zero (hdeg.trans hn)
      · have hA : Nontrivial A := by
          by_contra hA
          haveI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
          have hf0 : f = 0 := Subsingleton.elim _ _
          have hdeg0 : f.natDegree = 0 := by simp [hf0]
          exact hn (hdeg.symm.trans hdeg0)
        letI := hA
        obtain ⟨a, ha⟩ := hroot f hf <| by
          rw [degree_eq_natDegree hf.ne_zero, hdeg]
          exact_mod_cast hn
        have hfactor : (X - C a) * (f /ₘ (X - C a)) = f :=
          mul_divByMonic_eq_iff_isRoot.mpr ha
        have hquot_monic : (f /ₘ (X - C a)).Monic :=
          (monic_X_sub_C a).of_mul_monic_left <| by
            simpa [hfactor] using hf
        have hquot_deg : (f /ₘ (X - C a)).natDegree < n := by
          rw [natDegree_divByMonic f (monic_X_sub_C a), hdeg, natDegree_X_sub_C]
          exact Nat.sub_lt (Nat.pos_of_ne_zero hn) (by decide)
        rw [← hfactor]
        exact (Splits.X_sub_C a).mul <| ih _ hquot_deg _ rfl hquot_monic
  intro f hf
  exact hP f.natDegree f rfl hf

namespace IsAbsolutelyIntegrallyClosed

/-- In an absolutely integrally closed ring, every monic polynomial of nonzero degree has a root. -/
theorem exists_root [IsAbsolutelyIntegrallyClosed A] (f : A[X]) (hf : f.Monic)
    (hdeg : f.degree ≠ 0) : ∃ a : A, f.IsRoot a :=
  (IsAbsolutelyIntegrallyClosed.splits f hf).exists_eval_eq_zero hdeg

section

variable {K : Type u} [Field K] [IsAbsolutelyIntegrallyClosed K]

/-- An absolutely integrally closed field is algebraically closed. -/
theorem isAlgClosed : IsAlgClosed K := by
  refine IsAlgClosed.of_exists_root K fun f hf hirr ↦ ?_
  exact (IsAbsolutelyIntegrallyClosed.splits f hf).exists_eval_eq_zero
    (Polynomial.degree_pos_of_irreducible hirr).ne'

end

/-- A commutative ring is absolutely integrally closed if every monic polynomial of nonzero degree
has a root. -/
theorem of_exists_root
    (hroot : ∀ (f : A[X]) (_ : f.Monic) (_ : f.degree ≠ 0), ∃ a : A, f.IsRoot a) :
    IsAbsolutelyIntegrallyClosed A :=
  ⟨splits_of_forall_monic_nonzero_degree_has_root hroot⟩

end IsAbsolutelyIntegrallyClosed

end
