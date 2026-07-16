import Mathlib

open scoped BigOperators

universe u

-- Declarations for this item will be appended below by the statement pipeline.

namespace Finset

/-- The gcd of a finite family of integers lies in the `ℤ`-span of that family. -/
theorem gcd_mem_span_image {ι : Type u} (s : Finset ι) (a : ι → ℤ) :
    s.gcd a ∈ Submodule.span ℤ (a '' (↑s : Set ι)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert b s hb ih =>
      rw [Finset.gcd_insert]
      have hsubset : a '' (↑s : Set ι) ⊆ a '' (↑(insert b s) : Set ι) := by
        rintro y ⟨i, hi, rfl⟩
        exact ⟨i, by simp [hi], rfl⟩
      have hs :
          s.gcd a ∈ Submodule.span ℤ (a '' (↑(insert b s) : Set ι)) :=
        (Submodule.span_mono hsubset) ih
      have hbez :
          GCDMonoid.gcd (a b) (s.gcd a) ∈ Submodule.span ℤ ({a b, s.gcd a} : Set ℤ) := by
        rw [Submodule.mem_span_pair]
        refine ⟨Int.gcdA (a b) (s.gcd a), Int.gcdB (a b) (s.gcd a), ?_⟩
        simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          (Int.gcd_eq_gcd_ab (a b) (s.gcd a)).symm
      have hbmem : a b ∈ Submodule.span ℤ (a '' (↑(insert b s) : Set ι)) :=
        Submodule.subset_span <| by
          exact ⟨b, by simp, rfl⟩
      rw [Submodule.mem_span_pair] at hbez
      rcases hbez with ⟨m, n, hmn⟩
      rw [← hmn]
      let P : Submodule ℤ ℤ := Submodule.span ℤ (a '' (↑(insert b s) : Set ι))
      exact P.add_mem (P.smul_mem m hbmem) (P.smul_mem n hs)

end Finset

/-- Theorem 1.1.57: a finite family of integers has gcd `1` if and only if `1` is an
integral linear combination of the family. -/
-- Proof sketch: use induction on the finite set. The base case is immediate. For the inductive
-- step, combine the Bézout identity for `gcd (a i) (s.gcd a)` with the induction hypothesis for
-- the remaining family, and conversely show every common divisor of the family divides the given
-- linear combination equal to `1`.
theorem finset_gcd_eq_one_iff_exists_integer_linear_combination {ι : Type u} (s : Finset ι)
    (a : ι → ℤ) : s.gcd a = 1 ↔ ∃ u : ι → ℤ, ∑ i ∈ s, u i * a i = 1 := by
  constructor
  · intro hgcd
    have hmem := Finset.gcd_mem_span_image s a
    rw [Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
    rcases hmem with ⟨u, hu⟩
    exact ⟨u, by simpa [smul_eq_mul] using hu.trans hgcd⟩
  · rintro ⟨u, hu⟩
    have hdvd : s.gcd a ∣ (1 : ℤ) := by
      rw [← hu]
      exact Finset.dvd_sum fun i hi ↦ dvd_mul_of_dvd_right (s.gcd_dvd hi) (u i)
    have hnormalize : normalize (s.gcd a) = s.gcd a := Finset.normalize_gcd
    exact dvd_antisymm_of_normalize_eq hnormalize normalize_one hdvd (one_dvd _)
