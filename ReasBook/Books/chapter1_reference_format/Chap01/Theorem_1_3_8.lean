import Mathlib
import Mathlib.RingTheory.Polynomial.Content
import chapter1_reference_format.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Polynomial

noncomputable section

section Bezout

variable {K : Type} [Field K]
variable {ι : Type*} [Fintype ι]

attribute [local instance] Classical.decEq

-- Proof sketch: the canonical owner from Definition 1.3.7 is the normalized gcd
-- `(Finset.univ : Finset ι).gcd P` of a finite polynomial family.
-- Transport membership of `1` across
-- `span_singleton_gcd_eq_span_range`, then use `Ideal.mem_span_range_iff_exists_fun` to rewrite
-- membership in the ideal span as a finite linear combination `∑ i, U i * P i = 1`. In the
-- reverse direction, membership of `1` in the singleton span means the gcd divides `1`, hence the
-- normalized gcd is exactly `1`.
/-- Theorem 1.3.8: [Bézout] a finite family of polynomials in `K[X]` is coprime exactly when `1`
is a `K[X]`-linear combination of the family. -/
theorem polynomial_family_coprime_iff_exists_bezout_combination
    (P : ι → K[X]) :
    (Finset.univ : Finset ι).gcd P = 1 ↔ ∃ U : ι → K[X], ∑ i, U i * P i = 1 := by
  have hspan := Polynomial.span_singleton_gcd_eq_span_range P
  constructor
  · intro hg
    have hmem : (1 : K[X]) ∈ Ideal.span ({(Finset.univ : Finset ι).gcd P} : Set K[X]) := by
      simp [hg]
    rw [hspan] at hmem
    exact Ideal.mem_span_range_iff_exists_fun.mp hmem
  · rintro ⟨U, hU⟩
    have hmem : (1 : K[X]) ∈ Ideal.span (Set.range P) :=
      Ideal.mem_span_range_iff_exists_fun.mpr ⟨U, hU⟩
    rw [← hspan] at hmem
    have hdiv :
        (Finset.univ : Finset ι).gcd P ∣ (1 : K[X]) :=
      Ideal.mem_span_singleton.mp hmem
    exact dvd_antisymm_of_normalize_eq
      (show
        normalize ((Finset.univ : Finset ι).gcd P) =
          (Finset.univ : Finset ι).gcd P from
        Finset.normalize_gcd)
      normalize_one hdiv (one_dvd _)

end Bezout

end
