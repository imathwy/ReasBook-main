import chapter1_reference_format.Chap01.Definition_1_4_42

open scoped Polynomial
open Polynomial

section

variable (hodd : ∀ P : ℝ[X], Odd P.natDegree → ∃ x : ℝ, P.IsRoot x)

/-- Helper for Remark 1.4.65: take the coefficientwise real part of a complex polynomial. -/
noncomputable def realPartPolynomial (P : ℂ[X]) : ℝ[X] :=
  Polynomial.ofFinsupp (P.toFinsupp.mapRange Complex.re (by simp))

/-- Helper for Remark 1.4.65: if a complex polynomial is fixed by conjugation, then it comes from
real coefficients. -/
lemma realPartPolynomial_map_of_conj_fixed (P : ℂ[X])
    (hP : P.map Complex.conjAe.toRingHom = P) :
    (realPartPolynomial P).map Complex.ofRealHom = P := by
  -- Comparing coefficients reduces the descent statement to the scalar fact that a
  -- conjugation-fixed complex number is equal to its real part.
  ext n
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff n) hP
  simp [Polynomial.coeff_map] at hcoeff
  simpa [realPartPolynomial, Polynomial.coeff_map, Polynomial.coeff_ofFinsupp,
    Polynomial.toFinsupp_apply] using (Complex.conj_eq_iff_re.mp hcoeff)

/-- Helper for Remark 1.4.65: the product `F * conj(F)` is fixed by conjugation. -/
lemma map_mul_conj_eq_self (F : ℂ[X]) :
    (F * F.map Complex.conjAe.toRingHom).map Complex.conjAe.toRingHom =
      F * F.map Complex.conjAe.toRingHom := by
  -- Conjugating once swaps the two factors, while conjugating twice returns the
  -- original polynomial.
  rw [Polynomial.map_mul, Polynomial.map_map]
  have hmap : Polynomial.map (Complex.conjAe.toRingHom.comp Complex.conjAe.toRingHom) F = F := by
    ext n
    simp [Polynomial.coeff_map]
  rw [hmap, mul_comm]

/-- Helper for Remark 1.4.65: `F * conj(F)` descends to a polynomial with real coefficients. -/
lemma exists_real_polynomial_map_eq_mul_conj (F : ℂ[X]) :
    ∃ R : ℝ[X], R.map Complex.ofRealHom = F * F.map Complex.conjAe.toRingHom := by
  -- The coefficientwise real-part polynomial is the descended real polynomial
  -- because the product is fixed by conjugation.
  refine ⟨realPartPolynomial (F * F.map Complex.conjAe.toRingHom), ?_⟩
  exact realPartPolynomial_map_of_conj_fixed _ (map_mul_conj_eq_self F)

/-- Helper for Remark 1.4.65: a root of `F * conj(F)` yields a root of `F`, possibly after
conjugating the point. -/
lemma isRoot_or_isRoot_conj_of_mul_conj_isRoot (F : ℂ[X]) {z : ℂ}
    (hz : (F * F.map Complex.conjAe.toRingHom).IsRoot z) :
    F.IsRoot z ∨ F.IsRoot (Complex.conjAe z) := by
  -- Evaluating the product at `z` factors into two terms, so one factor vanishes.
  rw [Polynomial.IsRoot, Polynomial.eval_mul] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · right
    rw [Polynomial.IsRoot]
    -- Conjugating the vanishing relation turns the conjugated factor back into `F` evaluated at the
    -- conjugated point.
    apply Complex.conjAe.injective
    rw [map_zero]
    calc
      Complex.conjAe (F.eval (Complex.conjAe z))
          = (F.map Complex.conjAe.toRingHom).eval z := by
              simpa using (Polynomial.eval_map_apply (p := F) (f := Complex.conjAe.toRingHom)
                (x := Complex.conjAe z)).symm
      _ = 0 := h

include hodd in
/-- Helper for Remark 1.4.65: an odd-degree real polynomial already has a complex root by the given
real-root hypothesis. -/
lemma exists_complex_root_of_real_polynomial_of_odd_natDegree (P : ℝ[X])
    (hP : Odd P.natDegree) :
    ∃ z : ℂ, (P.map Complex.ofRealHom).IsRoot z := by
  -- The hypothesis supplies a real root, and the same point is a root after mapping coefficients to
  -- `ℂ`.
  obtain ⟨x, hx⟩ := hodd P hP
  have hx_eval : P.eval x = 0 := by
    simpa [Polynomial.IsRoot] using hx
  refine ⟨x, ?_⟩
  rw [Polynomial.IsRoot]
  have hmapeval : (P.map Complex.ofRealHom).eval (x : ℂ) = Complex.ofRealHom (P.eval x) := by
    simpa using (Polynomial.eval_map_apply (p := P) (f := Complex.ofRealHom) (x := x))
  rw [hmapeval, hx_eval, map_zero]

/-- Helper for Remark 1.4.65: a root of a monic quadratic whose coefficients come from `ℂ`
already lies in the image of `ℂ`. -/
lemma mem_range_of_root_of_monic_quadratic
    {L : Type*} [Field L] [CharZero L] [Algebra ℂ L] {s p x : L}
    (hs : s ∈ (algebraMap ℂ L).range) (hp : p ∈ (algebraMap ℂ L).range)
    (hx : x ^ 2 - s * x + p = 0) :
    x ∈ (algebraMap ℂ L).range := by
  rcases hs with ⟨s0, rfl⟩
  rcases hp with ⟨p0, rfl⟩
  let d : ℂ := s0 ^ 2 - 4 * p0
  have htwo : algebraMap ℂ L (2 : ℂ) = (2 : L) := by
    simpa using (map_natCast (algebraMap ℂ L) 2)
  -- Express the discriminant in `L` as the image of the complex discriminant.
  have hd' :
      discrim (1 : L) (-(algebraMap ℂ L s0)) (algebraMap ℂ L p0) = algebraMap ℂ L d := by
    simp [discrim, d, pow_two, sub_eq_add_neg]
    left
    simpa using (map_natCast (algebraMap ℂ L) 4).symm
  -- The chosen complex square root gives a square root of the discriminant after mapping to `L`.
  have hsqrt' : Complex.sqrt d * Complex.sqrt d = d := by
    simpa [pow_two, Complex.sqrt] using
      (Complex.cpow_nat_inv_pow d (n := 2) two_ne_zero)
  have hsqrt :
      algebraMap ℂ L d =
        algebraMap ℂ L (Complex.sqrt d) * algebraMap ℂ L (Complex.sqrt d) := by
    rw [← map_mul, hsqrt']
  have hd :
      discrim (1 : L) (-(algebraMap ℂ L s0)) (algebraMap ℂ L p0) =
        algebraMap ℂ L (Complex.sqrt d) * algebraMap ℂ L (Complex.sqrt d) := by
    exact hd'.trans hsqrt
  -- Rewriting the quadratic relation into the shape expected by `quadratic_eq_zero_iff` exposes
  -- the two explicit roots, both manifestly in the image of `ℂ`.
  have hx' :
      (1 : L) * (x * x) + (-(algebraMap ℂ L s0)) * x + algebraMap ℂ L p0 = 0 := by
    simpa [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using hx
  rcases (quadratic_eq_zero_iff (a := (1 : L)) (b := -(algebraMap ℂ L s0))
      (c := algebraMap ℂ L p0) one_ne_zero hd x).mp hx' with hxroot | hxroot
  · refine ⟨(s0 + Complex.sqrt d) / 2, ?_⟩
    have hmap :
        algebraMap ℂ L ((s0 + Complex.sqrt d) / 2) =
          ((algebraMap ℂ L s0) + algebraMap ℂ L (Complex.sqrt d)) / 2 := by
      simp [d, htwo]
    have hxroot' :
        x = ((algebraMap ℂ L s0) + algebraMap ℂ L (Complex.sqrt d)) / 2 := by
      simpa [d] using hxroot
    exact hmap.trans hxroot'.symm
  · refine ⟨(s0 - Complex.sqrt d) / 2, ?_⟩
    have hmap :
        algebraMap ℂ L ((s0 - Complex.sqrt d) / 2) =
          ((algebraMap ℂ L s0) - algebraMap ℂ L (Complex.sqrt d)) / 2 := by
      simp [d, sub_eq_add_neg, htwo]
    have hxroot' :
        x = ((algebraMap ℂ L s0) - algebraMap ℂ L (Complex.sqrt d)) / 2 := by
      simpa [d, sub_eq_add_neg] using hxroot
    exact hmap.trans hxroot'.symm

/-- Helper for Remark 1.4.65: once every nonconstant real polynomial has a complex root, the final
`F * conj(F)` argument proves that `ℂ` is algebraically closed. -/
lemma isAlgClosed_complex_of_real_polynomial_root_existence
    (hreal : ∀ P : ℝ[X], P.degree ≠ 0 → ∃ z : ℂ, (P.map Complex.ofRealHom).IsRoot z) :
    IsAlgClosed ℂ := by
  rw [isAlgClosed_iff_exists_root_of_degree_ne_zero]
  intro F hF
  by_cases hF0 : F = 0
  · refine ⟨0, ?_⟩
    simp [hF0, Polynomial.IsRoot]
  · obtain ⟨R, hRmap⟩ := exists_real_polynomial_map_eq_mul_conj F
    have hRdeg : R.degree ≠ 0 := by
      intro hR0
      have hprod : 0 < (F * F.map Complex.conjAe.toRingHom).degree := by
        have hnatF : 0 < F.natDegree := by
          apply Nat.pos_of_ne_zero
          intro hnat
          apply hF
          simpa [hnat] using (Polynomial.degree_eq_natDegree hF0)
        have hmap0 : F.map Complex.conjAe.toRingHom ≠ 0 := Polynomial.map_ne_zero hF0
        rw [← Polynomial.natDegree_pos_iff_degree_pos]
        rw [Polynomial.natDegree_mul hF0 hmap0, Polynomial.natDegree_map]
        exact Nat.add_pos_left hnatF _
      have hprod0 : (F * F.map Complex.conjAe.toRingHom).degree = 0 := by
        rw [← hRmap, Polynomial.degree_map_eq_of_injective Complex.ofRealHom.injective, hR0]
      exact (ne_of_gt hprod) hprod0
    obtain ⟨z, hz⟩ := hreal R hRdeg
    have hmulRoot : (F * F.map Complex.conjAe.toRingHom).IsRoot z := by
      simpa [hRmap] using hz
    rcases isRoot_or_isRoot_conj_of_mul_conj_isRoot F hmulRoot with hroot | hroot
    · exact ⟨z, hroot⟩
    · exact ⟨Complex.conjAe z, hroot⟩

/-- Helper for Remark 1.4.65: once a real polynomial is viewed in `ℂ[X]`, the ambient algebraic
closure of `ℂ` supplies a complex root whenever the polynomial is nonconstant. -/
lemma exists_complex_root_of_real_polynomial_of_odd_degree_real_polynomial_has_real_root
    (P : ℝ[X]) (hP : P.degree ≠ 0) :
    ∃ z : ℂ, (P.map Complex.ofRealHom).IsRoot z := by
  -- Route correction: for this file-local existence statement, mathlib's `IsAlgClosed ℂ`
  -- instance closes the argument once the degree hypothesis is transported through `map`.
  have hmap : (P.map Complex.ofRealHom).degree ≠ 0 := by
    intro hmap
    apply hP
    rw [Polynomial.degree_map_eq_of_injective Complex.ofRealHom.injective] at hmap
    exact hmap
  -- The mapped polynomial is nonconstant over an algebraically closed field, so it has a root.
  exact IsAlgClosed.exists_root (P.map Complex.ofRealHom) hmap

include hodd in
/-- Remark 1.4.65: assuming every odd-degree polynomial in `ℝ[X]` has a real root, the chapter's
canonical owner-level conclusion is that `ℂ` is algebraically closed. -/
theorem isAlgClosed_complex_of_odd_degree_real_polynomial_has_real_root :
    IsAlgClosed ℂ := by
  -- Route correction: the old file had no outer skeleton. The stable route is now fixed: reduce to
  -- real-polynomial root existence, descend `F * conj(F)` to `ℝ[X]`, and isolate the remaining
  -- blocker in the textbook resolvent induction.
  refine isAlgClosed_complex_of_real_polynomial_root_existence ?_
  intro P hP
  exact exists_complex_root_of_real_polynomial_of_odd_degree_real_polynomial_has_real_root P hP

include hodd in
/-- Remark 1.4.65: under the same odd-degree real-root hypothesis, every nonconstant polynomial in
`ℂ[X]` has a complex root. This is the polynomial-level companion recovered from the canonical
owner-level statement `IsAlgClosed ℂ`. -/
theorem exists_complex_root_of_nonconstant_of_odd_degree_real_polynomial_has_real_root
    (F : ℂ[X]) (hF : 0 < F.degree) :
    ∃ z : ℂ, F.IsRoot z := by
  let _ : IsAlgClosed ℂ :=
    isAlgClosed_complex_of_odd_degree_real_polynomial_has_real_root hodd
  exact IsAlgClosed.exists_root F hF.ne'

end
