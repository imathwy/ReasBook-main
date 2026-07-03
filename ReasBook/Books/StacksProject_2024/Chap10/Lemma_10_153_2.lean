import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing Polynomial

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

-- Proof sketch: write `f(a + (b - a)) - f(a)` as
-- `f.derivative.eval a * (b - a) + c * (b - a)^2`. Since `a ≡ b [SMOD maximalIdeal R]`,
-- the difference `b - a` lies in `maximalIdeal R`. The hypothesis
-- `f.derivative.eval a ∉ maximalIdeal R` makes `f.derivative.eval a` a unit in the local ring,
-- and then factoring out `b - a` shows the remaining factor is also a unit, forcing `b - a = 0`.
/-- Lemma 10.153.2: if `a` and `b` are roots of a polynomial over a local ring, are congruent
modulo the maximal ideal, and the derivative at `a` is not in the maximal ideal, then `a = b`. -/
lemma eq_of_polynomial_roots_congruent_of_derivative_not_mem_maximalIdeal
    {f : R[X]} {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b)
    (hab : a ≡ b [SMOD maximalIdeal R])
    (hder : f.derivative.eval a ∉ maximalIdeal R) :
    a = b := by
  let d := b - a
  have hd : d ∈ maximalIdeal R := SModEq.sub_mem.mp hab.symm
  obtain ⟨c, hc⟩ := binomExpansion f a d
  have hfactor : f.derivative.eval a * d + c * d ^ 2 = (f.derivative.eval a + c * d) * d := by
    dsimp [d]
    ring
  have hsum : 0 = f.derivative.eval a * d + c * d ^ 2 := by
    simpa [d, ha.eq_zero, hb.eq_zero, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hc
  have hrootEq : (f.derivative.eval a + c * d) * d = 0 := by
    rw [hfactor] at hsum
    exact hsum.symm
  have hunit_der : IsUnit (f.derivative.eval a) := notMem_maximalIdeal.mp hder
  have hunit : IsUnit (f.derivative.eval a + c * d) := by
    rw [← residue_ne_zero_iff_isUnit]
    have hd_res : residue R d = 0 := (residue_eq_zero_iff d).2 hd
    simpa [map_add, map_mul, hd_res] using
      (residue_ne_zero_iff_isUnit (f.derivative.eval a)).2 hunit_der
  have hd_zero : d = 0 := hunit.mul_right_eq_zero.mp hrootEq
  exact (sub_eq_zero.mp hd_zero).symm

end
