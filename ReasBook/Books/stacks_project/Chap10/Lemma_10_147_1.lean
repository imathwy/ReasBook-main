import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

section

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/- Domain-style sampling:
- primary domain: commutative algebra of polynomial quotients and integrality over a base ring;
- inspected owner declarations:
  * `exists_derivative_mul_eq_and_isIntegral_coeff`
  * `Ideal.Quotient.mkₐ`
  * `Ideal.Quotient.mkₐ_surjective`
  * `Ideal.Quotient.mkₐ_ker`
- best owner abstraction: the canonical quotient algebra map `Ideal.Quotient.mkₐ R I` into
  `B[X] ⧸ I`, with the representative statement derived from the upstream mathlib theorem
  `exists_derivative_mul_eq_and_isIntegral_coeff`;
- primitive data: the mapped polynomial `f.map (algebraMap R B)`, its principal ideal quotient,
  and the integrality hypothesis on the quotient element `h`;
- derived API: the source-facing existence of a representative for
  `(f.map (algebraMap R B)).derivative * h` with `R`-integral coefficients.
-/

-- Proof sketch: after a syntomic finite free faithfully flat extension of `B`, Lemma `10.136.14`
-- splits `f.map (algebraMap R B)` into linear factors. Evaluating an integral equation for `h` at
-- those roots shows each value `h(αᵢ)` is integral over `R`. The interpolation formula for
-- `derivative (f.map (algebraMap R B)) * h` in the quotient then gives a polynomial
-- representative whose coefficients are integral over `R`, and comparing coordinates in the split
-- extension shows those coefficients already lie in `B`.
/-- Lemma 10.147.1: if `f : R[X]` is monic and `h` is integral over `R` in
`B[X] ⧸ Ideal.span {f.map (algebraMap R B)}`, then
`derivative (f.map (algebraMap R B)) * h` is represented by a polynomial over `B` whose
coefficients are integral over `R`. -/
theorem exists_representative_derivative_mul_with_integral_coeffs
    (f : R[X]) (hf : f.Monic)
    (h : B[X] ⧸ Ideal.span {f.map (algebraMap R B)})
    (hint : IsIntegral R h) :
    ∃ g : B[X],
      (∀ i : ℕ, IsIntegral R (g.coeff i)) ∧
        Ideal.Quotient.mk (Ideal.span {f.map (algebraMap R B)})
            (derivative (f.map (algebraMap R B))) *
          h =
            Ideal.Quotient.mk (Ideal.span {f.map (algebraMap R B)}) g := by
  let fB : B[X] := f.map (algebraMap R B)
  let I : Ideal B[X] := Ideal.span {fB}
  have hfB : fB.Monic := hf.map (algebraMap R B)
  have hfB_coeff : ∀ i, IsIntegral R (fB.coeff i) := fun i ↦ by
    simpa [fB] using (show IsIntegral R (algebraMap R B (f.coeff i)) from isIntegral_algebraMap)
  obtain ⟨g, hg, hgint⟩ :=
    exists_derivative_mul_eq_and_isIntegral_coeff
      (Ideal.Quotient.mkₐ_surjective R I) hfB hfB_coeff
      (Ideal.Quotient.mkₐ_ker R I) hint
  exact ⟨g, hgint, by simpa [fB, I] using hg⟩

end
