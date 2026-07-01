import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Pointwise

variable {R : Type u} [CommRing R]

/- Domain triage:
* primary domain: commutative algebra of principal-ideal quotient lengths and order of vanishing;
* sampled owner API: `Ring.ord`, `Ring.ord_mul`, `Ideal.exact_mulQuot_quotOfMul`, and
  `Module.length_eq_add_of_exact`;
* source/core/bridge triage:
  `source-facing`: the textbook quotient-length formulas for powers of a principal ideal;
  `core/canonical`: `Ring.ord` together with the multiplicative owner theorem `Ring.ord_mul`;
  `bridge/view`: unfolding `Ring.ord` and rewriting by `Ideal.span_singleton_pow`.

Primitive-vs-derived split:
* primitive data: the ring `R`, the element `x : R`, and the exponent `n`;
* derived API: the explicit quotient-length formulas are source-facing bridges from the owner-level
  `Ring.ord` statements; minimal-prime avoidance and dimension bounds belong only to later
  applications such as Lemma `15.126.2`.
-/

private lemma smul_span_singleton_eq_span_singleton_mul (a b : R) :
    b • Ideal.span ({a} : Set R) = Ideal.span ({a * b} : Set R) := by
  calc
    b • Ideal.span ({a} : Set R) = ({b} : Set R) • Ideal.span ({a} : Set R) := by
      symm
      exact Submodule.singleton_set_smul (Ideal.span ({a} : Set R)) b
    _ = Ideal.span ({b * a} : Set R) := by
      simpa [Set.singleton_mul_singleton] using
        (Submodule.set_smul_span ({b} : Set R) ({a} : Set R))
    _ = Ideal.span ({a * b} : Set R) := by
      rw [mul_comm]

private theorem ord_mul_le_add (a b : R) :
    Ring.ord R (a * b) ≤ Ring.ord R a + Ring.ord R b := by
  have hlen :
      Module.length R (R ⧸ b • Ideal.span ({a} : Set R)) =
        Module.length R (Ideal.quotOfMul b (Ideal.span ({a} : Set R))).ker +
          Module.length R (R ⧸ Ideal.span ({b} : Set R)) := by
    simpa using
      (Module.length_eq_add_of_exact
        ((Ideal.quotOfMul b (Ideal.span ({a} : Set R))).ker.subtype)
        (Ideal.quotOfMul b (Ideal.span ({a} : Set R)))
        (Submodule.subtype_injective _)
        (Ideal.quotOfMul_surjective (Ideal.span ({a} : Set R)))
        (LinearMap.exact_subtype_ker_map (Ideal.quotOfMul b (Ideal.span ({a} : Set R)))))
  have hker :
      Module.length R (Ideal.quotOfMul b (Ideal.span ({a} : Set R))).ker ≤
        Module.length R (R ⧸ Ideal.span ({a} : Set R)) := by
    have hrange :
        (Ideal.quotOfMul b (Ideal.span ({a} : Set R))).ker =
          (Ideal.mulQuot b (Ideal.span ({a} : Set R))).range :=
      LinearMap.exact_iff.mp (Ideal.exact_mulQuot_quotOfMul (Ideal.span ({a} : Set R)))
    calc
      Module.length R (Ideal.quotOfMul b (Ideal.span ({a} : Set R))).ker =
          Module.length R (Ideal.mulQuot b (Ideal.span ({a} : Set R))).range := by
            rw [hrange]
      _ =
          Module.length R
            ((R ⧸ Ideal.span ({a} : Set R)) ⧸ (Ideal.mulQuot b (Ideal.span ({a} : Set R))).ker) := by
            symm
            exact (LinearMap.quotKerEquivRange (Ideal.mulQuot b (Ideal.span ({a} : Set R)))).length_eq
      _ ≤ Module.length R (R ⧸ Ideal.span ({a} : Set R)) := by
            exact Module.length_le_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  calc
    Ring.ord R (a * b) =
        Module.length R (R ⧸ b • Ideal.span ({a} : Set R)) := by
          rw [Ring.ord, smul_span_singleton_eq_span_singleton_mul]
    _ =
        Module.length R (Ideal.quotOfMul b (Ideal.span ({a} : Set R))).ker +
          Module.length R (R ⧸ Ideal.span ({b} : Set R)) := hlen
    _ ≤
        Ring.ord R a + Ring.ord R b :=
      by
        simpa [Ring.ord, add_comm, add_left_comm, add_assoc] using
          add_le_add_right hker (Module.length R (R ⧸ Ideal.span ({b} : Set R)))

-- Proof sketch: iterate the product inequality `ord (ab) ≤ ord a + ord b`.
/-- Lemma 15.126.1 (1), core/canonical form: for every commutative ring `R`, element `x : R`, and
exponent `n : ℕ`, the order of vanishing of `x ^ n` is at most `n` times the order of vanishing of
`x`. The one-dimensional and minimal-prime hypotheses from the source are not part of this
canonical owner-level inequality; they are only needed in later applications. -/
theorem ord_pow_le_nsmul_ord (x : R) (n : ℕ) :
    Ring.ord R (x ^ n) ≤ n • Ring.ord R x := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        Ring.ord R (x ^ n.succ) = Ring.ord R (x ^ n * x) := by
          rw [pow_succ]
        _ ≤ Ring.ord R (x ^ n) + Ring.ord R x :=
          ord_mul_le_add (x ^ n) x
        _ ≤ n • Ring.ord R x + Ring.ord R x := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right ih (Ring.ord R x)
        _ = n.succ • Ring.ord R x := by
          rw [succ_nsmul]

/-- Lemma 15.126.1 (1), source-facing bridge: `length_R (R / (x)^n) ≤ n * length_R (R / (x))`. -/
theorem length_quotient_span_singleton_pow_le_mul_length_quotient_span_singleton
    (x : R) (n : ℕ) :
    Module.length R (R ⧸ (Ideal.span {x}) ^ n) ≤
      n • Module.length R (R ⧸ Ideal.span {x}) := by
  rw [Ideal.span_singleton_pow]
  simpa [Ring.ord] using ord_pow_le_nsmul_ord x n

-- Proof sketch: iterate the canonical multiplicativity theorem `Ring.ord_mul`.
/-- Lemma 15.126.1 (2), core/canonical form: if `x` is a nonzerodivisor, then
`Ring.ord R (x ^ n) = n • Ring.ord R x`. -/
theorem ord_pow_eq_nsmul_ord_of_mem_nonZeroDivisors
    {x : R} (hx : x ∈ nonZeroDivisors R) (n : ℕ) :
    Ring.ord R (x ^ n) = n • Ring.ord R x := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        Ring.ord R (x ^ n.succ) = Ring.ord R (x ^ n * x) := by
          rw [pow_succ]
        _ = Ring.ord R (x ^ n) + Ring.ord R x :=
          Ring.ord_mul R hx
        _ = n • Ring.ord R x + Ring.ord R x := by
          rw [ih]
        _ = n.succ • Ring.ord R x := by
          rw [succ_nsmul]

/-- Lemma 15.126.1 (2), source-facing bridge: if `x` is a nonzerodivisor, then
`length_R (R / (x)^n) = n * length_R (R / (x))`. -/
theorem length_quotient_span_singleton_pow_eq_mul_length_quotient_span_singleton_of_mem_nonZeroDivisors
    {x : R} (hx : x ∈ nonZeroDivisors R) (n : ℕ) :
    Module.length R (R ⧸ (Ideal.span {x}) ^ n) =
      n • Module.length R (R ⧸ Ideal.span {x}) := by
  rw [Ideal.span_singleton_pow]
  simpa [Ring.ord] using ord_pow_eq_nsmul_ord_of_mem_nonZeroDivisors hx n

end
