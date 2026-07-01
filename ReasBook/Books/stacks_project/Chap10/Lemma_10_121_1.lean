import Mathlib.RingTheory.OrderOfVanishing
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped nonZeroDivisors

section

variable {R : Type u} [CommRing R]

/-
Domain triage:
* primary domain: order of vanishing and lengths of principal quotients in commutative algebra;
* sampled owner API: `Ring.ord`, `Ring.ord_mul`, `isFiniteLength_quotient_span_singleton`, and
  `Module.length_ne_top_iff`;
* `core/canonical`: `Ring.ord` is the owner for the length of `R / (x)`, and `Ring.ord_mul` is
  the canonical multiplicativity theorem;
* `bridge/view`: the textbook `length_R (R / (x))` formulas are obtained by unfolding `Ring.ord`,
  while finite-length statements are derived from `IsFiniteLength`.

Primitive-vs-derived split:
* primitive data: the ring element `x` and the owner abstractions `Ring.ord` / `IsFiniteLength`;
* derived API: the source-facing equalities between explicit quotient lengths and the `< ⊤`
  reformulation of finite length.
-/

/- Owner bridge: the multiplicative length formula is exactly `Ring.ord_mul` with `Ring.ord`
unfolded. -/
recall Ring.ord_mul

/-- Lemma 10.121.1, source-facing form of `Ring.ord_mul`: if `b` is a nonzerodivisor, then
`length_R (R / (ab)) = length_R (R / (a)) + length_R (R / (b))`. -/
theorem length_quotient_span_singleton_mul_eq_add_of_mem_nonZeroDivisors
    {a b : R} (hb : b ∈ nonZeroDivisors R) :
    Module.length R (R ⧸ Ideal.span {a * b}) =
      Module.length R (R ⧸ Ideal.span {a}) + Module.length R (R ⧸ Ideal.span {b}) := by
  simpa [Ring.ord] using Ring.ord_mul R hb

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

/- Owner bridge: in dimension at most `1`, finite length of `R / xR` is owned by
`isFiniteLength_quotient_span_singleton`, and `Module.length_ne_top_iff` converts that owner
statement to the source-facing inequality. -/
recall isFiniteLength_quotient_span_singleton
recall Module.length_ne_top_iff

/-- If `x` is a nonzerodivisor in a Noetherian ring of Krull dimension at most `1`, then
`R / (x)` has finite length over `R`. -/
theorem length_quotient_span_singleton_lt_top_of_mem_nonZeroDivisors
    {x : R} (hx : x ∈ nonZeroDivisors R) :
    Module.length R (R ⧸ Ideal.span {x}) < ⊤ := by
  simpa [lt_top_iff_ne_top] using
    (Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton R hx))

end
