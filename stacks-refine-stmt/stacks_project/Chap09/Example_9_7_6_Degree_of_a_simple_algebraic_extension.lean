import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

section

variable {k : Type u} [Field k]

/- Domain-style sampling for Example 9.7.6:
- `source-facing`: the degree of the simple extension `k[t]/(P)`
- `core/canonical`: `finrank_quotient_span_eq_natDegree`
- `bridge/view`: `AdjoinRoot.instField`, which uses irreducibility to view the same quotient as a
  field

Primitive data is only the polynomial quotient. The irreducibility hypothesis belongs to the
derived field/simple-extension interface, not to a duplicate local degree theorem.
-/

/- Example 9.7.6 (Degree of a simple algebraic extension): once `P` is irreducible, Example 9.3.3
supplies the field structure on `k[X] ⧸ Ideal.span {P}`. The degree computation itself is the
canonical theorem `finrank_quotient_span_eq_natDegree`. -/
recall finrank_quotient_span_eq_natDegree (P : k[X]) :
    Module.finrank k (k[X] ⧸ Ideal.span {P}) = P.natDegree

end
