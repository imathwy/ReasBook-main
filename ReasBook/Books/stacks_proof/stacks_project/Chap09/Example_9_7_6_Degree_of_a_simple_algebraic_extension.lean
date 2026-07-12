import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap09.Definition_9_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

open scoped FieldExtensionDegree

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

/- Example 9.7.2: the canonical `ℝ`-basis of `ℂ` is the ordered pair `(1, I)`, so `ℂ` is a
two-dimensional `ℝ`-vector space and hence a finite extension of `ℝ` of degree `2`. -/
recall Complex.coe_basisOneI

/- Example 9.7.2: in the chapter's degree notation, the complex numbers form a degree-`2`
extension of the real numbers. This is the source-facing natural-number view of the canonical
owner theorem `Complex.rank_real_complex`. -/
@[stacks 09G4]
theorem complex_degree_eq_two : Cardinal.toNat [ℂ : ℝ] = 2 := by
  -- The chapter notation `[ℂ : ℝ]` is `Module.rank ℝ ℂ`, so the canonical rank theorem closes it.
  simp [Complex.rank_real_complex]
