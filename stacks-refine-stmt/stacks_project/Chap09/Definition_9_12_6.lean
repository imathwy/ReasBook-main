import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Polynomial

/- Domain-style sampling for Definition 9.12.6:
- primary domain: separable degree of polynomials over a field and its root-count realization over
  an algebraically closed extension;
- sampled owner declarations:
  * `Polynomial.natSepDegree`
  * `Polynomial.natSepDegree_eq_of_isAlgClosed`
  * `Polynomial.rootSet_def`
- best owner abstraction: the polynomial owner `P : F[X]` with canonical separable degree
  `P.natSepDegree`;
- primitive data: only the polynomial `P`;
- derived API: the textbook notation `deg_s(P)` and the root-set cardinality bridge below.

Source/core/bridge triage:
- `source-facing`: the textbook separable-degree notation `deg_s(P)`
- `core/canonical`: `natSepDegree`
- `bridge/view`: counting distinct roots in an algebraic closure via `rootSet`

The primitive owner is the canonical mathlib definition `natSepDegree`; the root-set formula is
derived API coming from `natSepDegree_eq_of_isAlgClosed`.
-/
scoped[PolynomialSeparableDegree] notation:max "deg_s(" P ")" => Polynomial.natSepDegree P

open scoped PolynomialSeparableDegree

variable {F : Type u} [Field F]

/- Definition 9.12.6: for an irreducible polynomial `P` over `F`, the textbook separable degree
`deg_s(P)` is the canonical mathlib natural number `P.natSepDegree`. This owner is defined for
all polynomials, and on the irreducible input of the text it is exactly the same notion. -/
recall natSepDegree

section

variable (Ω : Type v) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]

/-- Source-facing reformulation of Definition 9.12.6 over an algebraic closure: `deg_s(P)` is the
cardinality of the set of roots of `P` in `Ω`. This equality in fact holds for every
polynomial. -/
theorem deg_s_eq_card_rootSet (P : F[X]) :
    deg_s(P) = Fintype.card (P.rootSet Ω) := by
  classical
  simpa only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe] using
    (natSepDegree_eq_of_isAlgClosed Ω P)

end

/- Companion recall: `natSepDegree_eq_of_isAlgClosed` is the exact mathlib theorem
underlying the root-set reformulation above; it computes `P.natSepDegree` using `P.aroots Ω`. -/
recall natSepDegree_eq_of_isAlgClosed

end Polynomial
