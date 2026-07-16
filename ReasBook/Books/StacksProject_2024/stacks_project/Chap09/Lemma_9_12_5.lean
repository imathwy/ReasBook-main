import StacksProject_2024.stacks_project.Chap09.Definition_9_12_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {F : Type u} [Field F]
variable {p : ℕ} [Fact p.Prime] [CharP F p]
variable {Ω : Type v} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]

/- Source/core/bridge triage for Lemma 9.12.5:
- `source-facing`: the root-count statement for `P.comp (X ^ p)`;
- `core/canonical`: `Polynomial.natSepDegree` and its characteristic-`p` invariance
  `Polynomial.natSepDegree_expand`;
- `bridge/view`: `Polynomial.deg_s_eq_card_rootSet`, identifying separable degree with the number
  of distinct roots in an algebraic closure.
- primary domain: separable degree of polynomials in characteristic `p` and its interpretation as
  the number of distinct roots in an algebraic closure;
- sampled owner declarations:
  * `Polynomial.natSepDegree`
  * `Polynomial.natSepDegree_expand`
  * `Polynomial.deg_s_eq_card_rootSet`
- best owner abstraction: `Polynomial.natSepDegree`; counting roots in an algebraic closure is
  derived API coming from `Polynomial.deg_s_eq_card_rootSet`.
- primitive data: the polynomial `P`;
- ambient context: the characteristic-`p` field structure and an algebraically closed extension;
- derived API: the root-counting equality for `P` and `P.comp (X ^ p)`.
-/

namespace Polynomial

open scoped PolynomialSeparableDegree

/-- Lemma 9.12.5: over an algebraically closed extension of a field of characteristic `p > 0`, a
polynomial `P` and `P(x^p)`, i.e. `P.comp (X ^ p)`, have the same number of distinct roots. -/
theorem card_rootSet_comp_X_pow_eq (P : F[X]) :
    Fintype.card ((P.comp (X ^ p)).rootSet Ω) = Fintype.card (P.rootSet Ω) := by
  rw [← deg_s_eq_card_rootSet Ω (P.comp (X ^ p)), ← deg_s_eq_card_rootSet Ω P]
  simpa [pow_one, expand_eq_comp_X_pow] using
    (natSepDegree_expand P p : deg_s(expand F (p ^ 1) P) = deg_s(P))

end Polynomial
