import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {K : Type v} [CommRing R] [Field K] [Algebra R K]

/- Domain triage:
* primary domain: integral and algebraic commutative algebra over a field-valued algebra;
* core/canonical owners: `isField_of_isIntegral_of_isField`,
  `Algebra.IsIntegral.isAlgebraic`, `Algebra.IsIntegral.of_finite`, and
  `Algebra.IsAlgebraic.of_finite`;
* layer split: the two part `(1)` statements and the algebraicity statement in part `(2)` are
  direct owner recalls, while `isField_of_finite_subring_of_field` is the source-facing bridge
  from module-finiteness to the owner field criterion;
* primitive data vs. derived API: the primitive hypotheses are the `R`-algebra structure on the
  field `K`, injectivity of `algebraMap R K`, and, in part `(2)`, finite generation as an
  `R`-module. Integrality and algebraicity are derived from the owner instances, so no local
  wrapper structure is needed.
-/

/- Lemma 10.36.18 (1) (Stacks tag `00GR`): if `K` is integral over `R` and the structure map
`R → K` is injective, then `R` is a field. This is exactly the canonical mathlib theorem
`isField_of_isIntegral_of_isField`. -/
recall isField_of_isIntegral_of_isField

/- Lemma 10.36.18 (1) (Stacks tag `00GR`): if `K` is integral over `R` and `K` is a field, then
`K / R` is algebraic. This is the canonical owner instance
`Algebra.IsIntegral.isAlgebraic`; the subring language from the source is redundant here because
any algebra map `R → K` into a field already forces `R` to be nontrivial. -/
recall Algebra.IsIntegral.isAlgebraic

/-- Lemma 10.36.18 (2) (Stacks tag `00GR`): if `R` is identified with a subring of the field `K`
and `K` is finite over `R`, then `R` is a field. -/
theorem isField_of_finite_subring_of_field
    (hinj : Function.Injective (algebraMap R K)) [Module.Finite R K] :
    IsField R := by
  exact isField_of_isIntegral_of_isField hinj (Field.toIsField K)

/- Lemma 10.36.18 (2) (Stacks tag `00GR`): if `K` is finite over `R` and `K` is a field, then
`K / R` is algebraic. This is the field-codomain specialization of the canonical owner instance
`Algebra.IsAlgebraic.of_finite`. -/
recall Algebra.IsAlgebraic.of_finite

end
