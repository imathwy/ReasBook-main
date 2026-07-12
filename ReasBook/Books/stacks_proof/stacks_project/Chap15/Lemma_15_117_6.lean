import Mathlib
import StacksProject_2024.Chap09.Lemma_9_14_5
import StacksProject_2024.Chap09.Lemma_9_14_9_Multiplicativity
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap15.Definition_15_116_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

/- Domain-style sampling for Lemma 15.117.6:
- primary domain: Epp-style elimination of inseparability for solution fields of extensions of
  discrete valuation rings;
- sampled owner declarations:
  `IsSolutionFor`,
  `IsSeparableSolutionFor`,
  `solutionFor_of_finite_extension`,
  `exists_separable_solution_of_solution_of_purelyInseparable_degree_eq_prime`;
- best owner abstraction: the source-facing content is the existence upgrade from a solution to a
  separable solution, and the chapter owners from `Definition_15_116_1` already capture exactly
  that distinction; this file should therefore state the hypothesis and conclusion directly with
  `IsSolutionFor` and `IsSeparableSolutionFor`, rather than introducing a parallel wrapper for
  “having a solution”;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, the fraction
  fields `K ⊂ L`, the separability of `L / K`, the Nagata hypothesis on `B`, and the existence of
  one finite solution field; the conclusion that one may choose such a field separable over `K`
  is derived API, recorded by `IsSeparableSolutionFor`.

Source/core/bridge triage:
- `source-facing`: the existence theorem upgrading an arbitrary solution to a separable one;
- `core/canonical`: `IsSolutionFor` and `IsSeparableSolutionFor`;
- `bridge/view`: the induction step through
  `exists_separable_solution_of_solution_of_purelyInseparable_degree_eq_prime` and stability under
  finite extension via `solutionFor_of_finite_extension`. -/

section

open scoped IntermediateField

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [NagataRing B]

-- Proof sketch: choose a solution `K₂ / K` for `A ⊂ B` and argue by induction on the
-- inseparable degree `Field.insepDegree K K₂`. If this degree is `1`, the given solution is
-- already separable. Otherwise, factor `K₂ / K` through an intermediate field `K₁` with
-- `K₂ / K₁` purely inseparable of prime degree, apply Lemma `15.117.5` to replace `K₂` by a
-- separable solution over `K₁`, and use multiplicativity of inseparable degree to decrease the
-- induction parameter.
/-- Lemma 15.117.6: for an extension `A ⊂ B` of discrete valuation rings with fraction fields
`K ⊂ L`, if `L / K` is separable, `B` is Nagata, and there exists a solution for `A ⊂ B`, then
there exists a separable solution for `A ⊂ B`. -/
@[stacks 0BRN]
theorem exists_separableSolution_of_exists_solution
    (hsepKL : Algebra.IsSeparable K L)
    (hsol :
      ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
        (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
        IsSolutionFor A B K L K1) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSeparableSolutionFor A B K L K1 := by
  sorry

end
