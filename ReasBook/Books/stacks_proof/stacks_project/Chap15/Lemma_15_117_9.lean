import Mathlib
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap10.Lemma_10_162_6
import StacksProject_2024.Chap15.Definition_15_116_1
import StacksProject_2024.Chap15.Lemma_15_117_6
import StacksProject_2024.Chap15.Proposition_15_117_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B] [Algebra.EssFiniteType A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

/- Domain-style sampling for Lemma 15.117.9:
- primary domain: existence of separable solution fields for essentially finite type extensions of
  discrete valuation rings under Nagata hypotheses;
- sampled owner declarations:
  `IsSeparableSolutionFor`,
  `exists_finite_extension_solution_of_essentiallyFiniteType`,
  `exists_separableSolution_of_exists_solution`,
  `nagataRing_of_finiteType`,
  `localization_nagataRing`;
- best owner abstraction: the conclusion is owned by the chapter solution predicates from
  `Definition_15_116_1`, while the source-facing Nagata input for this lemma is the textbook
  disjunction `NagataRing A ∨ NagataRing B`; the canonical owner `[NagataRing B]` is the
  downstream bridge/view reduction obtained through the existing finite-type and localization
  permanence theorems;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, the fraction
  fields `K ⊂ L`, the essential finite type hypothesis, the separability of `L / K`, and the
  source-level Nagata disjunction; the reduction to the canonical owner on `B`, the finite
  solution field, and its separable refinement are derived API recorded directly via
  `IsSolutionFor` and `IsSeparableSolutionFor`.

Source/core/bridge triage:
- `source-facing`: `exists_separableSolution_of_essentiallyFiniteType_of_nagataRing`;
- `core/canonical`: `IsSolutionFor`, `IsSeparableSolutionFor`,
  `exists_finite_extension_solution_of_essentiallyFiniteType`, and
  `exists_separableSolution_of_exists_solution`;
- `bridge/view`: `exists_separableSolution_of_essentiallyFiniteType_of_target_nagataRing` and the
  passage from `NagataRing A` to `NagataRing B` through the canonical finite type model
  `Algebra.EssFiniteType.subalgebra A B` and the localization theorem
  `localization_nagataRing`.
-/

-- Proof sketch: the source text allows `NagataRing A ∨ NagataRing B`, but for essentially finite
-- type DVR extensions the left disjunct canonically implies `[NagataRing B]` by finite-type
-- permanence on the canonical finite type model and localization permanence. Proposition
-- `15.117.8` then gives a finite solution field, and Lemma `15.117.6` upgrades it to a
-- separable solution.
/-- Lemma 15.117.9: let `A → B` be an essentially finite type extension of discrete valuation
rings with fraction fields `K ⊂ L`. If `NagataRing A ∨ NagataRing B` and `L / K` is separable,
then there exists a separable solution for `A → B` in the sense of Definition `15.116.1`. -/
@[stacks 0BRP]
lemma exists_separableSolution_of_essentiallyFiniteType_of_nagataRing
    (hNagata : NagataRing A ∨ NagataRing B)
    (hsepKL : Algebra.IsSeparable K L) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSeparableSolutionFor A B K L K1 := by
  have hB : NagataRing B := by
    rcases hNagata with hA | hB
    · letI : NagataRing A := hA
      let B₀ := Algebra.EssFiniteType.subalgebra A B
      letI : Algebra A B₀ := B₀.algebra
      letI : NagataRing B₀ := nagataRing_of_finiteType A
      letI : Algebra B₀ B := inferInstance
      exact
        show NagataRing B from
          localization_nagataRing (Algebra.EssFiniteType.submonoid A B)
    · exact hB
  exact
    letI : NagataRing B := hB
    exists_separableSolution_of_exists_solution hsepKL
      exists_finite_extension_solution_of_essentiallyFiniteType

-- Proof sketch: this is the canonical owner-specialized reduction of Lemma `15.117.9`, obtained
-- by supplying the right-hand disjunct `NagataRing B`.
/-- Canonical bridge for Lemma 15.117.9: under the owner hypothesis `[NagataRing B]`, the
source-facing theorem applies by the right-hand disjunct. -/
@[stacks 0BRP]
lemma exists_separableSolution_of_essentiallyFiniteType_of_target_nagataRing [NagataRing B]
    (hsepKL : Algebra.IsSeparable K L) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSeparableSolutionFor A B K L K1 := by
  exact
    exists_separableSolution_of_essentiallyFiniteType_of_nagataRing
      (Or.inr inferInstance) hsepKL

end
