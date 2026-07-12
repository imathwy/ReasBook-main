import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import StacksProject_2024.Chap10.Lemma_10_6_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite R S] [Algebra.FinitePresentation R S]

namespace Module.FinitePresentation

/-
Source/core/bridge triage:
* source-facing: finite and finitely presented change of scalars for finitely presented modules.
* core/canonical: `Module.FinitePresentation` with the owner lemmas
  `of_restrictScalars_finiteType`, `of_finite_of_finitePresentation`, and `trans`.
* bridge/view: this theorem is the source-facing equivalence obtained by composing those owner
  lemmas in the two directions.
-/
-- Proof sketch: for the forward direction, combine finite presentation of `S` as an
-- `R`-algebra with finiteness of `S` over `R` to descend a finitely presented `R`-module structure
-- on `M` to a finitely presented `S`-module structure. For the reverse direction, use transitivity
-- of finite presentation along the finitely presented `R`-algebra `S`.
/-- Lemma 10.36.23: if `R → S` is finite and finitely presented, then an `S`-module `M` is
finitely presented over `R` if and only if it is finitely presented over `S`. -/
theorem iff_of_finite_finitePresentation :
    Module.FinitePresentation R M ↔ Module.FinitePresentation S M := sorry

end Module.FinitePresentation
