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
    Module.FinitePresentation R M ↔ Module.FinitePresentation S M := by
  constructor
  · intro hM
    -- The forward direction is the finite-type restriction-of-scalars bridge from Lemma 10.6.4.
    let _ : Module.FinitePresentation R M := hM
    exact Module.FinitePresentation.of_restrictScalars_finiteType (R := R)
  · intro hM
    -- For the reverse direction, first make `S` finitely presented as an `R`-module.
    let _ : Module.FinitePresentation S M := hM
    let _ : Module.FinitePresentation R S :=
      Module.FinitePresentation.of_finite_of_finitePresentation R S
    -- Transitivity along `R → S → M` then recovers finite presentation over `R`.
    exact Module.FinitePresentation.trans (R := R) (M := M) S

end Module.FinitePresentation
