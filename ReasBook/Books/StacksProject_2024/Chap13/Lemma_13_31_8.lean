import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap13.Lemma_13_31_3
import StacksProject_2024.Chap13.Lemma_13_31_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite

universe v u

namespace CategoryTheory

namespace SequentialInverseSystem

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 13.31.8 in the homological-complex / sequential-limit domain:
- sampled owner declarations:
  * `CochainComplex.IsKInjective`
  * `CategoryTheory.isKInjective_of_product`
  * `HomologicalComplex.isLimitConeOfHasLimitEval`
  * `SequentialInverseSystem.transitionMap`
- best owner abstractions:
  * `CochainComplex.IsKInjective` for the target property on the inverse-limit complex
  * `SequentialInverseSystem` for the sequential tower itself, with `transitionMap` as derived API
- primitive data:
  * the sequential inverse system `I`
  * termwise split-epimorphism hypotheses on the successor transition maps
  * degreewise existence of limits, which canonically induces `HasLimit I` via
    `HomologicalComplex.isLimitConeOfHasLimitEval`
- derived API:
  * the owner instances `∀ n : ℕ, (I.obj (op n)).IsKInjective`
- source/core/bridge triage:
  * `source-facing`: the K-injectivity statement for the inverse-limit complex
  * `core/canonical`: `CochainComplex.IsKInjective`, the chapter product theorem
    `isKInjective_of_product`, and the homological-complex limit owner
  * `bridge/view`: `SequentialInverseSystem.transitionMap`, which replaces the raw
    `I.map ((homOfLE _).op)` spelling

This item should therefore keep the source-facing limit theorem, but express the tower through the
chapter owner `SequentialInverseSystem` and its derived `transitionMap` API rather than by a
parallel coordinate-level map expression. -/

/-- Lemma 13.31.8: for a sequential inverse system of K-injective cochain complexes in an abelian
category, if every successor transition map is termwise split epic and each degreewise
inverse limit exists, then the inverse-limit complex is K-injective. -/
-- Proof sketch: identify the inverse limit degreewise with the kernel of the Milnor difference
-- map on the product of the tower, use `isKInjective_of_product` for the two product complexes,
-- and then apply `CochainComplex.isKInjective_obj₁_of_distinguished_triangle` to the
-- distinguished triangle coming from the resulting degreewise split short exact sequence.
theorem isKInjective_limit_of_termwiseSplitEpi
    (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ))
    [∀ n : ℕ, (I.obj (op n)).IsKInjective]
    [∀ m : ℤ, HasLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) m)]
    (hTermwiseSplitEpi : ∀ n : ℕ, ∀ m : ℤ, IsSplitEpi ((I.transitionMap (Nat.le_succ n)).f m)) :
    (limit I).IsKInjective := sorry

end

end SequentialInverseSystem

end CategoryTheory
