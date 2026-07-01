import Mathlib
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Lemma_15_65_6
import stacks_project.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.65.12:
- primary domain: derived scalar extension on module derived categories and preservation of
  pseudo-coherence;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `CochainComplex.IsTermwiseFiniteFree`;
- best owner abstraction: the core/canonical owner is the derived scalar-extension functor
  `derivedTensorWithAlgebra (algebraMap A B) : D(A) ⥤ D(B)`, with pseudo-coherence carried by the existing
  `DerivedCategory` predicates rather than any local wrapper;
- primitive vs. derived:
  primitive data are the ring map `A → B` and the pseudo-coherence witness on `K`;
  the preservation statements below are derived API over that owner;
- source/core/bridge triage:
  `source-facing`: scalar extension preserves `m`-pseudo-coherence and pseudo-coherence;
  `core/canonical`: `derivedTensorWithAlgebra` and the `DerivedCategory` pseudo-coherence owners;
  `bridge/view`: the notation `K ⊗[A]^L[B]` for the owner applied to an object.
- layer: this file is source-facing over canonical owners, so the theorem surface should use the
  existing owner notation instead of repeating raw functor application terms. -/

-- Proof sketch: choose a bounded finite-free approximation of `K` as in the definition of
-- `m`-pseudo-coherence, apply derived scalar extension to the comparison map, and use that
-- tensoring a finite free complex with `B` stays finite free over `B`, while the cone stays
-- acyclic in degrees `≥ m`.
/-- Lemma 15.65.12: derived extension of scalars along `A → B` preserves `m`-pseudo-coherent
objects of `D(A)`. -/
theorem derivedTensorWithAlgebra_isMPseudoCoherent
    (K : DModA) (m : ℤ) (hK : K.IsMPseudoCoherent m) :
    (K ⊗[A]^L[B]).IsMPseudoCoherent m := sorry

-- Proof sketch: rewrite pseudo-coherence as `m`-pseudo-coherence for all `m` using the canonical
-- owner theorem `isPseudoCoherent_iff_forall_isMPseudoCoherent`, then apply part `(1)` degreewise.
/-- Derived extension of scalars along `A → B` preserves pseudo-coherent objects of `D(A)`. -/
theorem derivedTensorWithAlgebra_isPseudoCoherent
    (K : DModA) (hK : K.IsPseudoCoherent) :
    (K ⊗[A]^L[B]).IsPseudoCoherent := by
  rw [isPseudoCoherent_iff_forall_isMPseudoCoherent] at hK ⊢
  intro m
  simpa using derivedTensorWithAlgebra_isMPseudoCoherent K m (hK m)

end

end CategoryTheory
