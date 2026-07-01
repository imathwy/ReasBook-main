import Mathlib
import stacks_project.Chap10.Lemma_10_110_9
import stacks_project.Chap10.Lemma_10_112_8
import stacks_project.Chap15.Lemma_15_43_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/- Domain-style sampling:
* primary domain: regular local rings and maximal-ideal adic completion in local commutative
  algebra;
* sampled owner declarations:
  `IsRegularLocalRing`,
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`,
  `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`,
  the canonical instance `Field (Ideal.Fiber (maximalIdeal A) ACompletion)`.
* owner abstraction: the canonical regular-local owner `IsRegularLocalRing` on `A` and on its
  maximal-ideal completion `AdicCompletion (maximalIdeal A) A`;
* primitive data: the Noetherian local ring `A`;
* derived API: Noetherianity and locality of the completion, the completion-map local-hom
  instance from Lemma `15.43.1`, and regularity of the closed fiber.

Source/core/bridge triage:
* source-facing: the textbook equivalence between regularity of `A` and of its maximal-ideal
  completion;
* core/canonical: the owner predicate `IsRegularLocalRing`;
* bridge/view: the completion map `A → A^∧` and the closed fiber
  `Ideal.Fiber (maximalIdeal A) A^∧`.
-/
local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) ACompletion

local instance : IsNoetherianRing ACompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal A)

-- Proof sketch: apply the flat local ascent lemma
-- `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber` to the completion map
-- `A → AdicCompletion (maximalIdeal A) A`; its closed fiber is the residue field of `A`, hence
-- regular. For the converse, use the flat local descent lemma
-- `isRegularLocalRing_of_flat_localHom_of_regularTarget`.
/-- Lemma 15.43.4: a Noetherian local ring is regular if and only if its maximal-ideal adic
completion is regular. -/
theorem isRegularLocalRing_iff_isRegularLocalRing_maximalIdeal_adicCompletion :
    IsRegularLocalRing A ↔ IsRegularLocalRing ACompletion := by
  have hclosedFiber : IsRegularLocalRing ClosedFiber := inferInstance
  constructor
  · intro hA
    let _ : IsRegularLocalRing A := hA
    exact isRegularLocalRing_of_flat_localHom_of_regular_closedFiber hclosedFiber
  · intro hCompletion
    let _ : IsRegularLocalRing ACompletion := hCompletion
    exact isRegularLocalRing_of_flat_localHom_of_regularTarget ACompletion

end
