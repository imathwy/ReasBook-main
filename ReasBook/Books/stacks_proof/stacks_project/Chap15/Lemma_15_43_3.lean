import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_130_3
import stacks_proof.stacks_project.Chap10.Lemma_10_163_3
import stacks_proof.stacks_project.Chap15.Lemma_15_43_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-
Domain-style sampling:
* primary domain: Cohen-Macaulay local rings under maximal-ideal adic completion.
* sampled owner declarations:
  `Module.CohenMacaulay`,
  `cohenMacaulayRing_iff_source_and_closedFiber`,
  `Ideal.Fiber`,
  `self_cohenMacaulay_of_krullDimLE_zero`.
* owner abstraction: the core owner is `Module.CohenMacaulay` on the self-module; this lemma is
  the `bridge/view` specialization of the flat-local closed-fiber equivalence to the canonical
  completion map `A → AdicCompletion (maximalIdeal A) A`.
* primitive data: the Noetherian local ring `A`.
* derived API: the completion map and target local structure from Lemma `15.43.1`, and the
  Cohen-Macaulayness of the completion closed fiber derived from its canonical field structure.
-/
local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) ACompletion

local instance : IsNoetherianRing ACompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal A)

private theorem closedFiber_cohenMacaulay :
    Module.CohenMacaulay ClosedFiber ClosedFiber := by
  let _ : Ring.KrullDimLE 0 ClosedFiber :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr <|
      ringKrullDim_eq_zero_of_field ClosedFiber
  exact self_cohenMacaulay_of_krullDimLE_zero ClosedFiber

-- Proof sketch: specialize the flat-local closed-fiber criterion of Lemma `10.163.3` to the
-- canonical completion map `A → ACompletion`. Lemma `15.43.1` supplies the required completion
-- map structure and identifies the closed fiber as a field, hence Cohen-Macaulay.
/-- Lemma 15.43.3: a Noetherian local ring is Cohen-Macaulay if and only if its maximal-ideal
adic completion is Cohen-Macaulay. -/
@[stacks 07NX]
theorem cohenMacaulayRing_iff_maximalIdeal_adicCompletion :
    Module.CohenMacaulay A A ↔ Module.CohenMacaulay ACompletion ACompletion := by
  have hiff :
      Module.CohenMacaulay ACompletion ACompletion ↔
        Module.CohenMacaulay A A ∧ Module.CohenMacaulay ClosedFiber ClosedFiber :=
    cohenMacaulayRing_iff_source_and_closedFiber
  constructor
  · intro hA
    exact hiff.2 ⟨hA, closedFiber_cohenMacaulay A⟩
  · intro hCompletion
    exact (hiff.1 hCompletion).1

end
