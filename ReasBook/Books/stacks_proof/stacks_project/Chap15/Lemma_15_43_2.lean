import Mathlib
import StacksProject_2024.Chap10.Lemma_10_163_2
import StacksProject_2024.Chap10.Lemma_10_130_3
import StacksProject_2024.Chap15.Lemma_15_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

-- Domain-style sampling:
-- * primary domain: local commutative algebra of depth and maximal-ideal adic completion.
-- * sampled owner declarations:
--   `moduleDepth`,
--   `depth_target_eq_depth_source_add_depth_closed_fiber`,
--   `moduleDepth_self_eq_zero_of_field`,
--   `maximalIdeal_adicCompletion_algebraMap_faithfullyFlat`,
--   the canonical instance `Field ClosedFiber`.
-- * owner abstraction: the local-depth owner `moduleDepth` together with the canonical closed
--   fiber owner `ClosedFiber`; the completion-specific local and flat
--   structure and the depth-zero field input are derived from the completion-map and closed-fiber
--   instances supplied by Lemma `15.43.1`.
-- * primitive data: the local Noetherian ring `A`.
-- * derived API: locality of the completion map, faithful flatness of the completion algebra, and
--   the identification of the closed fiber with the residue-field quotient.
--
-- Source/core/bridge triage:
-- * source-facing: equality of the depth of a Noetherian local ring and the depth of its
--   maximal-ideal adic completion;
-- * core/canonical: `moduleDepth` and the closed-fiber owner `ClosedFiber`;
-- * bridge/view: the completion map `A → ACompletion` together with the field identification of
--   its closed fiber.

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) ACompletion

local instance : IsNoetherianRing ACompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal A)

local instance : Module.Finite ACompletion ACompletion :=
  Module.Finite.self ACompletion

private theorem closedFiber_moduleDepth_eq_zero :
    moduleDepth ClosedFiber ClosedFiber = 0 := by
  letI : Ring.KrullDimLE 0 ClosedFiber :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr <|
      ringKrullDim_eq_zero_of_isField (Field.toIsField ClosedFiber)
  let hCM : Module.CohenMacaulay ClosedFiber ClosedFiber :=
    self_cohenMacaulay_of_krullDimLE_zero ClosedFiber
  have hdepth :
      ringKrullDim ClosedFiber = .some (moduleDepth ClosedFiber ClosedFiber) :=
    (Module.supportDim_self_eq_ringKrullDim ClosedFiber).symm.trans hCM.supportDim_eq_moduleDepth
  rw [ringKrullDim_eq_zero_of_isField (Field.toIsField ClosedFiber)] at hdepth
  simpa using hdepth.symm

-- Proof sketch: apply the flat local-homomorphism depth formula
-- `depth_target_eq_depth_source_add_depth_closed_fiber` to the completion map
-- `A → AdicCompletion (maximalIdeal A) A`. The closed fiber is canonically isomorphic to the
-- residue-field quotient by the extended maximal ideal, hence is a field and has depth `0`.
/-- Lemma 15.43.2: a Noetherian local ring and its maximal-ideal adic completion have the same
depth. -/
@[stacks 07NW]
theorem moduleDepth_eq_moduleDepth_maximalIdeal_adicCompletion :
    moduleDepth A A = moduleDepth ACompletion ACompletion := by
  let _ : Module.Flat A ACompletion :=
    (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A).flat
  have hdepth :
      moduleDepth ACompletion ACompletion =
        moduleDepth A A + moduleDepth ClosedFiber ClosedFiber :=
    depth_target_eq_depth_source_add_depth_closed_fiber
  simpa [closedFiber_moduleDepth_eq_zero A] using hdepth.symm

end
