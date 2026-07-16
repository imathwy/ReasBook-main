import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_96_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_10
import StacksProject_2024.stacks_project.Chap10.Lemma_10_99_11
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open IsLocalRing Algebra.TensorProduct
open scoped TensorProduct

universe u v

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] IsScalarTower.right

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "BCompletion" => AdicCompletion (maximalIdeal B) B

/- Domain triage:
* `source-facing`: Lemma `15.43.8` compares flatness of a local map of Noetherian local rings
  with flatness of the induced map on maximal-ideal completions.
* `core/canonical` owners: `maximalIdealCompletionMap` for the induced completed map and
  `RingHom.Flat` for the flatness property of ring homomorphisms.
* `bridge/view`: faithful flatness of the completion maps from Lemma `10.97.3`, the descent owner
  `algebraMap_flat_of_flat_of_faithfullyFlat` from Lemma `10.39.10`, and the canonical
  base-change owner `Module.Flat.baseChange`.
* sampled declarations in the same domain:
  `maximalIdealCompletionMap`,
  `maximalIdealCompletionMap_comp`,
  `maximalIdeal_adicCompletion_algebraMap_faithfullyFlat`,
  `algebraMap_flat_of_flat_of_faithfullyFlat`,
  `Module.Flat.baseChange`,
  `Algebra.TensorProduct.lidOfCompatibleSMul`.

Primitive data are the local ring map `f : A →+* B` and the Noetherian local hypotheses on `A`
and `B`. The completed comparison map and the faithfully-flat base-change/descent infrastructure
are derived from the owner declarations above, so this file keeps only the source-facing theorem. -/

/- The reverse implication follows the source route up to the final comparison step: first compose
with the faithfully flat target completion map, then base change that flatness along
`A → A^∧`, and only after that compare the base-changed tensor product with the actual completed
target. -/

/-- Helper for Lemma 15.43.8: if `f : A →+* B` is flat, then the composite map
`A → B^∧` obtained by completing the target remains flat. -/
private lemma flat_algebraMap_to_target_completion (f : A →+* B) [IsLocalHom f] (hf : f.Flat) :
    ((algebraMap B BCompletion).comp f).Flat := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B BCompletion := (algebraMap B BCompletion).toAlgebra
  letI : Algebra A BCompletion := ((algebraMap B BCompletion).comp f).toAlgebra
  have hBCompletion_ff : (algebraMap B BCompletion).FaithfullyFlat :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat B
  -- Compose the given flat map with the faithfully flat completion map on the target ring.
  exact RingHom.Flat.comp hf hBCompletion_ff.flat

-- Proof sketch: if the induced map `A^∧ → B^∧` is flat, compose it with the faithfully flat map
-- `A → A^∧` to obtain flatness of `A → B^∧`, then apply the owner descent theorem
-- `algebraMap_flat_of_flat_of_faithfullyFlat` to the faithfully flat map `B → B^∧`. Conversely,
-- if `A → B` is flat, then `A → B^∧` is flat because `B → B^∧` is flat; faithful flatness of
-- `A → A^∧` upgrades this by base change to flatness of `A^∧ ⊗[A] B^∧` over `A^∧`, and the
-- canonical tensor-action equivalence
-- `A^∧ ⊗[A] B^∧ ≃ B^∧` yields flatness of `A^∧ → B^∧`.
/-- Lemma 15.43.8: for a local homomorphism `f : A →+* B` of Noetherian local rings, the induced
map on maximal-ideal completions is flat if and only if `f` is flat. -/
theorem flat_iff_flat_maximalIdealCompletionMap (f : A →+* B) [IsLocalHom f] :
    (maximalIdealCompletionMap f).Flat ↔ f.Flat := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B BCompletion := (algebraMap B BCompletion).toAlgebra
  letI : Algebra A BCompletion := ((algebraMap B BCompletion).comp f).toAlgebra
  letI : Algebra ACompletion BCompletion := (maximalIdealCompletionMap f).toAlgebra
  letI : IsScalarTower A ACompletion BCompletion :=
    IsScalarTower.of_algebraMap_eq' <| by
      simpa [RingHom.algebraMap_toAlgebra] using (maximalIdealCompletionMap_comp f).symm
  have hACompletion_ff : (algebraMap A ACompletion).FaithfullyFlat :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A
  have hBCompletion_ff : (algebraMap B BCompletion).FaithfullyFlat :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat B
  letI : Module.FaithfullyFlat A ACompletion :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hACompletion_ff
  letI : Module.FaithfullyFlat B BCompletion :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hBCompletion_ff
  constructor
  · intro hCompletion
    have hABCompletion_comp : ((algebraMap B BCompletion).comp f).Flat := by
      simpa [maximalIdealCompletionMap_comp f] using
        RingHom.Flat.comp hACompletion_ff.flat hCompletion
    have hABCompletion : (algebraMap A BCompletion).Flat := by
      simpa [RingHom.algebraMap_toAlgebra] using hABCompletion_comp
    letI : Module.Flat A BCompletion := RingHom.flat_algebraMap_iff.mp hABCompletion
    letI : Module.Flat A (RestrictScalars A B BCompletion) := by
      change Module.Flat A BCompletion
      infer_instance
    simpa [RingHom.algebraMap_toAlgebra] using
      (algebraMap_flat_of_flat_of_faithfullyFlat BCompletion : (algebraMap A B).Flat)
  · intro hf
    -- First compose `A → B` with the faithfully flat completion map `B → B^∧`.
    have hABCompletion_comp : ((algebraMap B BCompletion).comp f).Flat := by
      exact flat_algebraMap_to_target_completion (f := f) hf
    have hABCompletion : (algebraMap A BCompletion).Flat := by
      simpa [RingHom.algebraMap_toAlgebra] using hABCompletion_comp
    have hBCompletion_flat : Module.Flat A BCompletion :=
      RingHom.flat_algebraMap_iff.mp hABCompletion
    letI : Module.Flat A BCompletion := hBCompletion_flat
    have hbase :
        Module.Flat ACompletion (ACompletion ⊗[A] BCompletion) := by
      -- Base change the flat `A`-module `B^∧` along the faithfully flat completion map
      -- `A → A^∧`.
      simpa using (Module.Flat.baseChange (R := A) (S := ACompletion) (M := BCompletion))
    letI : Module.Flat ACompletion (ACompletion ⊗[A] BCompletion) := hbase
    have hCompletionModule : Module.Flat ACompletion BCompletion := by
      -- Descend flatness from the base-changed tensor product along the faithfully flat map
      -- `A → A^∧`.
      exact (Module.Flat.iff_flat_tensorProduct (R := A) (M := BCompletion) ACompletion).mp hbase
    simpa [RingHom.algebraMap_toAlgebra] using
      (RingHom.flat_algebraMap_iff.mpr hCompletionModule :
        (algebraMap ACompletion BCompletion).Flat)

end
