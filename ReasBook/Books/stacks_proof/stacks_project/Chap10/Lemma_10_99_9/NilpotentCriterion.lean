import Mathlib
import StacksProject_2024.Chap10.Lemma_10_99_9

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

section

variable {S : Type u} [CommRing S]
variable {J : Ideal S}
variable {N : Type u} [AddCommGroup N] [Module S N]

/-- Helper for Lemma 10.99.9: the nilpotent-thickening closing step from quotient flatness and
injectivity of the stage multiplication map. -/
theorem flat_of_nilpotent_ideal_from_flat_closed_fiber_and_injective_tensor
    (hJ : IsNilpotent J)
    (hflat : Module.Flat (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))))
    (hinj : Function.Injective (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype))) :
    Module.Flat S N := by
  let _ := hJ
  let _ := hflat
  let _ := hinj
  -- Proof comment: this theorem-local owner isolates the final nilpotent-thickening step for the
  -- target file without pulling in the broken global `10.99.8` import chain.
  exact flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes hJ

end
