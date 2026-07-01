import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open TensorProduct
open AlgebraTensorModule

universe u v w

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.39.10: if an `S`-module `M` is flat as an `R`-module and faithfully flat as an
`S`-module, then the algebra map `R → S` is flat. -/
theorem algebraMap_flat_of_flat_of_faithfullyFlat (M : Type w) [AddCommGroup M] [Module S M]
    [Module.Flat R (RestrictScalars R S M)] [Module.FaithfullyFlat S M] :
    (algebraMap R S).Flat := by
  letI : Module R M := Module.restrictScalars R S M
  letI : IsScalarTower R S M := IsScalarTower.restrictScalars R S M
  letI : Module.Flat R M := by
    change Module.Flat R (RestrictScalars R S M)
    infer_instance
  rw [RingHom.flat_algebraMap_iff, Module.Flat.iff_lTensor_exact]
  intro N₁ N₂ N₃ _ _ _ _ _ _ l₁₂ l₂₃ h
  have hM : Function.Exact (lTensor S M l₁₂) (lTensor S M l₂₃) := by
    simpa [coe_lTensor] using Module.Flat.lTensor_exact M h
  have hSM :
      Function.Exact (lTensor S M (lTensor S S l₁₂))
        (lTensor S M (lTensor S S l₂₃)) :=
    (Function.Exact.iff_of_ladder_linearEquiv
      (lTensor_comp_cancelBaseChange R S S l₁₂)
      (lTensor_comp_cancelBaseChange R S S l₂₃)).1 hM
  simpa using
    (Module.FaithfullyFlat.lTensor_exact_iff_exact S M
      (lTensor S S l₁₂) (lTensor S S l₂₃)).1 hSM

end
