import StacksProject_2024.stacks_project.Chap10.Lemma_10_24_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

open IsLocalizedModule LocalizedModule

variable {A : Type u} [CommRing A]
variable (S S' : Submonoid A)
variable (M : Type v) [AddCommGroup M] [Module A M]

/- Proposition 10.9.11: viewing `S'⁻¹M` as an `A`-module, localizing it again at `S` is
canonically isomorphic to localizing `M` at the submonoid `S ⊔ S'`, which is the Lean realization
of the textbook multiplicative set `SS'`. This is exactly the specialized canonical equivalence
`IsLocalizedModule.linearEquiv` attached to the two localization maps. -/
#check
  (linearEquiv (S ⊔ S') (iteratedLocalizedModuleMkLinearMap S S' M) (mkLinearMap (S ⊔ S') M) :
    LocalizedModule S (LocalizedModule S' M) ≃ₗ[A] LocalizedModule (S ⊔ S') M)

/- Companion recall: the inverse comparison map carries the iterated localization map `M →
S⁻¹(S'⁻¹M)` back to the direct localization map `M → (S ⊔ S')⁻¹M`. This is the owner theorem
`IsLocalizedModule.iso_symm_comp` specialized to the iterated-localization map. -/
#check
  (iso_symm_comp (S ⊔ S') (iteratedLocalizedModuleMkLinearMap S S' M) :
    (iso (S ⊔ S') (iteratedLocalizedModuleMkLinearMap S S' M)).symm.toLinearMap.comp
        (iteratedLocalizedModuleMkLinearMap S S' M) =
      mkLinearMap (S ⊔ S') M)

end
