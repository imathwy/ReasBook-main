import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct
open RingTheory.Sequence

section FaithfullyFlatDescent

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
variable [AddCommGroup M] [Module R M]

private theorem isRegular_of_isRegular_tensorBaseChange {rs : List R}
    (hreg : IsRegular (S ⊗[R] M) (rs.map (algebraMap R S))) :
    IsRegular M rs := by
  induction rs generalizing M with
  | nil =>
      have htop : (⊤ : Submodule S (S ⊗[R] M)) ≠ ⊥ := by
        simpa [Ideal.ofList_nil] using hreg.top_ne_smul
      have hnontrivial_tensor : Nontrivial (S ⊗[R] M) := by
        refine not_subsingleton_iff_nontrivial.mp fun hsub ↦ ?_
        apply htop
        ext x
        simp [Subsingleton.elim x 0]
      have hnontrivial : Nontrivial M :=
        (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right R S).mp hnontrivial_tensor
      exact IsRegular.nil R M
  | cons r rs ih =>
      rw [List.map_cons, isRegular_cons_iff] at hreg
      rw [isRegular_cons_iff]
      refine ⟨?_, ?_⟩
      · have hsmul : IsSMulRegular (S ⊗[R] M) r :=
          hreg.1.of_map (algebraMap R S) (algebraMap_smul S r)
        exact hsmul.of_injective (TensorProduct.mk R S M 1) <|
          Module.FaithfullyFlat.tensorProduct_mk_injective M
      · have htail : IsRegular (S ⊗[R] QuotSMulTop r M) (rs.map (algebraMap R S)) := by
          exact
            (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop r M S).isRegular_congr
              (rs.map (algebraMap R S)) |>.mp hreg.2
        exact ih htail

end FaithfullyFlatDescent

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
variable [AddCommGroup M] [Module R M]

/-- Lemma 10.68.5: for a flat local homomorphism of local rings `R → S`, a sequence `rs` is
`M`-regular over `R` if and only if its image in `S` is regular on the base-change module
`S ⊗[R] M`. -/
@[stacks 00LM]
theorem isRegular_iff_isRegular_tensorBaseChange_of_flat_localHom {rs : List R} :
    IsRegular M rs ↔ IsRegular (S ⊗[R] M) (rs.map (algebraMap R S)) := by
  letI : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  constructor
  · exact IsRegular.of_faithfullyFlat_of_isBaseChange (TensorProduct.isBaseChange R M S)
  · exact isRegular_of_isRegular_tensorBaseChange

end
