import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

/- Layering for this item:
* source-facing: fiberwise nontriviality over prime and maximal residue fields;
* core/canonical owner: `Module.FaithfullyFlat` together with its tensor-faithfulness and
  proper-ideal criteria;
* bridge/view: the canonical comparison
  `M ⊗[R] m.ResidueField ≃ₗ[R] M ⧸ m • (⊤ : Submodule R M)` for maximal ideals.
-/

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- For a maximal ideal `m`, tensoring with `m.ResidueField` is equivalent to reducing modulo
`m • M`. This is the nontriviality form of the canonical quotient-residue-field identification
combined with `TensorProduct.tensorQuotEquivQuotSMul`. -/
theorem nontrivial_tensor_residueField_iff_nontrivial_quotSMul
    (m : Ideal R) [m.IsMaximal] :
    Nontrivial (M ⊗[R] m.ResidueField) ↔ Nontrivial (M ⧸ m • (⊤ : Submodule R M)) := by
  let e : M ⊗[R] m.ResidueField ≃ₗ[R] M ⧸ m • (⊤ : Submodule R M) :=
    (TensorProduct.congr (LinearEquiv.refl R M)
        (AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ m) m.ResidueField)
          (Ideal.bijective_algebraMap_quotient_residueField m)).toLinearEquiv).symm ≪≫ₗ
      TensorProduct.tensorQuotEquivQuotSMul M m
  exact e.nontrivial_congr

section Flat

variable [Module.Flat R M]

open Module.FaithfullyFlat

/-- A flat `R`-module is faithfully flat if and only if all of its fibers over maximal ideals are
nontrivial. -/
theorem faithfullyFlat_iff_forall_nontrivial_tensor_residueField :
    Module.FaithfullyFlat R M ↔
      ∀ (m : Ideal R) (_ : m.IsMaximal), Nontrivial (M ⊗[R] m.ResidueField) := by
  constructor
  · intro h m hm
    letI : Module.FaithfullyFlat R M := h
    letI : m.IsMaximal := hm
    infer_instance
  · intro h
    refine (iff_flat_and_proper_ideal R M).2 ?_
    refine ⟨inferInstance, fun I hI htop ↦ ?_⟩
    obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
    have hmQuot : Nontrivial (M ⧸ m • (⊤ : Submodule R M)) :=
      (nontrivial_tensor_residueField_iff_nontrivial_quotSMul m).mp (h m hm)
    have hmTop : m • (⊤ : Submodule R M) = ⊤ := eq_top_iff.2 <| by
      calc
        ⊤ = I • (⊤ : Submodule R M) := htop.symm
        _ ≤ m • (⊤ : Submodule R M) := Submodule.smul_mono hIm le_rfl
    exact (not_nontrivial_iff_subsingleton.mpr <| by rwa [Submodule.Quotient.subsingleton_iff]) hmQuot

/-- A flat `R`-module is faithfully flat if and only if all of its fibers over prime ideals are
nontrivial. -/
theorem faithfullyFlat_iff_forall_nontrivial_tensor_primeResidueField :
    Module.FaithfullyFlat R M ↔
      ∀ p : PrimeSpectrum R, Nontrivial (M ⊗[R] p.asIdeal.ResidueField) := by
  constructor
  · intro h p
    letI : Module.FaithfullyFlat R M := h
    infer_instance
  · intro h
    exact faithfullyFlat_iff_forall_nontrivial_tensor_residueField.2 fun m hm ↦ by
      letI : m.IsPrime := hm.isPrime
      exact h (⟨m, inferInstance⟩ : PrimeSpectrum R)

/-- Lemma 10.39.15: for a flat `R`-module `M`, the following are equivalent: `M` is faithfully
flat; for every nontrivial `R`-module `N`, the tensor product `M ⊗[R] N` is nontrivial; for every
prime `p : PrimeSpectrum R`, the fiber `M ⊗[R] κ(p)` is nontrivial; and for every maximal ideal
`m`, the tensor product `M ⊗[R] m.ResidueField` is nontrivial, equivalently `M ⧸ m • ⊤` is
nontrivial via `nontrivial_tensor_residueField_iff_nontrivial_quotSMul`. -/
-- Proof sketch: use `Module.FaithfullyFlat.iff_flat_and_lTensor_faithful` for the equivalence
-- between faithful flatness and nontriviality after tensoring with every nontrivial module. The
-- implications to prime and maximal residue fields are immediate specializations. For the converse,
-- use the maximal-ideal hypothesis together with the tensor-quotient identification
-- `M ⊗[R] κ(m) ≃ₗ[R] M ⧸ m • ⊤` and the canonical proper-ideal criterion
-- `Module.FaithfullyFlat.iff_flat_and_proper_ideal`.
@[stacks 00HP]
theorem faithfullyFlat_tfae_nontrivial_tensor_residueField :
    List.TFAE
      [Module.FaithfullyFlat R M,
        ∀ (N : Type (max u v)) [AddCommGroup N] [Module R N],
          Nontrivial N → Nontrivial (M ⊗[R] N),
        ∀ p : PrimeSpectrum R, Nontrivial (M ⊗[R] p.asIdeal.ResidueField),
        ∀ (m : Ideal R) (_ : m.IsMaximal), Nontrivial (M ⊗[R] m.ResidueField)] := by
  tfae_have 1 ↔ 2 := by
    rw [iff_flat_and_lTensor_faithful]
    exact and_iff_right inferInstance
  tfae_have 1 ↔ 3 := by
    exact faithfullyFlat_iff_forall_nontrivial_tensor_primeResidueField
  tfae_have 1 ↔ 4 := by
    exact faithfullyFlat_iff_forall_nontrivial_tensor_residueField
  tfae_finish

end Flat

end
