import Mathlib
import StacksProject_2024.Chap15.Lemma_15_105_10
import StacksProject_2024.Chap15.Lemma_15_105_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open IntermediateField

universe u

section

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/- Domain triage:
- primary domain: field extensions viewed through the weakly étale / formally unramified tensor
  square criterion;
- source-facing layer: the Stacks consequence that flatness of `L ⊗[K] L → L` forces `L/K`
  to be separable;
- sampled core/canonical owners:
  `tensorSquareMul_flat_of_faithfullyFlat`,
  `Algebra.FormallyUnramified.of_tensorSquareMul_flat`,
  `Algebra.FormallyUnramified.isSeparable`,
  `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`;
- primitive data: flatness of the tensor-square multiplication map;
- derived API: separability of each simple intermediate field `K⟮x⟯`, hence of `L/K`.

The refinement stays source-facing. The public theorem is still the field-theoretic conclusion,
but its proof now routes entirely through the canonical owner abstractions instead of a bespoke
local argument shell.
-/

-- Proof sketch: first descend the flatness hypothesis along finitely generated intermediate
-- subextensions, then use the finite-type criterion that formal unramifiedness of a field
-- extension is equivalent to separability; algebraicity is absorbed by the canonical separability
-- class for field extensions.
/-- Lemma 15.105.15: if the multiplication map `L ⊗[K] L → L` is flat, then `L/K` is an
algebraic separable extension. In mathlib this is expressed by the canonical class
`Algebra.IsSeparable K L`. -/
@[stacks 092P]
theorem isSeparable_of_flat_tensorSquareMultiplication
    (hflat : (Algebra.TensorProduct.lmul' K : L ⊗[K] L →ₐ[K] L).Flat) :
    Algebra.IsSeparable K L := by
  refine ⟨fun x ↦ ?_⟩
  let M : IntermediateField K L := K⟮x⟯
  letI : Algebra M L := M.val.toAlgebra
  letI : IsScalarTower K M L := inferInstance
  have hML : (algebraMap M L).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hMflat : (Algebra.TensorProduct.lmul' K : M ⊗[K] M →ₐ[K] M).Flat :=
    Algebra.tensorSquareMul_flat_of_faithfullyFlat hML hflat
  letI : Algebra.FormallyUnramified K M :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hMflat
  letI : Algebra.EssFiniteType K M := (IntermediateField.essFiniteType_iff).2 <|
    by simpa [M] using IntermediateField.fg_adjoin_finset ({x} : Finset L)
  have : Algebra.IsSeparable K M := Algebra.FormallyUnramified.isSeparable K M
  exact (isSeparable_adjoin_simple_iff_isSeparable K L).mp <| by simpa [M] using this

end
