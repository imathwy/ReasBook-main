import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct Subalgebra

universe u v w

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {A₂ : Type w} [Ring A₂] [Algebra k A₂]

/- Domain sampling for Lemma 11.4.1.
- primary domain: tensor-product subalgebras and centralizers in `A ⊗[k] A₂`;
- inspected owner declarations:
  `Subalgebra.centralizer_coe_sup`,
  `Subalgebra.centralizer_coe_map_includeLeft_eq_center_tensorProduct`,
  `Subalgebra.centralizer_coe_map_includeRight_eq_center_tensorProduct`,
  `Algebra.TensorProduct.map_range`;
- best owner abstraction: `Subalgebra.centralizer` applied to the canonical tensor-product
  subalgebra `(Algebra.TensorProduct.map B.val B₂.val).range`;
- primitive data: the subalgebras `B`, `B₂` and the owner tensor-product map;
- derived API: the one-sided centralizer computations and the `map_range` identification with the
  join of the left/right image subalgebras;
- layer classification:
  `source-facing`: the textbook centralizer statement for `B ⊗[k] B₂`;
  `core/canonical`: `Subalgebra.centralizer`;
  `bridge/view`: `Algebra.TensorProduct.map_range` and the one-sided centralizer lemmas. -/

/-- Lemma 11.4.1: for `k`-subalgebras `B ⊆ A` and `B' ⊆ A₂`, the centralizer of the tensor-product
subalgebra `B ⊗[k] B' ⊆ A ⊗[k] A₂` is the tensor product of the centralizers of `B` and `B'`. -/
-- Proof sketch: `(Algebra.TensorProduct.map B.val B₂.val).range` is the canonical tensor-product
-- subalgebra in `A ⊗[k] A₂`, and `Algebra.TensorProduct.map_range` identifies it with the
-- supremum of the left and right image subalgebras `B.map includeLeft` and
-- `B₂.map includeRight`. The one-sided owner lemmas compute the corresponding centralizers; the
-- remaining bridge identifies their intersection with the tensor product of the two centralizers,
-- for example by passing through the smaller ambient algebra `C_A(B) ⊗[k] A₂`.
theorem centralizer_tensorProduct_subalgebra_eq
    (B : Subalgebra k A) (B₂ : Subalgebra k A₂) :
    centralizer k (map B.val B₂.val).range =
      (map (centralizer k (B : Set A)).val (centralizer k (B₂ : Set A₂)).val).range := by
  let C : Subalgebra k A := centralizer k (B : Set A)
  let C₂ : Subalgebra k A₂ := centralizer k (B₂ : Set A₂)
  let ι : C ⊗[k] A₂ →ₐ[k] A ⊗[k] A₂ := map C.val (AlgHom.id k A₂)
  let S : Subalgebra k (A ⊗[k] A₂) := centralizer k (B₂.map (includeRight : A₂ →ₐ[k] A ⊗[k] A₂))
  let T : Subalgebra k (C ⊗[k] A₂) := centralizer k (B₂.map (includeRight : A₂ →ₐ[k] C ⊗[k] A₂))
  have h_tensor :
      (map B.val B₂.val).range =
        B.map (includeLeft : A →ₐ[k] A ⊗[k] A₂) ⊔
          B₂.map (includeRight : A₂ →ₐ[k] A ⊗[k] A₂) := by
    simpa [AlgHom.range_comp, range_val] using map_range B.val B₂.val
  have hι : Function.Injective ι := by
    change Function.Injective
      (TensorProduct.map C.val.toLinearMap (LinearMap.id : A₂ →ₗ[k] A₂))
    simpa using TensorProduct.map_injective_of_flat_flat
      C.val.toLinearMap (LinearMap.id : A₂ →ₗ[k] A₂) Subtype.val_injective
      (fun _ _ h ↦ h)
  have h_left :
      centralizer k (B.map (includeLeft : A →ₐ[k] A ⊗[k] A₂)) = ι.range := by
    simpa [C, ι, AlgHom.range_comp] using
      centralizer_coe_map_includeLeft_eq_center_tensorProduct k A A₂ B
  have h_comap : S.comap ι = T := by
    ext x
    rw [mem_comap, mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro hx y
      rintro ⟨b, hb, rfl⟩
      apply hι
      simpa using hx (includeRight b) ⟨b, hb, rfl⟩
    · intro hx y
      rintro ⟨b, hb, rfl⟩
      simpa using congrArg ι (hx (includeRight b) ⟨b, hb, rfl⟩)
  have h_right :
      T = (map (AlgHom.id k C) C₂.val).range := by
    simpa [C₂, T] using
      centralizer_coe_map_includeRight_eq_center_tensorProduct k C A₂ B₂
  have h_map :
      ((map (AlgHom.id k C) C₂.val).range).map ι = (map C.val C₂.val).range := by
    have h_comp :
        ι.comp (map (AlgHom.id k C) C₂.val) = map C.val C₂.val := by
      simpa [ι] using (map_comp C.val (AlgHom.id k C) (AlgHom.id k A₂) C₂.val).symm
    rw [← AlgHom.range_comp]
    exact congrArg AlgHom.range h_comp
  rw [h_tensor, centralizer_coe_sup, h_left,
    show centralizer k (B₂.map (includeRight : A₂ →ₐ[k] A ⊗[k] A₂)) = S from rfl,
    inf_comm, ← map_comap_eq ι S, h_comap, h_right, h_map]
