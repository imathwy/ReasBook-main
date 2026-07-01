import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open TensorProduct LinearMap
open scoped TensorProduct

universe u v

namespace Ideal

/-
Domain triage: this file is `source-facing` for the flat-module intersection identity
`IM ∩ JM = (I ∩ J) M`. For the algebra specialization, the owner abstraction is the
`InfTopHom` on ideals induced by `Ideal.map (algebraMap R S)` under flatness. Primitive data:
the flat module/algebra structure. Derived API: the algebra-valued reformulation and the
bundled `InfTopHom` used by later finite-intersection arguments.
-/

section Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]

/- The intersection of the images of two ideals on a flat module is the image of their
intersection. -/
-- Proof sketch: identify
-- `M → (R ⧸ I) ⊗[R] M × (R ⧸ J) ⊗[R] M`
-- with the tensor of `R → R ⧸ I × R ⧸ J`, use flatness to compute its kernel as the tensor of
-- `I ∩ J`, and then rewrite the resulting tensor-image as `(I ∩ J) • ⊤`.
/-- Lemma 10.39.2: for ideals `I` and `J` of a commutative ring `R` and a flat `R`-module `M`,
their images in `M` satisfy `IM ∩ JM = (I ∩ J)M`. -/
@[stacks 0BBY]
theorem smul_top_inf_smul_top_eq_inf_smul_top_of_flat (I J : Ideal R) :
    I • (⊤ : Submodule R M) ⊓ J • (⊤ : Submodule R M) = (I ⊓ J) • (⊤ : Submodule R M) := by
  let f : R →ₗ[R] (R ⧸ I) × (R ⧸ J) := I.mkQ.prod J.mkQ
  let l : R ⊗[R] M ≃ₗ[R] M := TensorProduct.lid R M
  let e : ((R ⧸ I) × (R ⧸ J)) ⊗[R] M ≃ₗ[R]
      ((R ⧸ I) ⊗[R] M) × ((R ⧸ J) ⊗[R] M) :=
    prodLeft R R (R ⧸ I) (R ⧸ J) M
  have hmap :
      (e.toLinearMap.comp (f.rTensor M)).comp l.symm.toLinearMap =
        (mk R (R ⧸ I) M 1).prod (mk R (R ⧸ J) M 1) := by
    ext m <;> simp [f, l, e]
  have hker_tensor :
      ker (f.rTensor M) = range ((ker f).subtype.rTensor M) := by
    rw [← exact_iff]
    exact Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map f)
  have hker : LinearMap.ker f = I ⊓ J := by
    ext r
    simp [f, ker_prod]
  calc
    I • (⊤ : Submodule R M) ⊓ J • (⊤ : Submodule R M)
        = ker ((mk R (R ⧸ I) M 1).prod (mk R (R ⧸ J) M 1)) := by
            rw [ker_prod, ker_tensorProductMk, ker_tensorProductMk]
    _ = ker ((e.toLinearMap.comp (f.rTensor M)).comp l.symm.toLinearMap) := by
          rw [hmap]
    _ = (I ⊓ J) • (⊤ : Submodule R M) := by
          rw [ker_comp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.ker_comp, hker_tensor,
            ← range_comp, hker]
          simpa using Ideal.subtype_rTensor_range M (I ⊓ J)

end Module

section Algebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [Module.Flat R S]

/-- For a flat `R`-algebra `S`, extension of ideals along `R → S` preserves binary intersections.

This is the algebra-valued specialization of Lemma 10.39.2, rewritten using
`Ideal.smul_top_eq_map`. -/
theorem map_inf_of_flat (I J : Ideal R) :
    Ideal.map (algebraMap R S) (I ⊓ J) =
      Ideal.map (algebraMap R S) I ⊓ Ideal.map (algebraMap R S) J := by
  have h :
      I • (⊤ : Submodule R S) ⊓ J • (⊤ : Submodule R S) = (I ⊓ J) • (⊤ : Submodule R S) :=
    smul_top_inf_smul_top_eq_inf_smul_top_of_flat I J
  apply Submodule.restrictScalars_injective R
  simpa [Ideal.smul_top_eq_map] using h.symm

/-- For a flat `R`-algebra `S`, ideal extension along `R → S` preserves finite intersections and
the top ideal. This is the owner abstraction used when later arguments need the ideal-extension
map as an `InfTopHom`. -/
def mapInfTopHom : InfTopHom (Ideal R) (Ideal S) where
  toFun := Ideal.map (algebraMap R S)
  map_inf' := map_inf_of_flat
  map_top' := map_top _

@[simp] theorem mapInfTopHom_apply (I : Ideal R) :
    mapInfTopHom I = Ideal.map (algebraMap R S) I := rfl

end Algebra

end Ideal
