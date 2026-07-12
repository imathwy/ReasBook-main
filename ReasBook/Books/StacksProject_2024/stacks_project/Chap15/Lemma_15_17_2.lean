import Mathlib.LinearAlgebra.TensorProduct.Quotient
import StacksProject_2024.Chap10.Lemma_10_101_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Ideal

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 15.17.2: an ideal `J` has flat quotient for `M` when `M / JM` is flat over
`R ⧸ J`. -/
abbrev IsFlatQuotient (J : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  Module.Flat (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))

end Ideal

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {R' : Type w} [CommRing R'] [Algebra R R']

/-- Helper for Lemma 15.17.2: if the image of `J` in `R'` is zero, then every element of `J`
maps to zero in `R'`. -/
lemma map_eq_zero_of_mem_of_map_eq_bot
    {J : Ideal R}
    (hmap : J.map (algebraMap R R') = ⊥)
    {a : R}
    (ha : a ∈ J) :
    (algebraMap R R') a = 0 := by
  -- Convert the vanishing of the mapped ideal into the kernel containment used on elements.
  have hle : J ≤ RingHom.ker (algebraMap R R') :=
    (Ideal.map_eq_bot_iff_le_ker (f := algebraMap R R')).mp hmap
  exact RingHom.mem_ker.mp (hle ha)

/-- Helper for Lemma 15.17.2: when `J` maps to zero in `R'`, the `R`-algebra structure on `R'`
factors through `R ⧸ J`. -/
noncomputable abbrev quotient_factor_alg_hom
    {J : Ideal R}
    (hmap : J.map (algebraMap R R') = ⊥) :
    R ⧸ J →ₐ[R] R' :=
  Ideal.Quotient.liftₐ (R₁ := R) (I := J) (Algebra.ofId R R')
    (fun a ha ↦ map_eq_zero_of_mem_of_map_eq_bot (R' := R') hmap (a := a) ha)

/-- Helper for Lemma 15.17.2: the quotient by the kernel of `R → R'` carries the canonical
injective comparison map to `R'`. -/
noncomputable abbrev kernel_quotient_alg_hom :
    R ⧸ RingHom.ker (algebraMap R R') →ₐ[R] R' :=
  Ideal.kerLiftAlg (Algebra.ofId R R')

/-- Helper for Lemma 15.17.2: the image-zero hypothesis forces the induced ideal action on the
base-changed tensor product to vanish. -/
lemma map_smul_top_eq_bot_of_map_eq_bot
    {J : Ideal R}
    (hmap : J.map (algebraMap R R') = ⊥) :
    J.map (algebraMap R R') • (⊤ : Submodule R' (R' ⊗[R] M)) = ⊥ := by
  -- Rewrite the scalar ideal to `⊥`, where the induced submodule is visibly zero.
  simpa [hmap]

/-- Helper for Lemma 15.17.2: after factoring the algebra structure through `R ⧸ J`, tensoring the
quotient module over `R ⧸ J` agrees with tensoring it over `R`. -/
noncomputable abbrev factor_tensor_quotient_equiv_base_tensor_quotient
    {J : Ideal R}
    [Algebra (R ⧸ J) R']
    [IsScalarTower R (R ⧸ J) R'] :
    (R' ⊗[R ⧸ J] (M ⧸ (J • (⊤ : Submodule R M)))) ≃ₗ[R']
      (R' ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) :=
  letI :
      TensorProduct.CompatibleSMul R (R ⧸ J) (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))) :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (R := R) (A := R ⧸ J) (M := R ⧸ J) (N := M ⧸ (J • (⊤ : Submodule R M)))
      Ideal.Quotient.mk_surjective
  let eLid :
      ((R ⧸ J) ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) ≃ₗ[R ⧸ J]
        (M ⧸ (J • (⊤ : Submodule R M))) :=
    TensorProduct.lidOfCompatibleSMul R (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') eLid.symm).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ J) R' R'
      (M ⧸ (J • (⊤ : Submodule R M))))

/-- Helper for Lemma 15.17.2: if `J` maps to zero in `R'`, then tensoring the quotient module
`M / JM` over `R` recovers the original base change `R' ⊗[R] M`. -/
noncomputable abbrev base_tensor_quotient_equiv_tensor_of_map_eq_bot
    {J : Ideal R}
    (hmap : J.map (algebraMap R R') = ⊥) :
    (R' ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) ≃ₗ[R'] (R' ⊗[R] M) :=
  let eBot :
      (R' ⊗[R] M) ≃ₗ[R']
        (((R' ⊗[R] M) ⧸
          J.map (algebraMap R R') • (⊤ : Submodule R' (R' ⊗[R] M)))) :=
    ((J.map (algebraMap R R') • (⊤ : Submodule R' (R' ⊗[R] M))).quotEquivOfEqBot
      (map_smul_top_eq_bot_of_map_eq_bot (R := R) (M := M) (R' := R') hmap)).symm
  let eTensorQuot :
      (((R' ⊗[R] M) ⧸
          J.map (algebraMap R R') • (⊤ : Submodule R' (R' ⊗[R] M)))) ≃ₗ[R']
        (R' ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) :=
    TensorProduct.tensorQuotMapSMulEquivTensorQuot (S := R') (M := M) J
  (eBot.trans eTensorQuot).symm

/-- Helper for Lemma 15.17.2: a flat quotient ideal remains flat after any base change whose
structure map kills that ideal. -/
lemma flat_tensorProduct_of_isFlatQuotient_of_map_eq_bot
    {J : Ideal R}
    (hflat : J.IsFlatQuotient M)
    (hmap : J.map (algebraMap R R') = ⊥) :
    Module.Flat R' (R' ⊗[R] M) := by
  -- Endow `R'` with its induced `R ⧸ J`-algebra structure so the quotient flatness can be
  -- base-changed along `R ⧸ J → R'`.
  let φ : R ⧸ J →ₐ[R] R' := quotient_factor_alg_hom (R := R) (R' := R') hmap
  letI : Algebra (R ⧸ J) R' := φ.toRingHom.toAlgebra
  have hbase :
      Module.Flat R' (R' ⊗[R ⧸ J] (M ⧸ (J • (⊤ : Submodule R M)))) := by
    -- Base change the flat quotient module over `R ⧸ J` to the new algebra `R'`.
    let _ : Module.Flat (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))) := hflat
    simpa using
      (Module.Flat.baseChange (R := R ⧸ J) (S := R')
        (M := M ⧸ (J • (⊤ : Submodule R M))))
  let eFactor :
      (R' ⊗[R ⧸ J] (M ⧸ (J • (⊤ : Submodule R M)))) ≃ₗ[R']
        (R' ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) :=
    factor_tensor_quotient_equiv_base_tensor_quotient
      (R := R) (M := M) (R' := R') (J := J)
  let eTensor :
      (R' ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) ≃ₗ[R'] (R' ⊗[R] M) :=
    base_tensor_quotient_equiv_tensor_of_map_eq_bot
      (R := R) (M := M) (R' := R') (J := J) hmap
  -- Route correction: transport flatness across the factor-ring tensor comparison first, then
  -- across the ambient tensor/quotient comparison forced by `J.map = ⊥`.
  let _ : Module.Flat R' (R' ⊗[R ⧸ J] (M ⧸ (J • (⊤ : Submodule R M)))) := hbase
  exact Module.Flat.of_linearEquiv (eFactor.trans eTensor).symm

variable [IsArtinianRing R]

/-- Helper for Lemma 15.17.2: if the base change `R' ⊗[R] M` is flat over `R'`, then the kernel
quotient `M / ker(R → R')M` is flat over `R / ker(R → R')`. -/
lemma ker_isFlatQuotient_of_flat_tensorProduct
    (hflat : Module.Flat R' (R' ⊗[R] M)) :
    (RingHom.ker (algebraMap R R')).IsFlatQuotient M := by
  let J : Ideal R := RingHom.ker (algebraMap R R')
  let φ : R ⧸ J →ₐ[R] R' := kernel_quotient_alg_hom (R := R) (R' := R')
  letI : Algebra (R ⧸ J) R' := φ.toRingHom.toAlgebra
  have hinj :
      Function.Injective (algebraMap (R ⧸ J) R') := by
    -- The kernel quotient comparison map is injective by construction.
    change Function.Injective φ
    simpa [φ, J, kernel_quotient_alg_hom] using
      (Ideal.kerLiftAlg_injective (Algebra.ofId R R'))
  have hmap :
      J.map (algebraMap R R') = ⊥ := by
    exact (Ideal.map_eq_bot_iff_le_ker (f := algebraMap R R')).mpr le_rfl
  let eFactor :
      (R' ⊗[R ⧸ J] (M ⧸ (J • (⊤ : Submodule R M)))) ≃ₗ[R']
        (R' ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) :=
    factor_tensor_quotient_equiv_base_tensor_quotient
      (R := R) (M := M) (R' := R') (J := J)
  let eTensor :
      (R' ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) ≃ₗ[R'] (R' ⊗[R] M) :=
    base_tensor_quotient_equiv_tensor_of_map_eq_bot
      (R := R) (M := M) (R' := R') (J := J) hmap
  have hquot :
      Module.Flat R' (R' ⊗[R ⧸ J] (M ⧸ (J • (⊤ : Submodule R M)))) := by
    -- Transport the given flatness witness back to the source-side tensor presentation used in the
    -- Artinian descent theorem.
    let _ : Module.Flat R' (R' ⊗[R] M) := hflat
    exact Module.Flat.of_linearEquiv (eFactor.trans eTensor)
  -- Apply the Artinian descent theorem over the kernel quotient ring.
  simpa [J, Ideal.IsFlatQuotient] using
    (flat_of_isArtinianRing_of_injective_algebraMap_of_flat_tensorProduct
      (R := R ⧸ J) (S := R')
      (M := M ⧸ (J • (⊤ : Submodule R M))) hinj hquot)

/- Domain triage:
- primary domain: commutative algebra of Artinian flatness criteria under quotienting and base
  change;
- sampled owner declarations of the same kind:
  `Ideal.IsFlatQuotient`,
  `Module.Flat.baseChange`,
  `IsBaseChange.tensorEquiv`,
  `TensorProduct.tensorQuotMapSMulEquivTensorQuot`;
- best owner abstraction in this chapter: the source-facing ideal predicate `J.IsFlatQuotient M`,
  whose canonical core is `Module.Flat` on the quotient ring and quotient module;
- primitive data: the base ring `R`, the module `M`, the least ideal `I`, and the target
  `R`-algebra `R'`;
- derived API: the base-change flatness criterion characterized by vanishing of the image ideal.

Layering:
- `source-facing`: this theorem identifies when the least flat-quotient ideal becomes zero after
  base change;
- `core/canonical`: `Ideal.IsFlatQuotient`, `Module.Flat`, the quotient-base-change owner
  `IsBaseChange.tensorEquiv`, the packaged quotient/tensor comparison
  `TensorProduct.tensorQuotMapSMulEquivTensorQuot`, and the
  Chapter 10 Artinian descent theorem
  `flat_of_isArtinianRing_of_injective_algebraMap_of_flat_tensorProduct`;
- no separate `bridge/view` owner is introduced here.
-/

-- Proof sketch: the quotient map `M → M ⧸ (I • ⊤)` is the base change of `M` along
-- `R → R ⧸ I`, so after any further `R ⧸ I`-algebra base change, `IsBaseChange.tensorEquiv`
-- identifies `R' ⊗[R ⧸ I] (M ⧸ (I • ⊤))` with `R' ⊗[R] M`. If `I.map (algebraMap R R') = ⊥`,
-- endow `R'` with its induced `R ⧸ I`-algebra structure and base-change the flat quotient module
-- to conclude that `R' ⊗[R] M` is flat. Conversely, for `J = RingHom.ker (algebraMap R R')`, the
-- same base-change comparison identifies `R' ⊗[R ⧸ J] (M ⧸ (J • ⊤))` with `R' ⊗[R] M`; applying
-- `flat_of_isArtinianRing_of_injective_algebraMap_of_flat_tensorProduct` over `R ⧸ J` shows
-- `J.IsFlatQuotient M`, and the leastness of `I` then forces `I ≤ J`, equivalently
-- `I.map (algebraMap R R') = ⊥`.

/-- Lemma 15.17.2: if `I` is the smallest ideal such that `M / IM` is flat over `R ⧸ I`, then
for any `R`-algebra `R'`, the base change `R' ⊗[R] M` is flat over `R'` if and only if the image
of `I` in `R'` is zero. -/
theorem flat_baseChange_iff_map_eq_bot_of_isLeast_flat_quotient_ideal
    {I : Ideal R}
    (hI : IsLeast {J : Ideal R | J.IsFlatQuotient M} I) :
    Module.Flat R' (R' ⊗[R] M) ↔ I.map (algebraMap R R') = ⊥ := by
  constructor
  · intro hflat
    -- Descend the base-changed flatness to the kernel quotient, then use the leastness of `I`.
    have hker :
        (RingHom.ker (algebraMap R R')).IsFlatQuotient M :=
      ker_isFlatQuotient_of_flat_tensorProduct (R := R) (M := M) (R' := R') hflat
    have hle : I ≤ RingHom.ker (algebraMap R R') := hI.2 hker
    exact (Ideal.map_eq_bot_iff_le_ker (f := algebraMap R R')).mpr hle
  · intro hmap
    -- The least flat quotient ideal stays flat after any base change annihilating it.
    exact
      flat_tensorProduct_of_isFlatQuotient_of_map_eq_bot
        (R := R) (M := M) (R' := R') hI.1 hmap

end
