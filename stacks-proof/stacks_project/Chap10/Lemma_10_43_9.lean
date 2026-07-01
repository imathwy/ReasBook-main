import stacks_project.Chap10.Definition_10_43_1
import stacks_project.Chap10.Lemma_10_43_5
import stacks_project.Chap10.Lemma_10_43_6
import stacks_project.Chap10.Lemma_10_43_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u w

namespace Algebra

section

open scoped TensorProduct
open Algebra.TensorProduct

variable {k k' : Type u} {A : Type w}
variable [Field k] [Field k'] [CommRing A]
variable [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
variable [Algebra.IsSeparable k k']

/-- Helper for Lemma 10.43.9: first commute the outer `k'`-tensor so the eventual
`cancelBaseChange` sees the duplicated base field on the right. -/
noncomputable def tensor_base_change_assoc_equiv_comm
    {K B : Type*} [Field K] [CommRing B] [Algebra k K] [Algebra k' B] [Algebra k B]
    [IsScalarTower k k' B] :
    let _ : Algebra k' (TensorProduct k K k') := Algebra.TensorProduct.rightAlgebra
    TensorProduct k' (TensorProduct k K k') B ≃ₐ[k'] TensorProduct k' B (TensorProduct k K k') :=
  -- Proof comment: this is the source proof's first tensor-order swap.
  let _ : Algebra k' (TensorProduct k K k') := Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.comm k' (TensorProduct k K k') B

/-- Helper for Lemma 10.43.9: after the outer commutation, rewrite the right factor into the
Stacks order `k' ⊗[k] K`. -/
noncomputable def tensor_base_change_assoc_equiv_reorder
    {K B : Type*} [Field K] [CommRing B] [Algebra k K] [Algebra k' B] [Algebra k B]
    [IsScalarTower k k' B] :
    let _ : Algebra k' (TensorProduct k K k') := Algebra.TensorProduct.rightAlgebra
    TensorProduct k' B (TensorProduct k K k') ≃ₐ[k'] TensorProduct k' B (TensorProduct k k' K) :=
  -- Proof comment: freeze the canonical right-factor `k'`-algebra and then apply the standard
  -- `commRight` comparison on that factor only.
  let _ : Algebra k' (TensorProduct k K k') := Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.congr
    (AlgEquiv.refl : B ≃ₐ[k'] B)
    ((Algebra.TensorProduct.commRight k k' K).symm)

/-- Helper for Lemma 10.43.9: once the duplicated base field sits on the right, the standard
`cancelBaseChange` removes it. -/
noncomputable def tensor_base_change_assoc_equiv_cancel
    {K B : Type*} [Field K] [CommRing B] [Algebra k K] [Algebra k' B] [Algebra k B]
    [IsScalarTower k k' B] :
    TensorProduct k' B (TensorProduct k k' K) ≃ₐ[k'] TensorProduct k B K :=
  -- Proof comment: this is the canonical base-change cancellation used in the source proof.
  Algebra.TensorProduct.cancelBaseChange k k' k' B K

/-- Helper for Lemma 10.43.9: the source proof identifies the iterated tensor product
`(K ⊗[k] k') ⊗[k'] A` with the direct base change `K ⊗[k] A`. -/
noncomputable def tensor_base_change_assoc_equiv
    {K B : Type*} [Field K] [CommRing B] [Algebra k K] [Algebra k' B] [Algebra k B]
    [IsScalarTower k k' B] :
    let _ : Algebra k' (TensorProduct k K k') := Algebra.TensorProduct.rightAlgebra
    TensorProduct k' (TensorProduct k K k') B ≃+* TensorProduct k K B :=
  -- Proof comment: follow the Stacks route verbatim: outer commutation, reorder the repeated
  -- base-change factor, cancel the duplicated `k'`, and then swap the remaining tensor factors.
  let _ : Algebra k' (TensorProduct k K k') := Algebra.TensorProduct.rightAlgebra
  (((tensor_base_change_assoc_equiv_comm (k := k) (k' := k') (K := K) (B := B)).trans
      (tensor_base_change_assoc_equiv_reorder (k := k) (k' := k') (K := K) (B := B))).trans
      (tensor_base_change_assoc_equiv_cancel (k := k) (k' := k') (K := K) (B := B))).toRingEquiv.trans
    (Algebra.TensorProduct.comm k B K).toRingEquiv

/-- Helper for Lemma 10.43.9: diagonal multiplication on `k' ⊗[k] k'` is compatible with the
left-factor `k'`-algebra structure. -/
lemma diagonal_lmul_left_commutes (x : k') :
    (TensorProduct.lmul' k : TensorProduct k k' k' →ₐ[k] k')
        (algebraMap k' (TensorProduct k k' k') x) =
      algebraMap k' k' x := by
  -- Proof comment: rewrite the scalar action through the left tensor inclusion and then apply the
  -- standard computation rule for tensor-product multiplication.
  change ((TensorProduct.lmul' k).comp Algebra.TensorProduct.includeLeft) x = x
  simpa using congr($(TensorProduct.lmul'_comp_includeLeft (R := k) (S := k')) x)

/-- Helper for Lemma 10.43.9: the diagonal multiplication map packaged as a `k'`-algebra map for
the left-factor `k'`-algebra structure on `k' ⊗[k] k'`. -/
noncomputable def diagonal_lmul_leftAlgHom :
    TensorProduct k k' k' →ₐ[k'] k' :=
  { __ := (TensorProduct.lmul' k : TensorProduct k k' k' →ₐ[k] k').toRingHom
    commutes' := diagonal_lmul_left_commutes (k := k) (k' := k') }

/-- Helper for Lemma 10.43.9: the packaged diagonal multiplication sends the pure tensor
`1 ⊗ₜ y` to `y`. -/
@[simp] lemma diagonal_lmul_left_apply_one_tmul (y : k') :
    diagonal_lmul_leftAlgHom (1 ⊗ₜ[k] y) = y := by
  -- Proof comment: unwrap the packaged diagonal map and apply the standard pure-tensor formula
  -- for tensor-product multiplication.
  change (TensorProduct.lmul' k : TensorProduct k k' k' →ₐ[k] k') (1 ⊗ₜ[k] y) = y
  simp [TensorProduct.lmul'_apply_tmul]

/-- Helper for Lemma 10.43.9: the localization witness of Lemma `10.43.8` is unchanged after
repackaging diagonal multiplication as the ambient `algebraMap`. -/
lemma diagonal_lmul_left_isLocalizationMap_toAlgebra
    (M : Submonoid (TensorProduct k k' k'))
    (hM : M.IsLocalizationMap (TensorProduct.lmul' k)) :
    letI : Algebra (TensorProduct k k' k') k' := diagonal_lmul_leftAlgHom.toAlgebra
    M.IsLocalizationMap (algebraMap (TensorProduct k k' k') k') := by
  letI : Algebra (TensorProduct k k' k') k' := diagonal_lmul_leftAlgHom.toAlgebra
  -- Proof comment: `toAlgebra` keeps the same underlying ring map, so the localization witness
  -- is literally the same after rewriting the target map as `algebraMap`.
  simpa [diagonal_lmul_leftAlgHom, RingHom.algebraMap_toAlgebra] using hM

/-- Helper for Lemma 10.43.9: the source ring from the right-tensored diagonal localization
identifies with the standard tensor product `K ⊗[k] k'`. -/
noncomputable def diagonal_tensor_source_algEquiv_to_baseChangeRight
    {K : Type*} [Field K] [Algebra k' K] [Algebra k K] [IsScalarTower k k' K] :
    let _ : Algebra k' (TensorProduct k k' k') := Algebra.TensorProduct.leftAlgebra
    TensorProduct k' (TensorProduct k k' k') K ≃ₐ[k'] TensorProduct k K k' :=
  -- Proof comment: the source proof uses exactly the outer `comm` followed by the standard
  -- `cancelBaseChange` with the left-factor `k'`-algebra on `k' ⊗[k] k'`.
  let _ : Algebra k' (TensorProduct k k' k') := Algebra.TensorProduct.leftAlgebra
  (Algebra.TensorProduct.comm k' (TensorProduct k k' k') K).trans
    (Algebra.TensorProduct.cancelBaseChange k k' k' K k')

/-- Helper for Lemma 10.43.9: tensoring a `k'`-algebra map on the right by `A` fixes the
canonical right tensor inclusion. -/
theorem tensor_right_map_includeRight_comp_local {Q : Type*} [CommRing Q]
    [Algebra k' Q] (φ : Q →ₐ[k'] A) :
    ((Algebra.TensorProduct.map φ (AlgHom.id k' A)).toRingHom).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
  ext x
  -- Proof comment: both composites send `x` to the pure tensor `1 ⊗ₜ x`.
  change Algebra.TensorProduct.map φ (AlgHom.id k' A) (1 ⊗ₜ[k'] x) = 1 ⊗ₜ[k'] x
  simp

/-- Helper for Lemma 10.43.9: after tensoring the diagonal multiplication on the right by `K`,
the target is collapsed to `K` through the left-unital tensor equivalence. -/
noncomputable def diagonal_tensor_source_to_lidAlgHom
    {K : Type*} [Field K] [Algebra k' K] [Algebra k K] [IsScalarTower k k' K] :
    TensorProduct k' (TensorProduct k k' k') K →ₐ[k'] K :=
  (TensorProduct.lid k' K).toAlgHom.comp
    (Algebra.TensorProduct.map diagonal_lmul_leftAlgHom (AlgHom.id k' K))

/-- Helper for Lemma 10.43.9: the standard map `K ⊗[k] k' → K` is a `k'`-algebra map for the
right-factor `k'`-algebra structure on the tensor product. -/
noncomputable def productMap_rightAlgHom
    {K : Type*} [Field K] [Algebra k' K] [Algebra k K] [IsScalarTower k k' K] :
    TensorProduct k K k' →ₐ[k'] K :=
  { __ := (Algebra.TensorProduct.productMap
      (AlgHom.id k K) (IsScalarTower.toAlgHom k k' K)).toRingHom
    commutes' := fun x ↦ by
      -- Proof comment: the right tensor inclusion is exactly the ambient `k'`-algebra map.
      simpa [RingHom.algebraMap_toAlgebra] using
        congr($(Algebra.TensorProduct.productMap_right
          (f := AlgHom.id k K) (g := IsScalarTower.toAlgHom k k' K)) x) }

/-- Helper for Lemma 10.43.9: under the source comparison equivalence, a pure tensor
`x ⊗ₜ y : K ⊗[k] k'` comes from the Stacks-style source tensor `(1 ⊗ₜ y) ⊗ₜ x`. -/
@[simp] lemma diagonal_tensor_source_algEquiv_to_baseChangeRight_symm_tmul
    {K : Type*} [Field K] [Algebra k' K] [Algebra k K] [IsScalarTower k k' K]
    (x : K) (y : k') :
    (diagonal_tensor_source_algEquiv_to_baseChangeRight
      (k := k) (k' := k') (K := K)).symm (x ⊗ₜ[k] y) =
      (1 ⊗ₜ[k] y) ⊗ₜ[k'] x := by
  -- Proof comment: unwind the comparison as the inverse of base-change cancellation followed by
  -- the inverse tensor commutor.
  simp [diagonal_tensor_source_algEquiv_to_baseChangeRight]

/-- Helper for Lemma 10.43.9: transporting the right-tensored diagonal multiplication from the
Stacks-style source identifies it with the standard map `K ⊗[k] k' → K`. -/
lemma transported_diagonal_tensor_map_eq_productMap
    {K : Type*} [Field K] [Algebra k' K] [Algebra k K] [IsScalarTower k k' K] :
    ((diagonal_tensor_source_to_lidAlgHom (k := k) (k' := k') (K := K)).toRingHom).comp
        ((diagonal_tensor_source_algEquiv_to_baseChangeRight
          (k := k) (k' := k') (K := K)).symm.toRingHom) =
      (productMap_rightAlgHom (k := k) (k' := k') (K := K)).toRingHom := by
  -- Proof comment: evaluate both maps on a pure tensor and simplify the transported diagonal map
  -- using the explicit inverse formula proved just above.
  refine RingHom.ext fun z ↦ ?_
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    -- Proof comment: on pure tensors, the source comparison sends `x ⊗ₜ y` to
    -- `(1 ⊗ₜ y) ⊗ₜ x`, after which the packaged diagonal multiplication and `TensorProduct.lid`
    -- reduce the left side to the standard product map formula.
    calc
      ((diagonal_tensor_source_to_lidAlgHom (k := k) (k' := k') (K := K)).toRingHom).comp
          ((diagonal_tensor_source_algEquiv_to_baseChangeRight
            (k := k) (k' := k') (K := K)).symm.toRingHom) (x ⊗ₜ[k] y) =
        diagonal_tensor_source_to_lidAlgHom (k := k) (k' := k') (K := K)
          ((1 ⊗ₜ[k] y) ⊗ₜ[k'] x) := by
            change diagonal_tensor_source_to_lidAlgHom (k := k) (k' := k') (K := K)
                (((diagonal_tensor_source_algEquiv_to_baseChangeRight
                  (k := k) (k' := k') (K := K)).symm) (x ⊗ₜ[k] y)) =
              diagonal_tensor_source_to_lidAlgHom (k := k) (k' := k') (K := K)
                ((1 ⊗ₜ[k] y) ⊗ₜ[k'] x)
            exact congrArg
              (diagonal_tensor_source_to_lidAlgHom (k := k) (k' := k') (K := K))
              (diagonal_tensor_source_algEquiv_to_baseChangeRight_symm_tmul
                (k := k) (k' := k') (K := K) x y)
      _ =
        (productMap_rightAlgHom (k := k) (k' := k') (K := K)).toRingHom (x ⊗ₜ[k] y) := by
          simp [diagonal_tensor_source_to_lidAlgHom, productMap_rightAlgHom,
      Algebra.TensorProduct.productMap_apply_tmul, TensorProduct.lid_tmul]
          rw [Algebra.smul_def, mul_comm]
  · intro z₁ z₂ hz₁ hz₂
    -- Proof comment: both sides are additive, so combine the induction hypotheses termwise.
    simpa [RingHom.comp_apply] using congrArg₂ HAdd.hAdd hz₁ hz₂

/-- Helper for Lemma 10.43.9: a localization witness for the diagonal map
`k' ⊗[k] k' → k'` transports to a localization witness for
`K ⊗[k] k' → K` along the source comparison and the right tensor by `K`. -/
lemma productMap_right_isLocalization_of_diagonal
    {K : Type*} [Field K] [Algebra k' K] [Algebra k K] [IsScalarTower k k' K]
    (M0 : Submonoid (TensorProduct k k' k'))
    (hM0 : M0.IsLocalizationMap (TensorProduct.lmul' k)) :
    let e := diagonal_tensor_source_algEquiv_to_baseChangeRight (k := k) (k' := k') (K := K)
    let M : Submonoid (TensorProduct k K k') :=
      (Algebra.algebraMapSubmonoid (TensorProduct k' (TensorProduct k k' k') K) M0).comap
        e.symm.toRingHom
    M.IsLocalizationMap ((productMap_rightAlgHom (k := k) (k' := k') (K := K)).toRingHom) := by
  -- Route correction: the remaining source-faithful blocker is exactly the two-step transport of
  -- Lemma `10.43.8`: tensor the diagonal localization on the right by `K`, then transport the
  -- target through `TensorProduct.lid` and the source through
  -- `diagonal_tensor_source_algEquiv_to_baseChangeRight`.
  -- TODO: first rewrite `hM0` as an `IsLocalization` witness for the packaged diagonal algebra map
  -- via `diagonal_lmul_left_isLocalizationMap_toAlgebra`, tensor that localization on the right by
  -- `K` using `isLocalization_tensor_right_of_isLocalization` and
  -- `tensor_right_map_includeRight_comp_local`, transport the target along `TensorProduct.lid`,
  -- and finally transport the source along
  -- `diagonal_tensor_source_algEquiv_to_baseChangeRight` using
  -- `transported_diagonal_tensor_map_eq_productMap`.
  sorry

/-- Helper for Lemma 10.43.9: the right-tensored diagonal localization from Lemma `10.43.8`
transports to a localization presentation of `K` over `K ⊗[k] k'`. -/
lemma exists_submonoid_tensorProduct_right_isLocalization
    {K : Type*} [Field K] [Algebra k' K] [Algebra k K] [IsScalarTower k k' K] :
    ∃ M : Submonoid (TensorProduct k K k'),
      M.IsLocalizationMap
        (Algebra.TensorProduct.productMap
          (AlgHom.id k K) (IsScalarTower.toAlgHom k k' K)).toRingHom := by
  obtain ⟨M0, hM0⟩ := exists_submonoid_tensorProduct_self_isLocalization (k := k) (K := k')
  let e := diagonal_tensor_source_algEquiv_to_baseChangeRight (k := k) (k' := k') (K := K)
  let M : Submonoid (TensorProduct k K k') :=
    (Algebra.algebraMapSubmonoid (TensorProduct k' (TensorProduct k k' k') K) M0).comap
      e.symm.toRingHom
  -- Proof comment: once the transported localization theorem is packaged for a fixed witness,
  -- the existential Stacks statement is obtained by instantiating it with Lemma `10.43.8`.
  refine ⟨M, ?_⟩
  simpa [M, e, productMap_rightAlgHom] using
    (productMap_right_isLocalization_of_diagonal
      (k := k) (k' := k') (K := K) M0 hM0)

/-- Helper for Lemma 10.43.9: after rewriting `K ⊗[k] A` as
`(K ⊗[k] k') ⊗[k'] A`, the diagonal-localization theorem of Lemma `10.43.8` should descend
reducedness from the `k`-base change to the `k'`-base change. -/
lemma isReduced_tensorProduct_over_extension_of_isReduced_baseChange
    {K : Type*} [Field K] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K]
    (hKA : IsReduced (TensorProduct k K A)) :
    IsReduced (TensorProduct k' K A) := by
  -- Proof comment: the intended route is the source proof verbatim: use Lemma `10.43.8` to
  -- present `K` as a localization of `K ⊗[k] k'`, tensor that localization on the right by `A`,
  -- and transport the resulting reduced localization back to `K ⊗[k'] A`.
  -- TODO: rewrite `K ⊗[k] A` as `((K ⊗[k] k') ⊗[k'] A)`, tensor the localization witness from
  -- `exists_submonoid_tensorProduct_right_isLocalization` on the right by `A`, and conclude with
  -- `isReduced_localizationPreserves`.
  sorry

/- Domain triage:
- `source-facing`: invariance of geometric reducedness under a separable algebraic change of the
  ground field.
- `core/canonical`: the owner abstraction is `Algebra.IsGeometricallyReduced`.
- `bridge/view`: Definition `10.43.1` provides the owner-level reformulation in terms of reduced
  tensor products, and Lemma `10.43.6` supplies the separable-algebraic reducedness input used in
  the proof.

Primitive data are the field-extension hypotheses and the ambient `k'`-algebra `A`; geometric
reducedness itself stays in the owner class rather than being repackaged by a local wrapper.
-/
/-- Lemma 10.43.9 (Tag 0C2Y): for a separable algebraic field extension `k' / k`, a `k'`-algebra
`A` is geometrically reduced over `k` if and only if it is geometrically reduced over `k'`. -/
@[stacks 0C2Y]
theorem isGeometricallyReduced_iff_of_isSeparable :
    IsGeometricallyReduced k A ↔ IsGeometricallyReduced k' A := by
  constructor
  · intro h
    rw [isGeometricallyReduced_iff_forall_isReduced_tensorProduct] at h
    rw [isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
    intro K _ _
    letI : Algebra k K := RingHom.toAlgebra ((algebraMap k' K).comp (algebraMap k k'))
    letI : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq' rfl
    -- Proof comment: first use the `k`-geometric hypothesis to control `K ⊗[k] A`.
    exact
      isReduced_tensorProduct_over_extension_of_isReduced_baseChange
        (k := k) (k' := k') (h K)
  · intro h
    rw [isGeometricallyReduced_iff_forall_isReduced_tensorProduct] at h
    rw [isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
    intro K _ _
    letI : Algebra k' (TensorProduct k K k') :=
      (Algebra.TensorProduct.includeRight : k' →ₐ[k] TensorProduct k K k').toAlgebra
    have hKk' : IsReduced (TensorProduct k K k') := by
      let e : TensorProduct k k' K ≃ₐ[k] TensorProduct k K k' :=
        Algebra.TensorProduct.comm k k' K
      letI : IsReduced (TensorProduct k k' K) :=
        Lemma_10_43_6 (k := k) (K := k') (S := K)
      -- Proof comment: Lemma `10.43.6` gives reducedness in the opposite tensor order, so commute.
      exact isReduced_of_injective e.symm.toRingHom e.symm.injective
    letI : IsReduced (TensorProduct k K k') := hKk'
    have hiter : IsReduced (TensorProduct k' (TensorProduct k K k') A) := by
      have hgeom : IsGeometricallyReduced k' A := by
        exact isGeometricallyReduced_iff_forall_isReduced_tensorProduct.mpr h
      letI : IsGeometricallyReduced k' A := hgeom
      -- Proof comment: now apply Lemma `10.43.5` over the intermediate base field `k'`.
      exact
        isReduced_tensorProduct_of_geometricallyReduced
          (k := k') (R := TensorProduct k K k') (S := A)
    let e : TensorProduct k' (TensorProduct k K k') A ≃+* TensorProduct k K A :=
      tensor_base_change_assoc_equiv (k := k) (k' := k') (K := K) (B := A)
    -- Proof comment: finally transport reducedness across the canonical tensor comparison.
    exact isReduced_of_injective e.symm.toMonoidWithZeroHom e.symm.injective

end

end Algebra
