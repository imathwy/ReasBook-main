import StacksProject_2024.Chap10.Definition_10_43_1
import StacksProject_2024.Chap10.Lemma_10_43_5
import StacksProject_2024.Chap10.Lemma_10_43_6
import StacksProject_2024.Chap10.Lemma_10_43_8
import Mathlib.Tactic.StacksAttribute

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

omit [Algebra.IsSeparable k k'] in
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

omit [Algebra.IsSeparable k k'] in
/-- Helper for Lemma 10.43.9: the packaged diagonal multiplication sends the pure tensor
`1 ⊗ₜ y` to `y`. -/
@[simp] lemma diagonal_lmul_left_apply_one_tmul (y : k') :
    diagonal_lmul_leftAlgHom (1 ⊗ₜ[k] y) = y := by
  -- Proof comment: unwrap the packaged diagonal map and apply the standard pure-tensor formula
  -- for tensor-product multiplication.
  change (TensorProduct.lmul' k : TensorProduct k k' k' →ₐ[k] k') (1 ⊗ₜ[k] y) = y
  simp [TensorProduct.lmul'_apply_tmul]

omit [Algebra.IsSeparable k k'] in
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

/-- Helper for Lemma 10.43.9: transport a localization-map witness across source and target
ring equivalences. -/
lemma isLocalizationMap_transport_ringEquiv
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (M : Submonoid R) (f : R →+* S) (f' : R' →+* S')
    (eR : R ≃+* R') (eS : S ≃+* S')
    (hM : M.IsLocalizationMap f)
    (hf : f' = eS.toRingHom.comp (f.comp eR.symm.toRingHom)) :
    (M.comap eR.symm.toRingHom).IsLocalizationMap f' := by
  -- Proof comment: rewrite the target map to the transported composite, then move each
  -- localization-map axiom through the two equivalences.
  subst hf
  refine ⟨?_, ?_, ?_⟩
  · intro y
    have hy : IsUnit (f (eR.symm y.1)) := hM.map_units ⟨eR.symm y.1, y.2⟩
    simpa [RingHom.comp_apply] using hy.map eS.toRingHom
  · intro z'
    obtain ⟨⟨x, m⟩, hz⟩ := hM.surj (eS.symm z')
    refine ⟨⟨eR x, ⟨eR m.1, ?_⟩⟩, ?_⟩
    · simpa using m.2
    · calc
        z' * (eS.toRingHom.comp (f.comp eR.symm.toRingHom)) (eR m.1) =
            eS (eS.symm z' * f m.1) := by
          simp [RingHom.comp_apply]
        _ = (eS.toRingHom.comp (f.comp eR.symm.toRingHom)) (eR x) := by
          simp [RingHom.comp_apply, hz]
  · intro x' y' hxy
    have hbase : f (eR.symm x') = f (eR.symm y') := by
      apply eS.injective
      simpa [RingHom.comp_apply] using hxy
    obtain ⟨c, hc⟩ := hM.exists_of_eq hbase
    refine ⟨⟨eR c.1, ?_⟩, ?_⟩
    · simpa using c.2
    · apply eR.symm.injective
      simpa using hc

/-- Helper for Lemma 10.43.9: tensoring an algebra map on the right fixes the canonical right
tensor inclusion. -/
theorem tensorProduct_map_includeRight_comp {R Q B C : Type*} [CommSemiring R]
    [CommSemiring Q] [CommSemiring B] [CommSemiring C]
    [Algebra R Q] [Algebra R B] [Algebra R C] (φ : Q →ₐ[R] B) :
    ((Algebra.TensorProduct.map φ (AlgHom.id R C)).toRingHom).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
  ext x
  -- Proof comment: both composites send `x` to the pure tensor `1 ⊗ₜ x`.
  change Algebra.TensorProduct.map φ (AlgHom.id R C) (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] x
  simp

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

/-- Helper for Chap10 Lemma 10 43 9: the left tensor map induced by a tower
`R → Q → S` sends `Q ⊗[R] T` to `S ⊗[R] T`. -/
private abbrev towerTensorLeftMap
    {R Q S T : Type*} [CommSemiring R] [CommSemiring Q] [CommSemiring S]
    [CommSemiring T] [Algebra R Q] [Algebra R S] [Algebra Q S]
    [IsScalarTower R Q S] [Algebra R T] :
    TensorProduct R Q T →ₐ[R] TensorProduct R S T :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R Q S) (AlgHom.id R T)

/-- Helper for Chap10 Lemma 10 43 9: the left tensor map fixes the right tensor inclusion. -/
private lemma towerTensorLeftMap_includeRight_comp
    {R Q S T : Type*} [CommSemiring R] [CommSemiring Q] [CommSemiring S]
    [CommSemiring T] [Algebra R Q] [Algebra R S] [Algebra Q S]
    [IsScalarTower R Q S] [Algebra R T] :
    letI : Algebra (TensorProduct R Q T) (TensorProduct R S T) :=
      (towerTensorLeftMap (R := R) (Q := Q) (S := S) (T := T)).toAlgebra
    letI : SMul (TensorProduct R Q T) (TensorProduct R S T) := Algebra.toSMul
    (algebraMap (TensorProduct R Q T) (TensorProduct R S T)).comp
        (Algebra.TensorProduct.includeRight : T →ₐ[R] TensorProduct R Q T).toRingHom =
      (Algebra.TensorProduct.includeRight : T →ₐ[R] TensorProduct R S T).toRingHom := by
  let baseMap : TensorProduct R Q T →ₐ[R] TensorProduct R S T :=
    towerTensorLeftMap (R := R) (Q := Q) (S := S) (T := T)
  -- Proof comment: after installing the algebra from `baseMap`, both composites send `t`
  -- to the same pure tensor `1 ⊗ₜ t`.
  rw [RingHom.algebraMap_toAlgebra baseMap.toRingHom]
  ext t
  simpa [baseMap, towerTensorLeftMap, Algebra.TensorProduct.includeRight_apply] using
    (Algebra.TensorProduct.map_tmul
      (IsScalarTower.toAlgHom R Q S) (AlgHom.id R T) (1 : Q) t)

/-- Helper for Chap10 Lemma 10 43 9: the left tensor map gives the scalar tower
`Q → Q ⊗[R] T → S ⊗[R] T` in the `TensorProduct.leftHasSMul` spelling. -/
private lemma towerTensorLeftMap_scalarTower
    {R Q S T : Type*} [CommSemiring R] [CommSemiring Q] [CommSemiring S]
    [CommSemiring T] [Algebra R Q] [Algebra R S] [Algebra Q S]
    [IsScalarTower R Q S] [Algebra R T] :
    letI : Module Q S := Algebra.toModule
    letI : SMul Q (TensorProduct R S T) := TensorProduct.leftHasSMul
    letI : Algebra (TensorProduct R Q T) (TensorProduct R S T) :=
      (towerTensorLeftMap (R := R) (Q := Q) (S := S) (T := T)).toAlgebra
    letI : SMul (TensorProduct R Q T) (TensorProduct R S T) := Algebra.toSMul
    IsScalarTower Q (TensorProduct R Q T) (TensorProduct R S T) := by
  letI : Module Q S := Algebra.toModule
  let baseMap : TensorProduct R Q T →ₐ[R] TensorProduct R S T :=
    towerTensorLeftMap (R := R) (Q := Q) (S := S) (T := T)
  letI : SMul Q (TensorProduct R S T) := TensorProduct.leftHasSMul
  letI : Algebra (TensorProduct R Q T) (TensorProduct R S T) := baseMap.toAlgebra
  letI : SMul (TensorProduct R Q T) (TensorProduct R S T) := Algebra.toSMul
  -- Proof comment: scalar-tower compatibility is checked on the canonical image of `q` in
  -- the left tensor factor.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro q
  rw [RingHom.algebraMap_toAlgebra baseMap.toRingHom]
  rw [Algebra.TensorProduct.algebraMap_apply]
  rw [Algebra.TensorProduct.algebraMap_apply]
  rw [Algebra.algebraMap_self_apply]
  exact (Algebra.TensorProduct.map_tmul
    (IsScalarTower.toAlgHom R Q S) (AlgHom.id R T) q (1 : T)).symm

/-- Helper for Chap10 Lemma 10 43 9: tensoring a localization on the left remains a
localization after base change along the right tensor factor. -/
private lemma towerTensorLeftMap_isLocalization
    {R Q S T : Type*} [CommSemiring R] [CommSemiring Q] [CommRing S]
    [CommSemiring T] [Algebra R Q] [Algebra R S] [Algebra Q S]
    [IsScalarTower R Q S] [Algebra R T] (M : Submonoid Q) [IsLocalization M S] :
    letI : Module Q S := Algebra.toModule
    letI : SMul Q (TensorProduct R S T) := TensorProduct.leftHasSMul
    letI : Algebra (TensorProduct R Q T) (TensorProduct R S T) :=
      (towerTensorLeftMap (R := R) (Q := Q) (S := S) (T := T)).toAlgebra
    letI : SMul (TensorProduct R Q T) (TensorProduct R S T) := Algebra.toSMul
    letI : Module (TensorProduct R Q T) (TensorProduct R S T) := Algebra.toModule
    IsLocalization (Algebra.algebraMapSubmonoid (TensorProduct R Q T) M)
      (TensorProduct R S T) := by
  letI : Module Q S := Algebra.toModule
  letI : SMul Q (TensorProduct R S T) := TensorProduct.leftHasSMul
  letI : Algebra (TensorProduct R Q T) (TensorProduct R S T) :=
    (towerTensorLeftMap (R := R) (Q := Q) (S := S) (T := T)).toAlgebra
  letI : SMul (TensorProduct R Q T) (TensorProduct R S T) := Algebra.toSMul
  letI : Module (TensorProduct R Q T) (TensorProduct R S T) := Algebra.toModule
  have hTower : IsScalarTower Q (TensorProduct R Q T) (TensorProduct R S T) :=
    towerTensorLeftMap_scalarTower (R := R) (Q := Q) (S := S) (T := T)
  letI : IsScalarTower Q (TensorProduct R Q T) (TensorProduct R S T) := hTower
  have hRight :
      (algebraMap (TensorProduct R Q T) (TensorProduct R S T)).comp
          (Algebra.TensorProduct.includeRight : T →ₐ[R] TensorProduct R Q T).toRingHom =
        (Algebra.TensorProduct.includeRight : T →ₐ[R] TensorProduct R S T).toRingHom :=
    towerTensorLeftMap_includeRight_comp (R := R) (Q := Q) (S := S) (T := T)
  -- Proof comment: with the action spelling fixed, mathlib's tensor-product localization
  -- theorem applies directly.
  exact
    @IsLocalization.tensorProduct_tensorProduct R T _ _ _ Q _ _ M S
      _ _ _ _ _ _ hTower hRight

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

omit [Algebra.IsSeparable k k'] in
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

omit [Algebra.IsSeparable k k'] in
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
            Algebra.TensorProduct.productMap_apply_tmul, TensorProduct.lid_tmul,
            Algebra.smul_def, mul_comm]
  · intro z₁ z₂ hz₁ hz₂
    -- Proof comment: both sides are additive, so combine the induction hypotheses termwise.
    simpa [RingHom.comp_apply] using congrArg₂ HAdd.hAdd hz₁ hz₂

omit [Algebra.IsSeparable k k'] in
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
  letI : Algebra k' (TensorProduct k k' k') := Algebra.TensorProduct.leftAlgebra
  letI : Algebra (TensorProduct k k' k') k' := diagonal_lmul_leftAlgHom.toAlgebra
  have hM0Alg :
      M0.IsLocalizationMap (algebraMap (TensorProduct k k' k') k') :=
    diagonal_lmul_left_isLocalizationMap_toAlgebra (k := k) (k' := k') M0 hM0
  letI : IsLocalization M0 k' :=
    (isLocalization_iff_isLocalizationMap M0 k').mpr hM0Alg
  let baseMap :
      TensorProduct k' (TensorProduct k k' k') K →ₐ[k'] TensorProduct k' k' K :=
    towerTensorLeftMap (R := k') (Q := TensorProduct k k' k') (S := k') (T := K)
  letI : Module (TensorProduct k k' k') k' := Algebra.toModule
  letI : SMul (TensorProduct k k' k') (TensorProduct k' k' K) :=
    TensorProduct.leftHasSMul
  letI : Algebra (TensorProduct k' (TensorProduct k k' k') K) (TensorProduct k' k' K) :=
    baseMap.toAlgebra
  letI : SMul (TensorProduct k' (TensorProduct k k' k') K) (TensorProduct k' k' K) :=
    Algebra.toSMul
  letI : Module (TensorProduct k' (TensorProduct k k' k') K) (TensorProduct k' k' K) :=
    Algebra.toModule
  letI :
      IsLocalization
        (Algebra.algebraMapSubmonoid (TensorProduct k' (TensorProduct k k' k') K) M0)
        (TensorProduct k' k' K) :=
    towerTensorLeftMap_isLocalization
      (R := k') (Q := TensorProduct k k' k') (S := k') (T := K) M0
  have hTensorMap :
      Submonoid.IsLocalizationMap
        (Algebra.algebraMapSubmonoid (TensorProduct k' (TensorProduct k k' k') K) M0)
        (algebraMap (TensorProduct k' (TensorProduct k k' k') K)
          (TensorProduct k' k' K)) :=
    (isLocalization_iff_isLocalizationMap
      (Algebra.algebraMapSubmonoid (TensorProduct k' (TensorProduct k k' k') K) M0)
      (TensorProduct k' k' K)).mp inferInstance
  let eR :=
    (diagonal_tensor_source_algEquiv_to_baseChangeRight
      (k := k) (k' := k') (K := K)).toRingEquiv
  let eS := (TensorProduct.lid k' K).toRingEquiv
  have hMap :
      (productMap_rightAlgHom (k := k) (k' := k') (K := K)).toRingHom =
        eS.toRingHom.comp
          ((algebraMap (TensorProduct k' (TensorProduct k k' k') K)
              (TensorProduct k' k' K)).comp eR.symm.toRingHom) := by
    -- Proof comment: the transported tensor-left algebra map is exactly the product map by the
    -- pure-tensor computation recorded in `transported_diagonal_tensor_map_eq_productMap`.
    rw [RingHom.algebraMap_toAlgebra baseMap.toRingHom]
    simpa [eR, eS, baseMap, towerTensorLeftMap, diagonal_tensor_source_to_lidAlgHom,
      RingHom.comp_assoc] using
      (transported_diagonal_tensor_map_eq_productMap
        (k := k) (k' := k') (K := K)).symm
  -- Proof comment: transport the tensor-localization witness from the diagonal source to the
  -- standard source and target of `productMap_rightAlgHom`.
  simpa [eR] using
    isLocalizationMap_transport_ringEquiv
      (M := Algebra.algebraMapSubmonoid (TensorProduct k' (TensorProduct k k' k') K) M0)
      (f := algebraMap (TensorProduct k' (TensorProduct k k' k') K) (TensorProduct k' k' K))
      (f' := (productMap_rightAlgHom (k := k) (k' := k') (K := K)).toRingHom)
      eR eS hTensorMap hMap

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
    {K : Type u} [Field K] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K]
    (hKA : IsReduced (TensorProduct k K A)) :
    IsReduced (TensorProduct k' K A) := by
  -- Proof comment: the intended route is the source proof verbatim: use Lemma `10.43.8` to
  -- present `K` as a localization of `K ⊗[k] k'`, tensor that localization on the right by `A`,
  -- and transport the resulting reduced localization back to `K ⊗[k'] A`.
  obtain ⟨M, hM⟩ :=
    exists_submonoid_tensorProduct_right_isLocalization (k := k) (k' := k') (K := K)
  letI : Algebra k' (TensorProduct k K k') := Algebra.TensorProduct.rightAlgebra
  letI : Module k' (TensorProduct k K k') := Algebra.toModule
  letI : SMul k' (TensorProduct k K k') := Algebra.toSMul
  let productMapRing : TensorProduct k K k' →+* K :=
    (Algebra.TensorProduct.productMap
      (AlgHom.id k K) (IsScalarTower.toAlgHom k k' K)).toRingHom
  letI : Algebra (TensorProduct k K k') K := productMapRing.toAlgebra
  have hTowerQ : IsScalarTower k' (TensorProduct k K k') K := by
    -- Proof comment: with the right-factor `k'`-algebra on `K ⊗[k] k'`, the product map sends
    -- the right tensor inclusion to the ambient `k' → K` algebra map.
    refine
      @IsScalarTower.of_algebraMap_eq k' (TensorProduct k K k') K
        _ _ _ _ _ _ ?_
    intro x
    rw [RingHom.algebraMap_toAlgebra productMapRing]
    change (algebraMap k' K) x =
      productMapRing ((Algebra.TensorProduct.includeRight : k' →ₐ[k] TensorProduct k K k') x)
    exact congr($(Algebra.TensorProduct.productMap_right
      (f := AlgHom.id k K) (g := IsScalarTower.toAlgHom k k' K)) x).symm
  letI : IsScalarTower k' (TensorProduct k K k') K := hTowerQ
  have hMAlg : M.IsLocalizationMap (algebraMap (TensorProduct k K k') K) := by
    -- Proof comment: the localization map from the existential statement is the same ring map
    -- as the ambient algebra map after installing the product-map ring hom as the algebra map.
    simpa [productMapRing, RingHom.algebraMap_toAlgebra] using hM
  letI : IsLocalization M K := (isLocalization_iff_isLocalizationMap M K).mpr hMAlg
  let baseMap : TensorProduct k' (TensorProduct k K k') A →ₐ[k'] TensorProduct k' K A :=
    towerTensorLeftMap (R := k') (Q := TensorProduct k K k') (S := K) (T := A)
  letI : Module (TensorProduct k K k') K := Algebra.toModule
  letI : SMul (TensorProduct k K k') (TensorProduct k' K A) :=
    TensorProduct.leftHasSMul
  letI : Algebra (TensorProduct k' (TensorProduct k K k') A) (TensorProduct k' K A) :=
    baseMap.toAlgebra
  letI : SMul (TensorProduct k' (TensorProduct k K k') A) (TensorProduct k' K A) :=
    Algebra.toSMul
  letI : Module (TensorProduct k' (TensorProduct k K k') A) (TensorProduct k' K A) :=
    Algebra.toModule
  letI :
      IsLocalization
        (Algebra.algebraMapSubmonoid (TensorProduct k' (TensorProduct k K k') A) M)
        (TensorProduct k' K A) :=
    towerTensorLeftMap_isLocalization
      (R := k') (Q := TensorProduct k K k') (S := K) (T := A) M
  have hSource : IsReduced (TensorProduct k' (TensorProduct k K k') A) := by
    let e : TensorProduct k' (TensorProduct k K k') A ≃+* TensorProduct k K A :=
      tensor_base_change_assoc_equiv (k := k) (k' := k') (K := K) (B := A)
    -- Proof comment: the associativity comparison imports reducedness from the original
    -- `k`-base change to the source of the tensor-localization.
    letI : IsReduced (TensorProduct k K A) := hKA
    exact isReduced_of_injective e.toRingHom e.injective
  letI : IsReduced (TensorProduct k' (TensorProduct k K k') A) := hSource
  -- Proof comment: reducedness is preserved by the localization obtained by tensoring
  -- `K` over `K ⊗[k] k'` with `A`.
  exact
    isReduced_localizationPreserves
      (Algebra.algebraMapSubmonoid (TensorProduct k' (TensorProduct k K k') A) M)
      (TensorProduct k' K A) hSource

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
/-- Chap10 Lemma 10 43 9 (Tag 0C2Y): for a separable algebraic field extension `k' / k`, a
`k'`-algebra `A` is geometrically reduced over `k` if and only if it is geometrically reduced over
`k'`. -/
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
