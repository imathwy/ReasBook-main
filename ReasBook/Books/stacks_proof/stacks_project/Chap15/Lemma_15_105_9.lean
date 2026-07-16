import stacks_proof.stacks_project.Chap10.Lemma_10_39_4
import stacks_proof.stacks_project.Chap10.Lemma_10_39_7
import stacks_proof.stacks_project.Chap15.Definition_15_105_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace Algebra

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

attribute [local instance] TensorProduct.rightAlgebra

/- Domain triage:
- primary domain: commutative algebra of weakly étale ring maps and tensor-square multiplication
  under composition;
- source-facing layer: part `(1)` is the tensor-square flatness statement for the composite;
- core/canonical owners sampled for this file:
  `Algebra.IsWeaklyEtale`,
  `Module.Flat.trans`,
  and `RingHom.Flat.comp`;
- primitive data: the two flat tensor-square multiplication maps, together with the owner facts on
  `A → B` and `B → C` for the composition theorem in part `(2)`;
- derived API: the source-facing tensor-square flatness theorem `tensorSquareMul_flat_comp`;
- bridge/view: there is no separate upstream ring-map owner in this environment, so part `(2)` is
  the owner theorem `Algebra.IsWeaklyEtale.comp` itself.
-/

-- Proof sketch: factor `C ⊗[A] C → C` through the base change of `B ⊗[A] B → B` along
-- `B ⊗[A] B → C ⊗[A] C`, identify the intermediate map with `C ⊗[B] C → C`, and apply flat base
-- change together with stability of flat ring maps under composition.
/-- Helper for Lemma 15.105.9: the two structure maps `B → C` induce the comparison map
`B ⊗[A] B → C ⊗[A] C`. -/
noncomputable abbrev tensor_square_map_to_composite :
    B ⊗[A] B →ₐ[A] C ⊗[A] C :=
  productMap
    (((includeLeft : C →ₐ[A] C ⊗[A] C).restrictScalars A).comp (IsScalarTower.toAlgHom A B C))
    (((includeRight : C →ₐ[A] C ⊗[A] C).restrictScalars A).comp (IsScalarTower.toAlgHom A B C))

/-- Helper for Lemma 15.105.9: the two copies of `C` in `C ⊗[B] C` induce the canonical map
`C ⊗[A] C → C ⊗[B] C`. -/
noncomputable abbrev composite_tensor_to_relativeTensor :
    C ⊗[A] C →ₐ[A] C ⊗[B] C :=
  productMap
    ((includeLeft : C →ₐ[B] C ⊗[B] C).restrictScalars A)
    ((includeRight : C →ₐ[B] C ⊗[B] C).restrictScalars A)

/-- Helper for Lemma 15.105.9: the left `B`-algebra structure on `C ⊗[B] C`, viewed over `A`. -/
noncomputable abbrev left_tensorFactor_to_relativeTensor :
    B →ₐ[A] C ⊗[B] C :=
  ((includeLeft : C →ₐ[B] C ⊗[B] C).restrictScalars A).comp
    (IsScalarTower.toAlgHom A B C)

/-- Helper for Lemma 15.105.9: the right `B`-algebra structure on `C ⊗[B] C`, viewed over `A`. -/
noncomputable abbrev right_tensorFactor_to_relativeTensor :
    B →ₐ[A] C ⊗[B] C :=
  ((includeRight : C →ₐ[B] C ⊗[B] C).restrictScalars A).comp
    (IsScalarTower.toAlgHom A B C)

/-- Helper for Lemma 15.105.9: the canonical map `B ⊗[A] B → C ⊗[A] B` using the left structure
map `B → C` and the unchanged right `B`-factor. -/
noncomputable abbrev tensor_rightFactor_map_to_baseChange :
    B ⊗[A] B →ₐ[A] C ⊗[A] B :=
  productMap
    (((includeLeft : C →ₐ[A] C ⊗[A] B).restrictScalars A).comp (IsScalarTower.toAlgHom A B C))
    (includeRight : B →ₐ[A] C ⊗[A] B)

/-- Helper for Lemma 15.105.9: after passing from `C ⊗[A] C` to `C ⊗[B] C`, the tensor-square
comparison map from `B ⊗[A] B` agrees with the left `B`-action coming from multiplication
`B ⊗[A] B → B`. -/
theorem composite_tensor_to_relativeTensor_comp_tensor_square_map :
    (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom.comp
        (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toRingHom =
      ((left_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
        (lmul' A)).toRingHom := by
  -- Reduce the comparison of ring maps to pure tensors in `B ⊗[A] B`.
  apply RingHom.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Both maps are additive and preserve zero.
    simp
  · intro b₁ b₂
    -- On pure tensors, the relative tensor relation rewrites `b₁ ⊗ b₂` as `(b₁ b₂) ⊗ 1`.
    simp [tensor_square_map_to_composite, composite_tensor_to_relativeTensor,
      left_tensorFactor_to_relativeTensor, Algebra.TensorProduct.productMap_apply_tmul]
  · intro x y hx hy
    -- Additivity reduces the remaining case to the induction hypotheses.
    calc
      composite_tensor_to_relativeTensor (tensor_square_map_to_composite (x + y))
          = composite_tensor_to_relativeTensor (tensor_square_map_to_composite x) +
              composite_tensor_to_relativeTensor (tensor_square_map_to_composite y) := by
            simp
      _ = (((algebraMap B C) ((lmul' A) x)) ⊗ₜ[B] (1 : C)) +
            (((algebraMap B C) ((lmul' A) y)) ⊗ₜ[B] (1 : C)) := by
            have hx' :
                composite_tensor_to_relativeTensor (tensor_square_map_to_composite x) =
                  (((algebraMap B C) ((lmul' A) x)) ⊗ₜ[B] (1 : C)) := hx
            have hy' :
                composite_tensor_to_relativeTensor (tensor_square_map_to_composite y) =
                  (((algebraMap B C) ((lmul' A) y)) ⊗ₜ[B] (1 : C)) := hy
            rw [hx', hy']
      _ = (((algebraMap B C) ((lmul' A) x)) + ((algebraMap B C) ((lmul' A) y))) ⊗ₜ[B] (1 : C) := by
            rw [TensorProduct.add_tmul]
      _ = ((algebraMap B C) ((lmul' A) (x + y))) ⊗ₜ[B] (1 : C) := by
            simp

/-- Helper for Lemma 15.105.9: in the relative tensor square `C ⊗[B] C`, the left and right
copies of `B` agree. -/
theorem left_tensorFactor_to_relativeTensor_eq_right_tensorFactor_to_relativeTensor :
    left_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C) =
      right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C) := by
  -- Compare the two `B`-algebra maps on generators and use the tensor relation over `B`.
  ext b
  simpa [left_tensorFactor_to_relativeTensor, right_tensorFactor_to_relativeTensor,
    Algebra.smul_def] using
    (TensorProduct.smul_tmul (R := B) (r := algebraMap B C b) (m := (1 : C)) (n := (1 : C)))

/-- Helper for Lemma 15.105.9: the comparison from `B ⊗[A] B` to `C ⊗[B] C` can equally be
described using the right `B`-factor. -/
theorem composite_tensor_to_relativeTensor_comp_tensor_square_map_right :
    (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom.comp
        (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toRingHom =
      ((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
        (lmul' A)).toRingHom := by
  -- Rewrite the already-proved left-factor comparison using the equality of the two `B`-actions.
  simpa [left_tensorFactor_to_relativeTensor_eq_right_tensorFactor_to_relativeTensor
    (A := A) (B := B) (C := C)] using
    composite_tensor_to_relativeTensor_comp_tensor_square_map (A := A) (B := B) (C := C)

/-- Helper for Lemma 15.105.9: the textbook base-change comparison
`((C ⊗[A] C) ⊗[B ⊗[A] B] B) → C ⊗[B] C` as an algebra map over `B ⊗[A] B`. -/
noncomputable def tensor_square_base_change_forward :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    let _ : Algebra R (C ⊗[B] C) :=
      (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
        (lmul' A))).toAlgebra
    ((C ⊗[A] C) ⊗[R] B) →ₐ[R] C ⊗[B] C := by
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  let _ : Algebra R (C ⊗[B] C) :=
    (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
      (lmul' A))).toAlgebra
  let leftMap : (C ⊗[A] C) →ₐ[R] C ⊗[B] C :=
    { toRingHom := (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom
      commutes' := by
        intro r
        -- The left factor respects the chosen `R`-action by the previously verified comparison.
        exact
          congrArg (fun f : R →+* (C ⊗[B] C) ↦ f r)
            (composite_tensor_to_relativeTensor_comp_tensor_square_map_right
              (A := A) (B := B) (C := C)) }
  let rightMap : B →ₐ[R] C ⊗[B] C :=
    { toRingHom := (right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom
      commutes' := by
        intro r
        rfl }
  -- This is the actual textbook forward comparison: apply the relative-tensor quotient map on the
  -- left factor and the right `B`-action on the scalar factor.
  exact Algebra.TensorProduct.productMap leftMap rightMap

/-- Helper for Lemma 15.105.9: the scalar `(1 ⊗ b)` in `B ⊗[A] B` acts on `C ⊗[A] C` through
the right `C`-factor. -/
theorem tensor_square_right_scalar_smul_tmul
    (c₁ c₂ : C) (b : B) :
    let R := B ⊗[A] B
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    (((1 : B) ⊗ₜ[A] b : R) • (c₁ ⊗ₜ[A] c₂ : C ⊗[A] C)) =
      c₁ ⊗ₜ[A] ((algebraMap B C b) * c₂) := by
  let R := B ⊗[A] B
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  -- Expand the `R`-action through `tensor_square_map_to_composite` and evaluate on pure tensors.
  change
    tensor_square_map_to_composite (A := A) (B := B) (C := C) ((1 : B) ⊗ₜ[A] b) *
        (c₁ ⊗ₜ[A] c₂ : C ⊗[A] C) =
      c₁ ⊗ₜ[A] ((algebraMap B C b) * c₂)
  simp [tensor_square_map_to_composite, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- Helper for Lemma 15.105.9: the forward base-change comparison has the expected pure-tensor
formula. -/
theorem tensor_square_base_change_forward_apply_tmul
    (c₁ c₂ : C) (b : B) :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    let _ : Algebra R (C ⊗[B] C) :=
      (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
        (lmul' A))).toAlgebra
    tensor_square_base_change_forward (A := A) (B := B) (C := C)
        (((c₁ ⊗ₜ[A] c₂ : C ⊗[A] C) ⊗ₜ[R] b)) =
      c₁ ⊗ₜ[B] ((algebraMap B C b) * c₂) := by
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  let _ : Algebra R (C ⊗[B] C) :=
    (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
      (lmul' A))).toAlgebra
  -- Expand the forward comparison once and rewrite the outer tensor pure tensor explicitly.
  change
    composite_tensor_to_relativeTensor (A := A) (B := B) (C := C) (c₁ ⊗ₜ[A] c₂) *
        right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C) b =
      c₁ ⊗ₜ[B] ((algebraMap B C b) * c₂)
  -- Both factors are now explicit pure tensors in `C ⊗[B] C`, so multiplication simplifies.
  calc
    composite_tensor_to_relativeTensor (A := A) (B := B) (C := C) (c₁ ⊗ₜ[A] c₂) *
        right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C) b =
        (c₁ * (algebraMap B C b)) ⊗ₜ[B] c₂ := by
          simp [composite_tensor_to_relativeTensor, right_tensorFactor_to_relativeTensor,
            Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    _ = c₁ ⊗ₜ[B] ((algebraMap B C b) * c₂) := by
          calc
            (c₁ * (algebraMap B C b)) ⊗ₜ[B] c₂ =
                (c₁ ⊗ₜ[B] c₂) * ((algebraMap B C b) ⊗ₜ[B] (1 : C)) := by
                  simp [Algebra.TensorProduct.tmul_mul_tmul]
            _ = (c₁ ⊗ₜ[B] c₂) * ((1 : C) ⊗ₜ[B] (algebraMap B C b)) := by
                  have hswap :=
                    congrArg
                      (fun f : B →ₐ[A] C ⊗[B] C ↦ f b)
                      (left_tensorFactor_to_relativeTensor_eq_right_tensorFactor_to_relativeTensor
                        (A := A) (B := B) (C := C))
                  change
                    (((algebraMap B C b) ⊗ₜ[B] (1 : C)) : C ⊗[B] C) =
                      ((1 : C) ⊗ₜ[B] (algebraMap B C b)) at hswap
                  exact congrArg (fun z : C ⊗[B] C ↦ (c₁ ⊗ₜ[B] c₂) * z) hswap
            _ = c₁ ⊗ₜ[B] ((algebraMap B C b) * c₂) := by
                  simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

/-- Helper for Lemma 15.105.9: in the outer base-change tensor product, the scalar
`1 ⊗ b ∈ B ⊗[A] B` acts through the scalar factor `B`. -/
theorem tensor_square_base_change_right_scalar_eq
    (b : B) :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    ((((1 : C) ⊗ₜ[A] (algebraMap B C b)) : C ⊗[A] C) ⊗ₜ[R] (1 : B)) =
      ((((1 : C) ⊗ₜ[A] (1 : C)) : C ⊗[A] C) ⊗ₜ[R] b) := by
  let _ : Algebra (B ⊗[A] B) B := (lmul' A).toAlgebra
  let _ : Algebra (B ⊗[A] B) (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  -- Rewrite both sides as the two canonical `R`-algebra structure maps into the outer tensor.
  change
    (includeLeft : C ⊗[A] C →ₐ[B ⊗[A] B] ((C ⊗[A] C) ⊗[B ⊗[A] B] B))
        (((1 : C) ⊗ₜ[A] (algebraMap B C b)) : C ⊗[A] C) =
      (includeRight : B →ₐ[B ⊗[A] B] ((C ⊗[A] C) ⊗[B ⊗[A] B] B)) b
  have hmap :
      (((1 : C) ⊗ₜ[A] (algebraMap B C b)) : C ⊗[A] C) =
        tensor_square_map_to_composite (A := A) (B := B) (C := C) ((1 : B) ⊗ₜ[A] b) := by
    -- The `R`-algebra structure on `C ⊗[A] C` is exactly `tensor_square_map_to_composite`.
    simp [tensor_square_map_to_composite, Algebra.TensorProduct.productMap_apply_tmul]
  rw [hmap]
  -- The two canonical structure maps agree on `R`-scalars in the tensor product over `R`.
  calc
    (includeLeft : C ⊗[A] C →ₐ[B ⊗[A] B] ((C ⊗[A] C) ⊗[B ⊗[A] B] B))
        (tensor_square_map_to_composite (A := A) (B := B) (C := C) ((1 : B) ⊗ₜ[A] b)) =
        algebraMap (B ⊗[A] B) ((C ⊗[A] C) ⊗[B ⊗[A] B] B) ((1 : B) ⊗ₜ[A] b) := by
          exact
            (includeLeft : C ⊗[A] C →ₐ[B ⊗[A] B] ((C ⊗[A] C) ⊗[B ⊗[A] B] B)).commutes
              ((1 : B) ⊗ₜ[A] b)
    _ = (includeRight : B →ₐ[B ⊗[A] B] ((C ⊗[A] C) ⊗[B ⊗[A] B] B)) b := by
          symm
          simpa [RingHom.algebraMap_toAlgebra] using
            (includeRight : B →ₐ[B ⊗[A] B] ((C ⊗[A] C) ⊗[B ⊗[A] B] B)).commutes
              ((1 : B) ⊗ₜ[A] b)

/-- Helper for Lemma 15.105.9: in the outer base-change tensor product, the scalar
`b ⊗ 1 ∈ B ⊗[A] B` acts through the left `C`-factor. -/
theorem tensor_square_base_change_left_scalar_eq
    (b : B) :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    ((((algebraMap B C b) ⊗ₜ[A] (1 : C)) : C ⊗[A] C) ⊗ₜ[R] (1 : B)) =
      ((((1 : C) ⊗ₜ[A] (1 : C)) : C ⊗[A] C) ⊗ₜ[R] b) := by
  let _ : Algebra (B ⊗[A] B) B := (lmul' A).toAlgebra
  let _ : Algebra (B ⊗[A] B) (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  -- Rewrite both sides as the two canonical `R`-algebra structure maps into the outer tensor.
  change
    (includeLeft : C ⊗[A] C →ₐ[B ⊗[A] B] ((C ⊗[A] C) ⊗[B ⊗[A] B] B))
        (((algebraMap B C b) ⊗ₜ[A] (1 : C)) : C ⊗[A] C) =
      (includeRight : B →ₐ[B ⊗[A] B] ((C ⊗[A] C) ⊗[B ⊗[A] B] B)) b
  have hmap :
      (((algebraMap B C b) ⊗ₜ[A] (1 : C)) : C ⊗[A] C) =
        tensor_square_map_to_composite (A := A) (B := B) (C := C) (b ⊗ₜ[A] (1 : B)) := by
    -- The `R`-algebra structure on `C ⊗[A] C` is exactly `tensor_square_map_to_composite`.
    simp [tensor_square_map_to_composite, Algebra.TensorProduct.productMap_apply_tmul]
  rw [hmap]
  -- The two canonical structure maps agree on `R`-scalars in the tensor product over `R`.
  calc
    (includeLeft : C ⊗[A] C →ₐ[B ⊗[A] B] ((C ⊗[A] C) ⊗[B ⊗[A] B] B))
        (tensor_square_map_to_composite (A := A) (B := B) (C := C) (b ⊗ₜ[A] (1 : B))) =
        algebraMap (B ⊗[A] B) ((C ⊗[A] C) ⊗[B ⊗[A] B] B) (b ⊗ₜ[A] (1 : B)) := by
          exact
            (includeLeft : C ⊗[A] C →ₐ[B ⊗[A] B] ((C ⊗[A] C) ⊗[B ⊗[A] B] B)).commutes
              (b ⊗ₜ[A] (1 : B))
    _ = (includeRight : B →ₐ[B ⊗[A] B] ((C ⊗[A] C) ⊗[B ⊗[A] B] B)) b := by
          symm
          simpa [RingHom.algebraMap_toAlgebra] using
            (includeRight : B →ₐ[B ⊗[A] B] ((C ⊗[A] C) ⊗[B ⊗[A] B] B)).commutes
              (b ⊗ₜ[A] (1 : B))

/-- Helper for Lemma 15.105.9: the left copy of `C` defines the left `B`-algebra map into the
outer base-change tensor square. -/
theorem left_tensorFactor_to_baseChange_commutes
    (b : B) :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    ((includeLeft : C ⊗[A] C →ₐ[R] ((C ⊗[A] C) ⊗[R] B))
        (((algebraMap B C b) ⊗ₜ[A] (1 : C)) : C ⊗[A] C)) =
      algebraMap B ((C ⊗[A] C) ⊗[R] B) b := by
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  -- This is exactly the left-scalar relation proved above, restated as an algebra-map identity.
  simpa [RingHom.algebraMap_toAlgebra] using
    (tensor_square_base_change_left_scalar_eq (A := A) (B := B) (C := C) b)

/-- Helper for Lemma 15.105.9: the right copy of `C` defines the right `B`-algebra map into the
outer base-change tensor square. -/
theorem right_tensorFactor_to_baseChange_commutes
    (b : B) :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    ((includeLeft : C ⊗[A] C →ₐ[R] ((C ⊗[A] C) ⊗[R] B))
        (((1 : C) ⊗ₜ[A] (algebraMap B C b)) : C ⊗[A] C)) =
      algebraMap B ((C ⊗[A] C) ⊗[R] B) b := by
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  -- This is the previously proved right-scalar relation, rephrased as an algebra-map identity.
  simpa [RingHom.algebraMap_toAlgebra] using
    (tensor_square_base_change_right_scalar_eq (A := A) (B := B) (C := C) b)

/-- Helper for Lemma 15.105.9: the left factor of `C ⊗[B] C` maps into the outer base-change
tensor square by `c ↦ ((c ⊗ 1) ⊗ 1)`. -/
noncomputable abbrev left_tensorFactor_to_baseChange :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    C →ₐ[B] ((C ⊗[A] C) ⊗[R] B) :=
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  { toRingHom :=
      ((includeLeft : C ⊗[A] C →ₐ[R] ((C ⊗[A] C) ⊗[R] B)).toRingHom).comp
        (includeLeft : C →ₐ[A] C ⊗[A] C).toRingHom
    commutes' := left_tensorFactor_to_baseChange_commutes (A := A) (B := B) (C := C) }

/-- Helper for Lemma 15.105.9: the right factor of `C ⊗[B] C` maps into the outer base-change
tensor square by `c ↦ ((1 ⊗ c) ⊗ 1)`. -/
noncomputable abbrev right_tensorFactor_to_baseChange :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    C →ₐ[B] ((C ⊗[A] C) ⊗[R] B) :=
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  { toRingHom :=
      ((includeLeft : C ⊗[A] C →ₐ[R] ((C ⊗[A] C) ⊗[R] B)).toRingHom).comp
        (includeRight : C →ₐ[A] C ⊗[A] C).toRingHom
    commutes' := right_tensorFactor_to_baseChange_commutes (A := A) (B := B) (C := C) }

/-- Helper for Lemma 15.105.9: the outer tensor-product relation moves the right `B`-action from
the second `C`-factor to the base-changed scalar. -/
theorem tensor_square_base_change_backward_tmul
    (c₁ c₂ : C) (b : B) :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    ((((c₁ ⊗ₜ[A] ((algebraMap B C b) * c₂)) : C ⊗[A] C) ⊗ₜ[R] (1 : B))) =
      ((((c₁ ⊗ₜ[A] c₂) : C ⊗[A] C) ⊗ₜ[R] b)) := by
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  -- First isolate the scalar-only pure tensor, then multiply it with the fixed left factor.
  calc
    ((((c₁ ⊗ₜ[A] ((algebraMap B C b) * c₂)) : C ⊗[A] C)) ⊗ₜ[R] (1 : B)) =
        ((((c₁ ⊗ₜ[A] c₂ : C ⊗[A] C) ⊗ₜ[R] (1 : B))) *
          ((((1 : C) ⊗ₜ[A] (algebraMap B C b) : C ⊗[A] C)) ⊗ₜ[R] (1 : B))) := by
          symm
          simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
    _ = ((((c₁ ⊗ₜ[A] c₂ : C ⊗[A] C) ⊗ₜ[R] (1 : B))) *
          ((((1 : C) ⊗ₜ[A] (1 : C) : C ⊗[A] C)) ⊗ₜ[R] b)) := by
          rw [tensor_square_base_change_right_scalar_eq (A := A) (B := B) (C := C) b]
    _ = ((((c₁ ⊗ₜ[A] c₂) : C ⊗[A] C) ⊗ₜ[R] b)) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- Helper for Lemma 15.105.9: the textbook base-change ring
`((C ⊗[A] C) ⊗[B ⊗[A] B] B)` admits the explicit backward comparison from `C ⊗[B] C`. -/
noncomputable abbrev tensor_square_base_change_backward :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    C ⊗[B] C →ₐ[B] ((C ⊗[A] C) ⊗[R] B) :=
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  @Algebra.TensorProduct.productMap B (((C ⊗[A] C) ⊗[R] B)) C C _ _ _ _ _ _ _
    (left_tensorFactor_to_baseChange (A := A) (B := B) (C := C))
    (right_tensorFactor_to_baseChange (A := A) (B := B) (C := C))

/-- Helper for Lemma 15.105.9: the backward comparison sends a pure tensor in `C ⊗[B] C` to the
corresponding pure tensor with scalar factor `1`. -/
theorem tensor_square_base_change_backward_apply_tmul
    (c₁ c₂ : C) :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    tensor_square_base_change_backward (A := A) (B := B) (C := C) (c₁ ⊗ₜ[B] c₂) =
      ((((c₁ ⊗ₜ[A] c₂) : C ⊗[A] C) ⊗ₜ[R] (1 : B))) := by
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  -- Expand the backward comparison and multiply the two explicit tensor factors.
  rw [tensor_square_base_change_backward]
  rw [Algebra.TensorProduct.productMap_apply_tmul]
  simp [left_tensorFactor_to_baseChange, right_tensorFactor_to_baseChange,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- Helper for Lemma 15.105.9: applying the backward comparison after the forward comparison
to a generator `x ⊗ b` of the outer base-change tensor recovers that generator. -/
theorem tensor_square_base_change_backward_forward_apply_tmul
    (x : C ⊗[A] C) (b : B) :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    let _ : Algebra R (C ⊗[B] C) :=
      (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
        (lmul' A))).toAlgebra
    tensor_square_base_change_backward (A := A) (B := B) (C := C)
        (tensor_square_base_change_forward (A := A) (B := B) (C := C) (x ⊗ₜ[R] b)) =
      (x ⊗ₜ[R] b) := by
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  let _ : Algebra R (C ⊗[B] C) :=
    (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
      (lmul' A))).toAlgebra
  let f : ((C ⊗[A] C) ⊗[R] B) →+* C ⊗[B] C :=
    (tensor_square_base_change_forward (A := A) (B := B) (C := C)).toRingHom
  let g : (C ⊗[B] C) →+* ((C ⊗[A] C) ⊗[R] B) :=
    (tensor_square_base_change_backward (A := A) (B := B) (C := C)).toRingHom
  -- Route correction: isolate the generator computation so the additive branches stay on `RingHom`s.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- The zero generator is immediate from the additive structure of the two comparison maps.
    change g (f (0 ⊗ₜ[R] b)) = 0 ⊗ₜ[R] b
    calc
      g (f (0 ⊗ₜ[R] b)) = g (f (0 : (C ⊗[A] C) ⊗[R] B)) := by
        rw [TensorProduct.zero_tmul]
      _ = g (0 : C ⊗[B] C) := by
        rw [f.map_zero]
      _ = (0 : (C ⊗[A] C) ⊗[R] B) := by
        rw [g.map_zero]
      _ = 0 ⊗ₜ[R] b := by
        rw [TensorProduct.zero_tmul]
  · intro c₁ c₂
    -- On pure tensors, expand the two comparison formulas and move the right scalar to `B`.
    have hf :
        f ((((c₁ ⊗ₜ[A] c₂) : C ⊗[A] C) ⊗ₜ[R] b)) =
          c₁ ⊗ₜ[B] ((algebraMap B C b) * c₂) := by
      simpa [f] using
        (tensor_square_base_change_forward_apply_tmul (A := A) (B := B) (C := C) c₁ c₂ b)
    have hg :
        g (c₁ ⊗ₜ[B] ((algebraMap B C b) * c₂)) =
          ((((c₁ ⊗ₜ[A] ((algebraMap B C b) * c₂)) : C ⊗[A] C) ⊗ₜ[R] (1 : B))) := by
      simpa [R, g] using
        (tensor_square_base_change_backward_apply_tmul (A := A) (B := B) (C := C) c₁
          ((algebraMap B C b) * c₂))
    calc
      g (f ((((c₁ ⊗ₜ[A] c₂) : C ⊗[A] C) ⊗ₜ[R] b))) =
          g (c₁ ⊗ₜ[B] ((algebraMap B C b) * c₂)) := by
            rw [hf]
      _ = ((((c₁ ⊗ₜ[A] ((algebraMap B C b) * c₂)) : C ⊗[A] C) ⊗ₜ[R] (1 : B))) := by
            rw [hg]
      _ = ((((c₁ ⊗ₜ[A] c₂) : C ⊗[A] C) ⊗ₜ[R] b)) := by
            rw [tensor_square_base_change_backward_tmul (A := A) (B := B) (C := C)]
  · intro x y hx hy
    -- Additivity reduces the mixed tensor to the two induction hypotheses.
    have hx' : g (f (x ⊗ₜ[R] b)) = x ⊗ₜ[R] b := by
      simpa [f, g] using hx
    have hy' : g (f (y ⊗ₜ[R] b)) = y ⊗ₜ[R] b := by
      simpa [f, g] using hy
    calc
      g (f (((x + y) ⊗ₜ[R] b))) = g (f (x ⊗ₜ[R] b + y ⊗ₜ[R] b)) := by
        rw [TensorProduct.add_tmul]
      _ = g (f (x ⊗ₜ[R] b) + f (y ⊗ₜ[R] b)) := by
        rw [f.map_add]
      _ = g (f (x ⊗ₜ[R] b)) + g (f (y ⊗ₜ[R] b)) := by
        rw [g.map_add]
      _ = (x ⊗ₜ[R] b) + (y ⊗ₜ[R] b) := by
        rw [hx', hy']
      _ = ((x + y) ⊗ₜ[R] b) := by
        rw [TensorProduct.add_tmul]

/-- Helper for Lemma 15.105.9: applying the forward comparison after the backward comparison
to a pure tensor in `C ⊗[B] C` recovers that pure tensor. -/
theorem tensor_square_base_change_forward_backward_apply_tmul
    (c₁ c₂ : C) :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    let _ : Algebra R (C ⊗[B] C) :=
      (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
        (lmul' A))).toAlgebra
    tensor_square_base_change_forward (A := A) (B := B) (C := C)
        (tensor_square_base_change_backward (A := A) (B := B) (C := C) (c₁ ⊗ₜ[B] c₂)) =
      (c₁ ⊗ₜ[B] c₂) := by
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  let _ : Algebra R (C ⊗[B] C) :=
    (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
      (lmul' A))).toAlgebra
  -- Expand the backward map on a pure tensor and then apply the forward pure-tensor formula at `1`.
  calc
    tensor_square_base_change_forward (A := A) (B := B) (C := C)
        (tensor_square_base_change_backward (A := A) (B := B) (C := C) (c₁ ⊗ₜ[B] c₂)) =
        tensor_square_base_change_forward (A := A) (B := B) (C := C)
          ((((c₁ ⊗ₜ[A] c₂) : C ⊗[A] C) ⊗ₜ[R] (1 : B))) := by
            rw [tensor_square_base_change_backward_apply_tmul (A := A) (B := B) (C := C)]
    _ = c₁ ⊗ₜ[B] ((algebraMap B C (1 : B)) * c₂) := by
          rw [tensor_square_base_change_forward_apply_tmul (A := A) (B := B) (C := C)]
    _ = c₁ ⊗ₜ[B] c₂ := by
          simp

/-- Helper for Lemma 15.105.9: applying the backward comparison after the forward comparison
recovers the original element of the outer base-change tensor square. -/
theorem tensor_square_base_change_backward_forward_apply :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    let _ : Algebra R (C ⊗[B] C) :=
      (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
        (lmul' A))).toAlgebra
    ∀ x : ((C ⊗[A] C) ⊗[R] B),
      tensor_square_base_change_backward (A := A) (B := B) (C := C)
        (tensor_square_base_change_forward (A := A) (B := B) (C := C) x) = x := by
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  let _ : Algebra R (C ⊗[B] C) :=
    (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
      (lmul' A))).toAlgebra
  let f : ((C ⊗[A] C) ⊗[R] B) →+* C ⊗[B] C :=
    (tensor_square_base_change_forward (A := A) (B := B) (C := C)).toRingHom
  let g : (C ⊗[B] C) →+* ((C ⊗[A] C) ⊗[R] B) :=
    (tensor_square_base_change_backward (A := A) (B := B) (C := C)).toRingHom
  refine fun x ↦ ?_
  -- Route correction: perform only the outer tensor induction here; the generator case is isolated above.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- The two comparison maps preserve zero.
    change
      tensor_square_base_change_backward (A := A) (B := B) (C := C)
          (tensor_square_base_change_forward (A := A) (B := B) (C := C)
            (0 : (C ⊗[A] C) ⊗[R] B)) =
        (0 : (C ⊗[A] C) ⊗[R] B)
    rw [map_zero, map_zero]
  · intro y b
    -- The generator case is the dedicated pure-tensor computation.
    exact tensor_square_base_change_backward_forward_apply_tmul
      (A := A) (B := B) (C := C) y b
  · intro x y hx hy
    -- Additivity stays entirely on the local `RingHom` aliases.
    have hx' : g (f x) = x := by
      simpa [f, g] using hx
    have hy' : g (f y) = y := by
      simpa [f, g] using hy
    calc
      g (f (x + y)) = g (f x + f y) := by
        rw [f.map_add]
      _ = g (f x) + g (f y) := by
        rw [g.map_add]
      _ = x + y := by
        rw [hx', hy']

/-- Helper for Lemma 15.105.9: the backward comparison is a right inverse to the forward map on
`C ⊗[B] C`. -/
theorem tensor_square_base_change_forward_backward_apply :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    let _ : Algebra R (C ⊗[B] C) :=
      (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
        (lmul' A))).toAlgebra
    ∀ x : C ⊗[B] C,
      tensor_square_base_change_forward (A := A) (B := B) (C := C)
        (tensor_square_base_change_backward (A := A) (B := B) (C := C) x) = x := by
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  let _ : Algebra R (C ⊗[B] C) :=
    (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
      (lmul' A))).toAlgebra
  let f : ((C ⊗[A] C) ⊗[R] B) →+* C ⊗[B] C :=
    (tensor_square_base_change_forward (A := A) (B := B) (C := C)).toRingHom
  let g : (C ⊗[B] C) →+* ((C ⊗[A] C) ⊗[R] B) :=
    (tensor_square_base_change_backward (A := A) (B := B) (C := C)).toRingHom
  refine fun x ↦ ?_
  -- Reduce the right-inverse statement to pure tensors and additive bookkeeping.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- The two comparison maps preserve zero.
    rw [map_zero, map_zero]
  · intro c₁ c₂
    -- The pure-tensor branch is the explicit backward-then-forward computation above.
    exact tensor_square_base_change_forward_backward_apply_tmul
      (A := A) (B := B) (C := C) c₁ c₂
  · intro x y hx hy
    -- Additivity again stays on the local `RingHom` aliases.
    have hx' : f (g x) = x := by
      simpa [f, g] using hx
    have hy' : f (g y) = y := by
      simpa [f, g] using hy
    calc
      f (g (x + y)) = f (g x + g y) := by
        rw [g.map_add]
      _ = f (g x) + f (g y) := by
        rw [f.map_add]
      _ = x + y := by
        rw [hx', hy']

/-- Helper for Lemma 15.105.9: the forward base-change comparison is bijective. -/
theorem tensor_square_base_change_forward_bijective :
    let R := B ⊗[A] B
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R (C ⊗[A] C) :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    let _ : Algebra R (C ⊗[B] C) :=
      (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
        (lmul' A))).toAlgebra
    Function.Bijective (tensor_square_base_change_forward (A := A) (B := B) (C := C)).toRingHom := by
  let R := B ⊗[A] B
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R (C ⊗[A] C) :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  let _ : Algebra R (C ⊗[B] C) :=
    (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
      (lmul' A))).toAlgebra
  let f : ((C ⊗[A] C) ⊗[R] B) →+* C ⊗[B] C :=
    (tensor_square_base_change_forward (A := A) (B := B) (C := C)).toRingHom
  let g : (C ⊗[B] C) →+* ((C ⊗[A] C) ⊗[R] B) :=
    (tensor_square_base_change_backward (A := A) (B := B) (C := C)).toRingHom
  have hleft : Function.LeftInverse g f := by
    -- The backward comparison is a left inverse by the outer tensor induction above.
    intro x
    simpa [f, g] using
      (tensor_square_base_change_backward_forward_apply (A := A) (B := B) (C := C) x)
  have hright : Function.RightInverse g f := by
    -- The backward comparison is also a right inverse by tensor induction on `C ⊗[B] C`.
    intro x
    simpa [f, g] using
      (tensor_square_base_change_forward_backward_apply (A := A) (B := B) (C := C) x)
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

/-- Helper for Lemma 15.105.9: composing the algebra map into the outer base-change tensor with
the forward comparison recovers the canonical map `C ⊗[A] C → C ⊗[B] C`. -/
theorem tensor_square_base_change_forward_comp_algebraMap :
    let R := B ⊗[A] B
    let S := C ⊗[A] C
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R S :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    let _ : Algebra S (S ⊗[R] B) := TensorProduct.leftAlgebra
    let _ : Algebra R (C ⊗[B] C) :=
      (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
        (lmul' A))).toAlgebra
    (tensor_square_base_change_forward (A := A) (B := B) (C := C)).toRingHom.comp
        (algebraMap S (S ⊗[R] B)) =
      (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom := by
  let R := B ⊗[A] B
  let S := C ⊗[A] C
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R S :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  let _ : Algebra S (S ⊗[R] B) := TensorProduct.leftAlgebra
  let _ : Algebra R (C ⊗[B] C) :=
    (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
      (lmul' A))).toAlgebra
  apply RingHom.ext
  intro x
  -- Reduce to pure tensors in `C ⊗[A] C`, where the comparison formula is explicit.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro c₁ c₂
    change
      tensor_square_base_change_forward (A := A) (B := B) (C := C)
          ((((c₁ ⊗ₜ[A] c₂) : C ⊗[A] C) ⊗ₜ[R] (1 : B))) =
        composite_tensor_to_relativeTensor (A := A) (B := B) (C := C) (c₁ ⊗ₜ[A] c₂)
    rw [tensor_square_base_change_forward_apply_tmul (A := A) (B := B) (C := C) c₁ c₂ (1 : B)]
    simp [composite_tensor_to_relativeTensor, Algebra.TensorProduct.productMap_apply_tmul]
  · intro x y hx hy
    change
      tensor_square_base_change_forward (A := A) (B := B) (C := C) ((x + y) ⊗ₜ[R] (1 : B)) =
        composite_tensor_to_relativeTensor (A := A) (B := B) (C := C) (x + y)
    have hx' :
        tensor_square_base_change_forward (A := A) (B := B) (C := C) (x ⊗ₜ[R] (1 : B)) =
          composite_tensor_to_relativeTensor (A := A) (B := B) (C := C) x := by
      simpa [RingHom.comp_apply] using hx
    have hy' :
        tensor_square_base_change_forward (A := A) (B := B) (C := C) (y ⊗ₜ[R] (1 : B)) =
          composite_tensor_to_relativeTensor (A := A) (B := B) (C := C) y := by
      simpa [RingHom.comp_apply] using hy
    calc
      tensor_square_base_change_forward (A := A) (B := B) (C := C) ((x + y) ⊗ₜ[R] (1 : B)) =
          tensor_square_base_change_forward (A := A) (B := B) (C := C)
            (x ⊗ₜ[R] (1 : B) + y ⊗ₜ[R] (1 : B)) := by
              rw [TensorProduct.add_tmul]
      _ = tensor_square_base_change_forward (A := A) (B := B) (C := C) (x ⊗ₜ[R] (1 : B)) +
            tensor_square_base_change_forward (A := A) (B := B) (C := C) (y ⊗ₜ[R] (1 : B)) := by
              exact (tensor_square_base_change_forward (A := A) (B := B) (C := C)).toRingHom.map_add _ _
      _ = composite_tensor_to_relativeTensor (A := A) (B := B) (C := C) x +
            composite_tensor_to_relativeTensor (A := A) (B := B) (C := C) y := by
              rw [hx', hy']
      _ = composite_tensor_to_relativeTensor (A := A) (B := B) (C := C) (x + y) := by
              symm
              exact (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom.map_add x y

/-- Helper for Lemma 15.105.9: flatness of `B ⊗[A] B → B` stays flat after the outer base change
to `C ⊗[A] C`. -/
theorem tensor_square_outer_base_change_algebraMap_flat
    (hAB : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    let R := B ⊗[A] B
    let S := C ⊗[A] C
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R S :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    let T := S ⊗[R] B
    let _ : Algebra S T := TensorProduct.leftAlgebra
    (algebraMap S T).Flat := by
  let R := B ⊗[A] B
  let S := C ⊗[A] C
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R S :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  let T := S ⊗[R] B
  let _ : Algebra S T := TensorProduct.leftAlgebra
  -- Rewrite the source flatness into the canonical algebra-map form over `R`.
  have hAB_alg : (algebraMap R B).Flat := by
    simpa [RingHom.algebraMap_toAlgebra] using
      (show (lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom.Flat from hAB)
  let _ : Module.Flat R B := RingHom.flat_algebraMap_iff.mp hAB_alg
  -- Apply the standard base-change owner on modules and convert back to ring-map flatness.
  have hbaseModule : Module.Flat S T := by
    simpa [T] using (Module.Flat.baseChange (R := R) (S := S) (M := B))
  exact RingHom.flat_algebraMap_iff.mpr hbaseModule

/-- Helper for Lemma 15.105.9: the forward comparison is flat because it is bijective. -/
theorem tensor_square_forward_flat_of_bijective :
    let R := B ⊗[A] B
    let S := C ⊗[A] C
    let _ : Algebra R B := (lmul' A).toAlgebra
    let _ : Algebra R S :=
      (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
    let T := S ⊗[R] B
    let _ : Algebra S T := TensorProduct.leftAlgebra
    let _ : Algebra R (C ⊗[B] C) :=
      (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
        (lmul' A))).toAlgebra
    ((tensor_square_base_change_forward (A := A) (B := B) (C := C)).toRingHom).Flat := by
  let R := B ⊗[A] B
  let S := C ⊗[A] C
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R S :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  let T := S ⊗[R] B
  let _ : Algebra S T := TensorProduct.leftAlgebra
  let _ : Algebra R (C ⊗[B] C) :=
    (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
      (lmul' A))).toAlgebra
  -- The comparison is bijective, so flatness follows from the canonical owner theorem.
  exact RingHom.Flat.of_bijective
    (tensor_square_base_change_forward_bijective (A := A) (B := B) (C := C))

/-- Helper for Lemma 15.105.9: base changing the flat multiplication map
`B ⊗[A] B → B` along `B ⊗[A] B → C ⊗[A] C` yields flatness of `C ⊗[B] C` over `C ⊗[A] C`. -/
theorem tensor_square_base_change_flat
    (hAB : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).Flat := by
  let R := B ⊗[A] B
  let S := C ⊗[A] C
  let _ : Algebra R B := (lmul' A).toAlgebra
  let _ : Algebra R S :=
    (tensor_square_map_to_composite (A := A) (B := B) (C := C)).toAlgebra
  let T := S ⊗[R] B
  let _ : Algebra S T := TensorProduct.leftAlgebra
  let _ : Algebra R (C ⊗[B] C) :=
    (((right_tensorFactor_to_relativeTensor (A := A) (B := B) (C := C)).comp
      (lmul' A))).toAlgebra
  -- Route correction: keep the source base-change comparison, but freeze the outer map and the
  -- bijective comparison as separate `RingHom.Flat` facts before composing them.
  change (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom.Flat
  let i : S →+* T := algebraMap S T
  let f : T →+* (C ⊗[B] C) :=
    (tensor_square_base_change_forward (A := A) (B := B) (C := C)).toRingHom
  -- The outer algebra map is flat by base change of `B ⊗[A] B → B`.
  have hi : i.Flat := by
    simpa [i] using
      (tensor_square_outer_base_change_algebraMap_flat
        (A := A) (B := B) (C := C) hAB)
  -- The comparison map is flat because the previous tensor identifications made it bijective.
  have hf : f.Flat := by
    simpa [f] using
      (tensor_square_forward_flat_of_bijective (A := A) (B := B) (C := C))
  -- Compose the two flat maps, then rewrite the composite back to the canonical comparison.
  have hcomp : (f.comp i).Flat := RingHom.Flat.comp hi hf
  have hEq :
      f.comp i = (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom := by
    simpa [f, i] using
      (tensor_square_base_change_forward_comp_algebraMap (A := A) (B := B) (C := C))
  rw [hEq] at hcomp
  simpa using hcomp

/-- Lemma 15.105.9 (1): if the multiplication maps `B ⊗[A] B → B` and `C ⊗[B] C → C` are flat,
then the multiplication map `C ⊗[A] C → C` is flat. -/
@[stacks 092J]
theorem tensorSquareMul_flat_comp
    (hAB : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat)
    (hBC : (lmul' B : C ⊗[B] C →ₐ[B] C).Flat) :
    (lmul' A : C ⊗[A] C →ₐ[A] C).Flat := by
  let f : (C ⊗[A] C) →+* (C ⊗[B] C) :=
    (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom
  let g : (C ⊗[B] C) →+* C := (lmul' B).toRingHom
  -- Factor `C ⊗[A] C → C` through the comparison map `C ⊗[A] C → C ⊗[B] C`.
  have hcomp : (g.comp f).Flat := by
    exact RingHom.Flat.comp
      (tensor_square_base_change_flat (A := A) (B := B) (C := C) hAB)
      (show g.Flat by simpa [g] using (show (lmul' B : C ⊗[B] C →ₐ[B] C).toRingHom.Flat from hBC))
  -- The composite is exactly the tensor-square multiplication over `A`.
  have hmul_eq : g.comp f = (lmul' A : C ⊗[A] C →ₐ[A] C).toRingHom := by
    apply RingHom.ext
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro c₁ c₂
      simp [f, g, composite_tensor_to_relativeTensor,
        Algebra.TensorProduct.productMap_apply_tmul]
    · intro x y hx hy
      calc
        (g.comp f) (x + y) = (g.comp f) x + (g.comp f) y := by
          simp [g, f]
        _ = (lmul' A : C ⊗[A] C →ₐ[A] C).toRingHom x +
            (lmul' A : C ⊗[A] C →ₐ[A] C).toRingHom y := by
          rw [hx, hy]
        _ = (lmul' A : C ⊗[A] C →ₐ[A] C) (x + y) := by
          simp
  rw [hmul_eq] at hcomp
  simpa using hcomp

namespace IsWeaklyEtale

-- Proof sketch: compose flatness of `A → B` and `B → C` by `Module.Flat.trans`, and use part
-- `(1)` for the tensor-square multiplication clause of the composite.
/-- Lemma 15.105.9 (2): the composite of weakly étale ring maps is weakly étale. -/
@[stacks 092J]
theorem comp (hAB : IsWeaklyEtale A B) (hBC : IsWeaklyEtale B C) : IsWeaklyEtale A C := by
  letI : Module.Flat A B := hAB.moduleFlat
  letI : Module.Flat B C := hBC.moduleFlat
  exact
    { moduleFlat := Module.Flat.trans A B C
      flat_tensorSquareMultiplication :=
        tensorSquareMul_flat_comp hAB.flat_tensorSquareMultiplication
          hBC.flat_tensorSquareMultiplication }

end IsWeaklyEtale

end

end Algebra
