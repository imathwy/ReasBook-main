import StacksProject_2024.Chap15.Definition_15_105_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

variable {A : Type u} {A' : Type v} {B : Type w}
variable [CommRing A] [CommRing A'] [CommRing B] [Algebra A B] [Algebra A A']

local notation "B'" => A' ⊗[A] B

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Domain-style sampling for weakly étale base change:
- primary domain: commutative algebra of flat ring maps and weakly étale morphisms under tensor
  base change;
- source-facing layer: part `(1)` is the tensor-square flatness clause in the weakly étale
  criterion after base change;
- core/canonical owner: the chapter-local ring-map owner `Algebra.IsWeaklyEtale`;
- sampled bridge API: `RingHom.Flat.tensorProductMap` for tensor-product flatness and
  `Algebra.TensorProduct.cancelBaseChange` / `assoc` for the canonical identification of the
  base-changed tensor square;
- primitive data: flatness of `lmul' A`;
- derived API: flatness of `lmul' A'` and the owner theorem `Algebra.IsWeaklyEtale.baseChange`.
-/

namespace Algebra

/-- Helper for Lemma 15.105.7: the tensor square after base change is canonically the base change
of the original tensor square. -/
noncomputable def tensorSquare_baseChangeAlgEquiv :
    B' ⊗[A'] B' ≃ₐ[A'] A' ⊗[A] (B ⊗[A] B) :=
  (Algebra.TensorProduct.cancelBaseChange A A' A' B' B).trans
    (Algebra.TensorProduct.assoc A A A' A' B B)

/-- Helper for Lemma 15.105.7: on pure tensors, `tensorSquare_baseChangeAlgEquiv` multiplies the
two base-change scalars and keeps the original tensor-square factor. -/
theorem tensorSquare_baseChangeAlgEquiv_tmul (a a' : A') (b b' : B) :
    tensorSquare_baseChangeAlgEquiv (A := A) (A' := A') (B := B)
        ((a ⊗ₜ[A] b) ⊗ₜ[A'] (a' ⊗ₜ[A] b')) =
      (a * a') ⊗ₜ[A] (b ⊗ₜ[A] b') := by
  -- Reduce the algebra equivalence to the mixed-base linear equivalences with explicit
  -- computation rules.
  change (TensorProduct.AlgebraTensorModule.assoc A A A' A' B B)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A A' A' B' B)
        ((a ⊗ₜ[A] b) ⊗ₜ[A'] (a' ⊗ₜ[A] b'))) = _
  -- The first bridge cancels one copy of the base change.
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  -- The second bridge reassociates the remaining tensor product.
  convert (TensorProduct.AlgebraTensorModule.assoc_tmul A A A' (a' • a) b b') using 1
  simp [smul_eq_mul, mul_comm]

/-- Helper for Lemma 15.105.7: after transporting the base-changed multiplication map along
`tensorSquare_baseChangeAlgEquiv`, one recovers the multiplication map on the base-changed
algebra. -/
theorem tensorSquare_baseChange_mul_eq :
    ((Algebra.TensorProduct.map (AlgHom.id A' A') (lmul' A)).toRingHom.comp
      (show B' ⊗[A'] B' →ₐ[A'] A' ⊗[A] (B ⊗[A] B) from
        tensorSquare_baseChangeAlgEquiv (A := A) (A' := A') (B := B)).toRingHom) =
      (lmul' A').toRingHom := by
  let f : B' ⊗[A'] B' →ₐ[A'] B' :=
    (Algebra.TensorProduct.map (AlgHom.id A' A') (lmul' A)).comp
      (tensorSquare_baseChangeAlgEquiv (A := A) (A' := A') (B := B))
  -- Compare the transported multiplication map and `lmul' A'` on the left tensor generators.
  have hleft :
      (AlgHom.restrictScalars A' f).comp
        (Algebra.TensorProduct.includeLeft : B' →ₐ[A'] B' ⊗[A'] B') =
      (AlgHom.restrictScalars A' (lmul' A')).comp
        (Algebra.TensorProduct.includeLeft : B' →ₐ[A'] B' ⊗[A'] B') := by
    apply DFunLike.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [f]
    | tmul a b =>
        -- On a pure tensor, the comparison sends `x ⊗ 1` to the same pure tensor in `B'`.
        simp [f, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.one_def,
          tensorSquare_baseChangeAlgEquiv_tmul]
    | add x y hx hy =>
        simpa [map_add, hx, hy]
  -- The right tensor generators are handled by the same pure-tensor computation.
  have hright :
      (AlgHom.restrictScalars A' f).comp
        (Algebra.TensorProduct.includeRight : B' →ₐ[A'] B' ⊗[A'] B') =
      (AlgHom.restrictScalars A' (lmul' A')).comp
        (Algebra.TensorProduct.includeRight : B' →ₐ[A'] B' ⊗[A'] B') := by
    apply DFunLike.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [f]
    | tmul a b =>
        -- On a pure tensor, the comparison sends `1 ⊗ x` to the same pure tensor in `B'`.
        simp [f, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.one_def,
          tensorSquare_baseChangeAlgEquiv_tmul]
    | add x y hx hy =>
        simpa [map_add, hx, hy]
  -- The tensor-product universal property upgrades the generator checks to equality of algebra maps.
  have hf : f = lmul' A' := Algebra.TensorProduct.ext hleft hright
  simpa [f] using congrArg AlgHom.toRingHom hf

-- Proof sketch: identify the multiplication map
-- `(A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B) → A' ⊗[A] B` with the base change of
-- `B ⊗[A] B → B` along `A → A'`, and then apply flat base change from Lemma `10.39.7`.
/-- Lemma 15.105.7 (1): if the multiplication map `B ⊗[A] B → B` is flat, then the multiplication
map `(A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B) → A' ⊗[A] B` is flat. -/
theorem tensorSquareMul_flat_baseChange
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    let _ : Algebra (B' ⊗[A'] B') B' := (lmul' A').toAlgebra
    Module.Flat (B' ⊗[A'] B') B' := by
  -- First base change the flat multiplication map `B ⊗[A] B → B` along `A → A'`.
  have hid : (AlgHom.id A' A' : A' →ₐ[A'] A').Flat := by
    simpa using
      (RingHom.Flat.of_bijective
        (Function.bijective_id : Function.Bijective (RingHom.id A')))
  let f : A' ⊗[A] (B ⊗[A] B) →ₐ[A'] B' :=
    Algebra.TensorProduct.map (AlgHom.id A' A') (lmul' A)
  let _ : CommRing (A' ⊗[A] (B ⊗[A] B)) := inferInstance
  let _ : CommRing B' := inferInstance
  have hbaseChangeMap : RingHom.Flat (f.toRingHom) := by
    simpa [f] using
      RingHom.Flat.tensorProductMap
        (A := A') (B := B ⊗[A] B) (C := A') (D := B) hid hflatMul
  let e : B' ⊗[A'] B' ≃ₐ[A'] A' ⊗[A] (B ⊗[A] B) :=
    tensorSquare_baseChangeAlgEquiv (A := A) (A' := A') (B := B)
  let _ : CommRing (B' ⊗[A'] B') := inferInstance
  -- Then transport flatness across the canonical source-ring equivalence.
  have heFlat : RingHom.Flat (e.toRingHom) := RingHom.Flat.of_bijective e.bijective
  have htransported : RingHom.Flat (f.toRingHom.comp e.toRingHom) :=
    RingHom.Flat.comp heFlat hbaseChangeMap
  have hEq : f.toRingHom.comp e.toRingHom = (lmul' A').toRingHom := by
    simpa [f, e] using tensorSquare_baseChange_mul_eq (A := A) (A' := A') (B := B)
  have hlmul' : RingHom.Flat ((lmul' A' : B' ⊗[A'] B' →ₐ[A'] B').toRingHom) := by
    rw [hEq] at htransported
    exact htransported
  -- Finally convert ring-hom flatness of `lmul' A'` into module flatness for its algebra.
  let _ : Algebra (B' ⊗[A'] B') B' := (lmul' A').toAlgebra
  have halgebraMap : (algebraMap (B' ⊗[A'] B') B').Flat := by
    simpa [RingHom.algebraMap_toAlgebra] using hlmul'
  exact RingHom.flat_algebraMap_iff.mp halgebraMap

-- Proof sketch: flatness of the structure map after base change is canonical, and part `(1)`
-- gives the tensor-square multiplication clause.
namespace IsWeaklyEtale

/-- Lemma 15.105.7 (2): if `A → B` is weakly étale, then the base-changed map
`A' → A' ⊗[A] B` is weakly étale. -/
theorem baseChange (hAB : IsWeaklyEtale A B) : IsWeaklyEtale A' B' := by
  -- The structure map stays flat under base change.
  letI : Module.Flat A B := hAB.moduleFlat
  refine
    { moduleFlat := by
        simpa using (Module.Flat.baseChange A A' B)
      flat_tensorSquareMultiplication := by
        -- Part `(1)` gives flatness of the base-changed tensor-square multiplication map.
        let _ : CommRing (B' ⊗[A'] B') := inferInstance
        let _ : CommRing B' := inferInstance
        let _ : Algebra (B' ⊗[A'] B') B' := (lmul' A').toAlgebra
        have hflatMul :
            Module.Flat (B' ⊗[A'] B') B' :=
          tensorSquareMul_flat_baseChange (A := A) (A' := A') (B := B)
            hAB.flat_tensorSquareMultiplication
        have halgebraMap : RingHom.Flat (algebraMap (B' ⊗[A'] B') B') :=
          RingHom.flat_algebraMap_iff.mpr hflatMul
        simpa [RingHom.algebraMap_toAlgebra] using halgebraMap }

end IsWeaklyEtale

/- Bridge/view: weakly étaleness is preserved under tensor base change. -/
attribute [instance] IsWeaklyEtale.baseChange

end Algebra

end
