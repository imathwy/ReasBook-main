import StacksProject_2024.Chap10.Lemma_10_107_1
import StacksProject_2024.Chap15.Lemma_15_105_7
import StacksProject_2024.Chap15.Lemma_15_105_9
import StacksProject_2024.Chap15.Lemma_15_105_10
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

namespace Algebra
namespace IsWeaklyEtale

universe u v w

section

attribute [local instance] TensorProduct.leftAlgebra
attribute [local instance] TensorProduct.rightAlgebra
attribute [local instance] IsScalarTower.right

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/- Domain triage:
- primary domain: commutative algebra of weakly étale ring maps in an algebra tower;
- source-facing layer: the Stacks closure lemma asserting that in a tower `A → B → C`, if both
  `A → B` and `A → C` are weakly étale, then so is `B → C`;
- core/canonical owners sampled for this file: `Algebra.IsWeaklyEtale`,
  the tensor-square comparison `composite_tensor_to_relativeTensor`, and the canonical
  tensor-product map `Algebra.TensorProduct.lift`;
- primitive data: the two weakly étale owner facts on `A → B` and `A → C`;
- derived API: faithful flatness of `C → B ⊗[A] C`, surjectivity of
  `C ⊗[A] C → C ⊗[B] C`, and the tensor-square comparison lemmas needed for the source proof.

This item remains source-facing. The textbook proof applies Lemma `15.105.2` twice: first to
upgrade `A`-flatness of `C` to `B`-flatness, and then to upgrade flatness of `C` from
`C ⊗[A] C` to `C ⊗[B] C` across the surjective comparison map.
-/

variable (A B C)

/-!
The textbook proof compares the tensor-square multiplications over `A` and over `B`. The next
helpers isolate the tensor-product comparison maps used in those two flatness-transfer steps.
-/

/-- Helper for Lemma 15.105.11: if `A → B` is flat, then the right tensor inclusion
`C → B ⊗[A] C` is flat. -/
lemma tensor_right_flat_of_flat_left
    (hAB_flat : (algebraMap A B).Flat) :
    Module.Flat C (B ⊗[A] C) := by
  -- First base change the flat `A`-module `B` along `A → C`.
  let _ : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hAB_flat
  have hbase : Module.Flat C (C ⊗[A] B) := by
    simpa using (Module.Flat.baseChange (R := A) (S := C) (M := B))
  -- Then commute the tensor factors to recover the source-facing tensor order `B ⊗[A] C`.
  let e : B ⊗[A] C ≃ₗ[C] C ⊗[A] B :=
    (Algebra.TensorProduct.commRight A C B).symm.toLinearEquiv
  exact Module.Flat.of_linearEquiv e

/-- Helper for Lemma 15.105.11: tensor-product multiplication along the tower map `B → C`
retracts the right tensor inclusion `C → B ⊗[A] C`. -/
noncomputable abbrev tensor_right_retraction :
    B ⊗[A] C →ₐ[A] C :=
  Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom A B C)
    (AlgHom.id A C)
    (fun _ _ ↦ Commute.all _ _)

/-- Helper for Lemma 15.105.11: tensor-product multiplication is a left inverse to the right
tensor inclusion. -/
lemma tensor_right_retraction_left_inverse :
    Function.LeftInverse
      (tensor_right_retraction (A := A) (B := B) (C := C)).toRingHom
      (algebraMap C (B ⊗[A] C)) := by
  intro c
  -- The retraction is defined by the universal property, so on the right tensor generator it is
  -- exactly the identity.
  change (tensor_right_retraction (A := A) (B := B) (C := C)) ((1 : B) ⊗ₜ[A] c) = c
  simp [tensor_right_retraction]

/-- Helper for Lemma 15.105.11: the split map `C → B ⊗[A] C` is surjective on prime spectra. -/
lemma tensor_right_comap_surjective :
    Function.Surjective (PrimeSpectrum.comap (algebraMap C (B ⊗[A] C))) := by
  intro p
  refine
    ⟨PrimeSpectrum.comap (tensor_right_retraction (A := A) (B := B) (C := C)).toRingHom p, ?_⟩
  -- The retraction makes `PrimeSpectrum.comap (algebraMap C (B ⊗[A] C))` admit a right inverse.
  rw [← PrimeSpectrum.comap_comp_apply]
  ext c
  simpa using
    congrArg
      (fun x => x ∈ p.asIdeal)
      (tensor_right_retraction_left_inverse (A := A) (B := B) (C := C) c)

/-- Helper for Lemma 15.105.11: if `A → B` is flat, then the right tensor inclusion
`C → B ⊗[A] C` is faithfully flat. -/
lemma tensor_right_faithfully_flat_of_flat_left
    (hAB_flat : (algebraMap A B).Flat) :
    (algebraMap C (B ⊗[A] C)).FaithfullyFlat := by
  -- Combine the base-changed flatness with surjectivity on spectra coming from the retraction.
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨?_, tensor_right_comap_surjective (A := A) (B := B) (C := C)⟩
  let _ : Module.Flat C (B ⊗[A] C) :=
    tensor_right_flat_of_flat_left (A := A) (B := B) (C := C) hAB_flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- Helper for Lemma 15.105.11: the canonical comparison `C ⊗[A] C → C ⊗[B] C` is surjective,
because every pure tensor already comes from the same pure tensor over `A`. -/
lemma composite_tensor_to_relativeTensor_surjective :
    Function.Surjective (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)) := by
  intro z
  -- Reduce surjectivity to pure tensors in `C ⊗[B] C`, where the comparison is explicit.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp [composite_tensor_to_relativeTensor]⟩
  · intro c₁ c₂
    refine ⟨c₁ ⊗ₜ[A] c₂, ?_⟩
    simp [composite_tensor_to_relativeTensor, Algebra.TensorProduct.productMap_apply_tmul]
  · intro x y hx hy
    rcases hx with ⟨x', rfl⟩
    rcases hy with ⟨y', rfl⟩
    refine ⟨x' + y', ?_⟩
    simp [map_add]

/-- Helper for Lemma 15.105.11: after passing from `C ⊗[A] C` to `C ⊗[B] C`, tensor-square
multiplication still computes ordinary multiplication in `C`. -/
lemma comparison_mul_comp_eq_lmul :
    let R := C ⊗[A] C
    let S := C ⊗[B] C
    let _ : Algebra R S := (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toAlgebra
    ((lmul' B : S →ₐ[B] C).toRingHom).comp
        (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom =
      (lmul' A : R →ₐ[A] C).toRingHom := by
  let R := C ⊗[A] C
  let S := C ⊗[B] C
  let _ : Algebra R S := (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toAlgebra
  -- Compare the two ring maps on pure tensors in `C ⊗[A] C`.
  apply RingHom.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro c₁ c₂
    simp [composite_tensor_to_relativeTensor, Algebra.TensorProduct.productMap_apply_tmul]
  · intro x y hx hy
    calc
      ((lmul' B : S →ₐ[B] C).toRingHom.comp
          (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom) (x + y) =
          ((lmul' B : S →ₐ[B] C).toRingHom.comp
            (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom) x +
              ((lmul' B : S →ₐ[B] C).toRingHom.comp
                (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toRingHom) y := by
            simp
      _ = (lmul' A : R →ₐ[A] C).toRingHom x + (lmul' A : R →ₐ[A] C).toRingHom y := by
            rw [hx, hy]
      _ = (lmul' A : R →ₐ[A] C).toRingHom (x + y) := by
            simp

/-- Helper for Lemma 15.105.11: surjectivity of the comparison map forces the two canonical
tensor-factor maps for `C ⊗[A] C → C ⊗[B] C` to agree. -/
lemma comparison_includeLeft_eq_includeRight_of_surjective
    (hsurj : Function.Surjective (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C))) :
    let R := C ⊗[A] C
    let S := C ⊗[B] C
    let _ : Algebra R S := (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toAlgebra
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) =
      (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) := by
  let R := C ⊗[A] C
  let S := C ⊗[B] C
  let _ : Algebra R S := (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toAlgebra
  -- Surjectivity reduces the equality to elements coming from the base ring `R`.
  ext s
  obtain ⟨r, rfl⟩ := hsurj s
  -- It is enough to check equality on pure tensors of `R = C ⊗[A] C`.
  refine TensorProduct.induction_on r ?_ ?_ ?_
  · simp [composite_tensor_to_relativeTensor]
  · intro c₁ c₂
    change (algebraMap R S (c₁ ⊗ₜ[A] c₂)) ⊗ₜ[R] (1 : S) =
        (1 : S) ⊗ₜ[R] (algebraMap R S (c₁ ⊗ₜ[A] c₂))
    simpa [Algebra.smul_def] using
      (TensorProduct.smul_tmul
        (R := R) (r := (c₁ ⊗ₜ[A] c₂ : R)) (m := (1 : S)) (n := (1 : S)))
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Lemma 15.105.11: the surjective comparison `C ⊗[A] C → C ⊗[B] C` has bijective
tensor-square multiplication, because surjective algebra maps are epimorphisms. -/
lemma comparison_tensorSquareMultiplication_bijective_of_surjective
    (hsurj : Function.Surjective (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C))) :
    let R := C ⊗[A] C
    let S := C ⊗[B] C
    let _ : Algebra R S := (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toAlgebra
    Function.Bijective (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S) := by
  let R := C ⊗[A] C
  let S := C ⊗[B] C
  let _ : Algebra R S := (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toAlgebra
  -- First package surjectivity as the Chapter 10 epimorphism criterion.
  have hEpi : Algebra.IsEpi R S := by
    refine (algebra_isEpi_iff_includeLeft_eq_includeRight (R := R) (S := S)).2 ?_
    exact comparison_includeLeft_eq_includeRight_of_surjective (A := A) (B := B) (C := C) hsurj
  exact (algebra_isEpi_iff_bijective_lmul (R := R) (S := S)).1 hEpi

/-- Helper for Lemma 15.105.11: surjectivity of the comparison `C ⊗[A] C → C ⊗[B] C` makes the
relative tensor-square multiplication over `C ⊗[A] C` flat. -/
lemma comparison_tensorSquareMultiplication_flat_of_surjective
    (hsurj : Function.Surjective (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C))) :
    let R := C ⊗[A] C
    let S := C ⊗[B] C
    let _ : Algebra R S := (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toAlgebra
    (lmul' R : S ⊗[R] S →ₐ[R] S).Flat := by
  let R := C ⊗[A] C
  let S := C ⊗[B] C
  let _ : Algebra R S := (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toAlgebra
  -- The tensor-square multiplication is bijective because the comparison algebra map is epi.
  exact RingHom.Flat.of_bijective <|
    comparison_tensorSquareMultiplication_bijective_of_surjective
      (A := A) (B := B) (C := C) hsurj

/-- Helper for Lemma 15.105.11: after equipping `C ⊗[B] C` with its comparison algebra over
`C ⊗[A] C`, multiplication over `B` factors the `A`-multiplication map. -/
lemma comparison_target_algebraMap_eq :
    let R := C ⊗[A] C
    let S := C ⊗[B] C
    let _ : Algebra R S := (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toAlgebra
    let _ : Algebra R C := (lmul' A).toAlgebra
    let _ : Algebra S C := (lmul' B).toAlgebra
    (algebraMap R C) = (algebraMap S C).comp (algebraMap R S) := by
  let R := C ⊗[A] C
  let S := C ⊗[B] C
  let _ : Algebra R S := (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toAlgebra
  let _ : Algebra R C := (lmul' A).toAlgebra
  let _ : Algebra S C := (lmul' B).toAlgebra
  -- This is exactly the comparison identity already established at the tensor-square level.
  simpa [R, S, RingHom.algebraMap_toAlgebra] using
    (comparison_mul_comp_eq_lmul (A := A) (B := B) (C := C)).symm

/-- Helper for Lemma 15.105.11: multiplication `S ⊗[R] S → S` makes `S` into the scalar-tower
target over the left tensor inclusion `S → S ⊗[R] S`. -/
lemma tensor_square_target_collapse_isScalarTower
    {R : Type*} {S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] :
    let TSq := S ⊗[R] S
    let _ : Algebra TSq S := (lmul' R).toAlgebra
    IsScalarTower S TSq S := by
  intro TSq
  let leftAlg : Algebra S TSq := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra S TSq := leftAlg
  letI : Algebra TSq S := (lmul' R).toAlgebra
  -- Expanding the two algebra maps reduces the tower condition to `lmul' R (s ⊗ 1) = s`.
  simpa using
    (show IsScalarTower S TSq S from
      IsScalarTower.of_algebraMap_eq (R := S) (S := TSq) (A := S) fun s ↦ by
        change s = (lmul' R) (s ⊗ₜ[R] (1 : S))
        simp)

/-- Helper for Lemma 15.105.11: after tensoring once more with `S` over `S ⊗[R] S`, the standard
base-change cancellation followed by the tensor-unit identification collapses back to the target
module. -/
noncomputable def tensor_square_target_collapse_equiv
    {R : Type*} {S : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    {M : Type*} [AddCommGroup M] [Module S M] :
    let TSq := S ⊗[R] S
    let _ : Algebra TSq S := (lmul' R).toAlgebra
    let _ : IsScalarTower S TSq S :=
      tensor_square_target_collapse_isScalarTower (R := R) (S := S)
    S ⊗[TSq] (TSq ⊗[S] M) ≃ₗ[S] M := sorry

/-- Helper for Lemma 15.105.11: if `T` is flat over `R` and the tensor-square multiplication
`S ⊗[R] S → S` is flat, then `T` is flat over `S`. -/
lemma flat_target_of_flat_tensorSquareMultiplication
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T]
    (hcomp : (algebraMap R T) = (algebraMap S T).comp (algebraMap R S))
    (hflatMul : (lmul' R : S ⊗[R] S →ₐ[R] S).Flat)
    (hflatT : Module.Flat R T) :
    Module.Flat S T := by
  -- TODO: transport exactness of `T ⊗[R] -` through the forward tensor-square/base-change ladder,
  -- apply flatness of `lmul' R`, and then use `tensor_square_target_collapse_equiv` to collapse
  -- the final mixed-base tensor back to `T ⊗[S] -`.
  sorry

/-- Lemma 15.105.11: in a tower `A → B → C`, if both `A → B` and `A → C` are weakly étale, then
`B → C` is weakly étale. -/
@[stacks 092L]
theorem of_tower (hAB : IsWeaklyEtale A B) (hAC : IsWeaklyEtale A C) :
    IsWeaklyEtale B C := by
  -- Route correction: the shortcut through `B ⊗[A] C` is not a scalar tower, so we return to the
  -- textbook proof and isolate the `15.105.2`-style flatness transfer in one local helper.
  have hBC_moduleFlat : Module.Flat B C := by
    -- The first source step upgrades `A`-flatness of `C` to `B`-flatness using `A → B`.
    exact flat_target_of_flat_tensorSquareMultiplication
      (R := A) (S := B) (T := C)
      (IsScalarTower.algebraMap_eq A B C)
      hAB.flat_tensorSquareMultiplication hAC.moduleFlat
  have hBC_flat : (algebraMap B C).Flat := RingHom.flat_algebraMap_iff.mpr hBC_moduleFlat
  have hcomparison_surj :
      Function.Surjective (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)) :=
    composite_tensor_to_relativeTensor_surjective (A := A) (B := B) (C := C)
  have hflatMulBC : (lmul' B : C ⊗[B] C →ₐ[B] C).Flat := by
    let _ : Algebra (C ⊗[A] C) (C ⊗[B] C) :=
      (composite_tensor_to_relativeTensor (A := A) (B := B) (C := C)).toAlgebra
    let _ : Algebra (C ⊗[A] C) C := (lmul' A).toAlgebra
    let _ : Algebra (C ⊗[B] C) C := (lmul' B).toAlgebra
    have hflatC_R_alg : (algebraMap (C ⊗[A] C) C).Flat := by
      -- Weak étaleness of `A → C` already identifies `C` as flat over `C ⊗[A] C`.
      simpa [RingHom.algebraMap_toAlgebra] using
        (show (lmul' A : C ⊗[A] C →ₐ[A] C).toRingHom.Flat from
          hAC.flat_tensorSquareMultiplication)
    have hflatC_R : Module.Flat (C ⊗[A] C) C := RingHom.flat_algebraMap_iff.mp hflatC_R_alg
    have hflatMulBC_module : Module.Flat (C ⊗[B] C) C := by
      -- The second source step transfers flatness across the surjective comparison
      -- `C ⊗[A] C → C ⊗[B] C`.
      exact flat_target_of_flat_tensorSquareMultiplication
        (R := C ⊗[A] C) (S := C ⊗[B] C) (T := C)
        (comparison_target_algebraMap_eq (A := A) (B := B) (C := C))
        (comparison_tensorSquareMultiplication_flat_of_surjective
          (A := A) (B := B) (C := C) hcomparison_surj)
        hflatC_R
    have hflatMulBC_alg : (algebraMap (C ⊗[B] C) C).Flat :=
      RingHom.flat_algebraMap_iff.mpr hflatMulBC_module
    simpa [RingHom.algebraMap_toAlgebra] using hflatMulBC_alg
  -- These are exactly the two clauses in the definition of weak étaleness over `B`.
  exact
    { moduleFlat := RingHom.flat_algebraMap_iff.mp hBC_flat
      flat_tensorSquareMultiplication := hflatMulBC }

end

end IsWeaklyEtale
end Algebra
