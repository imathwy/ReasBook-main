import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_10
import StacksProject_2024.stacks_project.Chap15.Definition_15_105_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace Algebra

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/- Domain triage:
- primary domain: commutative algebra of faithfully flat descent for weakly étale ring maps;
- source-facing layer: part `(1)` is the tensor-square flatness descent statement appearing in the
  source text;
- core/canonical owners sampled for this file: `RingHom.FaithfullyFlat`,
  `flat_iff_flat_baseChange_of_faithfullyFlat`,
  `algebraMap_flat_of_flat_of_faithfullyFlat`, and the owner class `IsWeaklyEtale`;
- primitive data: faithful flatness of `B → C` and an explicit weakly étale owner proof on
  `A → C`;
- derived API: flatness of `A → B` and of the tensor-square multiplication `B ⊗[A] B → B`.

The file remains source-facing: there is no exact upstream owner theorem with this interface. The
refinement is to keep part `(1)` as the bridge theorem and expose part `(2)` as an owner theorem in
`IsWeaklyEtale`, matching the chapter's existing weakly étale API.
-/

-- Proof sketch: view `C ⊗[A] C → C` as the faithfully flat base change of
-- `B ⊗[A] B → B` along `B → C`. Then apply the flatness descent criterion of Lemma `10.39.9` to
-- descend flatness of `C` as a module over `C ⊗[A] C` to flatness of `B` as a module over
-- `B ⊗[A] B`.
/-- Lemma 15.105.10 (1): if `B → C` is faithfully flat and the multiplication map
`C ⊗[A] C → C` is flat, then the multiplication map `B ⊗[A] B → B` is flat. -/
theorem tensorSquareMul_flat_of_faithfullyFlat
    (hBC_ff : (algebraMap B C).FaithfullyFlat)
    (hflatMul : (lmul' A : C ⊗[A] C →ₐ[A] C).Flat) :
    (lmul' A : B ⊗[A] B →ₐ[A] B).Flat := by
  letI : Algebra (B ⊗[A] B) B := (lmul' A).toRingHom.toAlgebra
  letI : Algebra (B ⊗[A] B) C :=
    (((algebraMap B C).comp (lmul' A).toRingHom)).toAlgebra
  letI : IsScalarTower (B ⊗[A] B) B C := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.FaithfullyFlat B C := RingHom.faithfullyFlat_algebraMap_iff.mp hBC_ff
  -- First make `C` flat over `B ⊗[A] B` by factoring through `C ⊗[A] C`.
  let f : B →ₐ[A] C := IsScalarTower.toAlgHom A B C
  have hBC_flat : f.Flat := by
    simpa [f] using hBC_ff.flat
  have hbaseChange_flat :
      (Algebra.TensorProduct.map f f).toRingHom.Flat := by
    simpa [f] using RingHom.Flat.tensorProductMap hBC_flat hBC_flat
  have htarget_flat : (algebraMap (B ⊗[A] B) C).Flat := by
    have hcomp :
        (((lmul' A : C ⊗[A] C →ₐ[A] C).toRingHom).comp
          (Algebra.TensorProduct.map f f).toRingHom).Flat := by
      exact
        RingHom.Flat.comp
          hbaseChange_flat
          (show (lmul' A : C ⊗[A] C →ₐ[A] C).toRingHom.Flat from hflatMul)
    have hcomp_eq :
        ((lmul' A : C ⊗[A] C →ₐ[A] C).toRingHom).comp (Algebra.TensorProduct.map f f).toRingHom =
          (algebraMap B C).comp (lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom := by
      ext x <;> simp [f, mul_comm]
    rw [hcomp_eq] at hcomp
    simpa [RingHom.algebraMap_toAlgebra] using hcomp
  letI : Module.Flat (B ⊗[A] B) C := RingHom.flat_algebraMap_iff.mp htarget_flat
  have hrestrict_comm :
      ∀ x,
        (RestrictScalars.ringEquiv (B ⊗[A] B) B C)
            (algebraMap (B ⊗[A] B) (RestrictScalars (B ⊗[A] B) B C) x) =
          algebraMap (B ⊗[A] B) C x := by
    intro x
    simpa [RingHom.algebraMap_toAlgebra] using
      (RestrictScalars.ringEquiv_algebraMap (R := B ⊗[A] B) (S := B) (A := C) x)
  let e : RestrictScalars (B ⊗[A] B) B C ≃ₐ[B ⊗[A] B] C :=
    AlgEquiv.ofRingEquiv
      (f := RestrictScalars.ringEquiv (B ⊗[A] B) B C)
      hrestrict_comm
  letI : Module.Flat (B ⊗[A] B) (RestrictScalars (B ⊗[A] B) B C) :=
    Module.Flat.of_linearEquiv e.toLinearEquiv
  -- Then descend that flatness along the faithfully flat map `B → C`.
  have hsource_flat : (algebraMap (B ⊗[A] B) B).Flat :=
    algebraMap_flat_of_flat_of_faithfullyFlat C
  simpa [RingHom.algebraMap_toAlgebra] using hsource_flat

namespace IsWeaklyEtale

-- Proof sketch: weakly étale means flatness of `A → C` together with flatness of the
-- multiplication map `C ⊗[A] C → C`. Use the derived owner theorem `IsWeaklyEtale.flat` for
-- `A → C`, convert it back to the module-flat instance needed by Lemma `10.39.10`, and descend
-- along the faithfully flat map `B → C`. Then descend the tensor-square flatness by part `(1)`.
/-- Lemma 15.105.10 (2): if `B → C` is faithfully flat and `A → C` is weakly étale, then
`A → B` is weakly étale. -/
theorem of_faithfullyFlat
    (hBC_ff : (algebraMap B C).FaithfullyFlat)
    (hAC : IsWeaklyEtale A C) :
    IsWeaklyEtale A B := by
  letI : Module.FaithfullyFlat B C := RingHom.faithfullyFlat_algebraMap_iff.mp hBC_ff
  have hcomm :
      ∀ x, (RestrictScalars.ringEquiv A B C) (algebraMap A (RestrictScalars A B C) x) =
        algebraMap A C x := by
    intro x
    simpa [IsScalarTower.algebraMap_eq A B C] using
      (RestrictScalars.ringEquiv_algebraMap (R := A) (S := B) (A := C) x)
  let e : RestrictScalars A B C ≃ₐ[A] C :=
    AlgEquiv.ofRingEquiv
      (f := RestrictScalars.ringEquiv A B C)
      hcomm
  letI : Module.Flat A (RestrictScalars A B C) := Module.Flat.of_linearEquiv e.toLinearEquiv
  -- Descend flatness of the structure map `A → C` across the faithfully flat map `B → C`.
  have hAB_flat : (algebraMap A B).Flat := algebraMap_flat_of_flat_of_faithfullyFlat C
  -- The tensor-square flatness clause descends by part `(1)`.
  exact
    { moduleFlat := RingHom.flat_algebraMap_iff.mp hAB_flat
      flat_tensorSquareMultiplication :=
        tensorSquareMul_flat_of_faithfullyFlat hBC_ff hAC.flat_tensorSquareMultiplication }

end IsWeaklyEtale

end

end Algebra
