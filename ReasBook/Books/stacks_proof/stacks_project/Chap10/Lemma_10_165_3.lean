import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_165_2
import stacks_proof.stacks_project.Chap10.Lemma_10_164_3
import stacks_proof.stacks_project.Chap10.Lemma_10_165_5
import stacks_proof.stacks_project.Chap10.Lemma_10_37_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Algebra

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]
variable {B : Type w} [CommRing B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- Lemma 10.165.3: a localization of a geometrically normal `k`-algebra is geometrically normal. -/
-- Proof sketch: for any field extension `K/k`, the scalar extension `K ⊗[k] B` is a localization
-- of `K ⊗[k] A`; since normality is checked on prime localizations, localizing a normal ring
-- remains normal.
@[stacks 06DE]
theorem IsGeometricallyNormal.of_isLocalization (S : Submonoid A) [IsLocalization S B]
    [IsGeometricallyNormal k A] : IsGeometricallyNormal k B := by
  refine { isNormalRing_baseChange := ?_ }
  intro K instK instKA
  letI := instK
  letI := instKA
  haveI : IsNormalRing K := by infer_instance
  letI : IsNormalRing (TensorProduct k A K) := by infer_instance
  let e₀ : TensorProduct k A K ≃ₐ[k] TensorProduct k K A := Algebra.TensorProduct.comm k A K
  let f₀ : TensorProduct k K A →+* TensorProduct k A K := e₀.symm.toRingHom
  have hf₀ : RingHom.FaithfullyFlat f₀ := by
    let hbij : Function.Bijective f₀ := e₀.symm.bijective
    exact RingHom.FaithfullyFlat.of_bijective hbij
  letI : IsNormalRing (TensorProduct k K A) := isNormalRing_of_faithfullyFlat f₀ hf₀
  letI : Algebra A (TensorProduct k K A) := Algebra.TensorProduct.rightAlgebra
  letI : IsLocalization (Algebra.algebraMapSubmonoid (TensorProduct k K A) S)
      (TensorProduct A (TensorProduct k K A) B) := by
    infer_instance
  letI : IsNormalRing (TensorProduct A (TensorProduct k K A) B) :=
    isNormalRing_of_isLocalization (Algebra.algebraMapSubmonoid (TensorProduct k K A) S)
  let e : TensorProduct A (TensorProduct k K A) B ≃ₐ[K] TensorProduct k K B :=
    Algebra.IsPushout.cancelBaseChangeAlg k K A (TensorProduct k K A) B
  letI : CommRing (TensorProduct k K B) := inferInstance
  letI : CommRing (TensorProduct A (TensorProduct k K A) B) := inferInstance
  let f : TensorProduct k K B →+* TensorProduct A (TensorProduct k K A) B := e.symm.toRingHom
  have hf : RingHom.FaithfullyFlat f := by
    let hbij : Function.Bijective f := e.symm.bijective
    exact RingHom.FaithfullyFlat.of_bijective hbij
  exact isNormalRing_of_faithfullyFlat f hf

end Algebra
