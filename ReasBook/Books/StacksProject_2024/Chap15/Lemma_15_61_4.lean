import Mathlib
import StacksProject_2024.Chap15.Lemma_15_61_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R R' A B : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra R R']

-- Proof sketch: apply the Chapter 15 comparison morphism
-- `torBaseChangeComparison : Tor_i^R(A, B) ⊗[R] R' → Tor_i^{R'}(A ⊗[R] R', B ⊗[R] R')`,
-- specialized to the identity on `A ⊗[R] R'` and the canonical commutation map
-- `R' ⊗[R] B ≅ B ⊗[R] R'`, then use Definition 15.61.1 to reduce to the vanishing of the
-- original positive Tor groups.
/-- Lemma 15.61.4: if `A` and `B` are Tor independent over `R` and `R → R'` is flat, then
`A ⊗[R] R'` and `B ⊗[R] R'` are Tor independent over `R'`. -/
theorem IsTorIndependent.baseChange
    (h : IsTorIndependent R A B) [Module.Flat R R'] :
    IsTorIndependent R' (A ⊗[R] R') (B ⊗[R] R') := by
  intro p hp
  let aMap : A ⊗[R] R' →ₐ[R'] A ⊗[R] R' := AlgHom.id R' (A ⊗[R] R')
  let bMap : R' ⊗[R] B →ₐ[R'] B ⊗[R] R' := (Algebra.TensorProduct.commRight R R' B).toAlgHom
  have haFlat :
      letI : Algebra (A ⊗[R] R') (A ⊗[R] R') := aMap.toAlgebra
      Module.Flat (A ⊗[R] R') (A ⊗[R] R') := by
    exact Module.Flat.of_free
  have hbFlat :
      letI : Algebra (R' ⊗[R] B) (B ⊗[R] R') := bMap.toAlgebra
      Module.Flat (R' ⊗[R] B) (B ⊗[R] R') := by
    let e : R' ⊗[R] B ≃ₐ[R'] B ⊗[R] R' := Algebra.TensorProduct.commRight R R' B
    letI : Algebra (R' ⊗[R] B) (B ⊗[R] R') := bMap.toAlgebra
    let eLinear : B ⊗[R] R' ≃ₗ[R' ⊗[R] B] R' ⊗[R] B :=
      { __ := e.symm.toEquiv
        map_add' := e.symm.map_add
        map_smul' := by
          intro s x
          change e.symm (e s * x) = s * e.symm x
          simp }
    letI : Module.Flat (R' ⊗[R] B) (R' ⊗[R] B) := Module.Flat.of_free
    exact Module.Flat.of_linearEquiv eLinear
  let f := torBaseChangeComparison aMap bMap p
  letI : IsIso f := torBaseChangeComparison_isIso aMap bMap p hp haFlat hbFlat
  exact IsZero.of_iso
    ((ModuleCat.extendScalars (algebraMap R R')).map_isZero
      (h p hp))
    (asIso f).symm

end
