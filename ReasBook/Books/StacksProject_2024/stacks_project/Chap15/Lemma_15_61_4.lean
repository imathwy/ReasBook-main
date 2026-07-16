import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_76_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_61_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R R' A B : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra R R']

/-- Helper for Lemma 15.61.4: a linear equivalence of modules induces an isomorphism in
`ModuleCat`. -/
private noncomputable def moduleCatIsoOfLinearEquiv
    {S : Type u} [CommRing S] {M N : Type u} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (e : M ≃ₗ[S] N) :
    ModuleCat.of S M ≅ ModuleCat.of S N where
  hom := ModuleCat.ofHom e.toLinearMap
  inv := ModuleCat.ofHom e.symm.toLinearMap

/-- Helper for Lemma 15.61.4: restricting scalars on the ring viewed as a module does not change
its underlying linear object. -/
private noncomputable def restrictScalarsSelfEquiv
    (T : Type u) [CommRing T] [Algebra R T] :
    ↑((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)) ≃ₗ[T] T :=
  { __ := AddEquiv.refl T
    map_smul' := fun _ _ ↦ rfl }

/-- Helper for Lemma 15.61.4: the restricted scalar action on a ring module still forms a scalar
tower over the base ring. -/
private instance restrictScalarsSelfIsScalarTower
    (T : Type u) [CommRing T] [Algebra R T] :
    IsScalarTower R T ↑((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Lemma 15.61.4: extension of scalars on an `R`-module is the usual tensor product
with `R'`. -/
private noncomputable def extend_scalars_obj_iso
    (M : Type u) [AddCommGroup M] [Module R M] :
    (ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R M) ≅
      ModuleCat.of R' (R' ⊗[R] M) :=
  moduleCatIsoOfLinearEquiv
    (TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsSelfEquiv (R := R) R')
      (LinearEquiv.refl R M))

/-- Helper for Lemma 15.61.4: the Chapter 10 target written using `extendScalars` agrees with the
tensor-product presentation `R' ⊗[R] -` on both Tor variables. -/
private noncomputable def tor_extend_scalars_iso
    (p : ℕ) :
    (((Tor (ModuleCat R') p).obj
        ((ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R A))).obj
      ((ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R B))) ≅
      (((Tor (ModuleCat R') p).obj (ModuleCat.of R' (R' ⊗[R] A))).obj
        (ModuleCat.of R' (R' ⊗[R] B))) :=
  let eA :
      (ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R A) ≅
        ModuleCat.of R' (R' ⊗[R] A) :=
    extend_scalars_obj_iso (R := R) (R' := R') A
  let eB :
      (ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R B) ≅
        ModuleCat.of R' (R' ⊗[R] B) :=
    extend_scalars_obj_iso (R := R) (R' := R') B
  ((Tor (ModuleCat R') p).mapIso eA).app _ ≪≫ (((Tor (ModuleCat R') p).obj _).mapIso eB)

/-- Helper for Lemma 15.61.4: after commuting the tensor factors in each variable, the Chapter 10
base-changed Tor object becomes the desired `Tor_p^{R'}(A ⊗[R] R', B ⊗[R] R')`. -/
private noncomputable def tor_comm_right_iso
    (p : ℕ) :
    (((Tor (ModuleCat R') p).obj (ModuleCat.of R' (R' ⊗[R] A))).obj
      (ModuleCat.of R' (R' ⊗[R] B))) ≅
      Tor[R', p](A ⊗[R] R', B ⊗[R] R') :=
  let eA : ModuleCat.of R' (R' ⊗[R] A) ≅ ModuleCat.of R' (A ⊗[R] R') :=
    moduleCatIsoOfLinearEquiv ((Algebra.TensorProduct.commRight R R' A).toLinearEquiv)
  let eB : ModuleCat.of R' (R' ⊗[R] B) ≅ ModuleCat.of R' (B ⊗[R] R') :=
    moduleCatIsoOfLinearEquiv ((Algebra.TensorProduct.commRight R R' B).toLinearEquiv)
  ((Tor (ModuleCat R') p).mapIso eA).app _ ≪≫ (((Tor (ModuleCat R') p).obj _).mapIso eB)

/-- Helper for Lemma 15.61.4: positive Tor vanishing survives flat base change by transporting the
Chapter 10 flat base-change isomorphism and then commuting tensor factors. -/
private lemma positive_tor_vanishes_after_base_change
    (h : IsTorIndependent R A B) [Module.Flat R R'] (p : ℕ) (hp : 0 < p) :
    IsZero (Tor[R', p](A ⊗[R] R', B ⊗[R] R')) := by
  let f := torBaseChangeHom
    (algebraMap R R')
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (ModuleCat.of R A)
    (ModuleCat.of R B)
    p
  have hIso : IsIso f := flat_tor_base_change_map_isIso
    (algebraMap R R')
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
    A
    B
    p
  have hBase :
      IsZero
        ((((Tor (ModuleCat R') p).obj
            ((ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R A))).obj
          ((ModuleCat.extendScalars (algebraMap R R')).obj (ModuleCat.of R B)))) := by
    -- Extend scalars on the original vanishing Tor object, then apply the Chapter 10 isomorphism.
    exact IsZero.of_iso
      ((ModuleCat.extendScalars (algebraMap R R')).map_isZero (h p hp))
      (asIso f).symm
  have hTensor :
      IsZero
        ((((Tor (ModuleCat R') p).obj (ModuleCat.of R' (R' ⊗[R] A))).obj
          (ModuleCat.of R' (R' ⊗[R] B)))) := by
    -- Rewrite the `extendScalars` presentation as the usual tensor-product presentation.
    exact IsZero.of_iso hBase
      (tor_extend_scalars_iso (R := R) (R' := R') (A := A) (B := B) p).symm
  -- Commute the tensor factors to match the statement of the lemma.
  simpa using IsZero.of_iso hTensor
    (tor_comm_right_iso (R := R) (R' := R') (A := A) (B := B) p).symm

-- Proof sketch: apply Chapter 10 flat base change to `Tor_p^R(A, B)`, rewrite the two
-- `extendScalars` objects as `R' ⊗[R] A` and `R' ⊗[R] B`, commute tensor factors, and then use
-- Definition 15.61.1 to transfer the original Tor-vanishing.
/-- Lemma 15.61.4: if `A` and `B` are Tor independent over `R` and `R → R'` is flat, then
`A ⊗[R] R'` and `B ⊗[R] R'` are Tor independent over `R'`. -/
theorem IsTorIndependent.baseChange
    (h : IsTorIndependent R A B) [Module.Flat R R'] :
    IsTorIndependent R' (A ⊗[R] R') (B ⊗[R] R') := by
  intro p hp
  -- Reduce Tor independence to the vanishing of each positive Tor group after base change.
  exact positive_tor_vanishes_after_base_change
    (R := R) (R' := R') (A := A) (B := B) h p hp

end
