import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Mathlib.Tactic
import StacksProject_2024.Chap22.Lemma_22_13_1
import StacksProject_2024.Chap22.Lemma_22_13_3

open CochainComplex.HomComplex.Cochain

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "DGA" => CochainDGAlgebra R

/-
Source/core/bridge triage:
- `source-facing`: Remark 22.13.7, namely that the first-variable shift comparison
  `Hom^•(M^•, N^•)[-k] ⟶ Hom^•(M^•[k], N^•)` is compatible with the induced opposite-handed
  differential graded `A`-module structures on the internal Hom;
- `core/canonical`: `leftShiftLinearEquiv`, `CochainComplex.mapBifunctorShift₁Iso`, and the
  Chapter 22 fixed-underlying DG-module owners from Lemmas 22.13.1 and 22.13.3;
- `bridge/view`: this file packages the induced internal-Hom actions on the fixed Hom-complex
  underlying graded module so the shift comparison can be stated as an actual DG-module morphism.
-/

/-- The differential of a cochain complex in `ModuleCat R`, viewed as a family of linear maps. -/
private abbrev complexDLinear (M : CochainComplex (ModuleCat R) ℤ) :
    ∀ n : ℤ, M.X n →ₗ[R] M.X (n + 1) :=
  fun n ↦ (M.d n (n + 1)).hom

/-- The degree-`n` piece of `Hom^•(M, N)` as an `R`-module. -/
private abbrev homComplexFamily (M N : CochainComplex (ModuleCat R) ℤ) (n : ℤ) : ModuleCat R :=
  ModuleCat.of R (CochainComplex.HomComplex.Cochain M N n)

/-- The Hom-complex differential on `Hom^•(M, N)`. -/
private abbrev homComplexD (M N : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    homComplexFamily M N n →ₗ[R] homComplexFamily M N (n + 1) :=
  CochainComplex.HomComplex.δ_hom R M N n (n + 1)

/-- The degree-`n` piece of the shifted Hom complex `Hom^•(M, N)[-k]`. -/
private abbrev shiftedHomComplexFamily
    (M N : CochainComplex (ModuleCat R) ℤ) (k n : ℤ) : ModuleCat R :=
  homComplexFamily M N (n - k)

/-- The differential on `Hom^•(M, N)[-k]`. -/
private def shiftedHomComplexD
    (M N : CochainComplex (ModuleCat R) ℤ) (k n : ℤ) :
    shiftedHomComplexFamily M N k n →ₗ[R] shiftedHomComplexFamily M N k (n + 1) :=
  castLinearMap
    (congrArg (homComplexFamily M N) (by omega))
    (((-k).negOnePow : R) • homComplexD M N (n - k))

/-- The degree-`i` action cochain on `M` induced by a fixed-underlying left differential graded
`A`-module structure on `M`. -/
private abbrev leftModuleActionCochain
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (i : ℤ) (a : A.X i) :
    CochainComplex.HomComplex.Cochain M M i :=
  mk fun p q hpq ↦
    ModuleCat.ofHom <|
      castLinearMap (congrArg M.X (by rw [← hpq, add_comm])) (rho.toEndomorphismDGAHom.map i a p)

/-- The degree-`i` action cochain on `M` induced by a fixed-underlying right differential graded
`A`-module structure on `M`. -/
private abbrev rightModuleActionCochain
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (i : ℤ) (a : A.X i) :
    CochainComplex.HomComplex.Cochain M M i :=
  mk fun p q hpq ↦
    ModuleCat.ofHom <|
      castLinearMap (congrArg M.X (by rw [← hpq, add_comm])) (rho.toEndomorphismDGAHom.map i a p)

/-- The shifted degree-`i` action cochain on `M⟦k⟧` induced from a left differential graded
`A`-module structure on `M`. -/
private abbrev leftModuleActionShiftCochain
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k i : ℤ) (a : A.X i) :
    CochainComplex.HomComplex.Cochain (M⟦k⟧) (M⟦k⟧) i :=
  (leftModuleActionCochain rho i a).shift k

/-- The shifted degree-`i` action cochain on `M⟦k⟧` induced from a right differential graded
`A`-module structure on `M`. -/
private abbrev rightModuleActionShiftCochain
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k i : ℤ) (a : A.X i) :
    CochainComplex.HomComplex.Cochain (M⟦k⟧) (M⟦k⟧) i :=
  (rightModuleActionCochain rho i a).shift k

/-- A left differential graded `A`-module structure on `M` induces the opposite-handed
endomorphism-DGA map on `Hom^•(M, N)`. -/
private def internalHomRightEndomorphismDGAHomOfLeft
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M)) :
    EndomorphismDGAHom A.opposite
      (homComplexFamily M N) (homComplexD M N) where
  map i :=
    { toFun := fun a p ↦
        { toFun := fun f ↦
            (leftModuleActionCochain rho i a).comp f (by omega)
          map_add' := by
            sorry
          map_smul' := by
            sorry }
      map_add' := by
        sorry
      map_smul' := by
        sorry }
  map_one := by
    sorry
  map_mul := by
    sorry
  comm_d := by
    sorry

/-- The induced right differential graded `A`-module structure on `Hom^•(M, N)`. -/
private def internalHomRightDGModuleWithFixedUnderlyingOfLeft
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M)) :
    DifferentialGradedModule.WithFixedUnderlying A
      (homComplexFamily M N) (homComplexD M N) :=
  DifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom
    (internalHomRightEndomorphismDGAHomOfLeft N rho)

/-- Reindexing the induced right action gives the right differential graded `A`-module structure
on `Hom^•(M, N)[-k]`. -/
private def shiftedInternalHomRightEndomorphismDGAHomOfLeft
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    EndomorphismDGAHom A.opposite
      (shiftedHomComplexFamily M N k) (shiftedHomComplexD M N k) where
  map i :=
    { toFun := fun a p ↦
        castLinearMap
          (congrArg (homComplexFamily M N) (by omega))
          ((internalHomRightEndomorphismDGAHomOfLeft N rho).map i a (p - k))
      map_add' := by
        sorry
      map_smul' := by
        sorry }
  map_one := by
    sorry
  map_mul := by
    sorry
  comm_d := by
    sorry

/-- The induced right differential graded `A`-module structure on `Hom^•(M, N)[-k]`. -/
private def shiftedInternalHomRightDGModuleWithFixedUnderlyingOfLeft
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    DifferentialGradedModule.WithFixedUnderlying A
      (shiftedHomComplexFamily M N k) (shiftedHomComplexD M N k) :=
  DifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom
    (shiftedInternalHomRightEndomorphismDGAHomOfLeft N rho k)

/-- The shifted source complex `M⟦k⟧` carries the induced right differential graded
`A`-module structure on `Hom^•(M⟦k⟧, N)`. -/
private def shiftedSourceInternalHomRightEndomorphismDGAHomOfLeft
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    EndomorphismDGAHom A.opposite
      (homComplexFamily (M⟦k⟧) N) (homComplexD (M⟦k⟧) N) where
  map i :=
    { toFun := fun a p ↦
        { toFun := fun f ↦
            (leftModuleActionShiftCochain rho k i a).comp f (by omega)
          map_add' := by
            sorry
          map_smul' := by
            sorry }
      map_add' := by
        sorry
      map_smul' := by
        sorry }
  map_one := by
    sorry
  map_mul := by
    sorry
  comm_d := by
    sorry

/-- The induced right differential graded `A`-module structure on `Hom^•(M⟦k⟧, N)`. -/
private def shiftedSourceInternalHomRightDGModuleWithFixedUnderlyingOfLeft
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    DifferentialGradedModule.WithFixedUnderlying A
      (homComplexFamily (M⟦k⟧) N) (homComplexD (M⟦k⟧) N) :=
  DifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom
    (shiftedSourceInternalHomRightEndomorphismDGAHomOfLeft N rho k)

/-- A right differential graded `A`-module structure on `M` induces the opposite-handed
endomorphism-DGA map on `Hom^•(M, N)`. -/
private def internalHomLeftEndomorphismDGAHomOfRight
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M)) :
    EndomorphismDGAHom A (homComplexFamily M N) (homComplexD M N) where
  map i :=
    { toFun := fun a p ↦
        { toFun := fun f ↦
            (rightModuleActionCochain rho i a).comp f (by omega)
          map_add' := by
            sorry
          map_smul' := by
            sorry }
      map_add' := by
        sorry
      map_smul' := by
        sorry }
  map_one := by
    sorry
  map_mul := by
    sorry
  comm_d := by
    sorry

/-- The induced left differential graded `A`-module structure on `Hom^•(M, N)`. -/
private def internalHomLeftDGModuleWithFixedUnderlyingOfRight
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M)) :
    LeftDifferentialGradedModule.WithFixedUnderlying A
      (homComplexFamily M N) (homComplexD M N) :=
  LeftDifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom
    (internalHomLeftEndomorphismDGAHomOfRight N rho)

/-- Reindexing the induced left action gives the left differential graded `A`-module structure
on `Hom^•(M, N)[-k]`. -/
private def shiftedInternalHomLeftEndomorphismDGAHomOfRight
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    EndomorphismDGAHom A (shiftedHomComplexFamily M N k) (shiftedHomComplexD M N k) where
  map i :=
    { toFun := fun a p ↦
        castLinearMap
          (congrArg (homComplexFamily M N) (by omega))
          ((internalHomLeftEndomorphismDGAHomOfRight N rho).map i a (p - k))
      map_add' := by
        sorry
      map_smul' := by
        sorry }
  map_one := by
    sorry
  map_mul := by
    sorry
  comm_d := by
    sorry

/-- The induced left differential graded `A`-module structure on `Hom^•(M, N)[-k]`. -/
private def shiftedInternalHomLeftDGModuleWithFixedUnderlyingOfRight
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    LeftDifferentialGradedModule.WithFixedUnderlying A
      (shiftedHomComplexFamily M N k) (shiftedHomComplexD M N k) :=
  LeftDifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom
    (shiftedInternalHomLeftEndomorphismDGAHomOfRight N rho k)

/-- The shifted source complex `M⟦k⟧` carries the induced left differential graded
`A`-module structure on `Hom^•(M⟦k⟧, N)`. -/
private def shiftedSourceInternalHomLeftEndomorphismDGAHomOfRight
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    EndomorphismDGAHom A (homComplexFamily (M⟦k⟧) N) (homComplexD (M⟦k⟧) N) where
  map i :=
    { toFun := fun a p ↦
        { toFun := fun f ↦
            (rightModuleActionShiftCochain rho k i a).comp f (by omega)
          map_add' := by
            sorry
          map_smul' := by
            sorry }
      map_add' := by
        sorry
      map_smul' := by
        sorry }
  map_one := by
    sorry
  map_mul := by
    sorry
  comm_d := by
    sorry

/-- The induced left differential graded `A`-module structure on `Hom^•(M⟦k⟧, N)`. -/
private def shiftedSourceInternalHomLeftDGModuleWithFixedUnderlyingOfRight
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    LeftDifferentialGradedModule.WithFixedUnderlying A
      (homComplexFamily (M⟦k⟧) N) (homComplexD (M⟦k⟧) N) :=
  LeftDifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom
    (shiftedSourceInternalHomLeftEndomorphismDGAHomOfRight N rho k)

/-- The induced right differential graded `A`-module on `Hom^•(M^•, N^•)[-k]`. -/
abbrev shiftedInternalHomRightDGModuleOfLeft
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    RightDifferentialGradedModule A :=
  (shiftedInternalHomRightDGModuleWithFixedUnderlyingOfLeft N rho k).toRightDifferentialGradedModule

/-- The induced right differential graded `A`-module on `Hom^•(M^•⟦k⟧, N^•)`. -/
abbrev shiftedSourceInternalHomRightDGModuleOfLeft
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    RightDifferentialGradedModule A :=
  (shiftedSourceInternalHomRightDGModuleWithFixedUnderlyingOfLeft N rho k).toRightDifferentialGradedModule

/-- The induced left differential graded `A`-module on `Hom^•(M^•, N^•)[-k]`. -/
abbrev shiftedInternalHomLeftDGModuleOfRight
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    LeftDifferentialGradedModule A :=
  (shiftedInternalHomLeftDGModuleWithFixedUnderlyingOfRight N rho k).toLeftDifferentialGradedModule

/-- The induced left differential graded `A`-module on `Hom^•(M^•⟦k⟧, N^•)`. -/
abbrev shiftedSourceInternalHomLeftDGModuleOfRight
    {A : DGA} {M : CochainComplex (ModuleCat R) ℤ}
    (N : CochainComplex (ModuleCat R) ℤ)
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    LeftDifferentialGradedModule A :=
  (shiftedSourceInternalHomLeftDGModuleWithFixedUnderlyingOfRight N rho k).toLeftDifferentialGradedModule

/-- Remark 22.13.7, left-module case: the first-variable shift comparison
`Hom^•(M^•, N^•)[-k] ⟶ Hom^•(M^•[k], N^•)` is a morphism of the induced right differential
graded `A`-module structures. -/
@[stacks 0FQ9]
def leftShiftInternalHomRightDGModuleHom
    {A : DGA} {M N : CochainComplex (ModuleCat R) ℤ}
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    shiftedInternalHomRightDGModuleOfLeft N rho k ⟶
      shiftedSourceInternalHomRightDGModuleOfLeft N rho k where
  hom n := (leftShiftLinearEquiv R M N (n - k) k n (by omega)).toLinearMap
  comm_d := by
    intro n f
    sorry
  comm_smul := by
    intro p i f a
    sorry

/-- Remark 22.13.7, right-module case: the first-variable shift comparison
`Hom^•(M^•, N^•)[-k] ⟶ Hom^•(M^•[k], N^•)` is a morphism of the induced left differential
graded `A`-module structures. -/
@[stacks 0FQ9]
def leftShiftInternalHomLeftDGModuleHom
    {A : DGA} {M N : CochainComplex (ModuleCat R) ℤ}
    (rho : DifferentialGradedModule.WithFixedUnderlying A
      (fun n ↦ M.X n) (complexDLinear M))
    (k : ℤ) :
    shiftedInternalHomLeftDGModuleOfRight N rho k ⟶
      shiftedSourceInternalHomLeftDGModuleOfRight N rho k where
  hom n := (leftShiftLinearEquiv R M N (n - k) k n (by omega)).toLinearMap
  comm_d := by
    intro n f
    sorry
  comm_smul := by
    intro p i a f
    sorry

end
