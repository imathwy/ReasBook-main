import StacksProject_2024.Chap15.«15_60_1_1»

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CommRingCat
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

local instance restrictScalars_preservesFiniteLimits
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars f) := by
  sorry

local instance restrictScalars_preservesFiniteColimits
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars f) := by
  sorry

/-- Restriction of scalars along `R_{n + 1} → R_n`, lifted to derived categories. -/
abbrev sequentialRingedModuleTransitionFunctor
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (σ : ∀ n, R (n + 1) →+* R n) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (R n)) ⥤
      DerivedCategory (ModuleCat.{u} (R (n + 1))) :=
  (ModuleCat.restrictScalars (σ n)).mapDerivedCategory

/-- A compatible stagewise tower in derived module categories over a sequential inverse system of
commutative rings. This is the shared bridge/view layer for Chapter 15 stagewise arguments. -/
structure DerivedModuleTower
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (σ : ∀ n, R (n + 1) →+* R n) where
  /-- The stage `n` object of the tower. -/
  obj (n : ℕ) : DerivedCategory (ModuleCat.{u} (R n))
  /-- The transition morphism from stage `n + 1` to stage `n`, viewed after restriction of
  scalars along `R_{n + 1} → R_n`. -/
  stepMap (n : ℕ) :
    obj (n + 1) ⟶ (sequentialRingedModuleTransitionFunctor R σ n).obj (obj n)

namespace DerivedModuleTower

section LimitRestriction

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u})

/-- The `n`th ring `A_n` in a sequential inverse system of commutative rings. -/
abbrev stageRing (n : ℕ) : Type u :=
  (F.obj (op n) : Type u)

/-- The transition ring map `A_{n + 1} → A_n` in a sequential inverse system. -/
abbrev stageTransitionRingHom (n : ℕ) : stageRing F (n + 1) →+* stageRing F n :=
  (F.map (homOfLE (Nat.le_succ n)).op).hom

/-- The inverse limit ring `A = \varprojlim_n A_n` of the sequential inverse system. -/
abbrev inverseLimitRing : Type u :=
  ((limit F : CommRingCat.{u}) : Type u)

/-- The canonical projection `A → A_n` from the inverse limit ring to the `n`th stage. -/
abbrev limitProjectionRingHom (n : ℕ) : inverseLimitRing F →+* stageRing F n :=
  (limit.π F (op n)).hom

/-- Each stage ring is naturally an algebra over the inverse limit ring. -/
instance instAlgebraInverseLimitRingStageRing (n : ℕ) :
    Algebra (inverseLimitRing F) (stageRing F n) :=
  RingHom.toAlgebra (limitProjectionRingHom F n)

/-- Each transition ring map endows `A_n` with its natural `A_{n + 1}`-algebra structure. -/
instance instAlgebraStageSuccStage (n : ℕ) :
    Algebra (stageRing F (n + 1)) (stageRing F n) :=
  RingHom.toAlgebra (stageTransitionRingHom F n)

/-- The `n`th stage object viewed over a fixed base ring `S` by restriction of scalars
along `S → A_n`. -/
abbrev stageRestrictionToBase
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} S) :=
  (ModuleCat.restrictScalars (algebraMap S (stageRing F n))).mapDerivedCategory.obj (T.obj n)

/-- The stagewise derived base change
`K_{n + 1} \otimes_{A_{n + 1}}^{\mathbf L} A_n`
of a compatible tower along `A_{n + 1} → A_n`. -/
abbrev stageDerivedBaseChange
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (stageRing F n)) :=
  (derivedTensorWithAlgebra (stageTransitionRingHom F n)).obj (T.obj (n + 1))

/-- The derived base change
`K \otimes_A^{\mathbf L} A_n`
of an inverse-limit object along the projection `A → A_n`. -/
abbrev inverseLimitBaseChange
    (K : DerivedCategory (ModuleCat.{u} (inverseLimitRing F))) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (stageRing F n)) :=
  (derivedTensorWithAlgebra (limitProjectionRingHom F n)).obj K

private theorem stageRestrictionToBase_algebraMap_comp
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (n : ℕ) :
    algebraMap S (stageRing F n) =
      (stageTransitionRingHom F n).comp (algebraMap S (stageRing F (n + 1))) := by
  ext x
  simp [RingHom.algebraMap_toAlgebra,
    IsScalarTower.algebraMap_apply S (stageRing F (n + 1)) (stageRing F n)]

private abbrev stageRestrictionToBaseFunctor
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    ModuleCat.{u} (stageRing F n) ⥤ ModuleCat.{u} S :=
  ModuleCat.restrictScalars (algebraMap S (stageRing F n))

private abbrev stageRestrictionToBaseDerivedFunctor
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (stageRing F n)) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  (stageRestrictionToBaseFunctor F S n).mapDerivedCategory

local instance stageRestrictionToBaseDerivedFunctor_isRightDerivedFunctor
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    (stageRestrictionToBaseDerivedFunctor F S n).IsRightDerivedFunctor
      ((stageRestrictionToBaseFunctor F S n).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso (ModuleCat.{u} (stageRing F n)) (ComplexShape.up ℤ)) := by
  simpa [stageRestrictionToBaseDerivedFunctor] using
    (Functor.isRightDerivedFunctor_of_inverts
      (HomologicalComplex.quasiIso (ModuleCat.{u} (stageRing F n)) (ComplexShape.up ℤ))
      (stageRestrictionToBaseDerivedFunctor F S n)
      ((stageRestrictionToBaseFunctor F S n).mapDerivedCategoryFactors))

private abbrev stageRestrictionToBaseThenTransitionFunctor
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    ModuleCat.{u} (stageRing F n) ⥤ ModuleCat.{u} S :=
  ModuleCat.restrictScalars (stageTransitionRingHom F n) ⋙
    stageRestrictionToBaseFunctor F S (n + 1)

private abbrev stageRestrictionToBaseThenTransitionDerivedFunctor
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (stageRing F n)) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  sequentialRingedModuleTransitionFunctor (stageRing F) (stageTransitionRingHom F) n ⋙
    stageRestrictionToBaseDerivedFunctor F S (n + 1)

private noncomputable abbrev stageRestrictionToBaseThenTransitionFactors
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    ((stageRestrictionToBaseThenTransitionFunctor F S n).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S))) ≅
      (((DerivedCategory.Q :
          CochainComplex (ModuleCat.{u} (stageRing F n)) ℤ ⥤
            DerivedCategory (ModuleCat.{u} (stageRing F n))) ⋙
        sequentialRingedModuleTransitionFunctor (stageRing F) (stageTransitionRingHom F) n) ⋙
          stageRestrictionToBaseDerivedFunctor F S (n + 1)) := by
  simpa [stageRestrictionToBaseFunctor, stageRestrictionToBaseDerivedFunctor,
      stageRestrictionToBaseThenTransitionFunctor,
      stageRestrictionToBaseThenTransitionDerivedFunctor,
      sequentialRingedModuleTransitionFunctor] using
    calc
      (stageRestrictionToBaseThenTransitionFunctor F S n).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S)) ≅
        (ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙
          ((stageRestrictionToBaseFunctor F S (n + 1)).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Q :
                CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S))) :=
        Functor.associator
          ((ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapHomologicalComplex
            (ComplexShape.up ℤ))
          ((stageRestrictionToBaseFunctor F S (n + 1)).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S))
      _ ≅
          (ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapHomologicalComplex
              (ComplexShape.up ℤ) ⋙
            ((DerivedCategory.Q :
                CochainComplex (ModuleCat.{u} (stageRing F (n + 1))) ℤ ⥤
                  DerivedCategory (ModuleCat.{u} (stageRing F (n + 1)))) ⋙
              stageRestrictionToBaseDerivedFunctor F S (n + 1)) :=
        Functor.isoWhiskerLeft
          ((ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapHomologicalComplex
            (ComplexShape.up ℤ))
          (stageRestrictionToBaseFunctor F S (n + 1)).mapDerivedCategoryFactors.symm
      _ ≅
          (((ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapHomologicalComplex
                (ComplexShape.up ℤ)) ⋙
              (DerivedCategory.Q :
                CochainComplex (ModuleCat.{u} (stageRing F (n + 1))) ℤ ⥤
                  DerivedCategory (ModuleCat.{u} (stageRing F (n + 1))))) ⋙
            stageRestrictionToBaseDerivedFunctor F S (n + 1) :=
        (Functor.associator
          ((ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapHomologicalComplex
            (ComplexShape.up ℤ))
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{u} (stageRing F (n + 1))) ℤ ⥤
              DerivedCategory (ModuleCat.{u} (stageRing F (n + 1))))
          (stageRestrictionToBaseDerivedFunctor F S (n + 1))).symm
      _ ≅
          (((DerivedCategory.Q :
              CochainComplex (ModuleCat.{u} (stageRing F n)) ℤ ⥤
                DerivedCategory (ModuleCat.{u} (stageRing F n))) ⋙
            sequentialRingedModuleTransitionFunctor (stageRing F) (stageTransitionRingHom F) n) ⋙
              stageRestrictionToBaseDerivedFunctor F S (n + 1)) :=
        by
          simpa [sequentialRingedModuleTransitionFunctor] using
            Functor.isoWhiskerRight
              (ModuleCat.restrictScalars (stageTransitionRingHom F n)).mapDerivedCategoryFactors.symm
              (stageRestrictionToBaseDerivedFunctor F S (n + 1))

private theorem stageRestrictionToBaseThenTransitionDerived_isRightDerivedFunctor
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    (n : ℕ) :
    (stageRestrictionToBaseThenTransitionDerivedFunctor F S n).IsRightDerivedFunctor
      (stageRestrictionToBaseThenTransitionFactors F S n).hom
      (HomologicalComplex.quasiIso (ModuleCat.{u} (stageRing F n)) (ComplexShape.up ℤ)) := by
  sorry

private abbrev stageRestrictionToBaseCompIso
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (n : ℕ) :
    stageRestrictionToBaseFunctor F S n ≅
      stageRestrictionToBaseThenTransitionFunctor F S n := by
  simpa [stageRestrictionToBaseFunctor, stageRestrictionToBaseThenTransitionFunctor] using
    (ModuleCat.restrictScalarsComp'
      (algebraMap S (stageRing F (n + 1)))
      (stageTransitionRingHom F n)
      (algebraMap S (stageRing F n))
      (stageRestrictionToBase_algebraMap_comp F S n))

private noncomputable abbrev stageRestrictionToBaseCompIsoOnComplexes
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (n : ℕ) :
    (stageRestrictionToBaseFunctor F S n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S)) ≅
      (stageRestrictionToBaseThenTransitionFunctor F S n).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S)) :=
  Functor.isoWhiskerRight
    (CategoryTheory.NatIso.mapHomologicalComplex
      (stageRestrictionToBaseCompIso F S n) (ComplexShape.up ℤ))
    (DerivedCategory.Q :
      CochainComplex (ModuleCat.{u} S) ℤ ⥤ DerivedCategory (ModuleCat.{u} S))

private noncomputable abbrev stageRestrictionToBaseDerivedIso
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (n : ℕ) :
    stageRestrictionToBaseDerivedFunctor F S n ≅
      stageRestrictionToBaseThenTransitionDerivedFunctor F S n := by
  letI := stageRestrictionToBaseThenTransitionDerived_isRightDerivedFunctor F S n
  exact Functor.rightDerivedNatIso
    (stageRestrictionToBaseDerivedFunctor F S n)
    (stageRestrictionToBaseThenTransitionDerivedFunctor F S n)
    ((stageRestrictionToBaseFunctor F S n).mapDerivedCategoryFactors.inv)
    (stageRestrictionToBaseThenTransitionFactors F S n).hom
    (HomologicalComplex.quasiIso (ModuleCat.{u} (stageRing F n)) (ComplexShape.up ℤ))
    (stageRestrictionToBaseCompIsoOnComplexes F S n)

private noncomputable abbrev stageRestrictionToBaseStep
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    stageRestrictionToBase F S T (n + 1) ⟶ stageRestrictionToBase F S T n := by
  simpa [stageRestrictionToBase, stageRestrictionToBaseDerivedFunctor] using
    (stageRestrictionToBaseDerivedFunctor F S (n + 1)).map (T.stepMap n) ≫
      (stageRestrictionToBaseDerivedIso F S n).inv.app (T.obj n)

/-- The canonical fixed-base inverse system in `D(S)` attached to `T`, obtained by restricting
each stage `T.obj n ∈ D(A_n)` along the chosen base maps `S → A_n`. -/
abbrev stageRestrictionToBaseTower
    (S : Type u) [CommRing S] [∀ n, Algebra S (stageRing F n)]
    [∀ n, IsScalarTower S (stageRing F (n + 1)) (stageRing F n)]
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat S) :=
  Functor.ofOpSequence (stageRestrictionToBaseStep F S T)

private theorem limitProjectionRingHom_comp (n : ℕ) :
    limitProjectionRingHom F n =
      (stageTransitionRingHom F n).comp (limitProjectionRingHom F (n + 1)) := by
  ext x
  simpa [stageTransitionRingHom, limitProjectionRingHom] using congrArg
    (fun f : limit F ⟶ F.obj (op n) ↦ f x)
    ((limit.w F ((homOfLE (Nat.le_succ n)).op)).symm)

local instance limitProjection_isScalarTower (n : ℕ) :
    IsScalarTower (inverseLimitRing F) (stageRing F (n + 1)) (stageRing F n) :=
  by
    apply IsScalarTower.of_algebraMap_eq'
    simpa [RingHom.algebraMap_toAlgebra] using limitProjectionRingHom_comp F n

/-- The `n`th stage object viewed over the inverse limit ring `A` by restriction of scalars
along `A → A_n`. -/
abbrev stageRestrictionToLimit
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (inverseLimitRing F)) :=
  stageRestrictionToBase F (inverseLimitRing F) T n

/-- The canonical fixed-base inverse system in `D(A)` attached to `T`, obtained by restricting
each stage `T.obj n ∈ D(A_n)` along the projection `A = \varprojlim_n A_n → A_n`. -/
abbrev stageRestrictionToLimitTower
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat (inverseLimitRing F)) :=
  stageRestrictionToBaseTower F (inverseLimitRing F) T

end LimitRestriction

end DerivedModuleTower

end
