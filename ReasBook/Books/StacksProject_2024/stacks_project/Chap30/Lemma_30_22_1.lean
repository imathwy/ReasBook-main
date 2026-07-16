import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»
import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap20.Lemma_20_27_1
import StacksProject_2024.stacks_project.Chap21.Remark_21_19_3_core
import StacksProject_2024.stacks_project.Chap29.Definition_29_25_1
import StacksProject_2024.stacks_project.Chap30.Lemma_30_7_2
import StacksProject_2024.stacks_project.Chap30.Lemma_30_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic search note: `lean_leansearch` timed out in this repair run. Local search found the Chapter
20 derived-global-sections owners `RingedSpace.moduleDerivedPushforward` and
`RingedSpace.moduleDerivedGlobalSections`, the Chapter 30 Cech representatives
`Scheme.pushforwardOpenCoverCechComplexInt`, and the Chapter 21 generic base-change owner
`CategoryTheory.derivedBaseChangeMap`. The labeled statements below use the cover-free
affine-base derived global-sections owner rather than cover-dependent Cech representatives. The
Stacks tag evidence is consistent for tag `07VK`. -/

/-- The affine-base global-sections functor preserves zero morphisms. This proof-only companion
instance keeps the canonical derived-functor infrastructure out of the source-facing statements. -/
instance affineBaseModuleSpecΓFunctor_preservesZeroMorphisms
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    (Scheme.Modules.pushforward f ⋙
      @moduleSpecΓFunctor (CommRingCat.of A)).PreservesZeroMorphisms := sorry

/-- The affine-base global-sections functor admits the total right derived functor used to define
cover-free affine-base derived global sections. -/
instance affineBaseModuleSpecΓFunctor_hasRightDerivedFunctor
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    Functor.HasRightDerivedFunctor
      (((Scheme.Modules.pushforward f ⋙ @moduleSpecΓFunctor (CommRingCat.of A)).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) := sorry

/-- The cover-free affine-base derived global-sections functor
`RΓ(X, -) : D(𝒪_X) ⥤ D(A)` for a morphism `X ⟶ Spec A`, defined as the total right derived
functor of affine global sections after direct image to `Spec A`. -/
abbrev affineBaseModuleDerivedGlobalSectionsFunctor
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [(Scheme.Modules.pushforward f ⋙
      @moduleSpecΓFunctor (CommRingCat.of A)).PreservesZeroMorphisms]
    [Functor.HasRightDerivedFunctor
      (((Scheme.Modules.pushforward f ⋙ @moduleSpecΓFunctor (CommRingCat.of A)).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))] :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat A) :=
  Functor.totalRightDerived
    (((Scheme.Modules.pushforward f ⋙ @moduleSpecΓFunctor (CommRingCat.of A)).mapHomologicalComplex
      (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    DerivedCategory.Q
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The defining normal form for the cover-free affine-base derived global-sections functor. -/
theorem affineBaseModuleDerivedGlobalSectionsFunctor_def
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [(Scheme.Modules.pushforward f ⋙
      @moduleSpecΓFunctor (CommRingCat.of A)).PreservesZeroMorphisms]
    [Functor.HasRightDerivedFunctor
      (((Scheme.Modules.pushforward f ⋙ @moduleSpecΓFunctor (CommRingCat.of A)).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))] :
    affineBaseModuleDerivedGlobalSectionsFunctor A f =
      Functor.totalRightDerived
        (((Scheme.Modules.pushforward f ⋙
              @moduleSpecΓFunctor (CommRingCat.of A)).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
        DerivedCategory.Q
        (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) := sorry

/-- The cover-free object `RΓ(X, ℱ)` in `D(A)` for `f : X ⟶ Spec A`. -/
abbrev affineBaseModuleDerivedGlobalSections
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [(Scheme.Modules.pushforward f ⋙
      @moduleSpecΓFunctor (CommRingCat.of A)).PreservesZeroMorphisms]
    [Functor.HasRightDerivedFunctor
      (((Scheme.Modules.pushforward f ⋙ @moduleSpecΓFunctor (CommRingCat.of A)).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))]
    (ℱ : X.Modules) :
    DerivedCategory (ModuleCat A) :=
  (affineBaseModuleDerivedGlobalSectionsFunctor A f).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)

/-- The defining normal form for `RΓ(X, ℱ)` over an affine base. -/
theorem affineBaseModuleDerivedGlobalSections_def
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [(Scheme.Modules.pushforward f ⋙
      @moduleSpecΓFunctor (CommRingCat.of A)).PreservesZeroMorphisms]
    [Functor.HasRightDerivedFunctor
      (((Scheme.Modules.pushforward f ⋙ @moduleSpecΓFunctor (CommRingCat.of A)).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))]
    (ℱ : X.Modules) :
    affineBaseModuleDerivedGlobalSections A f ℱ =
      (affineBaseModuleDerivedGlobalSectionsFunctor A f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ) := sorry

/-- The cover-free derived global sections of the base-changed module
`ℱ_{A'}` on `X ×_{Spec A} Spec A'`. -/
abbrev affineBaseChangedModuleDerivedGlobalSections
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [(Scheme.Modules.pushforward
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A A')))) ⋙
          @moduleSpecΓFunctor (CommRingCat.of A')).PreservesZeroMorphisms]
    [Functor.HasRightDerivedFunctor
      (((Scheme.Modules.pushforward
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A A')))) ⋙
            @moduleSpecΓFunctor (CommRingCat.of A')).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso
        (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap A A'))) : Scheme.{u}).Modules
        (ComplexShape.up ℤ))]
    (ℱ : X.Modules) :
    DerivedCategory (ModuleCat A') :=
  affineBaseModuleDerivedGlobalSections A'
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
    (Scheme.baseChangeModule f (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ℱ)

/-- The defining normal form for derived global sections after affine base change. -/
theorem affineBaseChangedModuleDerivedGlobalSections_def
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [(Scheme.Modules.pushforward
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A A')))) ⋙
          @moduleSpecΓFunctor (CommRingCat.of A')).PreservesZeroMorphisms]
    [Functor.HasRightDerivedFunctor
      (((Scheme.Modules.pushforward
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A A')))) ⋙
            @moduleSpecΓFunctor (CommRingCat.of A')).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso
        (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap A A'))) : Scheme.{u}).Modules
        (ComplexShape.up ℤ))]
    (ℱ : X.Modules) :
    affineBaseChangedModuleDerivedGlobalSections A A' f ℱ =
      affineBaseModuleDerivedGlobalSections A'
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
        (Scheme.baseChangeModule f (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ℱ) := sorry

/-- The affine morphism `Spec(A') ⟶ Spec(A)` induced by an `A`-algebra `A'`. -/
private abbrev affineBaseChangeSpecMap
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A'] :
    Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A A'))

/-- The projection `X ×_{Spec A} Spec A' ⟶ Spec(A')` from the affine base change of `f`. -/
private abbrev affineBaseChangedMorphism
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    (Limits.pullback f (affineBaseChangeSpecMap A A') : Scheme.{u}) ⟶ Spec (CommRingCat.of A') :=
  pullback.snd f (affineBaseChangeSpecMap A A')

/-- The affine-base derived global-sections functor is treated as a right adjoint when forming
the canonical affine-base base-change mate. -/
private theorem affineBaseModuleDerivedGlobalSectionsFunctor_isRightAdjoint
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    (affineBaseModuleDerivedGlobalSectionsFunctor A f).IsRightAdjoint := sorry

attribute [local instance] affineBaseModuleDerivedGlobalSectionsFunctor_isRightAdjoint

/-- The left adjoint used to form the affine-base derived global-sections base-change mate. -/
private abbrev affineBaseModuleDerivedPullbackFunctor
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    DerivedCategory (ModuleCat A) ⥤ DerivedCategory X.Modules :=
  (affineBaseModuleDerivedGlobalSectionsFunctor A f).leftAdjoint

/-- The adjunction behind affine-base derived global sections. -/
private abbrev affineBaseModuleDerivedGlobalSectionsAdjunction
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    affineBaseModuleDerivedPullbackFunctor A f ⊣
      affineBaseModuleDerivedGlobalSectionsFunctor A f :=
  Adjunction.ofIsRightAdjoint (affineBaseModuleDerivedGlobalSectionsFunctor A f)

/-- The derived pullback functor along `X ×_{Spec A} Spec A' ⟶ X`. -/
private abbrev affineBaseModuleDerivedBaseChangeFunctor
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    DerivedCategory X.Modules ⥤
      DerivedCategory (Limits.pullback f (affineBaseChangeSpecMap A A') : Scheme.{u}).Modules :=
  RingedSpace.modulePullbackDerived
    (pullback.fst f (affineBaseChangeSpecMap A A')).toLRSHom.toShHom

/-- The canonical comparison between the two affine-base pullback routes in the base-change
square. -/
private noncomputable def affineBaseModuleDerivedPullbackSquareIso
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    CategoryTheory.derivedTensorWithAlgebra (algebraMap A A') ⋙
        affineBaseModuleDerivedPullbackFunctor A' (affineBaseChangedMorphism A A' f) ≅
      affineBaseModuleDerivedPullbackFunctor A f ⋙
        affineBaseModuleDerivedBaseChangeFunctor A A' f := sorry

/-- The comparison from derived pullback of a degree-zero module to the degree-zero base-changed
module. -/
private noncomputable def affineBaseModuleDerivedBaseChangeSingleComparison
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    (ℱ : X.Modules) :
    (affineBaseModuleDerivedBaseChangeFunctor A A' f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ) ⟶
      (DerivedCategory.singleFunctor
        (Limits.pullback f (affineBaseChangeSpecMap A A') : Scheme.{u}).Modules
        0).obj
        (Scheme.baseChangeModule f (affineBaseChangeSpecMap A A') ℱ) := sorry

/-- The canonical affine-base base-change morphism
`RΓ(X, ℱ) ⊗_A^L A' ⟶ RΓ(X_{A'}, ℱ_{A'})`. -/
noncomputable def affineBaseModuleDerivedGlobalSectionsBaseChangeMap
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    (ℱ : X.Modules) :
    (CategoryTheory.derivedTensorWithAlgebra (algebraMap A A')).obj
        (affineBaseModuleDerivedGlobalSections A f ℱ) ⟶
      affineBaseChangedModuleDerivedGlobalSections A A' f ℱ :=
  CategoryTheory.derivedBaseChangeMap
      (affineBaseModuleDerivedPullbackFunctor A f)
      (affineBaseModuleDerivedPullbackFunctor A' (affineBaseChangedMorphism A A' f))
      (CategoryTheory.derivedTensorWithAlgebra (algebraMap A A'))
      (affineBaseModuleDerivedBaseChangeFunctor A A' f)
      (affineBaseModuleDerivedGlobalSectionsFunctor A f)
      (affineBaseModuleDerivedGlobalSectionsFunctor A' (affineBaseChangedMorphism A A' f))
      (affineBaseModuleDerivedGlobalSectionsAdjunction A f)
      (affineBaseModuleDerivedGlobalSectionsAdjunction A' (affineBaseChangedMorphism A A' f))
      (affineBaseModuleDerivedPullbackSquareIso A A' f)
      ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ) ≫
    (affineBaseModuleDerivedGlobalSectionsFunctor A'
      (affineBaseChangedMorphism A A' f)).map
        (affineBaseModuleDerivedBaseChangeSingleComparison A A' f ℱ)

/-- The defining expression for the canonical affine-base base-change morphism. -/
theorem affineBaseModuleDerivedGlobalSectionsBaseChangeMap_def
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    (ℱ : X.Modules) :
    affineBaseModuleDerivedGlobalSectionsBaseChangeMap A A' f ℱ =
      CategoryTheory.derivedBaseChangeMap
          (affineBaseModuleDerivedPullbackFunctor A f)
          (affineBaseModuleDerivedPullbackFunctor A' (affineBaseChangedMorphism A A' f))
          (CategoryTheory.derivedTensorWithAlgebra (algebraMap A A'))
          (affineBaseModuleDerivedBaseChangeFunctor A A' f)
          (affineBaseModuleDerivedGlobalSectionsFunctor A f)
          (affineBaseModuleDerivedGlobalSectionsFunctor A' (affineBaseChangedMorphism A A' f))
          (affineBaseModuleDerivedGlobalSectionsAdjunction A f)
          (affineBaseModuleDerivedGlobalSectionsAdjunction A' (affineBaseChangedMorphism A A' f))
          (affineBaseModuleDerivedPullbackSquareIso A A' f)
          ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ) ≫
        (affineBaseModuleDerivedGlobalSectionsFunctor A'
          (affineBaseChangedMorphism A A' f)).map
            (affineBaseModuleDerivedBaseChangeSingleComparison A A' f ℱ) := sorry

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
variable {X : Scheme.{u}}

/-- Lemma 30.22.1 (1): let `A` be Noetherian, `S = Spec(A)`, let `f : X ⟶ S` be proper, and
let `ℱ` be a coherent `𝒪_X`-module flat over `S`. Then the intrinsic affine-base derived
global-sections object `RΓ(X, ℱ)` is perfect in `D(A)`. -/
@[stacks 07VK]
theorem properFlatCoherent_affineBaseModuleDerivedGlobalSections_isPerfect
    [IsNoetherianRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (hflat : flatOver ℱ f) :
    (affineBaseModuleDerivedGlobalSections A f ℱ).IsPerfect := sorry

/-- Lemma 30.22.1 (2): under the hypotheses of Lemma 30.22.1, for every ring map
`A → A'`, the canonical base-change morphism
`RΓ(X, ℱ) ⊗_A^L A' ⟶ RΓ(X_{A'}, ℱ_{A'})` is an isomorphism. -/
@[stacks 07VK]
theorem properFlatCoherent_affineBaseModuleDerivedGlobalSections_baseChangeMap_isIso
    [IsNoetherianRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (hflat : flatOver ℱ f) :
    IsIso (affineBaseModuleDerivedGlobalSectionsBaseChangeMap A A' f ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
