import Mathlib
import stacks_project.Chap13.Remark_13_10_9
import stacks_project.Chap20.Lemma_20_27_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Functor.OplaxMonoidal
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace}

/-- The localization functor from complexes to the homotopy category of `\mathcal O_X`-modules.
-/
private abbrev complexToHomotopy (X : RingedSpace) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
  HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ)

/-- The canonical functor from complexes of `\mathcal O_X`-modules to `D(\mathcal O_X)`. -/
private abbrev complexToDerived (X : RingedSpace) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X) :=
  complexToHomotopy X ⋙
    (DerivedCategory.Qh :
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X))

/-- Pullback of complexes of module sheaves along a morphism of ringed spaces. -/
private abbrev modulePullbackComplex {X Y : RingedSpace} (f : X ⟶ Y)
    [(modulePullback f).Additive] :
    CochainComplex (RingedSpace.Modules Y) ℤ ⥤ CochainComplex (RingedSpace.Modules X) ℤ :=
  (modulePullback f).mapHomologicalComplex (up ℤ)

/-- The canonical abelian structure on `\mathcal O_X`-modules. -/
local instance instAbelianSourceModules : Abelian (RingedSpace.Modules X) :=
  SheafOfModules.instAbelian (RingedSpace.ringCatSheaf X)

/-- The canonical abelian structure on `\mathcal O_Y`-modules. -/
local instance instAbelianTargetModules : Abelian (RingedSpace.Modules Y) :=
  SheafOfModules.instAbelian (RingedSpace.ringCatSheaf Y)

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor ((RingedSpace.Modules X))).Additive]
variable [∀ ℱ, ((curriedTensor ((RingedSpace.Modules X))).obj ℱ).Additive]
variable [∀ (ℱ 𝒢), CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ((RingedSpace.Modules X)))]

variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [MonoidalCategory (RingedSpace.Modules Y)]
variable [MonoidalPreadditive (RingedSpace.Modules Y)]
variable [HasColimits (RingedSpace.Modules Y)]
variable [(curriedTensor ((RingedSpace.Modules Y))).Additive]
variable [∀ ℱ, ((curriedTensor ((RingedSpace.Modules Y))).obj ℱ).Additive]
variable [∀ (ℱ 𝒢), CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ((RingedSpace.Modules Y)))]

section PullbackTensorCounitLadder

local infixr:70 " ⊗c " => HomologicalComplex.tensorObj

/-- The canonical counit comparing derived pullback of a complex with ordinary pullback of that
complex. -/
private abbrev modulePullbackCounitApp (f : X ⟶ Y) [(modulePullback f).Additive]
    (K : CochainComplex (RingedSpace.Modules Y) ℤ) :
    (modulePullbackDerived f).obj ((complexToDerived Y).obj K) ⟶
      (complexToDerived X).obj ((modulePullbackComplex f).obj K) :=
  ((modulePullbackToDerived f).totalLeftDerivedCounit DerivedCategory.Qh (ModuleQis Y)).app
    ((complexToHomotopy Y).obj K)

/-- Tensor-totalization on `K(\mathcal O_Y)` with fixed right factor `M^\bullet`. -/
private abbrev targetTensorHomotopyFunctorOfComplex
    (M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤
      HomotopyCategory (RingedSpace.Modules Y) (up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules Y) (up ℤ))
    ((((curriedTensor (RingedSpace.Modules Y)).map₂CochainComplex).flip.obj M) ⋙
      HomotopyCategory.quotient (RingedSpace.Modules Y) (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 M)
          (curriedTensor (RingedSpace.Modules Y)) (up ℤ)))

/-- The homotopy-category tensor functor with fixed right factor `M^\bullet`, followed by
localization to `D(\mathcal O_Y)`. -/
private abbrev targetDerivedTensorComplexSourceFunctor
    (M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  targetTensorHomotopyFunctorOfComplex M ⋙
    DerivedCategory.Qh

-- Proof sketch: choose K-flat resolutions of the varying left factor and use the same argument as
-- in Definition `20.26.14`, now with the fixed right factor given by the literal complex
-- `M^\bullet`.
/-- Tensoring on `K(\mathcal O_Y)` with a fixed complex `M^\bullet` admits a total left derived
functor. -/
private theorem targetDerivedTensorComplexSourceFunctor_hasLeftDerivedFunctor
    (M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    (targetDerivedTensorComplexSourceFunctor M).HasLeftDerivedFunctor (ModuleQis Y) := by
  sorry

/-- The derived tensor functor `- \otimes_{\mathcal O_Y}^{\mathbf L} M^\bullet` attached to a
fixed complex `M^\bullet`. -/
private abbrev targetDerivedTensorOfComplex
    (M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  letI := targetDerivedTensorComplexSourceFunctor_hasLeftDerivedFunctor M
  (targetDerivedTensorComplexSourceFunctor M).totalLeftDerived DerivedCategory.Qh (ModuleQis Y)

/-- The canonical counit from derived tensoring with a fixed right complex `M^\bullet` to the
ordinary tensor total complex `K^\bullet ⊗ M^\bullet`. -/
private abbrev targetTensorCounitApp
    (K M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    (targetDerivedTensorOfComplex M).obj ((complexToDerived Y).obj K) ⟶
      (complexToDerived Y).obj (K ⊗c M) :=
  letI := targetDerivedTensorComplexSourceFunctor_hasLeftDerivedFunctor M
  ((targetDerivedTensorComplexSourceFunctor M).totalLeftDerivedCounit
    DerivedCategory.Qh (ModuleQis Y)).app ((complexToHomotopy Y).obj K)

/-- Tensor-totalization on `K(\mathcal O_X)` with fixed right factor `M^\bullet`. -/
private abbrev sourceTensorHomotopyFunctorOfComplex
    (M : CochainComplex (RingedSpace.Modules X) ℤ) :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
    ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj M) ⋙
      HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 M)
          (curriedTensor (RingedSpace.Modules X)) (up ℤ)))

/-- The homotopy-category tensor functor with fixed right factor `M^\bullet`, followed by passage
to the derived category `D(\mathcal O_X)`. -/
private abbrev sourceDerivedTensorComplexSourceFunctor
    (M : CochainComplex (RingedSpace.Modules X) ℤ) :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  sourceTensorHomotopyFunctorOfComplex M ⋙
    (DerivedCategory.Qh :
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X))

-- Proof sketch: as on `Y`, fix the right complex `M^\bullet`, resolve the varying left factor by
-- K-flat complexes, and invoke the universal property of the total left derived functor.
/-- Tensoring on `K(\mathcal O_X)` with a fixed complex `M^\bullet` admits a total left derived
functor. -/
private theorem sourceDerivedTensorComplexSourceFunctor_hasLeftDerivedFunctor
    (M : CochainComplex (RingedSpace.Modules X) ℤ) :
    (sourceDerivedTensorComplexSourceFunctor M).HasLeftDerivedFunctor (ModuleQis X) := by
  sorry

/-- The derived tensor functor `- \otimes_{\mathcal O_X}^{\mathbf L} M^\bullet` attached to a
fixed complex `M^\bullet`. -/
private abbrev sourceDerivedTensorOfComplex
    (M : CochainComplex (RingedSpace.Modules X) ℤ) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  letI := sourceDerivedTensorComplexSourceFunctor_hasLeftDerivedFunctor M
  (sourceDerivedTensorComplexSourceFunctor M).totalLeftDerived
    (DerivedCategory.Qh :
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X))
    (ModuleQis X)

/-- The canonical counit from derived tensoring with a fixed right complex `M^\bullet` to the
ordinary tensor total complex `K^\bullet ⊗ M^\bullet`. -/
private abbrev sourceTensorCounitApp
    (K M : CochainComplex (RingedSpace.Modules X) ℤ) :
    (sourceDerivedTensorOfComplex M).obj ((complexToDerived X).obj K) ⟶
      (complexToDerived X).obj (K ⊗c M) :=
  letI := sourceDerivedTensorComplexSourceFunctor_hasLeftDerivedFunctor M
  ((sourceDerivedTensorComplexSourceFunctor M).totalLeftDerivedCounit
    (DerivedCategory.Qh :
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X))
    (ModuleQis X)).app ((complexToHomotopy X).obj K)

variable
  (f : X ⟶ Y) [(modulePullback f).Additive]

/-- The underived pullback-tensor comparison on total tensor complexes exists canonically. -/
private theorem underivedPullbackTensorComparison_nonempty :
    Nonempty
      (∀ (K M : CochainComplex (RingedSpace.Modules Y) ℤ),
        (complexToDerived X).obj ((modulePullbackComplex f).obj (K ⊗c M)) ⟶
      (complexToDerived X).obj
        (((modulePullbackComplex f).obj K) ⊗c ((modulePullbackComplex f).obj M))) := by
  sorry

/-- The canonical underived pullback-tensor comparison on total tensor complexes. -/
private noncomputable abbrev underivedPullbackTensorComparison
    (K M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    (complexToDerived X).obj ((modulePullbackComplex f).obj (K ⊗c M)) ⟶
      (complexToDerived X).obj
        (((modulePullbackComplex f).obj K) ⊗c ((modulePullbackComplex f).obj M)) :=
  Classical.choice (underivedPullbackTensorComparison_nonempty f) K M

-- Proof sketch: resolve the varying left factor by K-flat complexes, keep the literal right
-- complex `M^\bullet` fixed, and descend the underived pullback-tensor comparison to the derived
-- categories.
/-- The fixed-right-factor pullback-tensor comparison of Lemma `20.27.3`, specialized to a
literal right complex `M^\bullet`. -/
private theorem modulePullbackDerived_tensorComplex_iso_nonempty :
    Nonempty
      (∀ M : CochainComplex (RingedSpace.Modules Y) ℤ,
        targetDerivedTensorOfComplex M ⋙ modulePullbackDerived f ≅
          modulePullbackDerived f ⋙
            sourceDerivedTensorOfComplex ((modulePullbackComplex f).obj M)) := by
  sorry

/-- The fixed-right-factor pullback-tensor comparison of Lemma `20.27.3`, specialized to a
literal right complex `M^\bullet`. -/
private noncomputable abbrev modulePullbackDerived_tensorComplex_iso
    (M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    targetDerivedTensorOfComplex M ⋙ modulePullbackDerived f ≅
      modulePullbackDerived f ⋙
        sourceDerivedTensorOfComplex ((modulePullbackComplex f).obj M) :=
  Classical.choice (modulePullbackDerived_tensorComplex_iso_nonempty f) M

-- Proof sketch: choose K-flat resolutions of `K` and `M` as in Lemma `20.26.8`, so that
-- derived pullback and derived tensor product are computed by ordinary pullback and tensor
-- totalization on those resolutions. The top horizontal arrow is the component of the
-- pullback-tensor comparison of Lemma `20.27.3` for the fixed right factor `M^\bullet`, the left
-- and right vertical arrows are the canonical counits of the corresponding total left derived
-- tensor functors, the lower horizontal arrow is the canonical derived-pullback counit on
-- `Tot(K \otimes M)`, and the remaining comparison is the oplax-monoidal tensor comparison for
-- ordinary pullback on total tensor complexes. The resulting
-- resolution-level ladder commutes, and hence so does the descended ladder in the derived
-- categories.
/-- Lemma 20.27.5, as the outer `CommSq` of the source ladder.

For complexes `K^\bullet` and `M^\bullet`, the outer rectangle built from the canonical
pullback-tensor comparison of Lemma `20.27.3`, the canonical tensor counits, the canonical
derived-pullback counit, and the canonical underived pullback-tensor comparison on total tensor
complexes is commutative.
-/
theorem modulePullback_tensor_counit_commSq
    (K M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    CommSq
      ((modulePullbackDerived_tensorComplex_iso f M).hom.app ((complexToDerived Y).obj K))
      ((modulePullbackDerived f).map (targetTensorCounitApp K M))
      ((sourceDerivedTensorOfComplex ((modulePullbackComplex f).obj M)).map
          (modulePullbackCounitApp f K) ≫
        sourceTensorCounitApp ((modulePullbackComplex f).obj K)
          ((modulePullbackComplex f).obj M))
      (modulePullbackCounitApp f (K ⊗c M) ≫
        underivedPullbackTensorComparison f K M) := by
  sorry

/-- Equality form of Lemma 20.27.5, obtained by taking `.w` of the canonical `CommSq`
statement. -/
theorem modulePullback_tensor_counit_ladder_commutes
    (K M : CochainComplex (RingedSpace.Modules Y) ℤ) :
    (modulePullbackDerived f).map (targetTensorCounitApp K M) ≫
        modulePullbackCounitApp f (K ⊗c M) ≫
        underivedPullbackTensorComparison f K M =
      ((modulePullbackDerived_tensorComplex_iso f M).hom.app ((complexToDerived Y).obj K)) ≫
        (sourceDerivedTensorOfComplex ((modulePullbackComplex f).obj M)).map
            (modulePullbackCounitApp f K) ≫
          sourceTensorCounitApp ((modulePullbackComplex f).obj K)
            ((modulePullbackComplex f).obj M) :=
  by
    simpa using (modulePullback_tensor_counit_commSq f K M).w.symm

end PullbackTensorCounitLadder

end AlgebraicGeometry.RingedSpace
