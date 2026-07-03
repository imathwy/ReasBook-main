import Mathlib
import StacksProject_2024.Chap15.Definition_15_59_13
import StacksProject_2024.Chap20.«20_14_1_1»
import StacksProject_2024.Chap20.Lemma_20_32_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The derived category `D(A)` for the global-sections ring `A = Γ(X, \mathcal O_X)`. -/
abbrev globalSectionsDerived (X : RingedSpace.{u}) :=
  DerivedCategory (ModuleCat (globalSectionsRing X))

/-- The restriction map `Γ(X, \mathcal O_X) → Γ(W, \mathcal O_X)` for an open subset `W ⊆ X`. -/
abbrev globalToOpenSectionsMap (X : RingedSpace.{u}) (W : Opens X.carrier) :
    globalSectionsRing X ⟶ sectionsRingOnOpen X W :=
  X.presheaf.map (TopologicalSpace.Opens.leTop W).op

/-- Restriction of scalars from `Γ(W, \mathcal O_X)` to `Γ(X, \mathcal O_X)`. -/
abbrev openSectionsRestrictionFunctor (X : RingedSpace.{u}) (W : Opens X.carrier) :
    ModuleCat (sectionsRingOnOpen X W) ⥤ ModuleCat (globalSectionsRing X) :=
  ModuleCat.restrictScalars (globalToOpenSectionsMap X W).hom

/-- Restriction of scalars along `Γ(X, \mathcal O_X) → Γ(W, \mathcal O_X)` is additive. -/
instance openSectionsRestrictionFunctor_additive (X : RingedSpace.{u}) (W : Opens X.carrier) :
    (openSectionsRestrictionFunctor X W).Additive := by
  infer_instance

/-- The derived restriction-of-scalars functor from `D(Γ(W, \mathcal O_X))` to `D(Γ(X, \mathcal
O_X))`. -/
abbrev openSectionsRestrictionDerived (X : RingedSpace.{u}) (W : Opens X.carrier) :
    DerivedCategory (ModuleCat (sectionsRingOnOpen X W)) ⥤ globalSectionsDerived X :=
  let F := ExactFunctor.of (openSectionsRestrictionFunctor X W)
  let _ : F.obj.Additive := openSectionsRestrictionFunctor_additive X W
  F.obj.mapDerivedCategory

/-- The open-sections functor `RΓ(W, -)` viewed in `D(Γ(X, \mathcal O_X))` via restriction of
scalars. -/
abbrev moduleDerivedSectionsOverGlobal (X : RingedSpace.{u}) (W : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤ globalSectionsDerived X :=
  moduleDerivedSectionsAtOpen X W ⋙ openSectionsRestrictionDerived X W

/-- The object `RΓ(X, K)` in `D(Γ(X, \mathcal O_X))`. -/
abbrev derivedGlobalSectionsObject (X : RingedSpace.{u}) (K : DerivedCategory (RingedSpace.Modules X)) :
    globalSectionsDerived X :=
  (moduleDerivedGlobalSections X).obj K

/-- The object `RΓ(W, K)` viewed in `D(Γ(X, \mathcal O_X))`. -/
abbrev derivedOpenSectionsOverGlobalObject (X : RingedSpace.{u}) (W : Opens X.carrier)
    (K : DerivedCategory (RingedSpace.Modules X)) : globalSectionsDerived X :=
  (moduleDerivedSectionsOverGlobal X W).obj K

/-- The middle Mayer-Vietoris term
`RΓ(U, K) \oplus RΓ(V, K)` viewed over `Γ(X, \mathcal O_X)`. -/
abbrev derivedOpenSectionsBiprodOverGlobalObject (X : RingedSpace.{u})
    (U V : Opens X.carrier) (K : DerivedCategory (RingedSpace.Modules X)) :
    globalSectionsDerived X :=
  derivedOpenSectionsOverGlobalObject X U K ⊞
    derivedOpenSectionsOverGlobalObject X V K

/-- The intersection Mayer-Vietoris term `RΓ(U ∩ V, K)` viewed over `Γ(X, \mathcal O_X)`. -/
abbrev derivedOpenSectionsIntersectionOverGlobalObject (X : RingedSpace.{u})
    (U V : Opens X.carrier) (K : DerivedCategory (RingedSpace.Modules X)) :
    globalSectionsDerived X :=
  derivedOpenSectionsOverGlobalObject X (U ⊓ V) K

/-- The Mayer-Vietoris triangle for `RΓ(-, E)` over the global-sections ring. -/
abbrev derivedSectionsMayerVietorisTriangle (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (E : DerivedCategory (RingedSpace.Modules X))
    (α : derivedGlobalSectionsObject X E ⟶
      derivedOpenSectionsBiprodOverGlobalObject X U V E)
    (β : derivedOpenSectionsBiprodOverGlobalObject X U V E ⟶
      derivedOpenSectionsIntersectionOverGlobalObject X U V E)
    (δ : derivedOpenSectionsIntersectionOverGlobalObject X U V E ⟶
      (derivedGlobalSectionsObject X E)⟦(1 : ℤ)⟧) :
    Triangle (globalSectionsDerived X) :=
  Triangle.mk α β δ

/-- The tensor-product object
`RΓ(X, K) \otimes_A^{\mathbf L} RΓ(X, M)` in `D(A)`. -/
abbrev derivedGlobalSectionsTensorObject (X : RingedSpace.{u})
    (K M : DerivedCategory (RingedSpace.Modules X)) : globalSectionsDerived X :=
  (CategoryTheory.derivedTensorProduct (derivedGlobalSectionsObject X K)).obj
    (derivedGlobalSectionsObject X M)

/-- The tensor-product object
`RΓ(X, K) \otimes_A^{\mathbf L} RΓ(W, M)` in `D(A)`. -/
abbrev derivedTensorOpenSectionsOverGlobalObject (X : RingedSpace.{u})
    (W : Opens X.carrier) (K M : DerivedCategory (RingedSpace.Modules X)) :
    globalSectionsDerived X :=
  (CategoryTheory.derivedTensorProduct (derivedGlobalSectionsObject X K)).obj
    (derivedOpenSectionsOverGlobalObject X W M)

/-- The tensor-product object
`RΓ(X, K) \otimes_A^{\mathbf L} (RΓ(U, M) \oplus RΓ(V, M))` in `D(A)`. -/
abbrev derivedTensorOpenSectionsBiprodOverGlobalObject (X : RingedSpace.{u})
    (U V : Opens X.carrier) (K M : DerivedCategory (RingedSpace.Modules X)) :
    globalSectionsDerived X :=
  (CategoryTheory.derivedTensorProduct (derivedGlobalSectionsObject X K)).obj
    (derivedOpenSectionsBiprodOverGlobalObject X U V M)

/-- A chosen derived tensor product `K \otimes_{\mathcal O_X}^{\mathbf L} M` in
`D(\mathcal O_X)`. -/
abbrev ringedSpaceDerivedTensorObject (X : RingedSpace.{u})
    (derivedTensorX :
      DerivedCategory (RingedSpace.Modules X) ⥤
        DerivedCategory (RingedSpace.Modules X) ⥤
          DerivedCategory (RingedSpace.Modules X))
    (K M : DerivedCategory (RingedSpace.Modules X)) : DerivedCategory (RingedSpace.Modules X) :=
  (derivedTensorX.obj M).obj K

/-- Applying the exact functor `RΓ(X, K) \otimes_A^{\mathbf L} -` to the Mayer-Vietoris triangle
for `M`. -/
abbrev tensorMayerVietorisSourceTriangle (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (K M : DerivedCategory (RingedSpace.Modules X))
    (α : derivedGlobalSectionsObject X M ⟶
      derivedOpenSectionsBiprodOverGlobalObject X U V M)
    (β : derivedOpenSectionsBiprodOverGlobalObject X U V M ⟶
      derivedOpenSectionsIntersectionOverGlobalObject X U V M)
    (δ : derivedOpenSectionsIntersectionOverGlobalObject X U V M ⟶
      (derivedGlobalSectionsObject X M)⟦(1 : ℤ)⟧) :
    Triangle (globalSectionsDerived X) :=
  ((CategoryTheory.derivedTensorProduct (derivedGlobalSectionsObject X K)).mapTriangle).obj
    (derivedSectionsMayerVietorisTriangle X U V M α β δ)

/-- The Mayer-Vietoris triangle for `K \otimes_{\mathcal O_X}^{\mathbf L} M`, viewed over
`Γ(X, \mathcal O_X)`. -/
abbrev tensorMayerVietorisTargetTriangle (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (derivedTensorX :
      DerivedCategory (RingedSpace.Modules X) ⥤
        DerivedCategory (RingedSpace.Modules X) ⥤
          DerivedCategory (RingedSpace.Modules X))
    (K M : DerivedCategory (RingedSpace.Modules X))
    (α : derivedGlobalSectionsObject X (ringedSpaceDerivedTensorObject X derivedTensorX K M) ⟶
      derivedOpenSectionsBiprodOverGlobalObject X U V
        (ringedSpaceDerivedTensorObject X derivedTensorX K M))
    (β : derivedOpenSectionsBiprodOverGlobalObject X U V
          (ringedSpaceDerivedTensorObject X derivedTensorX K M) ⟶
      derivedOpenSectionsIntersectionOverGlobalObject X U V
        (ringedSpaceDerivedTensorObject X derivedTensorX K M))
    (δ : derivedOpenSectionsIntersectionOverGlobalObject X U V
        (ringedSpaceDerivedTensorObject X derivedTensorX K M) ⟶
      (derivedGlobalSectionsObject X
        (ringedSpaceDerivedTensorObject X derivedTensorX K M))⟦(1 : ℤ)⟧) :
    Triangle (globalSectionsDerived X) :=
  derivedSectionsMayerVietorisTriangle X U V
    (ringedSpaceDerivedTensorObject X derivedTensorX K M) α β δ

section

variable {X : RingedSpace.{u}}

-- Proof sketch: choose the Mayer-Vietoris triangle for `M` over `Γ(X, \mathcal O_X)` and the
-- Mayer-Vietoris triangle for `K \otimes_{\mathcal O_X}^{\mathbf L} M`. The exact functor
-- `RΓ(X, K) \otimes_A^{\mathbf L} -` carries the first to a distinguished triangle, and the cup
-- product maps on `X`, `U`, `V`, and `U ∩ V` are compatible with restriction, so the two squares
-- on the first two rows and the square on the third row commute. These compatibilities assemble
-- into a morphism of triangles.
/-- Lemma 20.33.7: for a ringed space `(X, \mathcal O_X)` with `X = U ∪ V` and objects `K, M` of
`D(\mathcal O_X)`, there is a morphism from the distinguished triangle obtained by applying the
exact functor `RΓ(X, K) \otimes_{\Gamma(X,\mathcal O_X)}^{\mathbf L} -` to the Mayer-Vietoris
triangle for `M` to the Mayer-Vietoris distinguished triangle for
`K \otimes_{\mathcal O_X}^{\mathbf L} M`, for a chosen derived tensor-product bifunctor
`derivedTensorX`, whose components are the cup-product maps on `X`, `U ⊔ V`, and `U ∩ V`. -/
theorem derivedGlobalSections_tensor_mayerVietoris_triangle_morphism
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (derivedTensorX :
      DerivedCategory (RingedSpace.Modules X) ⥤
        DerivedCategory (RingedSpace.Modules X) ⥤
          DerivedCategory (RingedSpace.Modules X))
    (K M : DerivedCategory (RingedSpace.Modules X)) :
    ∃ (αM : derivedGlobalSectionsObject X M ⟶
          derivedOpenSectionsBiprodOverGlobalObject X U V M)
      (βM : derivedOpenSectionsBiprodOverGlobalObject X U V M ⟶
          derivedOpenSectionsIntersectionOverGlobalObject X U V M)
      (δM : derivedOpenSectionsIntersectionOverGlobalObject X U V M ⟶
          (derivedGlobalSectionsObject X M)⟦(1 : ℤ)⟧)
      (hM : derivedSectionsMayerVietorisTriangle X U V M αM βM δM ∈
          distTriang (globalSectionsDerived X))
      (αKM : derivedGlobalSectionsObject X
            (ringedSpaceDerivedTensorObject X derivedTensorX K M) ⟶
          derivedOpenSectionsBiprodOverGlobalObject X U V
            (ringedSpaceDerivedTensorObject X derivedTensorX K M))
      (βKM : derivedOpenSectionsBiprodOverGlobalObject X U V
            (ringedSpaceDerivedTensorObject X derivedTensorX K M) ⟶
          derivedOpenSectionsIntersectionOverGlobalObject X U V
            (ringedSpaceDerivedTensorObject X derivedTensorX K M))
      (δKM : derivedOpenSectionsIntersectionOverGlobalObject X U V
            (ringedSpaceDerivedTensorObject X derivedTensorX K M) ⟶
          (derivedGlobalSectionsObject X
            (ringedSpaceDerivedTensorObject X derivedTensorX K M))⟦(1 : ℤ)⟧)
      (hKM : tensorMayerVietorisTargetTriangle X U V derivedTensorX K M αKM βKM δKM ∈
          distTriang (globalSectionsDerived X))
      (cupX : derivedGlobalSectionsTensorObject X K M ⟶
          derivedGlobalSectionsObject X
            (ringedSpaceDerivedTensorObject X derivedTensorX K M))
      (cupUV : derivedTensorOpenSectionsBiprodOverGlobalObject X U V K M ⟶
          derivedOpenSectionsBiprodOverGlobalObject X U V
            (ringedSpaceDerivedTensorObject X derivedTensorX K M))
      (cupI : derivedTensorOpenSectionsOverGlobalObject X (U ⊓ V) K M ⟶
          derivedOpenSectionsIntersectionOverGlobalObject X U V
            (ringedSpaceDerivedTensorObject X derivedTensorX K M))
      (hLeft : tensorMayerVietorisSourceTriangle X U V K M αM βM δM ∈
          distTriang (globalSectionsDerived X)),
      ∃ φ : tensorMayerVietorisSourceTriangle X U V K M αM βM δM ⟶
          tensorMayerVietorisTargetTriangle X U V derivedTensorX K M αKM βKM δKM,
        ∃ hφ₁ : φ.hom₁ = cupX,
          ∃ hφ₂ : φ.hom₂ = cupUV, φ.hom₃ = cupI := sorry

end

end AlgebraicGeometry.RingedSpace
