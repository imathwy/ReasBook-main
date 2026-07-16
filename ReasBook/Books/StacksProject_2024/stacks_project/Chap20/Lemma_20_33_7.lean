import StacksProject_2024.stacks_project.Chap15.Definition_15_59_13
import StacksProject_2024.stacks_project.Chap20.Definition_20_26_14
import StacksProject_2024.stacks_project.Chap20.Lemma_20_33_4
import StacksProject_2024.stacks_project.Chap21.Lemma_21_33_1_core
import StacksProject_2024.stacks_project.Chap20.Sections_on_open_global
import StacksProject_2024.stacks_project.Chap20.OpensInstances

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry
open scoped DerivedTensorProduct
open scoped RingedSpaceDerivedTensor

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.33.7:
- primary domain: compatibility between Mayer-Vietoris distinguished triangles on derived sections
  and the canonical relative derived cup-product comparison maps;
- sampled owner declarations:
  `moduleDerivedGlobalSections`,
  `moduleDerivedSectionsOverGlobal`,
  `derivedGlobalSections_mayerVietoris_distinguishedTriangle`,
  `moduleDerivedSectionsOverGlobalMayerVietorisToBiprod`,
  `moduleDerivedSectionsOverGlobalMayerVietorisDifference`,
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.derivedTensorProduct`;
- best owner abstraction:
  `source-facing`: the over-global-scalar Mayer-Vietoris restriction and overlap-difference maps,
    together with a morphism of Mayer-Vietoris triangles for `M` and `M ⊗^L K` whose components
    are the canonical cup-product comparison maps on `X`, `U`, `V`, and `U ∩ V`;
  `core/canonical`: the Chapter 20 owners `moduleDerivedGlobalSections` and
    `moduleDerivedSectionsOverGlobal`, the categorical owner
  `CategoryTheory.relativeDerivedCupProduct`, the target tensor owner
  `CategoryTheory.derivedTensorProduct`, and the chapter-owned Mayer-Vietoris triangle shape on
  derived sections;
  `bridge/view`: the internal realization witnesses showing that the source-facing cup-product maps
    come from
    `CategoryTheory.relativeDerivedCupProduct`.
- primitive data: the cover `U ⊔ V = ⊤` and the objects `K`, `M`;
- derived API: the global cup-product map on `RΓ`, the theorem-local open cup-product bridge
  expressions on `RΓ[U]`, `RΓ[V]`, and `RΓ[U ∩ V]`, the source-facing over-global-scalar
  Mayer-Vietoris edge maps, the induced middle biproduct comparison map, and the corresponding
  Mayer-Vietoris triangle morphism. The adjunction/pullback-tensor realizations remain auxiliary
  witnesses behind these source-facing maps and the theorem below.

Source/core/bridge triage:
- `source-facing`: the morphism between the Mayer-Vietoris triangles for `M` and `M ⊗^L K`;
- `core/canonical`: `CategoryTheory.relativeDerivedCupProduct`,
  `moduleDerivedGlobalSections`, `moduleDerivedSectionsOverGlobal`,
  `derivedGlobalSections_mayerVietoris_distinguishedTriangle`, and
  `CategoryTheory.derivedTensorProduct`;
- `bridge/view`: restricting the coefficient factor from `RΓ(X, K)` to `RΓ(W, K)` before applying
  the local cup product on an open `W`, together with the realization predicates recording that a
  source-facing map is obtained from the generic `relativeDerivedCupProduct`.
-/

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DΓX" => DerivedCategory (ModuleCat (globalSectionsRing X))
local notation "RΓ" => moduleDerivedGlobalSections X
local notation "RΓ[" U "]" => moduleDerivedSectionsOverGlobal X U

section CupProductChoices

variable {U V : Opens X.carrier}

variable
  (leftDerivedPullbackX : DΓX ⥤ DModX)
  (globalSectionsAdj : leftDerivedPullbackX ⊣ RΓ)
  (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
  (derivedTensorΓ : DΓX ⥤ DΓX ⥤ DΓX)
  (pullbackTensorIsoX :
    ∀ A B : DΓX,
      leftDerivedPullbackX.obj ((derivedTensorΓ.obj B).obj A) ≅
        ((derivedTensorX.obj (leftDerivedPullbackX.obj B)).obj
          (leftDerivedPullbackX.obj A)))
  (leftDerivedPullbackU : DΓX ⥤ DModX)
  (sectionsOverGlobalAdjU : leftDerivedPullbackU ⊣ RΓ[U])
  (pullbackTensorIsoU :
    ∀ A B : DΓX,
      leftDerivedPullbackU.obj ((derivedTensorΓ.obj B).obj A) ≅
        ((derivedTensorX.obj (leftDerivedPullbackU.obj B)).obj
          (leftDerivedPullbackU.obj A)))
  (leftDerivedPullbackV : DΓX ⥤ DModX)
  (sectionsOverGlobalAdjV : leftDerivedPullbackV ⊣ RΓ[V])
  (pullbackTensorIsoV :
    ∀ A B : DΓX,
      leftDerivedPullbackV.obj ((derivedTensorΓ.obj B).obj A) ≅
        ((derivedTensorX.obj (leftDerivedPullbackV.obj B)).obj
          (leftDerivedPullbackV.obj A)))
  (leftDerivedPullbackUV : DΓX ⥤ DModX)
  (sectionsOverGlobalAdjUV : leftDerivedPullbackUV ⊣ RΓ[U ⊓ V])
  (pullbackTensorIsoUV :
    ∀ A B : DΓX,
      leftDerivedPullbackUV.obj ((derivedTensorΓ.obj B).obj A) ≅
        ((derivedTensorX.obj (leftDerivedPullbackUV.obj B)).obj
          (leftDerivedPullbackUV.obj A)))

-- Proof sketch: start from the Chapter 20 bridge
-- `derivedGlobalSections_mayerVietoris_distinguishedTriangle` for `M` and for `M ⊗^L K`, then
-- use the canonical `relativeDerivedCupProduct` directly on `RΓ(X,-)` and on the three
-- open-section owners `RΓ[U]`, `RΓ[V]`, and `RΓ[U ⊓ V]`, after restricting the coefficient factor
-- `RΓ(X, K)` to the relevant open. Combine the `U` and `V` components through the owner
-- `Functor.mapBiprod`.
/-- Lemma 20.33.7: for a ringed space `(X, 𝒪_X)` with `X = U ∪ V` and objects `K, M` of
`D(𝒪_X)`, choose tensor-functor owners `derivedTensorX` on `D(𝒪_X)` and `derivedTensorΓ` on
`D(Γ(X, 𝒪_X))` realizing the canonical derived tensor products, together with the usual
pullback-tensor comparison data for `RΓ(X,-)`, `RΓ(U,-)`, `RΓ(V,-)`, and `RΓ(U ∩ V,-)`.
Then the canonical cup-product comparison maps assemble into a morphism from the Mayer-Vietoris
triangle for `M`, after tensoring by `RΓ(X, K)` through `derivedTensorΓ`, to the Mayer-Vietoris
triangle for `((derivedTensorX.obj K).obj M)`. On each open term, the component map is the
restriction of the coefficient factor `RΓ(X, K)` to that open followed by the corresponding local
`relativeDerivedCupProduct`. -/
@[stacks 0G6X]
theorem derivedGlobalSections_tensor_mayerVietoris_triangle_morphism
    (U V : Opens X.carrier)
    (hUV : U ⊔ V = ⊤) (K M : DModX)
    [(derivedTensorΓ.obj ((RΓ).obj K)).CommShift ℤ] :
    ∃ δ δ' : RΓ[U ⊓ V] ⟶ RΓ ⋙ shiftFunctor DΓX (1 : ℤ),
      let sourceTriangle : Triangle DΓX :=
        Triangle.mk
          ((moduleDerivedSectionsOverGlobalMayerVietorisToBiprod X U V).app M)
          ((moduleDerivedSectionsOverGlobalMayerVietorisDifference X U V).app M)
          (δ.app M)
      let targetTriangle : Triangle DΓX :=
        Triangle.mk
          ((moduleDerivedSectionsOverGlobalMayerVietorisToBiprod X U V).app
            ((derivedTensorX.obj K).obj M))
          ((moduleDerivedSectionsOverGlobalMayerVietorisDifference X U V).app
            ((derivedTensorX.obj K).obj M))
          (δ'.app ((derivedTensorX.obj K).obj M))
      let openCupProduct := fun
          (W : Opens X.carrier)
          (leftDerivedPullbackW : DΓX ⥤ DModX)
          (sectionsOverGlobalAdjW : leftDerivedPullbackW ⊣ RΓ[W])
          (pullbackTensorIsoW :
            ∀ A B : DΓX,
              leftDerivedPullbackW.obj ((derivedTensorΓ.obj B).obj A) ≅
                ((derivedTensorX.obj (leftDerivedPullbackW.obj B)).obj
                  (leftDerivedPullbackW.obj A))) ↦
            ((derivedTensorΓ.map (moduleDerivedSectionsOverGlobalRestriction X W K)).app
                ((RΓ[W]).obj M)) ≫
              relativeDerivedCupProduct
                leftDerivedPullbackW
                (RΓ[W])
                sectionsOverGlobalAdjW
                derivedTensorX
                derivedTensorΓ
                pullbackTensorIsoW
                M
                K
      let biprodCupProduct :
          ((derivedTensorΓ.obj ((RΓ).obj K)).obj (((RΓ[U]).obj M) ⊞ ((RΓ[V]).obj M))) ⟶
            ((RΓ[U]).obj ((derivedTensorX.obj K).obj M)) ⊞
              ((RΓ[V]).obj ((derivedTensorX.obj K).obj M)) :=
        ((derivedTensorΓ.obj ((RΓ).obj K)).mapBiprod ((RΓ[U]).obj M) ((RΓ[V]).obj M)).hom ≫
          biprod.map
            (openCupProduct U leftDerivedPullbackU sectionsOverGlobalAdjU pullbackTensorIsoU)
            (openCupProduct V leftDerivedPullbackV sectionsOverGlobalAdjV pullbackTensorIsoV)
      sourceTriangle ∈ distTriang DΓX ∧
        targetTriangle ∈ distTriang DΓX ∧
        ∃ φ : (derivedTensorΓ.obj ((RΓ).obj K)).mapTriangle.obj sourceTriangle ⟶ targetTriangle,
          φ.hom₁ =
              relativeDerivedCupProduct
                leftDerivedPullbackX
                RΓ
                globalSectionsAdj
                derivedTensorX
                derivedTensorΓ
                pullbackTensorIsoX
                M
                K ∧
            φ.hom₂ = biprodCupProduct ∧
              φ.hom₃ =
                openCupProduct
                  (U ⊓ V)
                  leftDerivedPullbackUV
                  sectionsOverGlobalAdjUV
                  pullbackTensorIsoUV := sorry

end CupProductChoices

end

end AlgebraicGeometry.RingedSpace
