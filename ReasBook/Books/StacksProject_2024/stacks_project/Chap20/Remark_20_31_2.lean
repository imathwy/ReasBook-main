import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap21.Lemma_21_33_1_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

local notation "ModX" => Modules X
local notation "ModΓX" => ModuleCat (globalSectionsRing X)
local notation "DModX" => DerivedCategory ModX
local notation "DΓX" => DerivedCategory ModΓX
local notation "singleΓX" => DerivedCategory.singleFunctor ModΓX
local notation "ΓOX" => ModuleCat.of (globalSectionsRing X) (globalSectionsRing X)

/- Domain-style sampling for Remark 20.31.2:
- primary domain: the global-sections specialization of relative derived cup products on a ringed
  space, with a chosen shift-tensor identification for the coefficient class;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `Adjunction.homEquiv`,
  `DerivedCategory.singleFunctor`;
- source/core/bridge triage:
  `source-facing`: the morphism obtained by cupping a class
    `ξ : Γ(X, O_X)[-i] ⟶ RΓ(X, K)` with `RΓ(X, M)`, for a chosen right-adjoint realization
    `derivedGlobalSections` of `RΓ(X,-)`;
  `core/canonical`: `CategoryTheory.relativeDerivedCupProduct`;
  `bridge/view`: the present specialization using the chosen isomorphism
    `RΓ(X, M)[-i] ≅ Γ(X, O_X)[-i] ⊗^L_A RΓ(X, M)`.

Primitive data here are only the representative `ξ` and the chosen shift-tensor identification.
The cup product itself is already owned by the canonical categorical declaration, so this file
should keep only a theorem-level source-facing bridge to that owner, not a second morphism-valued
API. -/

/-- Remark 20.31.2: a representative `ξ : Γ(X, 𝒪_X)[-i] ⟶ RΓ(X, K)` determines the composite
`RΓ(X, M)[-i] ⟶ RΓ(X, K ⊗^L_{𝒪_X} M)` obtained from the chosen shift-tensor identification, the
tensor image of `ξ`, and the canonical relative derived cup product. Transposing that composite
across `leftDerivedPullback ⊣ derivedGlobalSections` recovers the same three ingredients on the
pullback side. Its induced map on cohomology is cup product by `ξ`. -/
@[stacks 0G6W]
theorem derivedGlobalSections_leftCupBy_spec
    (derivedGlobalSections : DModX ⥤ DΓX)
    (leftDerivedPullback : DΓX ⥤ DModX)
    (globalSectionsAdj : Adjunction leftDerivedPullback derivedGlobalSections)
    (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
    (derivedTensorΓ : DΓX ⥤ DΓX ⥤ DΓX)
    (pullbackTensorIso :
      ∀ (A B : DΓX),
        leftDerivedPullback.obj ((derivedTensorΓ.obj B).obj A) ≅
          ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj (leftDerivedPullback.obj A)))
    (K M : DModX)
    (i : ℤ)
    (shiftTensorIso :
      (derivedGlobalSections.obj M)⟦-i⟧ ≅
        (derivedTensorΓ.obj (derivedGlobalSections.obj M)).obj
          ((singleΓX (-i)).obj ΓOX))
    (ξ :
      ((singleΓX (-i)).obj ΓOX) ⟶
        derivedGlobalSections.obj K) :
    ((globalSectionsAdj.homEquiv
        ((derivedGlobalSections.obj M)⟦-i⟧)
        ((derivedTensorX.obj M).obj K)).symm
      (shiftTensorIso.hom ≫
        (derivedTensorΓ.obj (derivedGlobalSections.obj M)).map ξ ≫
          relativeDerivedCupProduct leftDerivedPullback derivedGlobalSections globalSectionsAdj
            derivedTensorX derivedTensorΓ pullbackTensorIso K M)) =
      leftDerivedPullback.map shiftTensorIso.hom ≫
        leftDerivedPullback.map
          ((derivedTensorΓ.obj (derivedGlobalSections.obj M)).map ξ) ≫
        relativeDerivedCupProductAdjointMap
          leftDerivedPullback derivedGlobalSections globalSectionsAdj
          derivedTensorX derivedTensorΓ pullbackTensorIso K M := by
  rw [globalSectionsAdj.homEquiv_naturality_left_symm shiftTensorIso.hom]
  rw [globalSectionsAdj.homEquiv_naturality_left_symm
    ((derivedTensorΓ.obj (derivedGlobalSections.obj M)).map ξ)]
  rw [relativeDerivedCupProduct_spec leftDerivedPullback derivedGlobalSections globalSectionsAdj
    derivedTensorX derivedTensorΓ pullbackTensorIso K M]

end

end AlgebraicGeometry.RingedSpace
