import Mathlib
import StacksProject_2024.Chap20.«20_14_1_1»

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The unbounded derived category `D(\mathcal O_X)` of sheaves of modules on a ringed space. -/
abbrev ringedSpaceModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The inclusion of a closed subset into the ambient ringed space. -/
abbrev closedSubsetInclusion (X : RingedSpace.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction `\mathcal O_X|_Z` of the structure sheaf to a closed subset `Z ⊆ X`. -/
abbrev closedSubsetRestrictedRingCatSheaf
    (X : RingedSpace.{u}) (Z : Set X) : TopCat.Sheaf RingCat.{u} (TopCat.of Z) :=
  (TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj (RingedSpace.ringCatSheaf X)

/-- The category of `\mathcal O_X|_Z`-modules on the closed subset `Z`. -/
abbrev closedSubsetModuleCategory (X : RingedSpace.{u}) (Z : Set X) :=
  SheafOfModules (closedSubsetRestrictedRingCatSheaf X Z)

/-- The unbounded derived category `D(\mathcal O_X|_Z)` on the closed subset `Z`. -/
abbrev closedSubsetModuleDerived (X : RingedSpace.{u}) (Z : Set X) :=
  DerivedCategory (closedSubsetModuleCategory X Z)

/-- The unbounded derived category of abelian groups used for derived global sections. -/
abbrev abelianDerived :=
  DerivedCategory AddCommGrpCat.{u}

section

variable {X : RingedSpace.{u}} {Z : Set X}

local notation "DModX" => ringedSpaceModuleDerived X
local notation "DModZ" => closedSubsetModuleDerived X Z
local notation "DAb" => abelianDerived

variable (sectionsWithSupportDerived : DModX ⥤ DModZ)
variable (derivedGlobalSectionsOnClosedSubset : DModZ ⥤ DAb)
variable (derivedGlobalSections : DModX ⥤ DAb)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable
  (sectionsWithSupportGlobalSectionsToGlobalSections :
    sectionsWithSupportDerived ⋙ derivedGlobalSectionsOnClosedSubset ⟶ derivedGlobalSections)

/-- The degree-`n` global cohomology object `H^n(X, K)` computed by a chosen derived
global-sections functor. -/
abbrev derivedCohomology
    (n : ℤ) (K : DModX) : AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj (derivedGlobalSections.obj K)

/-- The degree-`n` cohomology object with support in `Z`, computed by applying derived global
sections on `Z` to the chosen sections-with-support object. -/
abbrev derivedCohomologyWithSupport
    (n : ℤ) (K : DModX) : AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
    ((sectionsWithSupportDerived ⋙ derivedGlobalSectionsOnClosedSubset).obj K)

-- Proof sketch: unfold `derivedCohomology`; it is defined by applying the degree-`n` homology
-- functor to the chosen derived global-sections object.
/-- The global cohomology object is the degree-`n` homology of the chosen derived global sections.
-/
theorem derivedCohomology_def
    (n : ℤ) (K : DModX) :
    derivedCohomology derivedGlobalSections n K =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj (derivedGlobalSections.obj K) :=
  sorry

-- Proof sketch: unfold `derivedCohomologyWithSupport`; it is defined as the degree-`n` homology
-- of the derived global sections on `Z` applied to the sections-with-support object.
/-- The cohomology-with-support object is the degree-`n` homology of supported derived global
sections. -/
theorem derivedCohomologyWithSupport_def
    (n : ℤ) (K : DModX) :
    derivedCohomologyWithSupport
        sectionsWithSupportDerived
        derivedGlobalSectionsOnClosedSubset
        n
        K =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((sectionsWithSupportDerived ⋙ derivedGlobalSectionsOnClosedSubset).obj K) := sorry

/-- The canonical map `H^n_Z(X, K) \to H^n(X, K)` induced by forgetting support on derived global
sections. -/
abbrev cohomologyWithSupportToCohomology
    (n : ℤ) (K : DModX) :
    derivedCohomologyWithSupport
        sectionsWithSupportDerived
        derivedGlobalSectionsOnClosedSubset
        n
        K ⟶
      derivedCohomology derivedGlobalSections n K :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
    (sectionsWithSupportGlobalSectionsToGlobalSections.app K)

-- Proof sketch: unfold `cohomologyWithSupportToCohomology`; it is defined by applying the degree
-- `n` homology functor to the comparison morphism from supported derived global sections to
-- ordinary derived global sections.
/-- The forget-support map on cohomology is obtained by applying the degree-`n` homology functor to
the comparison morphism on derived global sections. -/
theorem cohomologyWithSupportToCohomology_def
    (n : ℤ) (K : DModX) :
    cohomologyWithSupportToCohomology
        sectionsWithSupportDerived
        derivedGlobalSectionsOnClosedSubset
        derivedGlobalSections
        sectionsWithSupportGlobalSectionsToGlobalSections
        n
        K =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
        (sectionsWithSupportGlobalSectionsToGlobalSections.app K) := sorry

variable
  (withSupportCupProduct :
    ∀ (i j : ℤ) (K M : DModX),
      derivedCohomology derivedGlobalSections i K ⨯
          derivedCohomologyWithSupport
            sectionsWithSupportDerived
            derivedGlobalSectionsOnClosedSubset
            j
            M ⟶
        derivedCohomologyWithSupport
          sectionsWithSupportDerived
          derivedGlobalSectionsOnClosedSubset
          (i + j)
          ((derivedTensorX.obj M).obj K))
variable
  (globalCupProduct :
    ∀ (i j : ℤ) (K M : DModX),
      derivedCohomology derivedGlobalSections i K ⨯
          derivedCohomology derivedGlobalSections j M ⟶
        derivedCohomology derivedGlobalSections (i + j) ((derivedTensorX.obj M).obj K))

-- Proof sketch: the cup product with support from Remark `20.34.10` is defined by restricting
-- `K` to `Z`, taking the cup product on `Z`, and then applying the tensor comparison from
-- Remark `20.34.9`. Forgetting support before or after this construction uses the same comparison
-- morphism `RΓ_Z(X, -) ⟶ RΓ(X, -)`, so after passing to degree-`i`, degree-`j`, and
-- degree-`i + j` homology the two composites agree.
/-- Lemma 20.34.11: with the notation of Remarks 20.34.9 and 20.34.10, the square comparing the
cup product
`H^i(X, K) × H^j_Z(X, M) \to H^{i + j}_Z(X, K \otimes_{\mathcal O_X}^{\mathbf L} M)`
with the ordinary cup product
`H^i(X, K) × H^j(X, M) \to H^{i + j}(X, K \otimes_{\mathcal O_X}^{\mathbf L} M)`
commutes, where the vertical arrows are induced by the canonical maps
`H^j_Z(X, M) \to H^j(X, M)` and
`H^{i + j}_Z(X, K \otimes_{\mathcal O_X}^{\mathbf L} M) \to
  H^{i + j}(X, K \otimes_{\mathcal O_X}^{\mathbf L} M)`. -/
theorem cohomologyWithSupport_cupProduct_forgetSupport_commSq
    (i j : ℤ) (K M : DModX) :
    CommSq
      (withSupportCupProduct i j K M)
      (Limits.prod.map
        (𝟙 (derivedCohomology derivedGlobalSections i K))
        (cohomologyWithSupportToCohomology
          sectionsWithSupportDerived
          derivedGlobalSectionsOnClosedSubset
          derivedGlobalSections
          sectionsWithSupportGlobalSectionsToGlobalSections
          j
          M))
      (cohomologyWithSupportToCohomology
        sectionsWithSupportDerived
        derivedGlobalSectionsOnClosedSubset
        derivedGlobalSections
        sectionsWithSupportGlobalSectionsToGlobalSections
        (i + j)
        ((derivedTensorX.obj M).obj K))
      (globalCupProduct i j K M) := sorry

end

end AlgebraicGeometry.RingedSpace
