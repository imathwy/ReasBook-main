import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_20_34_10 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry

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

/-- The derived global-sections functor `RΓ(X, -)` after forgetting the module structure on
`Γ(X, \mathcal O_X)`. -/
abbrev derivedGlobalSectionsToAbelian (X : RingedSpace.{u}) :
    ringedSpaceModuleDerived X ⥤ abelianDerived :=
  moduleDerivedGlobalSections X ⋙
    (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory

-- Proof sketch: this is just the definition of `derivedGlobalSectionsToAbelian`; it is the usual
-- derived global-sections functor with the module structure on `Γ(X, \mathcal O_X)` forgotten.
/-- The abelian-valued derived global-sections functor is obtained by forgetting the ambient
module structure on `RΓ(X, -)`. -/
theorem derivedGlobalSectionsToAbelian_def (X : RingedSpace.{u}) :
    derivedGlobalSectionsToAbelian X =
      moduleDerivedGlobalSections X ⋙
        (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory := sorry

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

local notation "DModX" => ringedSpaceModuleDerived X
local notation "DModZ" => closedSubsetModuleDerived X Z
local notation "DAb" => abelianDerived

variable (restrictionToClosedSubset : DModX ⥤ DModZ)
variable (sectionsWithSupportDerived : DModX ⥤ DModZ)
variable (derivedGlobalSectionsOnClosedSubset : DModZ ⥤ DAb)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)
variable (derivedTensorAb : DAb ⥤ DAb ⥤ DAb)
variable
    (closedSubsetDerivedCupProduct :
      ∀ (A B : DModZ),
        ((derivedTensorAb.obj (derivedGlobalSectionsOnClosedSubset.obj B)).obj
          (derivedGlobalSectionsOnClosedSubset.obj A)) ⟶
          derivedGlobalSectionsOnClosedSubset.obj ((derivedTensorZ.obj B).obj A))
variable
    (sectionsWithSupportTensorMap :
      ∀ (K M : DModX),
        ((derivedTensorZ.obj (sectionsWithSupportDerived.obj M)).obj
          (restrictionToClosedSubset.obj K)) ⟶
          sectionsWithSupportDerived.obj ((derivedTensorX.obj M).obj K))

/-- Remark 20.34.10: with the notation of Remark 20.34.9, restriction of `K` to the closed
subset `Z`, the cup product on `Z`, and the canonical map
`K|_Z \otimes_{\mathcal O_X|_Z}^{\mathbf L} R\mathcal H_Z(M) \to
R\mathcal H_Z(K \otimes_{\mathcal O_X}^{\mathbf L} M)` determine a canonical morphism in
`D(\mathrm{Ab})`. Its degree-`a + b` homology is the cup product
`H^a(X, K) × H^b_Z(X, M) \to H^{a + b}_Z(X, K \otimes_{\mathcal O_X}^{\mathbf L} M)`, where the
equalities in the textbook are the comparison isomorphisms of Lemma 20.34.4. -/
noncomputable def closedSubsetRestriction_sectionsWithSupportDerived_cupProduct
    (restrictionToClosedSubsetGlobalSections :
      derivedGlobalSectionsToAbelian X ⟶
        restrictionToClosedSubset ⋙ derivedGlobalSectionsOnClosedSubset)
    (K M : DModX) :
    ((derivedTensorAb.obj
        (derivedGlobalSectionsOnClosedSubset.obj (sectionsWithSupportDerived.obj M))).obj
      ((derivedGlobalSectionsToAbelian X).obj K)) ⟶
      derivedGlobalSectionsOnClosedSubset.obj
        (sectionsWithSupportDerived.obj ((derivedTensorX.obj M).obj K)) :=
  match restrictionToClosedSubsetGlobalSections with
  | η =>
      ((derivedTensorAb.obj
          (derivedGlobalSectionsOnClosedSubset.obj (sectionsWithSupportDerived.obj M))).map
        (η.app K)) ≫
        closedSubsetDerivedCupProduct
          (restrictionToClosedSubset.obj K) (sectionsWithSupportDerived.obj M) ≫
        derivedGlobalSectionsOnClosedSubset.map (sectionsWithSupportTensorMap K M)

-- Proof sketch: unfold the definition. The morphism is defined as the composite of the map on
-- derived global sections induced by restricting `K` to `Z`, the closed-subset cup product on
-- `Z`, and the map obtained by applying derived global sections on `Z` to the sections-with-
-- support tensor comparison.
/-- The closed-subset cup-product morphism is the composite of restriction on derived global
sections, the cup product on the closed subset, and the map induced by the sections-with-support
tensor comparison. -/
theorem closedSubsetRestriction_sectionsWithSupportDerived_cupProduct_def
    (restrictionToClosedSubsetGlobalSections :
      derivedGlobalSectionsToAbelian X ⟶
        restrictionToClosedSubset ⋙ derivedGlobalSectionsOnClosedSubset)
    (K M : DModX) :
    closedSubsetRestriction_sectionsWithSupportDerived_cupProduct
        hZ restrictionToClosedSubset sectionsWithSupportDerived
        derivedGlobalSectionsOnClosedSubset derivedTensorX derivedTensorZ derivedTensorAb
        closedSubsetDerivedCupProduct sectionsWithSupportTensorMap
        restrictionToClosedSubsetGlobalSections K M =
      ((derivedTensorAb.obj
          (derivedGlobalSectionsOnClosedSubset.obj (sectionsWithSupportDerived.obj M))).map
        (restrictionToClosedSubsetGlobalSections.app K)) ≫
        closedSubsetDerivedCupProduct
          (restrictionToClosedSubset.obj K) (sectionsWithSupportDerived.obj M) ≫
        derivedGlobalSectionsOnClosedSubset.map (sectionsWithSupportTensorMap K M) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_34_11 (from Chap20) -/
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

/-! ### Remark_20_34_12 (from Chap20) -/
open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {DModX DModX' DModZ DModZ' : Type u}
variable [Category DModX] [Category DModX'] [Category DModZ] [Category DModZ']

-- Proof sketch: the source object lies in the supported full subcategory by `hsource`.
-- The adjunction `supportedProperty.ι ⊣ supportedRightAdjoint` therefore identifies morphisms
-- from this supported source to `pullbackDerived.obj K` with morphisms from the same source to
-- `supportedRightAdjoint.obj (pullbackDerived.obj K)`. Transport the resulting unique factor
-- across `supportedRightAdjointAmbientIso`, and then across the base-change isomorphism
-- `baseChangeIso`, to obtain the desired unique morphism on the closed subsets.
/-- Remark 20.34.12: suppose `i_* : D(\mathcal O_X|_Z) ⥤ D(\mathcal O_X)` is left adjoint to
`R\mathcal H_Z`, suppose `D_{Z'}(\mathcal O_{X'})` is realized as a full subcategory of
`D(\mathcal O_{X'})` whose right adjoint is identified with
`i'_* \circ R\mathcal H_{Z'}`, and suppose the usual base-change isomorphism
`Lf^* \circ i_* \cong i'_* \circ L(f|_{Z'})^*` has been fixed. Then for every `K`, once
`Lf^*(i_*R\mathcal H_Z(K))` is known to lie in `D_{Z'}(\mathcal O_{X'})`, there is a unique
morphism `L(f|_{Z'})^*R\mathcal H_Z(K) ⟶ R\mathcal H_{Z'}(Lf^*K)` whose pushforward along `i'_*`
is the factorization of `Lf^*(i_*R\mathcal H_Z(K)) ⟶ Lf^*K` through the universal map
`i'_*R\mathcal H_{Z'}(Lf^*K) ⟶ Lf^*K`. -/
theorem existsUnique_closedSubsetPullback_sectionsWithSupportDerived_map
    (iPushforwardDerived : DModZ ⥤ DModX)
    (i'PushforwardDerived : DModZ' ⥤ DModX')
    (sectionsWithSupportDerived : DModX ⥤ DModZ)
    (sectionsWithSupportDerived' : DModX' ⥤ DModZ')
    (pullbackDerived : DModX ⥤ DModX')
    (restrictedPullbackDerived : DModZ ⥤ DModZ')
    (supportedProperty : ObjectProperty DModX')
    (supportedRightAdjoint : DModX' ⥤ supportedProperty.FullSubcategory)
    (baseChangeIso :
      iPushforwardDerived ⋙ pullbackDerived ≅
        restrictedPullbackDerived ⋙ i'PushforwardDerived)
    (adjZ : iPushforwardDerived ⊣ sectionsWithSupportDerived)
    (adjSupported : supportedProperty.ι ⊣ supportedRightAdjoint)
    (supportedRightAdjointAmbientIso :
      supportedRightAdjoint ⋙ supportedProperty.ι ≅
        sectionsWithSupportDerived' ⋙ i'PushforwardDerived)
    {K : DModX}
    (hsource :
      supportedProperty
        (pullbackDerived.obj
          (iPushforwardDerived.obj (sectionsWithSupportDerived.obj K)))) :
    ∃! τ :
        restrictedPullbackDerived.obj (sectionsWithSupportDerived.obj K) ⟶
          sectionsWithSupportDerived'.obj (pullbackDerived.obj K),
      baseChangeIso.hom.app (sectionsWithSupportDerived.obj K) ≫
          i'PushforwardDerived.map τ ≫
          supportedRightAdjointAmbientIso.inv.app (pullbackDerived.obj K) ≫
          adjSupported.counit.app (pullbackDerived.obj K) =
        pullbackDerived.map (adjZ.counit.app K) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_34_13 (from Chap20) -/
open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {DModX DModX' DModZ DModZ' : Type u}
variable [Category DModX] [Category DModX'] [Category DModZ] [Category DModZ']

/-- The top horizontal map on supported cohomology obtained by first pulling back the ambient
cohomology of `i_* R\mathcal H_Z(K)` and then applying the morphism from Remark `20.34.12`. -/
private abbrev closedSubsetPullback_sectionsWithSupportDerived_topMap
    (iPushforwardDerived : DModZ ⥤ DModX)
    (i'PushforwardDerived : DModZ' ⥤ DModX')
    (sectionsWithSupportDerived : DModX ⥤ DModZ)
    (sectionsWithSupportDerived' : DModX' ⥤ DModZ')
    (pullbackDerived : DModX ⥤ DModX')
    (restrictedPullbackDerived : DModZ ⥤ DModZ')
    (ambientCohomology : DModX ⥤ AddCommGrpCat.{u})
    (ambientCohomology' : DModX' ⥤ AddCommGrpCat.{u})
    (ambientPullbackMap : ambientCohomology ⟶ pullbackDerived ⋙ ambientCohomology')
    (baseChangeIso :
      iPushforwardDerived ⋙ pullbackDerived ≅
        restrictedPullbackDerived ⋙ i'PushforwardDerived)
    {K : DModX}
    (τ : restrictedPullbackDerived.obj (sectionsWithSupportDerived.obj K) ⟶
      sectionsWithSupportDerived'.obj (pullbackDerived.obj K)) :
    ambientCohomology.obj (iPushforwardDerived.obj (sectionsWithSupportDerived.obj K)) ⟶
      ambientCohomology'.obj
        (i'PushforwardDerived.obj (sectionsWithSupportDerived'.obj (pullbackDerived.obj K))) :=
  ambientPullbackMap.app (iPushforwardDerived.obj (sectionsWithSupportDerived.obj K)) ≫
    ambientCohomology'.map
      (baseChangeIso.hom.app (sectionsWithSupportDerived.obj K) ≫
        i'PushforwardDerived.map τ)

/-- The left vertical map from supported cohomology to ordinary cohomology induced by the counit
`i_* R\mathcal H_Z(K) ⟶ K`. -/
private abbrev closedSubsetPullback_sectionsWithSupportDerived_leftMap
    (iPushforwardDerived : DModZ ⥤ DModX)
    (sectionsWithSupportDerived : DModX ⥤ DModZ)
    (ambientCohomology : DModX ⥤ AddCommGrpCat.{u})
    (adjZ : iPushforwardDerived ⊣ sectionsWithSupportDerived)
    (K : DModX) :
    ambientCohomology.obj (iPushforwardDerived.obj (sectionsWithSupportDerived.obj K)) ⟶
      ambientCohomology.obj K :=
  ambientCohomology.map (adjZ.counit.app K)

/-- The right vertical map from supported cohomology on `X'` to ordinary cohomology on `X'`
induced by the supported-subcategory counit. -/
private abbrev closedSubsetPullback_sectionsWithSupportDerived_rightMap
    (i'PushforwardDerived : DModZ' ⥤ DModX')
    (sectionsWithSupportDerived' : DModX' ⥤ DModZ')
    (supportedProperty : ObjectProperty DModX')
    (supportedRightAdjoint : DModX' ⥤ supportedProperty.FullSubcategory)
    (ambientCohomology' : DModX' ⥤ AddCommGrpCat.{u})
    (adjSupported : supportedProperty.ι ⊣ supportedRightAdjoint)
    (supportedRightAdjointAmbientIso :
      supportedRightAdjoint ⋙ supportedProperty.ι ≅
        sectionsWithSupportDerived' ⋙ i'PushforwardDerived)
    (K' : DModX') :
    ambientCohomology'.obj
        (i'PushforwardDerived.obj (sectionsWithSupportDerived'.obj K')) ⟶
      ambientCohomology'.obj K' :=
  ambientCohomology'.map
    (supportedRightAdjointAmbientIso.inv.app K' ≫ adjSupported.counit.app K')

-- Proof sketch: identify the supported cohomology groups with the ambient cohomology of
-- `i_* R\mathcal H_Z(K)` and `i'_* R\mathcal H_{Z'}(Lf^* K)`. Naturality of the pullback map on
-- ambient cohomology gives the square obtained by pulling back `i_* R\mathcal H_Z(K) ⟶ K`, and
-- the defining relation for `τ` from Remark `20.34.12` identifies the right-hand composite with
-- the pullback of that counit.
/-- Lemma 20.34.13: after identifying `H^p_Z(X, K)` with the ambient cohomology of
`i_* R\mathcal H_Z(K)` and `H^p_{Z'}(X', Lf^* K)` with the ambient cohomology of
`i'_* R\mathcal H_{Z'}(Lf^* K)`, the pullback map on cohomology with support and the natural maps
to ordinary cohomology form a commutative square. -/
theorem closedSubsetPullback_sectionsWithSupportDerived_cohomology_commSq
    (iPushforwardDerived : DModZ ⥤ DModX)
    (i'PushforwardDerived : DModZ' ⥤ DModX')
    (sectionsWithSupportDerived : DModX ⥤ DModZ)
    (sectionsWithSupportDerived' : DModX' ⥤ DModZ')
    (pullbackDerived : DModX ⥤ DModX')
    (restrictedPullbackDerived : DModZ ⥤ DModZ')
    (supportedProperty : ObjectProperty DModX')
    (supportedRightAdjoint : DModX' ⥤ supportedProperty.FullSubcategory)
    (ambientCohomology : DModX ⥤ AddCommGrpCat.{u})
    (ambientCohomology' : DModX' ⥤ AddCommGrpCat.{u})
    (ambientPullbackMap : ambientCohomology ⟶ pullbackDerived ⋙ ambientCohomology')
    (baseChangeIso :
      iPushforwardDerived ⋙ pullbackDerived ≅
        restrictedPullbackDerived ⋙ i'PushforwardDerived)
    (adjZ : iPushforwardDerived ⊣ sectionsWithSupportDerived)
    (adjSupported : supportedProperty.ι ⊣ supportedRightAdjoint)
    (supportedRightAdjointAmbientIso :
      supportedRightAdjoint ⋙ supportedProperty.ι ≅
        sectionsWithSupportDerived' ⋙ i'PushforwardDerived)
    {K : DModX}
    (τ : restrictedPullbackDerived.obj (sectionsWithSupportDerived.obj K) ⟶
      sectionsWithSupportDerived'.obj (pullbackDerived.obj K))
    (hτ :
      baseChangeIso.hom.app (sectionsWithSupportDerived.obj K) ≫
          i'PushforwardDerived.map τ ≫
          supportedRightAdjointAmbientIso.inv.app (pullbackDerived.obj K) ≫
          adjSupported.counit.app (pullbackDerived.obj K) =
        pullbackDerived.map (adjZ.counit.app K)) :
    CommSq
      (closedSubsetPullback_sectionsWithSupportDerived_topMap
        iPushforwardDerived i'PushforwardDerived
        sectionsWithSupportDerived sectionsWithSupportDerived'
        pullbackDerived restrictedPullbackDerived
        ambientCohomology ambientCohomology' ambientPullbackMap
        baseChangeIso τ)
      (closedSubsetPullback_sectionsWithSupportDerived_leftMap
        iPushforwardDerived sectionsWithSupportDerived ambientCohomology adjZ K)
      (closedSubsetPullback_sectionsWithSupportDerived_rightMap
        i'PushforwardDerived sectionsWithSupportDerived'
        supportedProperty supportedRightAdjoint ambientCohomology'
        adjSupported supportedRightAdjointAmbientIso (pullbackDerived.obj K))
      (ambientPullbackMap.app K) := sorry

end

end AlgebraicGeometry.RingedSpace
