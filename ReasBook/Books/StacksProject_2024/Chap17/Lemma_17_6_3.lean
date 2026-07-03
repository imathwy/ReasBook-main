import Mathlib
import Mathlib.Topology.Sheaves.Abelian
import StacksProject_2024.Chap06.ClosedSubsetInclusion
import StacksProject_2024.Chap06.Lemma_6_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
local instance : HasKernels (TopCat.Sheaf AddCommGrpCat.{u} X) := inferInstance
local notation "iZ" => X.closedSubsetInclusion Z

/-
Domain-style sampling for Lemma 17.6.3:
- primary domain: abelian sheaves on a closed subset, the closed-subset pushforward functor, and
  its sections-with-support right adjoint;
- sampled owner declarations:
  `TopCat.closedSubsetInclusion`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `CategoryTheory.Adjunction`,
  `Adjunction.homEquiv`,
  `Adjunction.leftAdjoint_preservesColimits`;
- best owner abstraction: the adjunction between closed-subset pushforward and the
  sections-with-support functor, with `Sheaf.pushforward AddCommGrpCat iZ` as the ambient
  canonical owner and the kernel model below as the source-facing realization;
- primitive data: the closed subset `Z`, its inclusion `iZ`, the open complement `X \ Z`, and the
  unit map `ℱ ⟶ j_* j⁻¹ ℱ`;
- derived API: the kernel-model subsheaf and restricted sheaf of sections with support, the
  functoriality on those kernel objects, the adjunction, and the resulting left-adjoint/right-
  adjoint and colimit-preservation consequences.

Source/core/bridge triage:
- `source-facing`: the kernel-model constructions
  `closedSubsetSectionsWithSupportSubsheaf` and `closedSubsetSectionsWithSupportSheaf`;
- `core/canonical`: the adjunction
  `Sheaf.pushforward AddCommGrpCat iZ ⊣ 𝓗[hZ]`;
- `bridge/view`: the explicit kernel functoriality proving that the source-facing kernel model
  realizes the canonical right adjoint. -/

/-- The open complement of a closed subset `Z ⊆ X`. -/
private abbrev closedSubsetOpenComplement (hZ : IsClosed Z) : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The inclusion of the open complement `X \ Z` into `X`. -/
private abbrev closedSubsetOpenComplementInclusion (hZ : IsClosed Z) :
    (Opens.toTopCat X).obj (closedSubsetOpenComplement hZ) ⟶ X :=
  Opens.inclusion' (closedSubsetOpenComplement hZ)

/-- The unit map from an abelian sheaf to the pushforward of its restriction to the open
complement of a closed subset. -/
private abbrev closedSubsetOpenComplementRestriction
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    ℱ ⟶
      (Sheaf.pushforward AddCommGrpCat.{u}
        (closedSubsetOpenComplementInclusion hZ)).obj
        ((Sheaf.pullback AddCommGrpCat.{u}
          (closedSubsetOpenComplementInclusion hZ)).obj ℱ) :=
  (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (closedSubsetOpenComplementInclusion hZ)).unit.app ℱ

/-- The subsheaf of an abelian sheaf on `X` consisting of sections supported on the closed subset
`Z`. -/
def closedSubsetSectionsWithSupportSubsheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) : Subobject ℱ :=
  let f := closedSubsetOpenComplementRestriction hZ ℱ
  let _ : HasKernel f := HasKernels.has_limit f
  kernelSubobject f

/-- The sheaf on `Z` obtained by restricting the subsheaf of sections of `ℱ` supported on `Z`. -/
private abbrev closedSubsetSectionsWithSupportObject
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    X.Sheaf AddCommGrpCat.{u} :=
  ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ : Subobject ℱ) :
    X.Sheaf AddCommGrpCat.{u})

/-- The sheaf on `Z` obtained by restricting the subsheaf of sections of `ℱ` supported on `Z`. -/
def closedSubsetSectionsWithSupportSheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (TopCat.of Z).Sheaf AddCommGrpCat.{u} :=
  (Sheaf.pullback AddCommGrpCat.{u} iZ).obj
    (closedSubsetSectionsWithSupportObject hZ ℱ)

-- Proof sketch: this is the naturality of the unit of the adjunction `j^{-1} ⊣ j_*` for the open
-- complement inclusion `j : X \ Z ↪ X`.
/-- Naturality of the restriction map to the open complement of a closed subset. -/
private theorem closedSubsetSectionsWithSupportSubsheafMap_w
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢) :
    φ ≫ closedSubsetOpenComplementRestriction hZ 𝒢 =
      closedSubsetOpenComplementRestriction hZ ℱ ≫
        (Sheaf.pushforward AddCommGrpCat.{u}
          (closedSubsetOpenComplementInclusion hZ)).map
          ((Sheaf.pullback AddCommGrpCat.{u}
            (closedSubsetOpenComplementInclusion hZ)).map φ) := sorry

/-- The morphism on closed-support subsheaves induced by a morphism of abelian sheaves. -/
private def closedSubsetSectionsWithSupportSubsheafMap
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢) :
    closedSubsetSectionsWithSupportObject hZ ℱ ⟶
      closedSubsetSectionsWithSupportObject hZ 𝒢 :=
  let f := closedSubsetOpenComplementRestriction hZ ℱ
  let g := closedSubsetOpenComplementRestriction hZ 𝒢
  let _ : HasKernel f := HasKernels.has_limit f
  let _ : HasKernel g := HasKernels.has_limit g
  kernelSubobjectMap <|
    Arrow.homMk'
      φ
      ((Sheaf.pushforward AddCommGrpCat.{u}
        (closedSubsetOpenComplementInclusion hZ)).map
        ((Sheaf.pullback AddCommGrpCat.{u}
          (closedSubsetOpenComplementInclusion hZ)).map φ))
      (closedSubsetSectionsWithSupportSubsheafMap_w hZ φ)

-- Proof sketch: the induced map on kernels is functorial, and pullback along the closed
-- inclusion preserves identity morphisms.
/-- The induced morphism on sections-with-support sheaves respects identity morphisms. -/
private theorem closedSubsetSectionsWithSupportFunctor_map_id
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pullback AddCommGrpCat.{u} iZ).map
      (closedSubsetSectionsWithSupportSubsheafMap hZ (𝟙 ℱ)) =
    𝟙 (closedSubsetSectionsWithSupportSheaf hZ ℱ) := sorry

-- Proof sketch: compose the naturality squares for `φ` and `ψ`, then use functoriality of
-- `kernelSubobjectMap` and of pullback along the closed inclusion.
/-- The induced morphism on sections-with-support sheaves respects composition. -/
private theorem closedSubsetSectionsWithSupportFunctor_map_comp
    (hZ : IsClosed Z) {ℱ 𝒢 𝒦 : X.Sheaf AddCommGrpCat.{u}}
    (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ 𝒦) :
    (Sheaf.pullback AddCommGrpCat.{u} iZ).map
      (closedSubsetSectionsWithSupportSubsheafMap hZ (φ ≫ ψ)) =
    (Sheaf.pullback AddCommGrpCat.{u} iZ).map
      (closedSubsetSectionsWithSupportSubsheafMap hZ φ) ≫
      (Sheaf.pullback AddCommGrpCat.{u} iZ).map
        (closedSubsetSectionsWithSupportSubsheafMap hZ ψ) := sorry

/-- The functor sending an abelian sheaf on `X` to its sheaf of sections supported on the closed
subset `Z`. -/
def closedSubsetSectionsWithSupportFunctor
    (hZ : IsClosed Z) :
    X.Sheaf AddCommGrpCat.{u} ⥤ (TopCat.of Z).Sheaf AddCommGrpCat.{u} where
  obj ℱ := closedSubsetSectionsWithSupportSheaf hZ ℱ
  map φ := (Sheaf.pullback AddCommGrpCat.{u} iZ).map (closedSubsetSectionsWithSupportSubsheafMap hZ φ)
  map_id := closedSubsetSectionsWithSupportFunctor_map_id hZ
  map_comp := closedSubsetSectionsWithSupportFunctor_map_comp hZ

end

namespace ClosedSubsetSectionsWithSupport

scoped notation "𝓗[" hZ "]" => closedSubsetSectionsWithSupportFunctor hZ

end ClosedSubsetSectionsWithSupport

open scoped ClosedSubsetSectionsWithSupport

section

variable {X : TopCat.{u}} {Z : Set X}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

local notation "iZ" => X.closedSubsetInclusion Z
local instance : HasKernels (TopCat.Sheaf AddCommGrpCat.{u} X) := inferInstance

private theorem closedSubsetSectionsWithSupportSubsheaf_pushforward_eq_top
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    closedSubsetSectionsWithSupportSubsheaf hZ
        ((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ) =
      ⊤ := sorry

private theorem closedSubsetSectionsWithSupportObject_mem_essImage
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pushforward AddCommGrpCat.{u} iZ).essImage
      (closedSubsetSectionsWithSupportObject hZ ℱ) := sorry

private theorem closedSubsetSectionsWithSupportObject_pullback_pushforward_unit_isIso
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    IsIso
      ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} iZ).unit.app
        (closedSubsetSectionsWithSupportObject hZ ℱ)) := sorry

private abbrev closedSubsetSectionsWithSupportAdjunctionUnitApp
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    ℱ ⟶
      (𝓗[hZ]).obj ((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ) :=
  letI := subsetSheaf_pullback_pushforward_counit_isIso ℱ
  (asIso
      ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} iZ).counit.app ℱ)).inv ≫
    (Sheaf.pullback AddCommGrpCat.{u} iZ).map
      ((asIso
          ((⊤ : Subobject ((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ)).arrow)).inv ≫
        (Subobject.isoOfEq
          (closedSubsetSectionsWithSupportSubsheaf hZ
            ((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ))
          ⊤
          (closedSubsetSectionsWithSupportSubsheaf_pushforward_eq_top hZ ℱ)).symm.hom)

private abbrev closedSubsetSectionsWithSupportAdjunctionCounitApp
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj
        ((𝓗[hZ]).obj ℱ) ⟶
      ℱ :=
  letI := closedSubsetSectionsWithSupportObject_pullback_pushforward_unit_isIso hZ ℱ
  (asIso
      ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} iZ).unit.app
        (closedSubsetSectionsWithSupportObject hZ ℱ))).inv ≫
    (closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow

/-- Lemma 17.6.3: for a closed subset inclusion `i : Z ↪ X`, pushforward of abelian sheaves is
left adjoint to the explicit sections-with-support functor `𝓗[hZ] = \mathcal H_Z`. -/
noncomputable def closedSubset_pushforwardSectionsWithSupportAdjunction
    (hZ : IsClosed Z) :
    Sheaf.pushforward AddCommGrpCat.{u} iZ ⊣ 𝓗[hZ] where
  unit :=
    { app := closedSubsetSectionsWithSupportAdjunctionUnitApp hZ
      naturality := sorry }
  counit :=
    { app := closedSubsetSectionsWithSupportAdjunctionCounitApp hZ
      naturality := sorry }
  left_triangle_components := by sorry
  right_triangle_components := by sorry

section

variable (hZ : IsClosed Z)

/- The textbook left-adjoint conclusion of Lemma 17.6.3 is the generic owner theorem
`CategoryTheory.Adjunction.isLeftAdjoint`, specialized to the adjunction above. -/
#check
  ((closedSubset_pushforwardSectionsWithSupportAdjunction hZ).isLeftAdjoint :
    (Sheaf.pushforward AddCommGrpCat.{u} iZ).IsLeftAdjoint)

/- The right-adjoint conclusion for `𝓗[hZ]` is the generic owner theorem
`CategoryTheory.Adjunction.isRightAdjoint`, specialized to the same adjunction. -/
#check
  ((closedSubset_pushforwardSectionsWithSupportAdjunction hZ).isRightAdjoint :
    Functor.IsRightAdjoint (𝓗[hZ]))

/- Pushforward along the closed-subset inclusion preserves arbitrary colimits because it is the
left adjoint in the adjunction above; this is the generic owner-level consequence
`CategoryTheory.Adjunction.leftAdjoint_preservesColimits`. -/
#check
  ((closedSubset_pushforwardSectionsWithSupportAdjunction hZ).leftAdjoint_preservesColimits :
    PreservesColimits (Sheaf.pushforward AddCommGrpCat.{u} iZ))

end

end
