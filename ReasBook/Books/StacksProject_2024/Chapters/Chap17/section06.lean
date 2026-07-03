import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Sheaves.Abelian

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_17_6_1 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}

local notation "iZ" => X.closedSubsetInclusion Z

/- Definition 17.5.1 provides the canonical support owner for abelian sheaves. -/
recall abelianSheafSupport

/- A point lies in `abelianSheafSupport` exactly when the stalk at that point is nonzero. -/
recall mem_abelianSheafSupport_iff

-- Proof sketch: pushforward along the closed inclusion is both a right adjoint, via the canonical
-- pullback/pushforward adjunction, and a left adjoint, via the sections-with-support adjunction of
-- Lemma `17.6.3`. Hence it preserves finite limits and finite colimits, so it is exact.
/-- Lemma 17.6.1 (1): for the inclusion `i : Z → X` of a closed subset, the direct-image functor
`i_* : Ab(Z) ⥤ Ab(X)` on abelian sheaves is exact. -/
theorem closedSubsetAbelianSheafPushforward_exact
    (hZ : IsClosed Z)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] :
    exactFunctor ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) (X.Sheaf AddCommGrpCat.{u})
      (Sheaf.pushforward AddCommGrpCat.{u} iZ) := sorry

/- Lemma 17.6.1 (2): for the inclusion `i : Z → X` of a closed subset, the direct-image functor
`i_* : Ab(Z) ⥤ Ab(X)` is fully faithful. This is the `AddCommGrpCat` specialization of
`subsetSheafPushforward_fullyFaithful`. -/
recall subsetSheafPushforward_fullyFaithful

-- Proof sketch: by Lemma `closedSubsetAbelianSheafPushforward_essImage_iff_stalk_isZero_of_not_mem`,
-- an abelian sheaf lies in the essential image of `i_*` exactly when every stalk outside `Z` is
-- zero. Unfolding `abelianSheafSupport`, this is exactly the condition that the support be
-- contained in `Z`.
/-- Lemma 17.6.1 (3): the essential image of `i_* : Ab(Z) ⥤ Ab(X)` is exactly the abelian sheaves
whose support is contained in `Z`. -/
theorem closedSubsetAbelianSheafPushforward_essImage_iff_support_subset
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pushforward AddCommGrpCat.{u} iZ).essImage ℱ ↔
      abelianSheafSupport ℱ ⊆ Z := by
  rw [closedSubsetAbelianSheafPushforward_essImage_iff_stalk_isZero_of_not_mem hZ ℱ]
  constructor
  · intro h x hx
    by_contra hx'
    exact hx <| by simpa [mem_abelianSheafSupport_iff] using h x hx'
  · intro h x hx
    by_contra hx'
    exact hx <| h <| by simpa [mem_abelianSheafSupport_iff] using hx'

/- Lemma 17.6.1 (4): for the inclusion `i : Z → X`, the inverse-image functor `i⁻¹` is a left
inverse to `i_*`, equivalently the counit `i⁻¹ i_* ℱ ⟶ ℱ` is an isomorphism for every abelian
sheaf `ℱ` on `Z`. This is the `AddCommGrpCat` specialization of the subset-inclusion owner
theorem `subsetSheaf_pullback_pushforward_counit_isIso`. -/
recall subsetSheaf_pullback_pushforward_counit_isIso

end

/-! ### Remark_17_6_2 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open scoped ClosedSubsetSectionsWithSupport

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/- Domain-style sampling for Remark 17.6.2:
- primary domain: abelian sheaves on a closed subset and the canonical sections-with-support
  right adjoint to closed-subset pushforward;
- sampled owner declarations:
  `abelianSheafSectionSupport`,
  `closedSubsetOpenComplementRestriction`,
  `TopCat.closedSubsetInclusion`,
  `closedSubsetSectionsWithSupportSubsheaf`,
  `closedSubsetSectionsWithSupportFunctor`;
- owner abstraction: the chapter owner is
  `𝓗[hZ]`, together with its object part
  `closedSubsetSectionsWithSupportSubsheaf hZ ℱ`;
- primitive data: the closed subset `Z`, its closedness proof `hZ`, and the canonical kernel model
  already supplied by Lemma 17.6.3, plus the local-section support notion
  `abelianSheafSectionSupport`;
- derived API: the sectionwise support characterization of that owner, its support-containment and
  universal-factorization properties, and the left exactness of the canonical
  `Ab(X) ⥤ Ab(Z)` functor.

Source/core/bridge triage:
- `source-facing`: the Stacks remark that `𝒢 = 𝒥_Z(ℱ)` is the subsheaf of sections supported in
  `Z`, i.e. `𝒢(U) = { s ∈ ℱ(U) | support(s) ⊆ Z ∩ U }`, together with its support-based
  universal property;
- `core/canonical`: `TopCat.closedSubsetInclusion X Z` and the owner
  `𝓗[hZ]` from Lemma 17.6.3;
- `bridge/view`: this file adds the support-theoretic characterization of the existing owner rather
  than introducing a second `X`-valued functorial implementation of `𝒥_Z`. -/

/- Lemma 17.6.3 provides the canonical kernel-model owner for sections with support in `Z`,
together with the adjunction `i_* ⊣ 𝓗[hZ]`. -/
recall closedSubsetSectionsWithSupportSubsheaf
recall closedSubsetSectionsWithSupportSheaf
recall closedSubsetSectionsWithSupportFunctor
recall closedSubset_pushforwardSectionsWithSupportAdjunction

-- Proof sketch: a section of `ℱ(U)` lies in the kernel of the restriction to the open complement
-- exactly when its germs vanish at every point of `U ∩ Zᶜ`; by the definition of section support,
-- this is equivalent to the support being contained in `Z ∩ U`.
/-- Remark 17.6.2: for an open set `U ⊆ X`, the image of the canonical inclusion
`\mathcal H_Z(\mathcal F)(U) \hookrightarrow \mathcal F(U)` is exactly the set of sections whose
support is contained in `Z ∩ U`. This is the source-facing sectionwise description of
`\mathcal H_Z(\mathcal F)`. -/
theorem closedSubsetSectionsWithSupportSubsheaf_app_range
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) :
    Set.range ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U)) =
      { s | abelianSheafSectionSupport ℱ s ⊆ { x : U | x.1 ∈ Z } } := sorry

/-- A section of `ℱ(U)` lies in the image of `\mathcal H_Z(\mathcal F)(U)` exactly when its
support is contained in `Z ∩ U`. -/
theorem closedSubsetSectionsWithSupportSubsheaf_app_iff
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X)
    (s : ℱ.presheaf.obj (op U)) :
    s ∈ Set.range ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U)) ↔
      abelianSheafSectionSupport ℱ s ⊆ { x : U | x.1 ∈ Z } := by
  simp [closedSubsetSectionsWithSupportSubsheaf_app_range hZ ℱ U]

-- Proof sketch: at points of the open complement, the unit
-- `ℱ ⟶ j_* j⁻¹ ℱ` is an isomorphism on stalks, so the kernel stalk is zero there. Hence the
-- support of the kernel subsheaf is contained in the closed complement `Z`.
/-- The subsheaf of sections supported in `Z` has support contained in `Z`. -/
theorem closedSubsetSectionsWithSupportSubsheaf_support_subset
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    abelianSheafSupport (closedSubsetSectionsWithSupportSubsheaf hZ ℱ) ⊆ Z := sorry

-- Proof sketch: if a subsheaf `G ⊆ ℱ` is supported inside `Z`, then its restriction to the open
-- complement vanishes. Therefore the inclusion `G ⟶ ℱ` factors through the kernel of
-- `ℱ ⟶ j_* j⁻¹ ℱ`, which is exactly `closedSubsetSectionsWithSupportSubsheaf hZ ℱ`.
/-- Any abelian subsheaf of `ℱ` whose support is contained in `Z` factors through the
sections-with-support subsheaf. -/
theorem le_closedSubsetSectionsWithSupportSubsheaf_of_support_subset
    (hZ : IsClosed Z) {ℱ : X.Sheaf AddCommGrpCat.{u}} (G : Subobject ℱ)
    (hG : abelianSheafSupport G ⊆ Z) :
    G ≤ closedSubsetSectionsWithSupportSubsheaf hZ ℱ := sorry

variable (hZ : IsClosed Z)

local instance : Functor.IsRightAdjoint (𝓗[hZ]) :=
  (closedSubset_pushforwardSectionsWithSupportAdjunction hZ).isRightAdjoint

/- Remark 17.6.2: the canonical sections-with-support functor
`\mathcal H_Z : Ab(X) \to Ab(Z)` is left exact. This is the canonical owner form
`PreservesFiniteLimits (𝓗[hZ])`, obtained from the right-adjoint structure of `𝓗[hZ]`. -/
#synth PreservesFiniteLimits (𝓗[hZ])

end

/-! ### Lemma_17_6_3 (from Chap17) -/
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

/-! ### Remark_17_6_4 (from Chap17) -/
open CategoryTheory
open Opposite
open TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}

local notation "iZ" => X.closedSubsetInclusion Z

/- Domain-style sampling for Remark 17.6.4:
- primary domain: pointed sheaves on a closed subset, the closed-subset pushforward functor, and
  the pointed sheaf of sections with support in `Z`;
- sampled owner declarations:
  `TopCat.closedSubsetInclusion`,
  `Sheaf.pushforward`,
  `Sheaf.pullback`,
  `closedSubsetSectionsWithSupportFunctor`,
  `Sheaf.pullbackPushforwardAdjunction`,
  `subsetSheaf_pullback_pushforward_counit_isIso`;
- best owner abstraction:
  the source-facing owner is the pointed closed-support functor
  `ClosedSubsetSectionsWithSupport.Pointed.functor hZ`, written `𝓗[hZ]`, whose object part is the
  pointed sheaf on `Z` obtained by restricting the pointed sheaf on `X` of sections that become
  the distinguished point on `X \ Z`;
- primitive data:
  the closed subset `Z`, its open complement, the explicit support-condition subsheaf on `X`, and
  the canonical distinguished point section on that sheaf;
- derived API:
  the functor `𝓗[hZ]`, its objectwise pointed sheaf `((𝓗[hZ]).obj ℱ)`, and the
  left-adjoint/right-adjoint/exactness consequences for closed-subset pushforward.

Source/core/bridge triage:
- `source-facing`: the pointed closed-support functor `𝓗[hZ]` and its object part
  `((𝓗[hZ]).obj ℱ)`;
- `core/canonical`: the adjointness of `Sheaf.pushforward Pointed iZ` and the resulting exactness;
- `bridge/view`: the explicit support-condition subsheaf on `X`, pointified canonically on `X`
  before restricting to `Z`; there is no chosen `Type`-valued point data on `Z`. -/

/-- The open complement of a closed subset `Z ⊆ X`. -/
private abbrev closedSubsetOpenComplement (hZ : IsClosed Z) : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- A section of a pointed sheaf over `U` is supported in `Z` when its restriction to the open
complement `U ∩ (X \ Z)` is the distinguished point section. -/
def ClosedSubsetSectionsWithSupport.Pointed.appPred
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) (U : Opens X)
    (s : ℱ.presheaf.obj (op U)) : Prop :=
  ℱ.presheaf.map (Opens.infLELeft U (closedSubsetOpenComplement hZ)).op s =
    (ℱ.presheaf.obj (op (U ⊓ closedSubsetOpenComplement hZ))).point

/-- The `Type`-valued presheaf of local sections whose restriction to the open complement of `Z`
is the distinguished point section. -/
private def closedSubsetPointedSectionsWithSupportTypePresheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) : X.Presheaf (Type u) where
  obj U := { s : ℱ.presheaf.obj U // ClosedSubsetSectionsWithSupport.Pointed.appPred hZ ℱ U.unop s }
  map {U V} i s := ⟨ℱ.presheaf.map i s.1, by sorry⟩
  map_id := by sorry
  map_comp := by sorry

private theorem closedSubsetPointedSectionsWithSupportTypePresheaf_isSheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    (closedSubsetPointedSectionsWithSupportTypePresheaf hZ ℱ).IsSheaf := by
  sorry

/-- The `Type`-valued sheaf on `X` consisting of sections whose restriction to the open complement
of `Z` is the distinguished point section. -/
private def closedSubsetPointedSectionsWithSupportTypeSheafOnX
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) : X.Sheaf (Type u) :=
  ⟨closedSubsetPointedSectionsWithSupportTypePresheaf hZ ℱ,
    closedSubsetPointedSectionsWithSupportTypePresheaf_isSheaf hZ ℱ⟩

/-- The distinguished point section defines a canonical morphism from the singleton sheaf to the
`Type`-valued sections-with-support sheaf on `X`. -/
private def closedSubsetPointedSectionsWithSupportTypeSheafOnX_point
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    TopCat.sheafToType X (ULift Unit) ⟶
      closedSubsetPointedSectionsWithSupportTypeSheafOnX hZ ℱ :=
  ObjectProperty.homMk
    { app := fun U _ ↦
        ⟨(ℱ.presheaf.obj U).point, by
          show ClosedSubsetSectionsWithSupport.Pointed.appPred hZ ℱ U.unop (ℱ.presheaf.obj U).point
          unfold ClosedSubsetSectionsWithSupport.Pointed.appPred
          simpa using
            (ℱ.presheaf.map (Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op).map_point⟩
      naturality := by
        intro U V i
        sorry }

/-- The `Type`-valued map on sections-with-support sheaves induced by a morphism of pointed
sheaves. -/
private def closedSubsetPointedSectionsWithSupportTypeSheafOnX_map
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) :
    closedSubsetPointedSectionsWithSupportTypeSheafOnX hZ ℱ ⟶
      closedSubsetPointedSectionsWithSupportTypeSheafOnX hZ 𝒢 :=
  ObjectProperty.homMk
    { app := fun U s ↦ ⟨φ.1.app U s.1, by sorry⟩
      naturality := by
        intro U V i
        sorry }

/-- A sheaf of types with a distinguished singleton-valued section family canonically determines a
sheaf of pointed sets. -/
private def pointifySheaf {Y : TopCat.{u}} (F : Y.Sheaf (Type u))
    (η : TopCat.sheafToType Y (ULift Unit) ⟶ F) : Y.Sheaf Pointed := by
  refine ⟨?_, ?_⟩
  · let P : Y.Presheaf (Type u) := F.1
    refine
      { obj := fun U ↦ Pointed.of (η.1.app U (fun _ ↦ ⟨()⟩))
        map := fun {U V} i ↦ ⟨fun s ↦ P.map i s, by
          change P.map i (η.1.app U (fun _ ↦ ⟨()⟩)) = η.1.app V (fun _ ↦ ⟨()⟩)
          simpa using (congr_fun (η.1.naturality i) (fun _ ↦ ⟨()⟩)).symm⟩
        map_id := by sorry
        map_comp := by sorry }
  · sorry

/-- A morphism of type-valued sheaves respecting distinguished singleton-valued sections induces a
morphism of the associated sheaves of pointed sets. -/
private def pointifySheafMap {Y : TopCat.{u}} {F G : Y.Sheaf (Type u)}
    {ηF : TopCat.sheafToType Y (ULift Unit) ⟶ F}
    {ηG : TopCat.sheafToType Y (ULift Unit) ⟶ G}
    (φ : F ⟶ G) (hφ : ηF ≫ φ = ηG) :
    pointifySheaf F ηF ⟶ pointifySheaf G ηG :=
  ObjectProperty.homMk
    { app := fun U ↦
        ⟨φ.1.app U, by sorry⟩
      naturality := by
        sorry }

private theorem closedSubsetPointedSectionsWithSupportTypeSheafOnX_point_naturality
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) :
    closedSubsetPointedSectionsWithSupportTypeSheafOnX_point hZ ℱ ≫
        closedSubsetPointedSectionsWithSupportTypeSheafOnX_map hZ φ =
      closedSubsetPointedSectionsWithSupportTypeSheafOnX_point hZ 𝒢 := by
  sorry

/-- The pointed sheaf on `X` whose sections restrict to the distinguished point section on the
open complement `X \ Z`. -/
def ClosedSubsetSectionsWithSupport.Pointed.sheafOnX
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) : X.Sheaf Pointed :=
  pointifySheaf
    (closedSubsetPointedSectionsWithSupportTypeSheafOnX hZ ℱ)
    (closedSubsetPointedSectionsWithSupportTypeSheafOnX_point hZ ℱ)

/-- The pointed map on sections-with-support sheaves induced by a morphism of pointed sheaves. -/
private def sheafOnXMap
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf Pointed} (φ : ℱ ⟶ 𝒢) :
    ClosedSubsetSectionsWithSupport.Pointed.sheafOnX hZ ℱ ⟶
      ClosedSubsetSectionsWithSupport.Pointed.sheafOnX hZ 𝒢 :=
  pointifySheafMap
    (closedSubsetPointedSectionsWithSupportTypeSheafOnX_map hZ φ)
    (closedSubsetPointedSectionsWithSupportTypeSheafOnX_point_naturality hZ φ)

namespace ClosedSubsetSectionsWithSupport.Pointed

-- Proof sketch: sections with support in `Z` first form a pointed sheaf on `X`, namely the
-- pointed subsheaf whose sections restrict to the distinguished point on `X \ Z`; restricting
-- that pointed sheaf to `Z` yields the source-facing pointed closed-support functor
-- `\mathcal H_Z = 𝓗[hZ]`.
/-- The pointed sheaf on the closed subset `Z` obtained by restricting the pointed sheaf
`sheafOnX hZ ℱ` of sections that become the distinguished point on `X \ Z`. -/
def sheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    (TopCat.of Z).Sheaf Pointed :=
  (Sheaf.pullback Pointed iZ).obj (sheafOnX hZ ℱ)

/-- Remark 17.6.4: the pointed closed-support functor along a closed subset inclusion, written
`𝓗[hZ] = \mathcal H_Z`, sends a pointed sheaf `\mathcal F` on `X` to the pointed sheaf on `Z`
obtained by restricting the pointed sheaf on `X` of local sections whose restriction to
`X \ Z` is the distinguished point section. -/
def functor
    (hZ : IsClosed Z) :
    X.Sheaf Pointed ⥤ (TopCat.of Z).Sheaf Pointed where
  obj ℱ := sheaf hZ ℱ
  map φ := (Sheaf.pullback Pointed iZ).map (sheafOnXMap hZ φ)
  map_id := by
    sorry
  map_comp := by
    sorry

end ClosedSubsetSectionsWithSupport.Pointed

namespace ClosedSubsetSectionsWithSupport.Pointed

scoped notation "𝓗[" hZ "]" => functor hZ

end ClosedSubsetSectionsWithSupport.Pointed

open scoped ClosedSubsetSectionsWithSupport.Pointed

namespace ClosedSubsetSectionsWithSupport.Pointed

/-- The canonical morphism from the pointed sheaf of sections supported on `Z` back to `ℱ`. -/
def sheafOnXHom
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    sheafOnX hZ ℱ ⟶ ℱ := by
  refine ObjectProperty.homMk ?_
  refine
    { app := fun U ↦ ?_
      naturality := ?_ }
  · refine ⟨fun s ↦ s.1, ?_⟩
    rfl
  · intro U V i
    ext s
    rfl

variable (hZ : IsClosed Z)

/-- For an open set `U ⊆ X`, the image of the canonical map
`sheafOnX hZ ℱ(U) → ℱ(U)` is exactly the set of sections whose restriction to
`U ∩ (X \ Z)` is the distinguished point. -/
theorem sheafOnX_app_range
    (ℱ : X.Sheaf Pointed) (U : Opens X) :
    Set.range ((sheafOnXHom hZ ℱ).1.app (op U)) =
      { s | appPred hZ ℱ U s } := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact t.2
  · intro hs
    exact ⟨⟨s, hs⟩, rfl⟩

/-- A section of `ℱ(U)` lies in the image of `sheafOnX hZ ℱ(U) → ℱ(U)` exactly when its
restriction to `U ∩ (X \ Z)` is the distinguished point. -/
theorem sheafOnX_app_iff
    (ℱ : X.Sheaf Pointed) (U : Opens X) (s : ℱ.presheaf.obj (op U)) :
    s ∈ Set.range ((sheafOnXHom hZ ℱ).1.app (op U)) ↔
      appPred hZ ℱ U s := by
  simpa using congrArg (fun S : Set (ℱ.presheaf.obj (op U)) ↦ s ∈ S) (sheafOnX_app_range hZ ℱ U)

variable {hZ}

private theorem closedSubsetPointedSectionsWithSupportSheafOnX_pushforwardHom_isIso
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf Pointed) :
    IsIso
      (sheafOnXHom hZ
        ((Sheaf.pushforward Pointed iZ).obj ℱ)) := by
  sorry

private theorem closedSubsetPointedSectionsWithSupportSheafOnX_pullback_pushforward_unit_isIso
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    IsIso
      ((Sheaf.pullbackPushforwardAdjunction Pointed iZ).unit.app
        (sheafOnX hZ ℱ)) := by
  sorry

private noncomputable abbrev pushforwardSectionsWithSupportAdjunctionUnitApp
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf Pointed) :
    ℱ ⟶
      (𝓗[hZ]).obj ((Sheaf.pushforward Pointed iZ).obj ℱ) :=
  letI := subsetSheaf_pullback_pushforward_counit_isIso ℱ
  letI := closedSubsetPointedSectionsWithSupportSheafOnX_pushforwardHom_isIso hZ ℱ
  let e := asIso
    (sheafOnXHom hZ
      ((Sheaf.pushforward Pointed iZ).obj ℱ))
  (asIso ((Sheaf.pullbackPushforwardAdjunction Pointed iZ).counit.app ℱ)).inv ≫
    (Sheaf.pullback Pointed iZ).map e.inv

private noncomputable abbrev pushforwardSectionsWithSupportAdjunctionCounitApp
    (hZ : IsClosed Z) (ℱ : X.Sheaf Pointed) :
    (Sheaf.pushforward Pointed iZ).obj ((𝓗[hZ]).obj ℱ) ⟶ ℱ :=
  letI := closedSubsetPointedSectionsWithSupportSheafOnX_pullback_pushforward_unit_isIso hZ ℱ
  (asIso
      ((Sheaf.pullbackPushforwardAdjunction Pointed iZ).unit.app
        (sheafOnX hZ ℱ))).inv ≫
    sheafOnXHom hZ ℱ

/-- Remark 17.6.4: for a closed subset inclusion `i : Z ↪ X`, pushforward of pointed sheaves is
left adjoint to the explicit pointed sections-with-support functor `𝓗[hZ] = \mathcal H_Z`. -/
noncomputable def pushforwardSectionsWithSupportAdjunction
    (hZ : IsClosed Z) :
    Sheaf.pushforward Pointed iZ ⊣ 𝓗[hZ] where
  unit :=
    { app := pushforwardSectionsWithSupportAdjunctionUnitApp hZ
      naturality := by
        sorry }
  counit :=
    { app := pushforwardSectionsWithSupportAdjunctionCounitApp hZ
      naturality := by
        sorry }
  left_triangle_components := by
    sorry
  right_triangle_components := by
    sorry

section

variable (hZ : IsClosed Z)

/- Pushforward of pointed sheaves along a closed subset inclusion is a left adjoint. This is the
canonical owner theorem `Adjunction.isLeftAdjoint` for the adjunction above. -/
#check ((pushforwardSectionsWithSupportAdjunction hZ).isLeftAdjoint :
  (Sheaf.pushforward Pointed iZ).IsLeftAdjoint)

local instance : Functor.IsRightAdjoint (𝓗[hZ]) :=
  (pushforwardSectionsWithSupportAdjunction hZ).isRightAdjoint

/- The pointed closed-support functor `𝓗[hZ]` is a right adjoint. This is the canonical owner
form `Functor.IsRightAdjoint (𝓗[hZ])` coming from the specialized adjunction above. -/
#check (show Functor.IsRightAdjoint (𝓗[hZ]) from inferInstance)

-- Proof sketch: in the pointed setting, closed-subset pushforward is exact because Remark 17.6.4
-- makes it both a right adjoint and a left adjoint.
/-- Remark 17.6.4 (1): for a closed subset `Z ⊆ X`, the pushforward functor
`i_* : Sh(Z, Pointed) ⥤ Sh(X, Pointed)` is exact. -/
theorem pushforward_exact
    (hZ : IsClosed Z) :
    exactFunctor ((TopCat.of Z).Sheaf Pointed) (X.Sheaf Pointed)
      (Sheaf.pushforward Pointed iZ) := by
  sorry

end

end ClosedSubsetSectionsWithSupport.Pointed

end
