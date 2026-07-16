import Mathlib
import Mathlib.Topology.Sheaves.Abelian
import stacks_proof.stacks_project.Chap06.ClosedSubsetInclusion
import stacks_proof.stacks_project.Chap06.Lemma_6_32_1
import stacks_proof.stacks_project.Chap06.Lemma_6_32_3
import stacks_proof.stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

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
            (closedSubsetOpenComplementInclusion hZ)).map φ) := by
  -- This is exactly the unit naturality square for restriction to the open complement.
  simpa [closedSubsetOpenComplementRestriction] using
    (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (closedSubsetOpenComplementInclusion hZ)).unit.naturality φ

/-- The morphism on closed-support subsheaves induced by a morphism of abelian sheaves. -/
private def closedSubsetSectionsWithSupportSubsheafMap
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢) :
    closedSubsetSectionsWithSupportObject hZ ℱ ⟶
      closedSubsetSectionsWithSupportObject hZ 𝒢 :=
  let f := closedSubsetOpenComplementRestriction hZ ℱ
  let g := closedSubsetOpenComplementRestriction hZ 𝒢
  let _ : HasKernel f := HasKernels.has_limit f
  let _ : HasKernel g := HasKernels.has_limit g
  -- The kernel map is induced by the naturality square above.
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
    𝟙 (closedSubsetSectionsWithSupportSheaf hZ ℱ) := by
  -- Kernel maps along the identity square are identities, and pullback preserves identities.
  simp [closedSubsetSectionsWithSupportSheaf, closedSubsetSectionsWithSupportSubsheafMap,
    closedSubsetSectionsWithSupportObject, CategoryTheory.Limits.kernelSubobjectMap_id]

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
        (closedSubsetSectionsWithSupportSubsheafMap hZ ψ) := by
  -- Kernel maps compose functorially, and then pullback preserves the resulting composition.
  simp [closedSubsetSectionsWithSupportSubsheafMap,
    CategoryTheory.Limits.kernelSubobjectMap_comp]

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

/-- Helper for Lemma 17.6.3: an abelian sheaf on `X` lies in the essential image of pushforward
from the closed subset exactly when its support is contained in `Z`. -/
omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
private theorem closedSubsetAbelianSheafPushforward_essImage_iff_support_subset
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pushforward AddCommGrpCat.{u} iZ).essImage
      ℱ ↔
      abelianSheafSupport ℱ ⊆ Z := by
  -- Rewrite the Chapter 6 zero-stalk criterion in terms of the support owner used here.
  rw [closedSubsetAbelianSheafPushforward_essImage_iff_stalk_isZero_of_not_mem hZ ℱ]
  constructor
  · intro h x hx
    by_contra hx'
    exact hx <| by simpa [mem_abelianSheafSupport_iff] using h x hx'
  · intro h x hx
    by_contra hx'
    exact hx <| h <| by simpa [mem_abelianSheafSupport_iff] using hx'

/-- Helper for Lemma 17.6.3: the open-complement restriction of a pushed-forward sheaf from `Z`
vanishes. -/
omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
private theorem pushforward_section_eq_zero_of_le_complement
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) {U : Opens X}
    (hU : U ≤ closedSubsetOpenComplement hZ)
    (s : ((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ).presheaf.obj (op U)) :
    s = 0 := by
  -- On an open disjoint from `Z`, the inverse-image open in `Z` is empty, so every section is
  -- the unique section over the empty open and hence zero in `AddCommGrpCat`.
  have hEq : (Opens.map iZ).obj U = ⊥ := by
    ext z
    constructor
    · intro hz
      exact (hU hz) z.2
    · intro hz
      cases hz
  let A : AddCommGrpCat.{u} := ℱ.presheaf.obj (op ((Opens.map iZ).obj U))
  have hAterminal : IsTerminal A := by
    simpa [A] using ℱ.isTerminalOfEqEmpty hEq
  have hAsubsingleton : Subsingleton A := by
    exact (AddCommGrpCat.isZero_iff_subsingleton).1 hAterminal.isZero
  simpa [A] using (hAsubsingleton.elim s (0 : A))

private theorem closedSubsetOpenComplementRestriction_pushforward_eq_zero
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    closedSubsetOpenComplementRestriction hZ
        ((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ) =
      0 := by
  -- Evaluate the restriction map on an open `U`; it is restriction to `U ∩ (X \ Z)`, where the
  -- pushed-forward source already vanishes by the previous empty-open argument.
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  -- Expanding the unit identifies this component with restriction to `U ∩ (X \ Z)`.
  change
    (ConcreteCategory.hom
        (((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ).presheaf.map
          ((Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op)))
      s = 0
  simpa using
    pushforward_section_eq_zero_of_le_complement hZ ℱ
    (U := U.unop ⊓ closedSubsetOpenComplement hZ)
    (fun x hx ↦ hx.2)
    (((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ).presheaf.map
      ((Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op) s)

/-- Helper for Lemma 17.6.3: every morphism out of a pushed-forward sheaf lands in the
sections-with-support subsheaf of the target. -/
private theorem pushforwardToClosedSubsetSectionsWithSupport_factors
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    {𝒢 : X.Sheaf AddCommGrpCat.{u}}
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ ⟶ 𝒢) :
    (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢).Factors φ := by
  -- Naturality of restriction to the open complement reduces the claim to the vanishing of the
  -- restriction map on the pushed-forward source.
  let f := closedSubsetOpenComplementRestriction hZ 𝒢
  let _ : HasKernel f := HasKernels.has_limit f
  apply kernelSubobject_factors
  calc
    φ ≫ closedSubsetOpenComplementRestriction hZ 𝒢
        = closedSubsetOpenComplementRestriction hZ
            ((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ) ≫
            (Sheaf.pushforward AddCommGrpCat.{u}
              (closedSubsetOpenComplementInclusion hZ)).map
              ((Sheaf.pullback AddCommGrpCat.{u}
                (closedSubsetOpenComplementInclusion hZ)).map φ) := by
          rw [closedSubsetSectionsWithSupportSubsheafMap_w hZ φ]
    _ = 0 := by
      simp [closedSubsetOpenComplementRestriction_pushforward_eq_zero]

/-- Helper for Lemma 17.6.3: the chosen lift of a morphism through the sections-with-support
subsheaf of the target. -/
private noncomputable def pushforwardFactorToClosedSubsetSectionsWithSupport
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    {𝒢 : X.Sheaf AddCommGrpCat.{u}}
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ ⟶ 𝒢) :
    (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ ⟶
      closedSubsetSectionsWithSupportObject hZ 𝒢 :=
  (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢).factorThru φ
    (pushforwardToClosedSubsetSectionsWithSupport_factors hZ ℱ φ)

/-- Helper for Lemma 17.6.3: the chosen factorization through the sections-with-support subsheaf
composes back to the original morphism. -/
private theorem pushforwardFactorToClosedSubsetSectionsWithSupport_comp_arrow
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    {𝒢 : X.Sheaf AddCommGrpCat.{u}}
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ ⟶ 𝒢) :
    pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ φ ≫
        (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢).arrow =
      φ := by
  -- This is the defining property of `Subobject.factorThru`.
  exact Subobject.factorThru_arrow _ _ _

/-- Helper for Lemma 17.6.3: the chosen factorization is natural in the closed-subset source
sheaf. -/
private theorem pushforwardFactorToClosedSubsetSectionsWithSupport_naturality_left
    (hZ : IsClosed Z)
    {ℱ₁ ℱ₂ : (TopCat.of Z).Sheaf AddCommGrpCat.{u}}
    {𝒢 : X.Sheaf AddCommGrpCat.{u}}
    (u : ℱ₁ ⟶ ℱ₂)
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ₂ ⟶ 𝒢) :
    pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ₁
        ((Sheaf.pushforward AddCommGrpCat.{u} iZ).map u ≫ φ) =
      (Sheaf.pushforward AddCommGrpCat.{u} iZ).map u ≫
        pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ₂ φ := by
  -- Both morphisms become the same after composing with the mono support inclusion.
  apply (cancel_mono (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢).arrow).1
  simp [Category.assoc, pushforwardFactorToClosedSubsetSectionsWithSupport_comp_arrow]

/-- Helper for Lemma 17.6.3: the chosen factorization is natural in the ambient target sheaf. -/
private theorem pushforwardFactorToClosedSubsetSectionsWithSupport_naturality_right
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    {𝒢₁ 𝒢₂ : X.Sheaf AddCommGrpCat.{u}}
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ ⟶ 𝒢₁)
    (g : 𝒢₁ ⟶ 𝒢₂) :
    pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ (φ ≫ g) =
      pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ φ ≫
        closedSubsetSectionsWithSupportSubsheafMap hZ g := by
  -- After composing with the target support inclusion, both sides reduce to `φ ≫ g`.
  apply (cancel_mono (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢₂).arrow).1
  simp [Category.assoc, pushforwardFactorToClosedSubsetSectionsWithSupport_comp_arrow]
  simp [closedSubsetSectionsWithSupportSubsheafMap, Category.assoc]

/-- Helper for Lemma 17.6.3: factoring through the sections-with-support subsheaf is equivalent to
giving a raw morphism into the ambient sheaf. -/
private noncomputable def pushforwardFactorThroughClosedSubsetSectionsWithSupportEquiv
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    (𝒢 : X.Sheaf AddCommGrpCat.{u}) :
    (((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ) ⟶ 𝒢) ≃
      (((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ) ⟶
        closedSubsetSectionsWithSupportObject hZ 𝒢) :=
  { toFun := pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ
    invFun := fun φ ↦ φ ≫ (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢).arrow
    left_inv := pushforwardFactorToClosedSubsetSectionsWithSupport_comp_arrow hZ ℱ
    right_inv := by
      intro φ
      apply (cancel_mono (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢).arrow).1
      simpa [Category.assoc] using
        pushforwardFactorToClosedSubsetSectionsWithSupport_comp_arrow hZ ℱ
          (φ := φ ≫ (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢).arrow) }

/-- Helper for Lemma 17.6.3: maps out of a pushed-forward sheaf are equivalent to maps into the
sections-with-support sheaf on the closed subset. -/
private noncomputable def pushforwardClosedSubsetSectionsWithSupportHomEquiv
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    (𝒢 : X.Sheaf AddCommGrpCat.{u}) :
    (((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ) ⟶ 𝒢) ≃
      (ℱ ⟶ (𝓗[hZ]).obj 𝒢) :=
  -- First factor through the support subobject, then apply the ambient adjunction equivalence.
  (pushforwardFactorThroughClosedSubsetSectionsWithSupportEquiv hZ ℱ 𝒢).trans
    ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} iZ).homEquiv ℱ
      (closedSubsetSectionsWithSupportObject hZ 𝒢))

/-- Helper for Lemma 17.6.3: the Hom-equivalence is natural in the closed-subset source sheaf. -/
private theorem pushforwardClosedSubsetSectionsWithSupportHomEquiv_naturality_left
    (hZ : IsClosed Z)
    {ℱ₁ ℱ₂ : (TopCat.of Z).Sheaf AddCommGrpCat.{u}}
    {𝒢 : X.Sheaf AddCommGrpCat.{u}}
    (u : ℱ₁ ⟶ ℱ₂)
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ₂ ⟶ 𝒢) :
    pushforwardClosedSubsetSectionsWithSupportHomEquiv hZ ℱ₁ 𝒢
        ((Sheaf.pushforward AddCommGrpCat.{u} iZ).map u ≫ φ) =
      u ≫ pushforwardClosedSubsetSectionsWithSupportHomEquiv hZ ℱ₂ 𝒢 φ := by
  -- After normalizing the chosen factorization, this is the left naturality of the ambient
  -- pullback/pushforward adjunction.
  simpa [pushforwardClosedSubsetSectionsWithSupportHomEquiv,
    pushforwardFactorThroughClosedSubsetSectionsWithSupportEquiv,
    pushforwardFactorToClosedSubsetSectionsWithSupport_naturality_left] using
    (CategoryTheory.Adjunction.homEquiv_naturality_left_symm
      (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} iZ)
      u
      (pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ₂ φ))

/-- Helper for Lemma 17.6.3: the Hom-equivalence is natural in the ambient target sheaf. -/
private theorem pushforwardClosedSubsetSectionsWithSupportHomEquiv_naturality_right
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    {𝒢₁ 𝒢₂ : X.Sheaf AddCommGrpCat.{u}}
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ ⟶ 𝒢₁)
    (g : 𝒢₁ ⟶ 𝒢₂) :
    pushforwardClosedSubsetSectionsWithSupportHomEquiv hZ ℱ 𝒢₂ (φ ≫ g) =
      pushforwardClosedSubsetSectionsWithSupportHomEquiv hZ ℱ 𝒢₁ φ ≫ (𝓗[hZ]).map g := by
  -- Right naturality is the ambient adjunction naturality after rewriting the target-side
  -- factorization through the support subsheaf map.
  simpa [pushforwardClosedSubsetSectionsWithSupportHomEquiv,
    closedSubsetSectionsWithSupportFunctor,
    pushforwardFactorThroughClosedSubsetSectionsWithSupportEquiv,
    pushforwardFactorToClosedSubsetSectionsWithSupport_naturality_right] using
    (CategoryTheory.Adjunction.homEquiv_naturality_right
      (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} iZ)
      (pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ φ)
      (closedSubsetSectionsWithSupportSubsheafMap hZ g))

/-- Lemma 17.6.3: for a closed subset inclusion `i : Z ↪ X`, pushforward of abelian sheaves is
left adjoint to the explicit sections-with-support functor `𝓗[hZ] = \mathcal H_Z`. -/
@[stacks 01AZ]
noncomputable def closedSubset_pushforwardSectionsWithSupportAdjunction
    (hZ : IsClosed Z) :
    Sheaf.pushforward AddCommGrpCat.{u} iZ ⊣ 𝓗[hZ] :=
  -- Route correction: package the adjunction by the repaired Hom-bijection.
  Adjunction.mkOfHomEquiv
    { homEquiv := pushforwardClosedSubsetSectionsWithSupportHomEquiv hZ
      homEquiv_naturality_left_symm :=
        pushforwardClosedSubsetSectionsWithSupportHomEquiv_naturality_left hZ
      homEquiv_naturality_right :=
        pushforwardClosedSubsetSectionsWithSupportHomEquiv_naturality_right hZ }

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
