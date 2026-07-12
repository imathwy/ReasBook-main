import Mathlib
import StacksProject_2024.Chap06.ClosedSubsetInclusion
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap17.Lemma_17_5_2

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
local instance : HasKernels (TopCat.Sheaf AddCommGrpCat.{u} X) := inferInstance
local notation "iZ" => X.closedSubsetInclusion Z

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
- `bridge/view`: this file rebuilds the local kernel-model owner mirroring Lemma 17.6.3, and then
  proves the support-theoretic characterization of that owner. -/

/-- Helper for Remark 17.6.2: the open complement `X \ Z` viewed as an open subset. -/
private abbrev closedSubsetOpenComplement (hZ : IsClosed Z) : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- Helper for Remark 17.6.2: the inclusion of the open complement into `X`. -/
private abbrev closedSubsetOpenComplementInclusion (hZ : IsClosed Z) :
    (Opens.toTopCat X).obj (closedSubsetOpenComplement hZ) ⟶ X :=
  Opens.inclusion' (closedSubsetOpenComplement hZ)

/-- Helper for Remark 17.6.2: the restriction map from a sheaf on `X` to its pushforward from
the open complement `X \ Z`. -/
private abbrev openComplementRestriction
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    ℱ ⟶
      (Sheaf.pushforward AddCommGrpCat.{u}
        (closedSubsetOpenComplementInclusion hZ)).obj
        ((Sheaf.pullback AddCommGrpCat.{u}
          (closedSubsetOpenComplementInclusion hZ)).obj ℱ) :=
  (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (closedSubsetOpenComplementInclusion hZ)).unit.app ℱ

/-- Helper for Remark 17.6.2: the subsheaf of sections of `ℱ` supported on the closed subset
`Z`. -/
def closedSubsetSectionsWithSupportSubsheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) : Subobject ℱ :=
  let f := openComplementRestriction hZ ℱ
  let _ : HasKernel f := HasKernels.has_limit f
  kernelSubobject f

/-- Helper for Remark 17.6.2: the ambient sheaf on `X` underlying the sections-with-support
construction. -/
private abbrev closedSubsetSectionsWithSupportObject
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    X.Sheaf AddCommGrpCat.{u} :=
  ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ : Subobject ℱ) :
    X.Sheaf AddCommGrpCat.{u})

/-- Helper for Remark 17.6.2: the sheaf on `Z` obtained by restricting the closed-support
subsheaf. -/
def closedSubsetSectionsWithSupportSheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (TopCat.of Z).Sheaf AddCommGrpCat.{u} :=
  (Sheaf.pullback AddCommGrpCat.{u} iZ).obj
    (closedSubsetSectionsWithSupportObject hZ ℱ)

/-- Helper for Remark 17.6.2: naturality of the open-complement restriction map. -/
private theorem closedSubsetSectionsWithSupportSubsheafMap_w
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢) :
    φ ≫ openComplementRestriction hZ 𝒢 =
      openComplementRestriction hZ ℱ ≫
        (Sheaf.pushforward AddCommGrpCat.{u}
          (closedSubsetOpenComplementInclusion hZ)).map
          ((Sheaf.pullback AddCommGrpCat.{u}
            (closedSubsetOpenComplementInclusion hZ)).map φ) := by
  -- Proof comment: this is the unit naturality square for the restriction adjunction.
  simpa [openComplementRestriction] using
    (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (closedSubsetOpenComplementInclusion hZ)).unit.naturality φ

/-- Helper for Remark 17.6.2: the induced morphism on the ambient closed-support subsheaves. -/
private def closedSubsetSectionsWithSupportSubsheafMap
    (hZ : IsClosed Z) {ℱ 𝒢 : X.Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢) :
    closedSubsetSectionsWithSupportObject hZ ℱ ⟶
      closedSubsetSectionsWithSupportObject hZ 𝒢 :=
  let f := openComplementRestriction hZ ℱ
  let g := openComplementRestriction hZ 𝒢
  let _ : HasKernel f := HasKernels.has_limit f
  let _ : HasKernel g := HasKernels.has_limit g
  -- Proof comment: the kernel map is induced by the naturality square above.
  kernelSubobjectMap <|
    Arrow.homMk'
      φ
      ((Sheaf.pushforward AddCommGrpCat.{u}
        (closedSubsetOpenComplementInclusion hZ)).map
        ((Sheaf.pullback AddCommGrpCat.{u}
          (closedSubsetOpenComplementInclusion hZ)).map φ))
      (closedSubsetSectionsWithSupportSubsheafMap_w hZ φ)

/-- Helper for Remark 17.6.2: the induced morphism on sections-with-support sheaves preserves
identity morphisms. -/
private theorem closedSubsetSectionsWithSupportFunctor_map_id
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pullback AddCommGrpCat.{u} iZ).map
      (closedSubsetSectionsWithSupportSubsheafMap hZ (𝟙 ℱ)) =
    𝟙 (closedSubsetSectionsWithSupportSheaf hZ ℱ) := by
  -- Proof comment: kernel maps along identity squares are identities, and pullback preserves them.
  simp [closedSubsetSectionsWithSupportSheaf, closedSubsetSectionsWithSupportSubsheafMap,
    closedSubsetSectionsWithSupportObject, CategoryTheory.Limits.kernelSubobjectMap_id]

/-- Helper for Remark 17.6.2: the induced morphism on sections-with-support sheaves preserves
composition. -/
private theorem closedSubsetSectionsWithSupportFunctor_map_comp
    (hZ : IsClosed Z) {ℱ 𝒢 𝒦 : X.Sheaf AddCommGrpCat.{u}}
    (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ 𝒦) :
    (Sheaf.pullback AddCommGrpCat.{u} iZ).map
      (closedSubsetSectionsWithSupportSubsheafMap hZ (φ ≫ ψ)) =
    (Sheaf.pullback AddCommGrpCat.{u} iZ).map
      (closedSubsetSectionsWithSupportSubsheafMap hZ φ) ≫
      (Sheaf.pullback AddCommGrpCat.{u} iZ).map
        (closedSubsetSectionsWithSupportSubsheafMap hZ ψ) := by
  -- Proof comment: kernel maps compose functorially, and pullback preserves the composition.
  simp [closedSubsetSectionsWithSupportSubsheafMap,
    CategoryTheory.Limits.kernelSubobjectMap_comp]

/-- Helper for Remark 17.6.2: the sheaf-valued functor of sections supported on `Z`. -/
def closedSubsetSectionsWithSupportFunctor
    (hZ : IsClosed Z) :
    X.Sheaf AddCommGrpCat.{u} ⥤ (TopCat.of Z).Sheaf AddCommGrpCat.{u} where
  obj ℱ := closedSubsetSectionsWithSupportSheaf hZ ℱ
  map φ := (Sheaf.pullback AddCommGrpCat.{u} iZ).map
    (closedSubsetSectionsWithSupportSubsheafMap hZ φ)
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

/-- Helper for Remark 17.6.2: a section is killed by the open-complement restriction exactly when
its support is contained in `Z ∩ U`. -/
private theorem openComplementRestriction_eq_zero_iff_support_subset
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X)
    (s : ℱ.presheaf.obj (op U)) :
    (openComplementRestriction hZ ℱ).1.app (op U) s = 0 ↔
      abelianSheafSectionSupport ℱ s ⊆ { x : U | x.1 ∈ Z } := by
  let V : Opens X := U ⊓ closedSubsetOpenComplement hZ
  let i : V ⟶ U := Opens.infLELeft U (closedSubsetOpenComplement hZ)
  constructor
  · intro hs x hx
    -- Proof comment: if `x ∉ Z`, then the restricted section has zero germ at `x`, so the germ of
    -- the original section already vanishes there.
    by_contra hxZ
    have hxV : x.1 ∈ V := ⟨x.2, hxZ⟩
    have hzero :
        ℱ.presheaf.germ V x.1 hxV ((openComplementRestriction hZ ℱ).1.app (op U) s) = 0 := by
      rw [hs]
      simp
    have hgerm :
        ℱ.presheaf.germ U x.1 x.2 s = 0 := by
      calc
        ℱ.presheaf.germ U x.1 x.2 s =
            ℱ.presheaf.germ V x.1 hxV (ℱ.presheaf.map i.op s) := by
              symm
              exact TopCat.Presheaf.germ_res_apply ℱ.presheaf i x.1 hxV s
        _ = ℱ.presheaf.germ V x.1 hxV ((openComplementRestriction hZ ℱ).1.app (op U) s) := by
              simp [openComplementRestriction, V, i]
        _ = 0 := hzero
    exact hx (by simpa [mem_abelianSheafSectionSupport_iff] using hgerm)
  · intro hs
    -- Proof comment: on the open complement, every stalk germ vanishes, so the section itself is
    -- zero by sheaf extensionality.
    apply TopCat.Presheaf.section_ext ℱ.presheaf V ((openComplementRestriction hZ ℱ).1.app (op U) s) 0
    intro x hx
    have hx_not_mem : x ∉ Z := hx.2
    have hx_zero :
        ℱ.presheaf.germ U x hx.1 s = 0 := by
      by_contra hxg
      have hx_support : (⟨x, hx.1⟩ : U) ∈ abelianSheafSectionSupport ℱ s := by
        simpa [mem_abelianSheafSectionSupport_iff] using hxg
      exact hx_not_mem (hs hx_support)
    have hres : (openComplementRestriction hZ ℱ).1.app (op U) s = ℱ.presheaf.map i.op s := by
      simp [openComplementRestriction, V, i]
    rw [hres]
    rw [← TopCat.Presheaf.germ_res_apply ℱ.presheaf i x hx s, hx_zero]
    simp

/-- Helper for Remark 17.6.2: every section of the kernel subsheaf is annihilated by the
restriction to the open complement. -/
private theorem closedSubsetSupportSection_zero
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X)
    (t :
      (((closedSubsetSectionsWithSupportSubsheaf hZ ℱ : Subobject ℱ) :
        X.Sheaf AddCommGrpCat.{u}).presheaf.obj (op U))) :
    (openComplementRestriction hZ ℱ).1.app (op U)
      ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U) t) = 0 := by
  let f := openComplementRestriction hZ ℱ
  let _ : HasKernel f := HasKernels.has_limit f
  -- Proof comment: the defining property of `kernelSubobject` says the support arrow composes to
  -- zero with the open-complement restriction.
  simpa [closedSubsetSectionsWithSupportSubsheaf, f, Category.assoc] using
    congrArg (fun k : ((kernelSubobject f : Subobject ℱ) : X.Sheaf AddCommGrpCat.{u}) ⟶ _ ↦
      k.1.app (op U) t) (kernelSubobject_arrow_comp f)

/-- Helper for Remark 17.6.2: a section killed by the open-complement restriction lifts to a
section of the sections-with-support subsheaf. -/
private noncomputable def zeroSectionToClosedSubsetSupportSection
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X)
    (s : ℱ.presheaf.obj (op U))
    (hs : (openComplementRestriction hZ ℱ).1.app (op U) s = 0) :
    (((closedSubsetSectionsWithSupportSubsheaf hZ ℱ : Subobject ℱ) : X.Sheaf AddCommGrpCat.{u})
      .presheaf.obj (op U)) := by
  let f := openComplementRestriction hZ ℱ
  let _ : HasKernel f := HasKernels.has_limit f
  let ks : ↑(kernel (f.1.app (op U))) :=
    (AddCommGrpCat.kernelIsoKer (f.1.app (op U))).inv ⟨s, hs⟩
  let ps : (kernel f.1).obj (op U) :=
    (PreservesKernel.iso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) f.1).inv ks
  -- Proof comment: first lift the objectwise kernel element to the presheaf kernel, then transport
  -- it back through the sheaf-to-presheaf kernel comparison.
  simpa [closedSubsetSectionsWithSupportSubsheaf, f] using
    ((PreservesKernel.iso
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        f).inv.app (op U) ps)

/-- Helper for Remark 17.6.2: the lifted kernel section maps back to the original ambient section.
-/
private theorem zeroSectionToClosedSubsetSupportSection_arrow
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X)
    (s : ℱ.presheaf.obj (op U))
    (hs : (openComplementRestriction hZ ℱ).1.app (op U) s = 0) :
    ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U))
      (zeroSectionToClosedSubsetSupportSection hZ ℱ U s hs) = s := by
  let f := openComplementRestriction hZ ℱ
  let _ : HasKernel f := HasKernels.has_limit f
  let ks : ↑(kernel (f.1.app (op U))) :=
    (AddCommGrpCat.kernelIsoKer (f.1.app (op U))).inv ⟨s, hs⟩
  let ps : (kernel f.1).obj (op U) :=
    (PreservesKernel.iso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) f.1).inv ks
  -- Proof comment: compare after expanding the two kernel-preservation isomorphisms and the
  -- concrete kernel object in `AddCommGrpCat`.
  change
    ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U))
        (((PreservesKernel.iso
            (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
            f).inv.app (op U)) ps) = s
  have h₁ :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app
        (PreservesKernel.iso_inv_ι
          (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) f)
        (op U))
      ps
  have h₂ :=
    ConcreteCategory.congr_hom
      (PreservesKernel.iso_inv_ι ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) f.1)
      ks
  have h₃ :=
    ConcreteCategory.congr_hom
      (AddCommGrpCat.kernelIsoKer_inv_comp_ι (f.1.app (op U)))
      ⟨s, hs⟩
  simpa [closedSubsetSectionsWithSupportSubsheaf, f] using h₁.trans (h₂.trans h₃)

/-- Helper for Remark 17.6.2: a monomorphism of abelian sheaves preserves section support exactly.
-/
private theorem abelianSheafSectionSupport_map_eq_of_mono
    {𝒢 ℱ : X.Sheaf AddCommGrpCat.{u}} (φ : 𝒢 ⟶ ℱ) [Mono φ]
    (U : Opens X) (s : 𝒢.presheaf.obj (op U)) :
    abelianSheafSectionSupport ℱ (φ.1.app (op U) s) =
      abelianSheafSectionSupport 𝒢 s := by
  ext x
  constructor
  · -- Proof comment: support can only shrink under any sheaf morphism.
    exact AlgebraicGeometry.abelianSheafSectionSupport_map_subset φ s
  · intro hx
    -- Proof comment: stalkwise injectivity of a mono forces a nonzero germ to remain nonzero.
    rw [mem_abelianSheafSectionSupport_iff] at hx ⊢
    have hinj :
        Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map φ.1) := by
      exact
        (AddCommGrpCat.mono_iff_injective _).1
          ((TopCat.Presheaf.mono_iff_stalk_mono φ.1).1 inferInstance x.1)
    intro hx0
    apply hx
    apply hinj
    simpa [TopCat.Presheaf.stalkFunctor_map_germ_apply U x.1 x.2 φ.1 s] using hx0

/-- Helper for Remark 17.6.2: the support of a local section lies inside the support of the whole
sheaf. -/
private theorem sectionSupport_subset_sheafSupport
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) (s : ℱ.presheaf.obj (op U)) :
    Subtype.val '' abelianSheafSectionSupport ℱ s ⊆ abelianSheafSupport ℱ := by
  intro x hx
  -- Proof comment: each local section support is one summand in the union formula for sheaf
  -- support.
  rw [AlgebraicGeometry.abelianSheafSupport_eq_iUnion_abelianSheafSectionSupport]
  rcases hx with ⟨y, hy, rfl⟩
  exact Set.mem_iUnion.2 ⟨U, Set.mem_iUnion.2 ⟨s, ⟨y, hy, rfl⟩⟩⟩

-- Proof sketch: a section of `ℱ(U)` lies in the kernel of the restriction to the open complement
-- exactly when its germs vanish at every point of `U ∩ Zᶜ`; by the definition of section support,
-- this is equivalent to the support being contained in `Z ∩ U`.
/-- Remark 17.6.2: for an open set `U ⊆ X`, the image of the canonical inclusion
`\mathcal H_Z(\mathcal F)(U) \hookrightarrow \mathcal F(U)` is exactly the set of sections whose
support is contained in `Z ∩ U`. This is the source-facing sectionwise description of
`\mathcal H_Z(\mathcal F)`. -/
@[stacks 01AY]
theorem closedSubsetSectionsWithSupportSubsheaf_app_range
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) :
    Set.range ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U)) =
      { s | abelianSheafSectionSupport ℱ s ⊆ { x : U | x.1 ∈ Z } } := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    -- Proof comment: every section of the kernel subsheaf is killed by the complement
    -- restriction, so its support is contained in `Z`.
    exact (openComplementRestriction_eq_zero_iff_support_subset hZ ℱ U _).1
      (closedSubsetSupportSection_zero hZ ℱ U t)
  · intro hs
    -- Proof comment: a section supported in `Z` determines an objectwise kernel element, hence a
    -- section of the kernel subsheaf mapping back to the original section.
    refine ⟨zeroSectionToClosedSubsetSupportSection hZ ℱ U s
        ((openComplementRestriction_eq_zero_iff_support_subset hZ ℱ U s).2 hs), ?_⟩
    exact zeroSectionToClosedSubsetSupportSection_arrow hZ ℱ U s
      ((openComplementRestriction_eq_zero_iff_support_subset hZ ℱ U s).2 hs)

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
    abelianSheafSupport (closedSubsetSectionsWithSupportSubsheaf hZ ℱ) ⊆ Z := by
  intro x hx
  -- Proof comment: any point in the sheaf support comes from a local section, and that local
  -- section stays supported in `Z` after including it into `ℱ`.
  rw [AlgebraicGeometry.abelianSheafSupport_eq_iUnion_abelianSheafSectionSupport] at hx
  rcases Set.mem_iUnion.1 hx with ⟨U, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨s, hx⟩
  rcases hx with ⟨y, hy, rfl⟩
  have hy_image :
      y ∈ abelianSheafSectionSupport ℱ
        ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U) s) := by
    simpa [abelianSheafSectionSupport_map_eq_of_mono
      (closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow U s] using hy
  exact
    (closedSubsetSectionsWithSupportSubsheaf_app_iff hZ ℱ U
      (((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U)) s)).1
      ⟨s, rfl⟩ hy_image

-- Proof sketch: if a subsheaf `G ⊆ ℱ` is supported inside `Z`, then its restriction to the open
-- complement vanishes. Therefore the inclusion `G ⟶ ℱ` factors through the kernel of
-- `ℱ ⟶ j_* j⁻¹ ℱ`, which is exactly `closedSubsetSectionsWithSupportSubsheaf hZ ℱ`.
/-- Any abelian subsheaf of `ℱ` whose support is contained in `Z` factors through the
sections-with-support subsheaf. -/
theorem le_closedSubsetSectionsWithSupportSubsheaf_of_support_subset
    (hZ : IsClosed Z) {ℱ : X.Sheaf AddCommGrpCat.{u}} (G : Subobject ℱ)
    (hG : abelianSheafSupport G ⊆ Z) :
    G ≤ closedSubsetSectionsWithSupportSubsheaf hZ ℱ := by
  let f := openComplementRestriction hZ ℱ
  let _ : HasKernel f := HasKernels.has_limit f
  have hzero : G.arrow ≫ f = 0 := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    -- Proof comment: the image of a local section of `G` is supported inside `Z`, so its
    -- restriction to the open complement vanishes.
    apply (openComplementRestriction_eq_zero_iff_support_subset hZ ℱ U
      (G.arrow.1.app (op U) s)).2
    intro x hx
    have hxGsection :
        x ∈ abelianSheafSectionSupport ((G : Subobject ℱ) : X.Sheaf AddCommGrpCat.{u}) s := by
      exact AlgebraicGeometry.abelianSheafSectionSupport_map_subset G.arrow s hx
    have hxGsheaf : x.1 ∈ abelianSheafSupport ((G : Subobject ℱ) : X.Sheaf AddCommGrpCat.{u}) := by
      exact sectionSupport_subset_sheafSupport
        (((G : Subobject ℱ) : X.Sheaf AddCommGrpCat.{u})) U s ⟨x, hxGsection, rfl⟩
    exact hG hxGsheaf
  -- Proof comment: once the inclusion into `ℱ` is killed by the complement restriction, the
  -- universal property of the kernel subobject gives the desired factorization.
  have hle : G ≤ Subobject.mk ((kernelSubobject f).arrow) := by
    exact
      Subobject.mk_le_mk_of_comm
        (factorThruKernelSubobject f G.arrow hzero) (by
          rw [factorThruKernelSubobject_comp_arrow])
  simpa [closedSubsetSectionsWithSupportSubsheaf, f] using hle

/-- Helper for Remark 17.6.2: every section of a pushed-forward sheaf vanishes on an open subset
disjoint from the closed subset `Z`. -/
private theorem pushforwardSection_eq_zero_of_le_complement
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) {U : Opens X}
    (hU : U ≤ closedSubsetOpenComplement hZ)
    (s : ((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ).presheaf.obj (op U)) :
    s = 0 := by
  -- Proof comment: the inverse-image of such an open is empty inside `Z`, so the section is the
  -- unique section over the empty open.
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

/-- Helper for Remark 17.6.2: the open-complement restriction of a pushed-forward sheaf is zero.
-/
private theorem closedSubsetOpenComplementRestriction_pushforward_eq_zero
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    openComplementRestriction hZ
        ((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ) =
      0 := by
  -- Proof comment: evaluate on each open and reduce to the previous vanishing statement on
  -- `U ∩ (X \ Z)`.
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change
    (ConcreteCategory.hom
        (((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ).presheaf.map
          ((Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op)))
      s = 0
  simpa using
    pushforwardSection_eq_zero_of_le_complement hZ ℱ
      (U := U.unop ⊓ closedSubsetOpenComplement hZ)
      (fun x hx ↦ hx.2)
      (((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ).presheaf.map
        ((Opens.infLELeft U.unop (closedSubsetOpenComplement hZ)).op) s)

/-- Helper for Remark 17.6.2: every morphism out of a pushed-forward sheaf factors through the
closed-support subsheaf of the target. -/
private theorem pushforwardToClosedSubsetSectionsWithSupport_factors
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    {𝒢 : X.Sheaf AddCommGrpCat.{u}}
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ ⟶ 𝒢) :
    (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢).Factors φ := by
  let f := openComplementRestriction hZ 𝒢
  let _ : HasKernel f := HasKernels.has_limit f
  -- Proof comment: naturality reduces the factorization criterion to the vanishing statement for
  -- the pushed-forward source.
  apply kernelSubobject_factors
  calc
    φ ≫ openComplementRestriction hZ 𝒢 =
        openComplementRestriction hZ
            ((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ) ≫
          (Sheaf.pushforward AddCommGrpCat.{u}
            (closedSubsetOpenComplementInclusion hZ)).map
            ((Sheaf.pullback AddCommGrpCat.{u}
              (closedSubsetOpenComplementInclusion hZ)).map φ) := by
          rw [closedSubsetSectionsWithSupportSubsheafMap_w hZ φ]
    _ = 0 := by
      simp [closedSubsetOpenComplementRestriction_pushforward_eq_zero]

/-- Helper for Remark 17.6.2: the chosen factorization through the closed-support subsheaf. -/
private def pushforwardFactorToClosedSubsetSectionsWithSupport
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    {𝒢 : X.Sheaf AddCommGrpCat.{u}}
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ ⟶ 𝒢) :
    (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ ⟶
      closedSubsetSectionsWithSupportObject hZ 𝒢 :=
  (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢).factorThru φ
    (pushforwardToClosedSubsetSectionsWithSupport_factors hZ ℱ φ)

/-- Helper for Remark 17.6.2: the chosen factorization composes back to the original morphism. -/
private theorem pushforwardFactorToClosedSubsetSectionsWithSupport_comp_arrow
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    {𝒢 : X.Sheaf AddCommGrpCat.{u}}
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ ⟶ 𝒢) :
    pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ φ ≫
        (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢).arrow =
      φ := by
  -- Proof comment: this is the defining property of `Subobject.factorThru`.
  exact Subobject.factorThru_arrow _ _ _

/-- Helper for Remark 17.6.2: the chosen factorization is natural in the source sheaf on the
closed subset. -/
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
  -- Proof comment: both maps are equal after composing with the mono support inclusion.
  apply (cancel_mono (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢).arrow).1
  simp [Category.assoc, pushforwardFactorToClosedSubsetSectionsWithSupport_comp_arrow]

/-- Helper for Remark 17.6.2: the chosen factorization is natural in the ambient target sheaf. -/
private theorem pushforwardFactorToClosedSubsetSectionsWithSupport_naturality_right
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    {𝒢₁ 𝒢₂ : X.Sheaf AddCommGrpCat.{u}}
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ ⟶ 𝒢₁)
    (g : 𝒢₁ ⟶ 𝒢₂) :
    pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ (φ ≫ g) =
      pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ φ ≫
        closedSubsetSectionsWithSupportSubsheafMap hZ g := by
  -- Proof comment: compose with the support inclusion and normalize both sides to `φ ≫ g`.
  apply (cancel_mono (closedSubsetSectionsWithSupportSubsheaf hZ 𝒢₂).arrow).1
  simp [Category.assoc, pushforwardFactorToClosedSubsetSectionsWithSupport_comp_arrow]
  simp [closedSubsetSectionsWithSupportSubsheafMap, Category.assoc]

/-- Helper for Remark 17.6.2: factoring through the closed-support subsheaf is equivalent to
giving an arbitrary morphism into the ambient target sheaf. -/
private def pushforwardFactorThroughClosedSubsetSectionsWithSupportEquiv
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

/-- Helper for Remark 17.6.2: morphisms out of a pushed-forward sheaf correspond to morphisms
into the sections-with-support sheaf on `Z`. -/
private def pushforwardClosedSubsetSectionsWithSupportHomEquiv
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    (𝒢 : X.Sheaf AddCommGrpCat.{u}) :
    (((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ) ⟶ 𝒢) ≃
      (ℱ ⟶ (𝓗[hZ]).obj 𝒢) :=
  (pushforwardFactorThroughClosedSubsetSectionsWithSupportEquiv hZ ℱ 𝒢).trans
    ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} iZ).homEquiv ℱ
      (closedSubsetSectionsWithSupportObject hZ 𝒢))

/-- Helper for Remark 17.6.2: the Hom-equivalence is natural in the source sheaf on `Z`. -/
private theorem pushforwardClosedSubsetSectionsWithSupportHomEquiv_naturality_left
    (hZ : IsClosed Z)
    {ℱ₁ ℱ₂ : (TopCat.of Z).Sheaf AddCommGrpCat.{u}}
    {𝒢 : X.Sheaf AddCommGrpCat.{u}}
    (u : ℱ₁ ⟶ ℱ₂)
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ₂ ⟶ 𝒢) :
    pushforwardClosedSubsetSectionsWithSupportHomEquiv hZ ℱ₁ 𝒢
        ((Sheaf.pushforward AddCommGrpCat.{u} iZ).map u ≫ φ) =
      u ≫ pushforwardClosedSubsetSectionsWithSupportHomEquiv hZ ℱ₂ 𝒢 φ := by
  -- Proof comment: after normalizing the chosen factorization, this is left naturality of the
  -- pullback/pushforward adjunction.
  simpa [pushforwardClosedSubsetSectionsWithSupportHomEquiv,
    pushforwardFactorThroughClosedSubsetSectionsWithSupportEquiv,
    pushforwardFactorToClosedSubsetSectionsWithSupport_naturality_left] using
    (CategoryTheory.Adjunction.homEquiv_naturality_left_symm
      (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} iZ)
      u
      (pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ₂ φ))

/-- Helper for Remark 17.6.2: the Hom-equivalence is natural in the ambient target sheaf. -/
private theorem pushforwardClosedSubsetSectionsWithSupportHomEquiv_naturality_right
    (hZ : IsClosed Z) (ℱ : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    {𝒢₁ 𝒢₂ : X.Sheaf AddCommGrpCat.{u}}
    (φ : (Sheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ ⟶ 𝒢₁)
    (g : 𝒢₁ ⟶ 𝒢₂) :
    pushforwardClosedSubsetSectionsWithSupportHomEquiv hZ ℱ 𝒢₂ (φ ≫ g) =
      pushforwardClosedSubsetSectionsWithSupportHomEquiv hZ ℱ 𝒢₁ φ ≫ (𝓗[hZ]).map g := by
  -- Proof comment: right naturality comes from the ambient adjunction after the factorization
  -- step is rewritten through the support subsheaf map.
  simpa [pushforwardClosedSubsetSectionsWithSupportHomEquiv,
    closedSubsetSectionsWithSupportFunctor,
    pushforwardFactorThroughClosedSubsetSectionsWithSupportEquiv,
    pushforwardFactorToClosedSubsetSectionsWithSupport_naturality_right] using
    (CategoryTheory.Adjunction.homEquiv_naturality_right
      (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} iZ)
      (pushforwardFactorToClosedSubsetSectionsWithSupport hZ ℱ φ)
      (closedSubsetSectionsWithSupportSubsheafMap hZ g))

/-- Remark 17.6.2: pushforward from the closed subset is left adjoint to the sections-with-support
functor on abelian sheaves. -/
@[stacks 01AY]
def closedSubset_pushforwardSectionsWithSupportAdjunction
    (hZ : IsClosed Z) :
    Sheaf.pushforward AddCommGrpCat.{u} iZ ⊣ 𝓗[hZ] :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pushforwardClosedSubsetSectionsWithSupportHomEquiv hZ
      homEquiv_naturality_left_symm := by
        intro ℱ₁ ℱ₂ 𝒢 u φ
        exact pushforwardClosedSubsetSectionsWithSupportHomEquiv_naturality_left hZ u φ
      homEquiv_naturality_right := by
        intro ℱ 𝒢₁ 𝒢₂ φ g
        exact pushforwardClosedSubsetSectionsWithSupportHomEquiv_naturality_right hZ ℱ φ g }

variable (hZ : IsClosed Z)

local instance : Functor.IsRightAdjoint (𝓗[hZ]) :=
  (closedSubset_pushforwardSectionsWithSupportAdjunction hZ).isRightAdjoint

/- Remark 17.6.2: the canonical sections-with-support functor
`\mathcal H_Z : Ab(X) \to Ab(Z)` is left exact. This is the canonical owner form
`PreservesFiniteLimits (𝓗[hZ])`, obtained from the right-adjoint structure of `𝓗[hZ]`. -/
#synth PreservesFiniteLimits (𝓗[hZ])

end
