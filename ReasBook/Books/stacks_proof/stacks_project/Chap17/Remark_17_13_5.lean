import Mathlib
import StacksProject_2024.Chap06.ClosedSubsetInclusion
import StacksProject_2024.Chap06.Lemma_6_32_1
import StacksProject_2024.Chap06.Lemma_6_32_3
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_13_1
import StacksProject_2024.Chap17.Lemma_17_5_2

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Helper for Remark 17.13.5: abelian sheaves inherit the ambient preadditive structure. -/
noncomputable local instance abelianSheafPreadditive
    (Y : TopCat.{u}) [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}] :
    Preadditive (Y.Sheaf AddCommGrpCat.{u}) :=
  inferInstanceAs
    (Preadditive
      (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}))

/-- Helper for Remark 17.13.5: abelian sheaves have canonical zero morphisms. -/
noncomputable local instance abelianSheafHasZeroMorphisms
    (Y : TopCat.{u}) [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}] :
    HasZeroMorphisms (Y.Sheaf AddCommGrpCat.{u}) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- Helper for Remark 17.13.5: abelian sheaves have a canonical zero object. -/
noncomputable local instance abelianSheafHasZeroObject
    (Y : TopCat.{u}) [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}] :
    HasZeroObject (Y.Sheaf AddCommGrpCat.{u}) :=
  inferInstanceAs
    (HasZeroObject
      (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}))

section

variable {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)

local instance : HasKernels (TopCat.Sheaf AddCommGrpCat.{u} X) := inferInstance

/-- Helper for Remark 17.13.5: the open complement `X \ Z` viewed as an open subset of `X`. -/
private abbrev abelianOpenComplement : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- Helper for Remark 17.13.5: the inclusion of the open complement of `Z` into `X`. -/
private abbrev abelianOpenComplementInclusion :
    (Opens.toTopCat X).obj (abelianOpenComplement hZ) ⟶ X :=
  Opens.inclusion' (abelianOpenComplement hZ)

/-- Helper for Remark 17.13.5: the abelian restriction map to the pushforward from the open
complement. -/
private abbrev abelianOpenComplementRestriction
    (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    ℱ ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (abelianOpenComplementInclusion hZ)).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
          (abelianOpenComplementInclusion hZ)).obj ℱ) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (abelianOpenComplementInclusion hZ)).unit.app ℱ

/-- Helper for Remark 17.13.5: the abelian closed-support subsheaf is the kernel of the
open-complement restriction map. -/
private def closedSubsetSectionsWithSupportSubsheaf
    (ℱ : X.Sheaf AddCommGrpCat.{u}) : Subobject ℱ :=
  let f := abelianOpenComplementRestriction hZ ℱ
  let _ : HasKernel f := HasKernels.has_limit f
  kernelSubobject f

/-- Helper for Chap17 Remark 17 13 5: a section is killed by the open-complement restriction
exactly when its support is contained in `Z ∩ U`. -/
private theorem abelianOpenComplementRestriction_eq_zero_iff_support_subset
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X)
    (s : ℱ.presheaf.obj (op U)) :
    (abelianOpenComplementRestriction hZ ℱ).1.app (op U) s = 0 ↔
      abelianSheafSectionSupport ℱ s ⊆ { x : U | x.1 ∈ Z } := by
  let V : Opens X := U ⊓ abelianOpenComplement hZ
  let i : V ⟶ U := Opens.infLELeft U (abelianOpenComplement hZ)
  constructor
  · intro hs x hx
    -- Proof comment: outside `Z`, the restricted section has zero germ, so the original germ also
    -- vanishes and the point cannot lie in the support.
    by_contra hxZ
    have hxV : x.1 ∈ V := ⟨x.2, hxZ⟩
    have hzero :
        ℱ.presheaf.germ V x.1 hxV ((abelianOpenComplementRestriction hZ ℱ).1.app (op U) s) = 0 := by
      rw [hs]
      simp
    have hgerm :
        ℱ.presheaf.germ U x.1 x.2 s = 0 := by
      calc
        ℱ.presheaf.germ U x.1 x.2 s =
            ℱ.presheaf.germ V x.1 hxV (ℱ.presheaf.map i.op s) := by
              symm
              exact TopCat.Presheaf.germ_res_apply ℱ.presheaf i x.1 hxV s
        _ = ℱ.presheaf.germ V x.1 hxV ((abelianOpenComplementRestriction hZ ℱ).1.app (op U) s) := by
              simp [abelianOpenComplementRestriction, V, i]
        _ = 0 := hzero
    exact hx (by simpa [mem_abelianSheafSectionSupport_iff] using hgerm)
  · intro hs
    -- Proof comment: every germ on `U ∩ (X \ Z)` vanishes, so the restricted section is zero by
    -- sheaf extensionality.
    apply TopCat.Presheaf.section_ext ℱ.presheaf V ((abelianOpenComplementRestriction hZ ℱ).1.app (op U) s) 0
    intro x hx
    have hx_not_mem : x ∉ Z := hx.2
    have hx_zero :
        ℱ.presheaf.germ U x hx.1 s = 0 := by
      by_contra hxg
      have hx_support : (⟨x, hx.1⟩ : U) ∈ abelianSheafSectionSupport ℱ s := by
        simpa [mem_abelianSheafSectionSupport_iff] using hxg
      exact hx_not_mem (hs hx_support)
    have hres : (abelianOpenComplementRestriction hZ ℱ).1.app (op U) s = ℱ.presheaf.map i.op s := by
      simp [abelianOpenComplementRestriction, V, i]
    rw [hres]
    rw [← TopCat.Presheaf.germ_res_apply ℱ.presheaf i x hx s, hx_zero]
    simp

/-- Helper for Chap17 Remark 17 13 5: every section of the closed-support kernel subsheaf is
annihilated by restriction to the open complement. -/
private theorem closedSubsetSupportSection_zero
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X)
    (t :
      (((closedSubsetSectionsWithSupportSubsheaf hZ ℱ : Subobject ℱ) :
        X.Sheaf AddCommGrpCat.{u}).presheaf.obj (op U))) :
    (abelianOpenComplementRestriction hZ ℱ).1.app (op U)
      ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U) t) = 0 := by
  let f := abelianOpenComplementRestriction hZ ℱ
  let _ : HasKernel f := HasKernels.has_limit f
  -- Proof comment: this is the defining zero-composition property of the kernel subobject arrow.
  simpa [closedSubsetSectionsWithSupportSubsheaf, f, Category.assoc] using
    congrArg (fun k : ((kernelSubobject f : Subobject ℱ) : X.Sheaf AddCommGrpCat.{u}) ⟶ _ ↦
      k.1.app (op U) t) (kernelSubobject_arrow_comp f)

/-- Helper for Chap17 Remark 17 13 5: a section killed by the open-complement restriction lifts
to the closed-support kernel subsheaf. -/
private noncomputable def zeroSectionToClosedSubsetSupportSection
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X)
    (s : ℱ.presheaf.obj (op U))
    (hs : (abelianOpenComplementRestriction hZ ℱ).1.app (op U) s = 0) :
    (((closedSubsetSectionsWithSupportSubsheaf hZ ℱ : Subobject ℱ) : X.Sheaf AddCommGrpCat.{u})
      .presheaf.obj (op U)) := by
  let f := abelianOpenComplementRestriction hZ ℱ
  let _ : HasKernel f := HasKernels.has_limit f
  let ks : ↑(kernel (f.1.app (op U))) :=
    (AddCommGrpCat.kernelIsoKer (f.1.app (op U))).inv ⟨s, hs⟩
  let ps : (kernel f.1).obj (op U) :=
    (PreservesKernel.iso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) f.1).inv ks
  -- Proof comment: first produce the objectwise kernel element, then transport it through the
  -- presheaf and sheaf kernel comparison isomorphisms.
  simpa [closedSubsetSectionsWithSupportSubsheaf, f] using
    ((PreservesKernel.iso
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        f).inv.app (op U) ps)

/-- Helper for Chap17 Remark 17 13 5: the lifted kernel section maps back to the original
ambient section. -/
private theorem zeroSectionToClosedSubsetSupportSection_arrow
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X)
    (s : ℱ.presheaf.obj (op U))
    (hs : (abelianOpenComplementRestriction hZ ℱ).1.app (op U) s = 0) :
    ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U))
      (zeroSectionToClosedSubsetSupportSection hZ ℱ U s hs) = s := by
  let f := abelianOpenComplementRestriction hZ ℱ
  let _ : HasKernel f := HasKernels.has_limit f
  let ks : ↑(kernel (f.1.app (op U))) :=
    (AddCommGrpCat.kernelIsoKer (f.1.app (op U))).inv ⟨s, hs⟩
  let ps : (kernel f.1).obj (op U) :=
    (PreservesKernel.iso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) f.1).inv ks
  -- Proof comment: unwind the two kernel-preservation isomorphisms and the explicit
  -- `AddCommGrpCat` kernel to recover the original section.
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

/-- Helper for Chap17 Remark 17 13 5: a monomorphism of abelian sheaves preserves section support
exactly. -/
private theorem abelianSheafSectionSupport_map_eq_of_mono
    {𝒢 ℱ : X.Sheaf AddCommGrpCat.{u}} (φ : 𝒢 ⟶ ℱ) [Mono φ]
    (U : Opens X) (s : 𝒢.presheaf.obj (op U)) :
    abelianSheafSectionSupport ℱ (φ.1.app (op U) s) =
      abelianSheafSectionSupport 𝒢 s := by
  ext x
  constructor
  · -- Proof comment: support can only shrink under an arbitrary morphism.
    exact AlgebraicGeometry.abelianSheafSectionSupport_map_subset φ s
  · intro hx
    -- Proof comment: monomorphisms induce injective stalk maps, so a nonzero germ stays nonzero.
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

/-- Helper for Chap17 Remark 17 13 5: the support of a local section lies inside the support of
the ambient sheaf. -/
private theorem sectionSupport_subset_sheafSupport
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) (s : ℱ.presheaf.obj (op U)) :
    Subtype.val '' abelianSheafSectionSupport ℱ s ⊆ abelianSheafSupport ℱ := by
  intro x hx
  -- Proof comment: each section support is one of the summands in the union description of the
  -- whole sheaf support.
  rw [AlgebraicGeometry.abelianSheafSupport_eq_iUnion_abelianSheafSectionSupport]
  rcases hx with ⟨y, hy, rfl⟩
  exact Set.mem_iUnion.2 ⟨U, Set.mem_iUnion.2 ⟨s, ⟨y, hy, rfl⟩⟩⟩

/-- Helper for Remark 17.13.5: the image of the abelian closed-support inclusion on sections is
the set of sections supported in `Z ∩ U`. -/
private theorem closedSubsetSectionsWithSupportSubsheaf_app_range
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) :
    Set.range ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U)) =
      { s | abelianSheafSectionSupport ℱ s ⊆ { x : U | x.1 ∈ Z } } := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    -- Proof comment: every section from the kernel subsheaf is killed by restriction to the open
    -- complement, so its support lies inside `Z`.
    exact (abelianOpenComplementRestriction_eq_zero_iff_support_subset hZ ℱ U _).1
      (closedSubsetSupportSection_zero hZ ℱ U t)
  · intro hs
    -- Proof comment: a section supported in `Z` gives an objectwise kernel element, hence a
    -- section of the kernel subsheaf mapping back to the original section.
    refine ⟨zeroSectionToClosedSubsetSupportSection hZ ℱ U s
        ((abelianOpenComplementRestriction_eq_zero_iff_support_subset hZ ℱ U s).2 hs), ?_⟩
    exact zeroSectionToClosedSubsetSupportSection_arrow hZ ℱ U s
      ((abelianOpenComplementRestriction_eq_zero_iff_support_subset hZ ℱ U s).2 hs)

/-- Helper for Remark 17.13.5: the abelian closed-support subsheaf has support contained in `Z`.
-/
private theorem closedSubsetSectionsWithSupportSubsheaf_support_subset
    (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    abelianSheafSupport (closedSubsetSectionsWithSupportSubsheaf hZ ℱ) ⊆ Z := by
  intro x hx
  -- Proof comment: a support point is witnessed by a local section, and the image of that section
  -- in `ℱ` still has support contained in `Z` by the range description.
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
    (closedSubsetSectionsWithSupportSubsheaf_app_range hZ ℱ U
      (((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U)) s)).1
      ⟨s, rfl⟩ hy_image

/-- Helper for Remark 17.13.5: any abelian subsheaf supported in `Z` factors through the abelian
closed-support subsheaf. -/
private theorem le_closedSubsetSectionsWithSupportSubsheaf_of_support_subset
    {ℱ : X.Sheaf AddCommGrpCat.{u}} (G : Subobject ℱ)
    (hG : abelianSheafSupport G ⊆ Z) :
    G ≤ closedSubsetSectionsWithSupportSubsheaf hZ ℱ := by
  let f := abelianOpenComplementRestriction hZ ℱ
  let _ : HasKernel f := HasKernels.has_limit f
  have hzero : G.arrow ≫ f = 0 := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    -- Proof comment: the image of any local section of `G` has support inside `Z`, so its
    -- restriction to the open complement is zero.
    apply (abelianOpenComplementRestriction_eq_zero_iff_support_subset hZ ℱ U
      (G.arrow.1.app (op U) s)).2
    intro x hx
    have hxGsection :
        x ∈ abelianSheafSectionSupport ((G : Subobject ℱ) : X.Sheaf AddCommGrpCat.{u}) s := by
      exact AlgebraicGeometry.abelianSheafSectionSupport_map_subset G.arrow s hx
    have hxGsheaf : x.1 ∈ abelianSheafSupport ((G : Subobject ℱ) : X.Sheaf AddCommGrpCat.{u}) := by
      exact sectionSupport_subset_sheafSupport
        (((G : Subobject ℱ) : X.Sheaf AddCommGrpCat.{u})) U s ⟨x, hxGsection, rfl⟩
    exact hG hxGsheaf
  -- Proof comment: once the inclusion is killed by the complement restriction, it factors through
  -- the kernel subobject by the universal property.
  have hle : G ≤ Subobject.mk ((kernelSubobject f).arrow) := by
    exact
      Subobject.mk_le_mk_of_comm
        (factorThruKernelSubobject f G.arrow hzero) (by
          rw [factorThruKernelSubobject_comp_arrow])
  simpa [closedSubsetSectionsWithSupportSubsheaf, f] using hle

/- Route correction: keep the support-theoretic bridge local to this file, while reusing the
closed-support owner and support lemmas from `Remark_17_6_2`. -/
/-- Helper for Remark 17.13.5: an additive sheaf on `X` lies in the essential image of
pushforward from a closed subset exactly when its support is contained in that closed subset. -/
private theorem closedSubsetAbelianSheafPushforward_essImage_iff_support_subset
    (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (TopCat.closedSubsetInclusion X Z)).essImage ℱ ↔
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

end

/-
Domain-style sampling for Remark 17.13.5:
- primary domain: `\mathcal O_X`-modules on a ringed space `X`, sections with support in a closed
  subset `Z ⊆ X`, and the induced functor with values in `\operatorname{Mod}(\mathcal O_X|_Z)`;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `RingedSpace.Hom.pushforward`,
  `TopCat.closedSubsetInclusion`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`;
- best owner abstraction: the neutral ambient owner layer is the closed-subset module category
  `RingedSpace.closedSubsetModuleCategory X Z` together with the canonical functors
  `RingedSpace.closedSubsetModulePullback X Z` and
  `RingedSpace.closedSubsetModulePushforward X Z`; the source-facing owner is the closed-subset
  kernel model
  `RingedSpace.ClosedSubsetSectionsWithSupport.subsheaf hZ ℱ ⊆ ℱ`, together with the induced
  module sheaf `𝓗[hZ](ℱ)` on the closed subset with restricted structure sheaf
  `\mathcal O_X|_Z`; the adjunction with closed-subset pushforward is the next numbered companion
  item, and the closed-immersion presentation is only a bridge/view obtained by pulling this
  source-facing object back along a closed immersion whose image is `Z`;
- primitive data: a ringed space `X`, a closed subset `Z ⊆ X`, a proof `hZ : IsClosed Z`, and an
  `\mathcal O_X`-module `ℱ`;
- derived API: the kernel-model subsheaf on `X`, the restricted module sheaf on `Z`, the functor
  `𝓗[hZ] = \mathcal H_Z`, and its support/maximality and left-exactness properties.

Source/core/bridge triage:
- `core/canonical`: `RingedSpace.closedSubsetModuleCategory`,
  `RingedSpace.closedSubsetModulePullback`, and `RingedSpace.closedSubsetModulePushforward`;
- `source-facing`: `RingedSpace.ClosedSubsetSectionsWithSupport.subsheaf`,
  `RingedSpace.ClosedSubsetSectionsWithSupport.sheaf`,
  `RingedSpace.ClosedSubsetSectionsWithSupport.functor`;
- `bridge/internal`: `RingedSpace.closedSubsetStructureSheafHom`, the unit of
  `TopCat.Sheaf.pullbackPushforwardAdjunction` for `RingedSpace.closedSubsetInclusion`, together
  with the adjunction recorded as the next numbered item;
- `bridge/view`: the minimal closed-immersion specialization obtained by pulling the support
  subsheaf back along a closed immersion, used only internally to produce the induced
  left-adjoint structure on `i _*`.
-/

namespace RingedSpace

section

variable {X : RingedSpace.{u}} {Z : Set X}

/-- The inclusion of a closed subset into the ambient ringed space. -/
abbrev closedSubsetInclusion (X : RingedSpace.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.closedSubsetInclusion (X : TopCat) Z

/-- The inverse-image map on opens induced by the closed-subset inclusion is continuous for the
canonical Grothendieck topologies. -/
instance closedSubsetInclusion_opensMap_isContinuous (X : RingedSpace.{u}) (Z : Set X) :
    (Opens.map (closedSubsetInclusion X Z)).IsContinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z)) := by
  -- This is the underlying topological continuity of the subtype inclusion.
  change (Opens.map (TopCat.closedSubsetInclusion (X : TopCat) Z)).IsContinuous
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z))
  infer_instance

/-- The restricted structure sheaf `\mathcal O_X|_Z` on the closed subset `Z`. -/
abbrev closedSubsetRestrictedRingCatSheaf (X : RingedSpace.{u}) (Z : Set X) :
    TopCat.Sheaf RingCat.{u} (TopCat.of Z) :=
  (TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj (RingedSpace.ringCatSheaf X)

/-- The category of `\mathcal O_X|_Z`-modules on the closed subset `Z`. -/
abbrev closedSubsetModuleCategory (X : RingedSpace.{u}) (Z : Set X) :=
  SheafOfModules (closedSubsetRestrictedRingCatSheaf X Z)

/-- The canonical structure-sheaf map `\mathcal O_X \to i_* \mathcal O_X|_Z` attached to the
closed-subset inclusion `i : Z ↪ X`. -/
abbrev closedSubsetStructureSheafHom (X : RingedSpace.{u}) (Z : Set X) :
    RingedSpace.ringCatSheaf X ⟶
      (TopCat.Sheaf.pushforward RingCat.{u}
        (closedSubsetInclusion X Z)).obj (closedSubsetRestrictedRingCatSheaf X Z) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
    (closedSubsetInclusion X Z)).unit.app (RingedSpace.ringCatSheaf X)

/-- Restriction of `\mathcal O_X`-modules to the closed subset `Z`. -/
abbrev closedSubsetModulePullback (X : RingedSpace.{u}) (Z : Set X) :
    RingedSpace.Modules X ⥤ closedSubsetModuleCategory X Z :=
  SheafOfModules.pullback (closedSubsetStructureSheafHom X Z)

/-- Pushforward of `\mathcal O_X|_Z`-modules from the closed subset `Z` back to `X`. -/
noncomputable abbrev closedSubsetModulePushforward (X : RingedSpace.{u}) (Z : Set X) :
    closedSubsetModuleCategory X Z ⥤ RingedSpace.Modules X :=
  SheafOfModules.pushforward (closedSubsetStructureSheafHom X Z)

end

namespace ClosedSubsetSectionsWithSupport

section

variable {X : RingedSpace.{u}} {Z : Set X}

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

/-- The open complement of a closed subset of a ringed space. -/
abbrev openComplement : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The structural ring-sheaf morphism attached to the open complement of a closed subset. -/
private abbrev openComplementStructureSheafHom :
    RingedSpace.ringCatSheaf X ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} (openComplement hZ).inclusion').obj
        ((TopCat.Sheaf.pullback RingCat.{u} (openComplement hZ).inclusion').obj
          (RingedSpace.ringCatSheaf X)) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
    (openComplement hZ).inclusion').unit.app (RingedSpace.ringCatSheaf X)

/-- Restriction of `\mathcal O_X`-modules to the open complement of a closed subset. -/
private abbrev openComplementRestrictionFunctor :
    RingedSpace.Modules X ⥤
      SheafOfModules
        ((TopCat.Sheaf.pullback RingCat.{u} (openComplement hZ).inclusion').obj
          (RingedSpace.ringCatSheaf X)) :=
  moduleSheafRestrictionToOpen (openComplement hZ) (RingedSpace.ringCatSheaf X)

/-- Pushforward from the open complement back to `X`. -/
private abbrev openComplementPushforwardFunctor :
    SheafOfModules
        ((TopCat.Sheaf.pullback RingCat.{u} (openComplement hZ).inclusion').obj
          (RingedSpace.ringCatSheaf X)) ⥤
      RingedSpace.Modules X :=
  SheafOfModules.pushforward (openComplementStructureSheafHom hZ)

/-- The canonical restriction map from an `\mathcal O_X`-module to the pushforward of its
restriction to the open complement of a closed subset. -/
abbrev openComplementRestriction (ℱ : RingedSpace.Modules X) :
    ℱ ⟶
      (openComplementPushforwardFunctor hZ).obj
        ((openComplementRestrictionFunctor hZ).obj ℱ) :=
  (SheafOfModules.pullbackPushforwardAdjunction (openComplementStructureSheafHom hZ)).unit.app ℱ

/-- The source-facing subsheaf of `\mathcal F` consisting of sections whose support lies in the
closed subset `Z`. -/
def subsheaf (ℱ : RingedSpace.Modules X) : Subobject ℱ :=
  kernelSubobject (openComplementRestriction hZ ℱ)

/-- The sections-with-support subsheaf is the kernel of the canonical restriction map to the open
complement. -/
theorem subsheaf_eq_kernel (ℱ : RingedSpace.Modules X) :
    subsheaf hZ ℱ = kernelSubobject (openComplementRestriction hZ ℱ) :=
  rfl

private abbrev object (ℱ : RingedSpace.Modules X) : RingedSpace.Modules X :=
  ((subsheaf hZ ℱ : Subobject ℱ) : RingedSpace.Modules X)

/-- The sheaf on the closed subset `Z` obtained by restricting the subsheaf of sections of `ℱ`
supported on `Z`. -/
def sheaf (ℱ : RingedSpace.Modules X) : RingedSpace.closedSubsetModuleCategory X Z :=
  (RingedSpace.closedSubsetModulePullback X Z).obj (object hZ ℱ)

-- Proof sketch: this is the naturality of the unit of the adjunction `j^* ⊣ j_*` for the open
-- complement inclusion `j : X \ Z ↪ X`.
/-- Naturality of the restriction map to the open complement of a closed subset. -/
private theorem subsheafMap_w {ℱ 𝒢 : RingedSpace.Modules X} (φ : ℱ ⟶ 𝒢) :
    φ ≫ openComplementRestriction hZ 𝒢 =
      openComplementRestriction hZ ℱ ≫
        (openComplementPushforwardFunctor hZ).map
          ((openComplementRestrictionFunctor hZ).map φ) := by
  -- This is exactly the unit naturality square for the restriction/pushforward adjunction.
  simpa using
    (SheafOfModules.pullbackPushforwardAdjunction
      (openComplementStructureSheafHom hZ)).unit.naturality φ

/-- The morphism on closed-support subsheaves induced by a morphism of `\mathcal O_X`-modules. -/
def subsheafMap {ℱ 𝒢 : RingedSpace.Modules X} (φ : ℱ ⟶ 𝒢) :
    ((subsheaf hZ ℱ : Subobject ℱ) : RingedSpace.Modules X) ⟶
      ((subsheaf hZ 𝒢 : Subobject 𝒢) : RingedSpace.Modules X) :=
  kernelSubobjectMap <|
    Arrow.homMk'
      φ
      ((openComplementPushforwardFunctor hZ).map
        ((openComplementRestrictionFunctor hZ).map φ))
      (subsheafMap_w hZ φ)

-- Proof sketch: the induced map on kernels is functorial, and restriction to the closed subset
-- preserves identity morphisms.
/-- The induced morphism on sections-with-support sheaves respects identity morphisms. -/
private theorem functor_map_id (ℱ : RingedSpace.Modules X) :
    (RingedSpace.closedSubsetModulePullback X Z).map (subsheafMap hZ (𝟙 ℱ)) =
      𝟙 (sheaf hZ ℱ) := by
  -- Kernel maps along the identity square are identities, and pullback preserves identities.
  simp [sheaf, subsheafMap, object, CategoryTheory.Limits.kernelSubobjectMap_id]

-- Proof sketch: compose the naturality squares for `φ` and `ψ`, then use functoriality of
-- `kernelSubobjectMap` and restriction to the closed subset.
/-- The induced morphism on sections-with-support sheaves respects composition. -/
private theorem functor_map_comp
    {ℱ 𝒢 𝒦 : RingedSpace.Modules X} (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ 𝒦) :
    (RingedSpace.closedSubsetModulePullback X Z).map (subsheafMap hZ (φ ≫ ψ)) =
      (RingedSpace.closedSubsetModulePullback X Z).map (subsheafMap hZ φ) ≫
        (RingedSpace.closedSubsetModulePullback X Z).map (subsheafMap hZ ψ) := by
  -- Kernel maps compose functorially, and then pullback preserves the resulting composition.
  simp [subsheafMap, CategoryTheory.Limits.kernelSubobjectMap_comp]

/-- Remark 17.13.5: the functor `𝓗[hZ] = \mathcal H_Z` sending an `\mathcal O_X`-module to its
sheaf of sections supported on the closed subset `Z`, viewed as an `\mathcal O_X|_Z`-module. -/
@[stacks 0G6N]
def functor : RingedSpace.Modules X ⥤ RingedSpace.closedSubsetModuleCategory X Z where
  obj ℱ := sheaf hZ ℱ
  map φ := (RingedSpace.closedSubsetModulePullback X Z).map (subsheafMap hZ φ)
  map_id := functor_map_id hZ
  map_comp := functor_map_comp hZ

end

@[inherit_doc]
scoped[RingedSpaceClosedSubsetSectionsWithSupport] notation "𝓗[" hZ "]" =>
  RingedSpace.ClosedSubsetSectionsWithSupport.functor hZ

open scoped RingedSpaceClosedSubsetSectionsWithSupport

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

/-- Helper for Remark 17.13.5: any module subsheaf whose support is contained in `Z` factors
through the canonical sections-with-support subsheaf. -/
private theorem subsheaf_le_of_support_subset
    {ℱ : RingedSpace.Modules X} (𝒢 : Subobject ℱ) (h𝒢 : moduleSupport 𝒢 ⊆ Z) :
    𝒢 ≤ subsheaf hZ ℱ := by
  -- Forgetting to the underlying abelian sheaf reduces the maximality statement to the earlier
  -- closed-subset support theorem.
  simpa [moduleSupport] using
    (le_closedSubsetSectionsWithSupportSubsheaf_of_support_subset hZ 𝒢 h𝒢)

private theorem subsheaf_pushforward_eq_top
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z) :
    subsheaf hZ ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) = ⊤ := by
  -- The pushed-forward module already has support contained in `Z`, so maximality forces the
  -- support subsheaf to be the whole object.
  rw [eq_top_iff]
  have hsupport :
      moduleSupport ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) ⊆ Z := by
    -- Forget to additive sheaves, where the object is tautologically in the essential image of
    -- closed-subset pushforward.
    simpa [moduleSupport, RingedSpace.closedSubsetModulePushforward] using
      (closedSubsetAbelianSheafPushforward_essImage_iff_support_subset hZ
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj
          ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ))).1
        (by
          simpa [RingedSpace.closedSubsetModulePushforward] using
            (Functor.obj_mem_essImage
              (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
                (RingedSpace.closedSubsetInclusion X Z))
              ((SheafOfModules.toSheaf
                (RingedSpace.closedSubsetRestrictedRingCatSheaf X Z)).obj ℱ)))
  simpa using
    (subsheaf_le_of_support_subset hZ
      (⊤ : Subobject ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ))
      hsupport)

private theorem restriction_pushforward_counitApp_isIso
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z) :
    IsIso
      ((SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.closedSubsetStructureSheafHom X Z)).counit.app ℱ) := by
  -- The module counit is the closed-subset pullback/pushforward counit on the underlying sheaf.
  simpa using
    (subsetSheaf_pullback_pushforward_counit_isIso
      ((SheafOfModules.toSheaf (RingedSpace.closedSubsetRestrictedRingCatSheaf X Z)).obj ℱ))

private theorem object_restriction_pushforward_unitApp_isIso (ℱ : RingedSpace.Modules X) :
    IsIso
      ((SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.closedSubsetStructureSheafHom X Z)).unit.app (object hZ ℱ)) := by
  -- Reflect the module claim to the underlying abelian sheaf, where support containment puts the
  -- object in the essential image of closed-subset pushforward.
  apply isIso_of_reflects_iso _ (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X))
    have hsupport :
      abelianSheafSupport
          ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj (object hZ ℱ)) ⊆ Z := by
    -- The support object is exactly the abelian sections-with-support subsheaf on the underlying
    -- additive sheaf.
    simpa [RingedSpace.ClosedSubsetSectionsWithSupport.object]
      using closedSubsetSectionsWithSupportSubsheaf_support_subset hZ
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ)
  have hess :
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
          (RingedSpace.closedSubsetInclusion X Z)).essImage
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj (object hZ ℱ)) := by
    exact
      (closedSubsetAbelianSheafPushforward_essImage_iff_support_subset hZ
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj (object hZ ℱ))).2
        hsupport
  let _ :
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (RingedSpace.closedSubsetInclusion X Z)).Full := inferInstance
  let _ :
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (RingedSpace.closedSubsetInclusion X Z)).Faithful := inferInstance
  simpa [RingedSpace.closedSubsetModulePullback, RingedSpace.closedSubsetModulePushforward,
    RingedSpace.closedSubsetStructureSheafHom]
    using
      (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (RingedSpace.closedSubsetInclusion X Z)).isIso_unit_app_iff_mem_essImage :
          IsIso
            ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
              (RingedSpace.closedSubsetInclusion X Z)).unit.app
                ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj (object hZ ℱ))) ↔
              (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
                (RingedSpace.closedSubsetInclusion X Z)).essImage
                ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj (object hZ ℱ)))).2
        hess

/-- Helper for Remark 17.13.5: the canonical restriction of a pushed-forward closed-subset module
to the open complement vanishes. -/
private theorem pushforward_openComplementRestriction_eq_zero
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z) :
    openComplementRestriction hZ ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) = 0 := by
  -- Once the support subsheaf is `⊤`, its kernel arrow is invertible, so the defining
  -- restriction morphism must itself be zero.
  let 𝒢 := (RingedSpace.closedSubsetModulePushforward X Z).obj ℱ
  have hcomp :
      (subsheaf hZ 𝒢).arrow ≫ openComplementRestriction hZ 𝒢 = 0 := by
    simpa [subsheaf] using kernelSubobject_arrow_comp (openComplementRestriction hZ 𝒢)
  have hIso : IsIso (subsheaf hZ 𝒢).arrow := by
    exact (Subobject.isIso_arrow_iff_eq_top (subsheaf hZ 𝒢)).2 (subsheaf_pushforward_eq_top hZ ℱ)
  have hcancel :
      inv (subsheaf hZ 𝒢).arrow ≫ ((subsheaf hZ 𝒢).arrow ≫ openComplementRestriction hZ 𝒢) =
        openComplementRestriction hZ 𝒢 := by
    simpa [Category.assoc] using
      IsIso.inv_hom_id_assoc (subsheaf hZ 𝒢).arrow (openComplementRestriction hZ 𝒢)
  rw [← hcancel]
  simp [hcomp]

/-- Helper for Remark 17.13.5: every morphism from a pushed-forward closed-subset module factors
through the sections-with-support subsheaf of the target. -/
private theorem pushforwardToSubsheaf_factors
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z)
    {𝒢 : RingedSpace.Modules X}
    (φ : ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) ⟶ 𝒢) :
    (subsheaf hZ 𝒢).Factors φ := by
  -- Naturality of restriction to the open complement reduces the claim to the previous vanishing
  -- statement for the pushed-forward source.
  apply kernelSubobject_factors
  calc
    φ ≫ openComplementRestriction hZ 𝒢
        = openComplementRestriction hZ ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) ≫
            (openComplementPushforwardFunctor hZ).map
              ((openComplementRestrictionFunctor hZ).map φ) := by
          rw [subsheafMap_w hZ φ]
    _ = 0 := by
      simp [pushforward_openComplementRestriction_eq_zero]

/-- Helper for Remark 17.13.5: the factorization of a map from a pushed-forward module through the
sections-with-support subsheaf of the target. -/
private noncomputable def pushforwardFactorToSubsheaf
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z)
    {𝒢 : RingedSpace.Modules X}
    (φ : ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) ⟶ 𝒢) :
    ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) ⟶ object hZ 𝒢 :=
  (subsheaf hZ 𝒢).factorThru φ (pushforwardToSubsheaf_factors hZ ℱ φ)

/-- Helper for Remark 17.13.5: the chosen factorization through the support subsheaf composes
back to the original morphism. -/
private theorem pushforwardFactorToSubsheaf_comp_arrow
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z)
    {𝒢 : RingedSpace.Modules X}
    (φ : ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) ⟶ 𝒢) :
    pushforwardFactorToSubsheaf hZ ℱ φ ≫ (subsheaf hZ 𝒢).arrow = φ := by
  -- This is the defining property of `Subobject.factorThru`.
  exact Subobject.factorThru_arrow _ _ _

/-- Helper for Remark 17.13.5: factoring through the support subsheaf is natural in the
closed-subset source object. -/
private theorem pushforwardFactorToSubsheaf_naturality_left
    {ℱ₁ ℱ₂ : RingedSpace.closedSubsetModuleCategory X Z}
    {𝒢 : RingedSpace.Modules X}
    (u : ℱ₁ ⟶ ℱ₂)
    (φ : ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ₂) ⟶ 𝒢) :
    pushforwardFactorToSubsheaf hZ ℱ₁
        ((RingedSpace.closedSubsetModulePushforward X Z).map u ≫ φ) =
      (RingedSpace.closedSubsetModulePushforward X Z).map u ≫
        pushforwardFactorToSubsheaf hZ ℱ₂ φ := by
  -- Both morphisms become the same map after composing with the mono support inclusion.
  apply (cancel_mono (subsheaf hZ 𝒢).arrow).1
  rw [Category.assoc, pushforwardFactorToSubsheaf_comp_arrow]
  rw [Category.assoc, pushforwardFactorToSubsheaf_comp_arrow]

/-- Helper for Remark 17.13.5: factoring through the support subsheaf is natural in the ambient
module target. -/
private theorem pushforwardFactorToSubsheaf_naturality_right
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z)
    {𝒢₁ 𝒢₂ : RingedSpace.Modules X}
    (φ : ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) ⟶ 𝒢₁)
    (g : 𝒢₁ ⟶ 𝒢₂) :
    pushforwardFactorToSubsheaf hZ ℱ (φ ≫ g) =
      pushforwardFactorToSubsheaf hZ ℱ φ ≫ subsheafMap hZ g := by
  -- After composing with the target support inclusion, both sides reduce to `φ ≫ g`.
  apply (cancel_mono (subsheaf hZ 𝒢₂).arrow).1
  rw [Category.assoc, pushforwardFactorToSubsheaf_comp_arrow]
  rw [Category.assoc, Category.assoc, pushforwardFactorToSubsheaf_comp_arrow]
  simp [subsheafMap, Category.assoc]

/-- Helper for Remark 17.13.5: applying the Hom-equivalence and then its inverse recovers the
original morphism from the pushed-forward source. -/
private theorem pushforwardSectionsWithSupportHomEquiv_left_inv
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z)
    (𝒢 : RingedSpace.Modules X) :
    Function.LeftInverse
      (fun φ : ℱ ⟶ (𝓗[hZ]).obj 𝒢 =>
        ((SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.closedSubsetStructureSheafHom X Z)).homEquiv ℱ (object hZ 𝒢)).symm φ ≫
          (subsheaf hZ 𝒢).arrow)
      (fun φ : ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) ⟶ 𝒢 =>
        (SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.closedSubsetStructureSheafHom X Z)).homEquiv ℱ (object hZ 𝒢)
          (pushforwardFactorToSubsheaf hZ ℱ φ)) := by
  intro φ
  -- The ambient map is recovered by undoing the pullback/pushforward equivalence and then
  -- composing with the support inclusion.
  rw [Equiv.symm_apply_apply]
  exact pushforwardFactorToSubsheaf_comp_arrow hZ ℱ φ

/-- Helper for Remark 17.13.5: applying the inverse of the Hom-equivalence and then the
Hom-equivalence itself recovers the original morphism on the closed subset. -/
private theorem pushforwardSectionsWithSupportHomEquiv_right_inv
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z)
    (𝒢 : RingedSpace.Modules X) :
    Function.RightInverse
      (fun φ : ℱ ⟶ (𝓗[hZ]).obj 𝒢 =>
        ((SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.closedSubsetStructureSheafHom X Z)).homEquiv ℱ (object hZ 𝒢)).symm φ ≫
          (subsheaf hZ 𝒢).arrow)
      (fun φ : ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) ⟶ 𝒢 =>
        (SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.closedSubsetStructureSheafHom X Z)).homEquiv ℱ (object hZ 𝒢)
          (pushforwardFactorToSubsheaf hZ ℱ φ)) := by
  intro φ
  -- The chosen factorization of a map that already lands in the support subsheaf is the original
  -- lift, so the pullback/pushforward equivalence simplifies by `apply_symm_apply`.
  apply (SheafOfModules.pullbackPushforwardAdjunction
      (RingedSpace.closedSubsetStructureSheafHom X Z)).homEquiv ℱ (object hZ 𝒢) |>.injective
  apply (cancel_mono (subsheaf hZ 𝒢).arrow).1
  rw [Category.assoc, pushforwardFactorToSubsheaf_comp_arrow]
  rw [Equiv.apply_symm_apply]

/-- Helper for Remark 17.13.5: maps out of a pushed-forward closed-subset module are equivalent to
maps into the sections-with-support module on the closed subset. -/
private noncomputable def pushforwardSectionsWithSupportHomEquiv
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z)
    (𝒢 : RingedSpace.Modules X) :
    (((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) ⟶ 𝒢) ≃
      (ℱ ⟶ (𝓗[hZ]).obj 𝒢) :=
  { toFun := fun φ =>
      (SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.closedSubsetStructureSheafHom X Z)).homEquiv ℱ (object hZ 𝒢)
        (pushforwardFactorToSubsheaf hZ ℱ φ)
    invFun := fun φ =>
      ((SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.closedSubsetStructureSheafHom X Z)).homEquiv ℱ (object hZ 𝒢)).symm φ ≫
        (subsheaf hZ 𝒢).arrow
    left_inv := pushforwardSectionsWithSupportHomEquiv_left_inv hZ ℱ 𝒢
    right_inv := pushforwardSectionsWithSupportHomEquiv_right_inv hZ ℱ 𝒢 }

/-- Helper for Remark 17.13.5: the Hom-equivalence is natural in the closed-subset source
variable. -/
private theorem pushforwardSectionsWithSupportHomEquiv_naturality_left
    {ℱ₁ ℱ₂ : RingedSpace.closedSubsetModuleCategory X Z}
    {𝒢 : RingedSpace.Modules X}
    (u : ℱ₁ ⟶ ℱ₂)
    (φ : ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ₂) ⟶ 𝒢) :
    pushforwardSectionsWithSupportHomEquiv hZ ℱ₁ 𝒢
        ((RingedSpace.closedSubsetModulePushforward X Z).map u ≫ φ) =
      u ≫ pushforwardSectionsWithSupportHomEquiv hZ ℱ₂ 𝒢 φ := by
  -- After normalizing the chosen factorization, this is exactly the left naturality of the
  -- ambient pullback/pushforward adjunction.
  simpa [pushforwardSectionsWithSupportHomEquiv,
    pushforwardFactorToSubsheaf_naturality_left] using
    (CategoryTheory.Adjunction.homEquiv_naturality_left_symm
      (SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.closedSubsetStructureSheafHom X Z))
      u
      (pushforwardFactorToSubsheaf hZ ℱ₂ φ))

/-- Helper for Remark 17.13.5: the Hom-equivalence is natural in the ambient module target. -/
private theorem pushforwardSectionsWithSupportHomEquiv_naturality_right
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z)
    {𝒢₁ 𝒢₂ : RingedSpace.Modules X}
    (φ : ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) ⟶ 𝒢₁)
    (g : 𝒢₁ ⟶ 𝒢₂) :
    pushforwardSectionsWithSupportHomEquiv hZ ℱ 𝒢₂ (φ ≫ g) =
      pushforwardSectionsWithSupportHomEquiv hZ ℱ 𝒢₁ φ ≫ (𝓗[hZ]).map g := by
  -- The right naturality likewise comes directly from the owner adjunction after rewriting the
  -- target-side factorization through `subsheafMap`.
  simpa [pushforwardSectionsWithSupportHomEquiv,
    RingedSpace.ClosedSubsetSectionsWithSupport.functor,
    pushforwardFactorToSubsheaf_naturality_right] using
    (CategoryTheory.Adjunction.homEquiv_naturality_right
      (SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.closedSubsetStructureSheafHom X Z))
      (pushforwardFactorToSubsheaf hZ ℱ φ)
      (subsheafMap hZ g))

private noncomputable abbrev pushforwardSectionsWithSupportAdjunctionUnitApp
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z) :
    ℱ ⟶
      (𝓗[hZ]).obj ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) :=
  @inv _ _ _ _
      ((SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.closedSubsetStructureSheafHom X Z)).counit.app ℱ)
      (restriction_pushforward_counitApp_isIso ℱ) ≫
    (RingedSpace.closedSubsetModulePullback X Z).map
      ((asIso ((⊤ : Subobject
          ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ)).arrow)).inv ≫
        (Subobject.isoOfEq
          (subsheaf hZ ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ))
          ⊤
          (subsheaf_pushforward_eq_top hZ ℱ)).symm.hom)

private noncomputable abbrev pushforwardSectionsWithSupportAdjunctionCounitApp
    (ℱ : RingedSpace.Modules X) :
    (RingedSpace.closedSubsetModulePushforward X Z).obj ((𝓗[hZ]).obj ℱ) ⟶ ℱ :=
  @inv _ _ _ _
      ((SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.closedSubsetStructureSheafHom X Z)).unit.app (object hZ ℱ))
      (object_restriction_pushforward_unitApp_isIso hZ ℱ) ≫
    (subsheaf hZ ℱ).arrow

-- Proof sketch: the explicit sections-with-support construction on `X` yields the canonical
-- closed-subset adjunction used in Lemma 17.13.6.
/-- The canonical adjunction between pushforward from the closed subset `Z` and the explicit
sections-with-support functor `𝓗[hZ] = \mathcal H_Z`. -/
noncomputable def pushforwardSectionsWithSupportAdjunction :
    RingedSpace.closedSubsetModulePushforward X Z ⊣ 𝓗[hZ] :=
  -- Route correction: package the adjunction by a Hom-equivalence, so the proof only uses the
  -- kernel factorization and the existing pullback/pushforward adjunction.
  Adjunction.mkOfHomEquiv
    { homEquiv := pushforwardSectionsWithSupportHomEquiv hZ
      homEquiv_naturality_left_symm :=
        pushforwardSectionsWithSupportHomEquiv_naturality_left hZ
      homEquiv_naturality_right :=
        pushforwardSectionsWithSupportHomEquiv_naturality_right hZ }

end

/-- For an open set `U ⊆ X`, the image of the canonical inclusion
`\mathcal H_Z(\mathcal F)_X(U) \hookrightarrow \mathcal F(U)` is exactly the set of sections whose
support is contained in `Z ∩ U`. -/
theorem subsheaf_app_range
    {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)
    (ℱ : RingedSpace.Modules X) (U : Opens X) :
    Set.range ((subsheaf hZ ℱ).arrow.val.app (op U)) =
      { s | moduleSectionSupport s ⊆ { x : U | x.1 ∈ Z } } := by
  -- Forgetting the module structure reduces the claim to the abelian closed-support statement.
  simpa [moduleSectionSupport] using
    (closedSubsetSectionsWithSupportSubsheaf_app_range hZ
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ) U)

/-- A section of `\mathcal F(U)` lies in the image of `\mathcal H_Z(\mathcal F)(U)` exactly when
its support is contained in `Z ∩ U`. -/
theorem subsheaf_app_iff
    {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)
    (ℱ : RingedSpace.Modules X) (U : Opens X) (s : ℱ.val.obj (op U)) :
    s ∈ Set.range ((subsheaf hZ ℱ).arrow.val.app (op U)) ↔
      moduleSectionSupport s ⊆ { x : U | x.1 ∈ Z } := by
  simpa using
    congrArg (fun S : Set (ℱ.val.obj (op U)) ↦ s ∈ S) (subsheaf_app_range hZ ℱ U)

-- Proof sketch: the sectionwise support description forces every stalk outside `Z` to vanish.
/-- The sections-with-support subsheaf has support contained in the closed subset `Z`. -/
theorem subsheaf_support_subset
    {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)
    (ℱ : RingedSpace.Modules X) :
    moduleSupport (subsheaf hZ ℱ) ⊆ Z := by
  -- Forgetting the module structure identifies module support with abelian sheaf support.
  simpa [moduleSupport] using
    (closedSubsetSectionsWithSupportSubsheaf_support_subset hZ
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ))

-- Proof sketch: any subsheaf whose support is contained in `Z` has all of its local sections
-- supported there, so it factors through the sections-with-support subsheaf.
/-- Among subsheaves of `\mathcal F`, the sections-with-support subsheaf is the largest one whose
support is contained in `Z`. -/
theorem le_subsheaf_of_support_subset
    {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)
    {ℱ : RingedSpace.Modules X} (𝒢 : Subobject ℱ) (h𝒢 : moduleSupport 𝒢 ⊆ Z) :
    𝒢 ≤ subsheaf hZ ℱ := by
  -- The maximality statement is the module specialization of the earlier abelian result.
  simpa [moduleSupport] using
    (le_closedSubsetSectionsWithSupportSubsheaf_of_support_subset hZ 𝒢 h𝒢)

end

end ClosedSubsetSectionsWithSupport
end RingedSpace

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

open RingedSpace.ClosedSubsetSectionsWithSupport
open scoped RingedSpaceClosedSubsetSectionsWithSupport

/- Remark 17.13.5: for a closed subset `Z ⊆ X`, the owner functor of sections with support is the
explicit functor `𝓗[hZ] = \mathcal H_Z` valued in `\operatorname{Mod}(\mathcal O_X|_Z)`. -/
#check (𝓗[hZ] :
  RingedSpace.Modules X ⥤ RingedSpace.closedSubsetModuleCategory X Z)

local instance : Functor.IsRightAdjoint (𝓗[hZ]) :=
  let adj := RingedSpace.ClosedSubsetSectionsWithSupport.pushforwardSectionsWithSupportAdjunction hZ
  adj.isRightAdjoint

-- Proof sketch: pushforward from the closed subset is exact on the underlying abelian sheaves, so
-- it preserves biproducts and zero morphisms on module sheaves.
/-- Pushforward from the closed subset is additive on sheaves of modules. -/
instance closedSubsetModulePushforward_additive
    (X : RingedSpace.{u}) (Z : Set X) :
    (RingedSpace.closedSubsetModulePushforward X Z).Additive := by
  infer_instance

-- Proof sketch: `𝓗[hZ]` is the right adjoint in the closed-subset adjunction, so it is additive
-- in the ambient abelian setting.
/-- The sections-with-support functor is additive. -/
instance closedSubsetSectionsWithSupport_additive :
    (𝓗[hZ]).Additive :=
  let adj := RingedSpace.ClosedSubsetSectionsWithSupport.pushforwardSectionsWithSupportAdjunction hZ
  adj.right_adjoint_additive

/- Remark 17.13.5: the sections-with-support functor `\mathcal H_Z` is left exact because right
adjoints preserve finite limits. -/
#synth PreservesFiniteLimits (𝓗[hZ])

end

section

variable {X Z : RingedSpace.{u}} (i : Z ⟶ X)
variable [RingedSpace.IsClosedImmersion i]

/-- The closed image of a closed immersion of ringed spaces. -/
private abbrev closedImmersionImage : Set X :=
  Set.range i.hom.base

/-- The closed image of a closed immersion is a closed subset of the target. -/
private theorem closedImmersionImage_isClosed : IsClosed (closedImmersionImage i) := by
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  exact hi.isClosedEmbedding.isClosed_range

/-- Closed-immersion bridge/view: the support subsheaf on `X` is the source-facing closed-subset
owner specialized to the closed image of `i`. -/
private abbrev ringedSpaceModuleSectionsWithSupportSubsheaf (ℱ : RingedSpace.Modules X) : Subobject ℱ :=
  RingedSpace.ClosedSubsetSectionsWithSupport.subsheaf (closedImmersionImage_isClosed i) ℱ

/-- The underlying `\mathcal O_X`-module sheaf of the sections-with-support subsheaf. -/
private abbrev ringedSpaceModuleSectionsWithSupportObject (ℱ : RingedSpace.Modules X) :
    RingedSpace.Modules X :=
  ((ringedSpaceModuleSectionsWithSupportSubsheaf i ℱ : Subobject ℱ) : RingedSpace.Modules X)

/-- Closed-immersion bridge/view: pull back the closed-subset support subsheaf to the source
ringed space `Z`. -/
private abbrev ringedSpaceModuleSectionsWithSupportSheaf (ℱ : RingedSpace.Modules X) : RingedSpace.Modules Z :=
  (RingedSpace.Hom.pullback i).obj (ringedSpaceModuleSectionsWithSupportObject i ℱ)

/-- The morphism on sections-with-support subsheaves induced by a morphism of
`\mathcal O_X`-modules. -/
private def ringedSpaceModuleSectionsWithSupportSubsheafMap
    {ℱ 𝒢 : RingedSpace.Modules X} (φ : ℱ ⟶ 𝒢) :
    ringedSpaceModuleSectionsWithSupportObject i ℱ ⟶
      ringedSpaceModuleSectionsWithSupportObject i 𝒢 :=
  RingedSpace.ClosedSubsetSectionsWithSupport.subsheafMap
    (closedImmersionImage_isClosed i) φ

-- Proof sketch: the closed-immersion bridge functor is obtained by pulling back the
-- source-facing support object along `i`.
/-- The induced morphism on sections-with-support sheaves respects identity morphisms. -/
private theorem ringedSpaceModuleSectionsWithSupportFunctor_map_id
    (ℱ : RingedSpace.Modules X) :
    (RingedSpace.Hom.pullback i).map (ringedSpaceModuleSectionsWithSupportSubsheafMap i (𝟙 ℱ)) =
      𝟙 (ringedSpaceModuleSectionsWithSupportSheaf i ℱ) := by
  -- The bridge functor is just pullback of the closed-subset support object, so identity follows
  -- from the same kernel functoriality used above.
  simp [ringedSpaceModuleSectionsWithSupportSheaf,
    ringedSpaceModuleSectionsWithSupportSubsheafMap,
    RingedSpace.ClosedSubsetSectionsWithSupport.subsheafMap,
    RingedSpace.ClosedSubsetSectionsWithSupport.sheaf,
    RingedSpace.ClosedSubsetSectionsWithSupport.object,
    CategoryTheory.Limits.kernelSubobjectMap_id]

-- Proof sketch: combine the functoriality of the closed-subset support object with the
-- functoriality of pullback along `i`.
/-- The induced morphism on sections-with-support sheaves respects composition. -/
private theorem ringedSpaceModuleSectionsWithSupportFunctor_map_comp
    {ℱ 𝒢 𝒦 : RingedSpace.Modules X} (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ 𝒦) :
    (RingedSpace.Hom.pullback i).map
        (ringedSpaceModuleSectionsWithSupportSubsheafMap i (φ ≫ ψ)) =
      (RingedSpace.Hom.pullback i).map (ringedSpaceModuleSectionsWithSupportSubsheafMap i φ) ≫
        (RingedSpace.Hom.pullback i).map (ringedSpaceModuleSectionsWithSupportSubsheafMap i ψ) := by
  -- The bridge composition law is inherited from the closed-subset kernel construction.
  simp [ringedSpaceModuleSectionsWithSupportSubsheafMap,
    RingedSpace.ClosedSubsetSectionsWithSupport.subsheafMap,
    CategoryTheory.Limits.kernelSubobjectMap_comp]

private def closedImmersionSectionsWithSupportFunctor :
    RingedSpace.Modules X ⥤ RingedSpace.Modules Z where
  obj ℱ := ringedSpaceModuleSectionsWithSupportSheaf i ℱ
  map φ := (RingedSpace.Hom.pullback i).map (ringedSpaceModuleSectionsWithSupportSubsheafMap i φ)
  map_id := ringedSpaceModuleSectionsWithSupportFunctor_map_id i
  map_comp := ringedSpaceModuleSectionsWithSupportFunctor_map_comp i

/-- Helper for Remark 17.13.5: the open complement of the image of the closed immersion. -/
private abbrev ringedSpaceModuleOpenComplement : Opens X :=
  RingedSpace.ClosedSubsetSectionsWithSupport.openComplement (closedImmersionImage_isClosed i)

/-- Helper for Remark 17.13.5: the structure-sheaf morphism attached to the open complement of
the closed image. -/
private abbrev ringedSpaceModuleOpenComplementStructureSheafHom :
    RingedSpace.ringCatSheaf X ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} (ringedSpaceModuleOpenComplement i).inclusion').obj
        ((TopCat.Sheaf.pullback RingCat.{u} (ringedSpaceModuleOpenComplement i).inclusion').obj
          (RingedSpace.ringCatSheaf X)) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
    (ringedSpaceModuleOpenComplement i).inclusion').unit.app (RingedSpace.ringCatSheaf X)

/-- Helper for Remark 17.13.5: restriction of modules to the open complement of the closed image.
-/
private abbrev ringedSpaceModuleOpenComplementRestrictionFunctor :
    RingedSpace.Modules X ⥤
      SheafOfModules
        ((TopCat.Sheaf.pullback RingCat.{u} (ringedSpaceModuleOpenComplement i).inclusion').obj
          (RingedSpace.ringCatSheaf X)) :=
  moduleSheafRestrictionToOpen (ringedSpaceModuleOpenComplement i) (RingedSpace.ringCatSheaf X)

/-- Helper for Remark 17.13.5: pushforward from the open complement of the closed image back to
`X`. -/
private abbrev ringedSpaceModuleOpenComplementPushforwardFunctor :
    SheafOfModules
        ((TopCat.Sheaf.pullback RingCat.{u} (ringedSpaceModuleOpenComplement i).inclusion').obj
          (RingedSpace.ringCatSheaf X)) ⥤
      RingedSpace.Modules X :=
  SheafOfModules.pushforward (ringedSpaceModuleOpenComplementStructureSheafHom i)

/-- Helper for Remark 17.13.5: naturality of restriction to the open complement of the closed
image. -/
private theorem ringedSpaceModuleOpenComplementRestriction_w
    {ℱ 𝒢 : RingedSpace.Modules X} (φ : ℱ ⟶ 𝒢) :
    φ ≫
        RingedSpace.ClosedSubsetSectionsWithSupport.openComplementRestriction
          (closedImmersionImage_isClosed i) 𝒢 =
      RingedSpace.ClosedSubsetSectionsWithSupport.openComplementRestriction
          (closedImmersionImage_isClosed i) ℱ ≫
        (ringedSpaceModuleOpenComplementPushforwardFunctor i).map
          ((ringedSpaceModuleOpenComplementRestrictionFunctor i).map φ) := by
  -- This is the unit naturality square for restriction to the open complement of the closed
  -- image.
  simpa [RingedSpace.ClosedSubsetSectionsWithSupport.openComplementRestriction,
    ringedSpaceModuleOpenComplementStructureSheafHom] using
    (SheafOfModules.pullbackPushforwardAdjunction
      (ringedSpaceModuleOpenComplementStructureSheafHom i)).unit.naturality φ

/-- Helper for Remark 17.13.5: the pushforward of a module from the closed immersion source is
already supported on the closed image. -/
private theorem ringedSpaceModuleSectionsWithSupportSubsheaf_pushforward_eq_top
    (ℱ : RingedSpace.Modules Z) :
    ringedSpaceModuleSectionsWithSupportSubsheaf i
        ((RingedSpace.Hom.pushforward i).obj ℱ) = ⊤ := by
  -- The source is already supported on the closed image, so the maximal support subsheaf is all
  -- of it.
  rw [eq_top_iff]
  have hsupport :
      moduleSupport ((RingedSpace.Hom.pushforward i).obj ℱ) ⊆ closedImmersionImage i := by
    intro x hx
    by_contra hx'
    let hi : RingedSpace.IsClosedImmersion i := inferInstance
    let e : Z ≅ TopCat.of (closedImmersionImage i) :=
      TopCat.isoOfHomeo hi.1.toHomeomorph
    let ℱ' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (closedImmersionImage i)) :=
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Z)).obj ℱ)
    have hZero :
        IsZero (RingedSpace.stalkModuleCat ((RingedSpace.Hom.pushforward i).obj ℱ) x) := by
      -- Off the image, the underlying additive stalk vanishes after identifying `i_*` with
      -- closed-subset pushforward along the image.
      apply isZero_of_reflects_iso _ (forget₂
        (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u})
      simpa [ℱ'] using
        (closedSubsetAbelianSheaf_pushforward_stalk_isZero_of_not_mem
          (X := X) (Z := closedImmersionImage i) (closedImmersionImage_isClosed i) ℱ' hx')
    let hsub :
        Subsingleton (RingedSpace.stalkModuleCat ((RingedSpace.Hom.pushforward i).obj ℱ) x) := by
      simpa [ModuleCat.isZero_iff_subsingleton] using hZero
    rw [mem_moduleSupport_iff] at hx
    rcases hx with ⟨m, hm⟩
    exact hm (hsub m 0)
  simpa using
    (RingedSpace.ClosedSubsetSectionsWithSupport.le_subsheaf_of_support_subset
      (closedImmersionImage_isClosed i)
      (⊤ : Subobject ((RingedSpace.Hom.pushforward i).obj ℱ))
      hsupport)

/-- Helper for Remark 17.13.5: the restriction of a pushed-forward module to the complement of
the closed image is zero. -/
private theorem ringedSpaceModulePushforward_openComplementRestriction_eq_zero
    (ℱ : RingedSpace.Modules Z) :
    RingedSpace.ClosedSubsetSectionsWithSupport.openComplementRestriction
        (closedImmersionImage_isClosed i)
        ((RingedSpace.Hom.pushforward i).obj ℱ) = 0 := by
  -- Once the support subsheaf is `⊤`, its kernel arrow is invertible and the defining
  -- restriction map must vanish.
  let 𝒢 := (RingedSpace.Hom.pushforward i).obj ℱ
  have hcomp :
      (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).arrow ≫
          RingedSpace.ClosedSubsetSectionsWithSupport.openComplementRestriction
            (closedImmersionImage_isClosed i) 𝒢 =
        0 := by
    simpa [ringedSpaceModuleSectionsWithSupportSubsheaf] using
      kernelSubobject_arrow_comp
        (RingedSpace.ClosedSubsetSectionsWithSupport.openComplementRestriction
          (closedImmersionImage_isClosed i) 𝒢)
  have hIso : IsIso (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).arrow := by
    exact
      (Subobject.isIso_arrow_iff_eq_top (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢)).2
        (ringedSpaceModuleSectionsWithSupportSubsheaf_pushforward_eq_top i ℱ)
  have hcancel :
      inv (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).arrow ≫
          ((ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).arrow ≫
            RingedSpace.ClosedSubsetSectionsWithSupport.openComplementRestriction
              (closedImmersionImage_isClosed i) 𝒢) =
        RingedSpace.ClosedSubsetSectionsWithSupport.openComplementRestriction
          (closedImmersionImage_isClosed i) 𝒢 := by
    simpa [Category.assoc] using
      IsIso.inv_hom_id_assoc
        (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).arrow
        (RingedSpace.ClosedSubsetSectionsWithSupport.openComplementRestriction
          (closedImmersionImage_isClosed i) 𝒢)
  rw [← hcancel]
  simp [hcomp]

/-- Helper for Remark 17.13.5: every map out of a pushed-forward module factors through the
sections-with-support subsheaf of the target. -/
private theorem ringedSpaceModulePushforwardToSubsheaf_factors
    (ℱ : RingedSpace.Modules Z)
    {𝒢 : RingedSpace.Modules X}
    (φ : ((RingedSpace.Hom.pushforward i).obj ℱ) ⟶ 𝒢) :
    (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).Factors φ := by
  -- Naturality of restriction to the open complement reduces the kernel criterion to the
  -- vanishing statement for the pushed-forward source.
  apply kernelSubobject_factors
  calc
    φ ≫
        RingedSpace.ClosedSubsetSectionsWithSupport.openComplementRestriction
          (closedImmersionImage_isClosed i) 𝒢 =
      RingedSpace.ClosedSubsetSectionsWithSupport.openComplementRestriction
          (closedImmersionImage_isClosed i)
          ((RingedSpace.Hom.pushforward i).obj ℱ) ≫
        (ringedSpaceModuleOpenComplementPushforwardFunctor i).map
          ((ringedSpaceModuleOpenComplementRestrictionFunctor i).map φ) := by
          rw [ringedSpaceModuleOpenComplementRestriction_w i φ]
    _ = 0 := by
      simp [ringedSpaceModulePushforward_openComplementRestriction_eq_zero]

/-- Helper for Remark 17.13.5: the chosen factorization through the support subsheaf of the
target. -/
private noncomputable def ringedSpaceModulePushforwardFactorToSubsheaf
    (ℱ : RingedSpace.Modules Z)
    {𝒢 : RingedSpace.Modules X}
    (φ : ((RingedSpace.Hom.pushforward i).obj ℱ) ⟶ 𝒢) :
    ((RingedSpace.Hom.pushforward i).obj ℱ) ⟶ ringedSpaceModuleSectionsWithSupportObject i 𝒢 :=
  (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).factorThru φ
    (ringedSpaceModulePushforwardToSubsheaf_factors i ℱ φ)

/-- Helper for Remark 17.13.5: the chosen factorization composes back to the original morphism.
-/
private theorem ringedSpaceModulePushforwardFactorToSubsheaf_comp_arrow
    (ℱ : RingedSpace.Modules Z)
    {𝒢 : RingedSpace.Modules X}
    (φ : ((RingedSpace.Hom.pushforward i).obj ℱ) ⟶ 𝒢) :
    ringedSpaceModulePushforwardFactorToSubsheaf i ℱ φ ≫
        (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).arrow =
      φ := by
  -- This is the defining property of `Subobject.factorThru`.
  exact Subobject.factorThru_arrow _ _ _

/-- Helper for Remark 17.13.5: factoring through the support subsheaf is natural in the source
module on `Z`. -/
private theorem ringedSpaceModulePushforwardFactorToSubsheaf_naturality_left
    {ℱ₁ ℱ₂ : RingedSpace.Modules Z}
    {𝒢 : RingedSpace.Modules X}
    (u : ℱ₁ ⟶ ℱ₂)
    (φ : ((RingedSpace.Hom.pushforward i).obj ℱ₂) ⟶ 𝒢) :
    ringedSpaceModulePushforwardFactorToSubsheaf i ℱ₁
        ((RingedSpace.Hom.pushforward i).map u ≫ φ) =
      (RingedSpace.Hom.pushforward i).map u ≫
        ringedSpaceModulePushforwardFactorToSubsheaf i ℱ₂ φ := by
  -- Both sides agree after composing with the mono support inclusion.
  apply (cancel_mono (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).arrow).1
  rw [Category.assoc, ringedSpaceModulePushforwardFactorToSubsheaf_comp_arrow]
  rw [Category.assoc, ringedSpaceModulePushforwardFactorToSubsheaf_comp_arrow]

/-- Helper for Remark 17.13.5: factoring through the support subsheaf is natural in the ambient
target module. -/
private theorem ringedSpaceModulePushforwardFactorToSubsheaf_naturality_right
    (ℱ : RingedSpace.Modules Z)
    {𝒢₁ 𝒢₂ : RingedSpace.Modules X}
    (φ : ((RingedSpace.Hom.pushforward i).obj ℱ) ⟶ 𝒢₁)
    (g : 𝒢₁ ⟶ 𝒢₂) :
    ringedSpaceModulePushforwardFactorToSubsheaf i ℱ (φ ≫ g) =
      ringedSpaceModulePushforwardFactorToSubsheaf i ℱ φ ≫
        ringedSpaceModuleSectionsWithSupportSubsheafMap i g := by
  -- After composing with the target support inclusion, both sides reduce to `φ ≫ g`.
  apply (cancel_mono (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢₂).arrow).1
  rw [Category.assoc, ringedSpaceModulePushforwardFactorToSubsheaf_comp_arrow]
  rw [Category.assoc, Category.assoc,
    ringedSpaceModulePushforwardFactorToSubsheaf_comp_arrow]
  simp [ringedSpaceModuleSectionsWithSupportSubsheafMap, Category.assoc]

/-- Helper for Remark 17.13.5: the inverse-transpose route recovers the original morphism out of
the pushed-forward source. -/
private theorem closedImmersionPushforwardSectionsWithSupportHomEquiv_left_inv
    (ℱ : RingedSpace.Modules Z)
    (𝒢 : RingedSpace.Modules X) :
    Function.LeftInverse
      (fun φ : ℱ ⟶ (closedImmersionSectionsWithSupportFunctor i).obj 𝒢 =>
        ((SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.Hom.toRingCatSheafHom i)).homEquiv ℱ
            (ringedSpaceModuleSectionsWithSupportObject i 𝒢)).symm φ ≫
          (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).arrow)
      (fun φ : ((RingedSpace.Hom.pushforward i).obj ℱ) ⟶ 𝒢 =>
        (SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.Hom.toRingCatSheafHom i)).homEquiv ℱ
          (ringedSpaceModuleSectionsWithSupportObject i 𝒢)
          (ringedSpaceModulePushforwardFactorToSubsheaf i ℱ φ)) := by
  intro φ
  -- Undoing the ambient adjunction and then composing with the support inclusion recovers `φ`.
  rw [Equiv.symm_apply_apply]
  exact ringedSpaceModulePushforwardFactorToSubsheaf_comp_arrow i ℱ φ

/-- Helper for Remark 17.13.5: the transpose of a map already landing in the support object is
the original morphism on `Z`. -/
private theorem closedImmersionPushforwardSectionsWithSupportHomEquiv_right_inv
    (ℱ : RingedSpace.Modules Z)
    (𝒢 : RingedSpace.Modules X) :
    Function.RightInverse
      (fun φ : ℱ ⟶ (closedImmersionSectionsWithSupportFunctor i).obj 𝒢 =>
        ((SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.Hom.toRingCatSheafHom i)).homEquiv ℱ
            (ringedSpaceModuleSectionsWithSupportObject i 𝒢)).symm φ ≫
          (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).arrow)
      (fun φ : ((RingedSpace.Hom.pushforward i).obj ℱ) ⟶ 𝒢 =>
        (SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.Hom.toRingCatSheafHom i)).homEquiv ℱ
          (ringedSpaceModuleSectionsWithSupportObject i 𝒢)
          (ringedSpaceModulePushforwardFactorToSubsheaf i ℱ φ)) := by
  intro φ
  -- The factorization of a map that already lands in the support object is the original lift.
  apply (SheafOfModules.pullbackPushforwardAdjunction
      (RingedSpace.Hom.toRingCatSheafHom i)).homEquiv ℱ
      (ringedSpaceModuleSectionsWithSupportObject i 𝒢) |>.injective
  apply (cancel_mono (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).arrow).1
  rw [Category.assoc, ringedSpaceModulePushforwardFactorToSubsheaf_comp_arrow]
  rw [Equiv.apply_symm_apply]

/-- Helper for Remark 17.13.5: maps out of a pushed-forward module are equivalent to maps into
the closed-immersion sections-with-support functor. -/
private noncomputable def closedImmersionPushforwardSectionsWithSupportHomEquiv
    (ℱ : RingedSpace.Modules Z)
    (𝒢 : RingedSpace.Modules X) :
    (((RingedSpace.Hom.pushforward i).obj ℱ) ⟶ 𝒢) ≃
      (ℱ ⟶ (closedImmersionSectionsWithSupportFunctor i).obj 𝒢) :=
  { toFun := fun φ =>
      (SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom i)).homEquiv ℱ
        (ringedSpaceModuleSectionsWithSupportObject i 𝒢)
        (ringedSpaceModulePushforwardFactorToSubsheaf i ℱ φ)
    invFun := fun φ =>
      ((SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom i)).homEquiv ℱ
        (ringedSpaceModuleSectionsWithSupportObject i 𝒢)).symm φ ≫
        (ringedSpaceModuleSectionsWithSupportSubsheaf i 𝒢).arrow
    left_inv := closedImmersionPushforwardSectionsWithSupportHomEquiv_left_inv i ℱ 𝒢
    right_inv := closedImmersionPushforwardSectionsWithSupportHomEquiv_right_inv i ℱ 𝒢 }

/-- Helper for Remark 17.13.5: the Hom-equivalence is natural in the source module on `Z`. -/
private theorem closedImmersionPushforwardSectionsWithSupportHomEquiv_naturality_left
    {ℱ₁ ℱ₂ : RingedSpace.Modules Z}
    {𝒢 : RingedSpace.Modules X}
    (u : ℱ₁ ⟶ ℱ₂)
    (φ : ((RingedSpace.Hom.pushforward i).obj ℱ₂) ⟶ 𝒢) :
    closedImmersionPushforwardSectionsWithSupportHomEquiv i ℱ₁ 𝒢
        ((RingedSpace.Hom.pushforward i).map u ≫ φ) =
      u ≫ closedImmersionPushforwardSectionsWithSupportHomEquiv i ℱ₂ 𝒢 φ := by
  -- After rewriting the chosen factorization, this is the owner adjunction's left naturality.
  simpa [closedImmersionPushforwardSectionsWithSupportHomEquiv,
    ringedSpaceModulePushforwardFactorToSubsheaf_naturality_left] using
    (CategoryTheory.Adjunction.homEquiv_naturality_left_symm
      (SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom i))
      u
      (ringedSpaceModulePushforwardFactorToSubsheaf i ℱ₂ φ))

/-- Helper for Remark 17.13.5: the Hom-equivalence is natural in the ambient target module. -/
private theorem closedImmersionPushforwardSectionsWithSupportHomEquiv_naturality_right
    (ℱ : RingedSpace.Modules Z)
    {𝒢₁ 𝒢₂ : RingedSpace.Modules X}
    (φ : ((RingedSpace.Hom.pushforward i).obj ℱ) ⟶ 𝒢₁)
    (g : 𝒢₁ ⟶ 𝒢₂) :
    closedImmersionPushforwardSectionsWithSupportHomEquiv i ℱ 𝒢₂ (φ ≫ g) =
      closedImmersionPushforwardSectionsWithSupportHomEquiv i ℱ 𝒢₁ φ ≫
        (closedImmersionSectionsWithSupportFunctor i).map g := by
  -- The right naturality is likewise inherited from the ambient pullback/pushforward adjunction.
  simpa [closedImmersionPushforwardSectionsWithSupportHomEquiv,
    closedImmersionSectionsWithSupportFunctor,
    ringedSpaceModulePushforwardFactorToSubsheaf_naturality_right] using
    (CategoryTheory.Adjunction.homEquiv_naturality_right
      (SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom i))
      (ringedSpaceModulePushforwardFactorToSubsheaf i ℱ φ)
      (ringedSpaceModuleSectionsWithSupportSubsheafMap i g))

/-- The closed-immersion sections-with-support functor is right adjoint to pushforward along the
closed immersion. -/
private noncomputable def closedImmersionPushforwardSectionsWithSupportAdjunction :
    RingedSpace.Hom.pushforward i ⊣ closedImmersionSectionsWithSupportFunctor i :=
  -- Route correction: package the adjunction by the Hom-equivalence, exactly as in the
  -- closed-subset block, instead of carrying brittle explicit triangle identities.
  Adjunction.mkOfHomEquiv
    { homEquiv := closedImmersionPushforwardSectionsWithSupportHomEquiv i
      homEquiv_naturality_left_symm :=
        closedImmersionPushforwardSectionsWithSupportHomEquiv_naturality_left i
      homEquiv_naturality_right :=
        closedImmersionPushforwardSectionsWithSupportHomEquiv_naturality_right i }

end

/-- Closed-immersion bridge/view: pushforward along a closed immersion is a left adjoint. -/
noncomputable instance ringedSpaceModulePushforward_isLeftAdjoint_of_isClosedImmersion
    {X Z : RingedSpace.{u}} (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i] :
    (RingedSpace.Hom.pushforward i).IsLeftAdjoint :=
  (closedImmersionPushforwardSectionsWithSupportAdjunction i).isLeftAdjoint

end AlgebraicGeometry
