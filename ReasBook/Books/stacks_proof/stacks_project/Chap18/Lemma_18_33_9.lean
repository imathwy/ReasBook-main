import Mathlib
import stacks_proof.stacks_project.Chap18.Lemma_18_33_2
import stacks_proof.stacks_project.Chap18.Lemma_18_33_9_Owner

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-
Domain-style sampling for Lemma 18.33.9:
- primary domain: square-zero extensions of sheaves of commutative rings on a general site, their
  intrinsic kernel ideal sheaves, restriction of scalars for sheaves of modules on a ringed site,
  and relative derivations into the kernel ideal viewed as an `O₂`-module via a chosen section;
- sampled owner declarations:
  `CategoryTheory.Limits.kernel`,
  `SheafOfModules.RingedSite.restrictionAlong`,
  `SheafOfModules.unitToPushforwardObjUnit`,
  `SheafOfModules.RingedSite.ringedSiteStructureMap`,
  `Der[φ ; F]`;
- best owner abstraction: the intrinsic kernel ideal sheaf
  `kernel (SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap π))` as an
  `A`-module, with the `O₂`-module structure for a fixed section `s : O₂ ⟶ A` obtained by the
  canonical owner `restrictionAlong s`;
- primitive data: the maps `φ : O₁ ⟶ O₂`, `ψ : O₁ ⟶ A`, `π : A ⟶ O₂`, one compatible section
  `s`, and the square-zero condition on the actual kernel ideal of `π`;
- derived API: compatible algebra sections, perturbations by derivations into the intrinsic kernel,
  and the torsor-style existence and uniqueness statements.

Source/core/bridge triage:
- `source-facing`: compatible algebra sections and their difference-by-a-derivation relation;
- `core/canonical`: `kernel`, `kernel.ι`, `restrictionAlong`, and
  `Der[φ ; F]`;
- `bridge/view`: the restriction-of-scalars identification sending an `A`-module sheaf to an
  `O₂`-module sheaf along a fixed section `s : O₂ ⟶ A`.

This file therefore refines to the intrinsic kernel owner `Ker π`, with its theorem-facing
`O₂`-module structure obtained directly from the canonical owner `restrictionAlong`, rather than
from auxiliary sectionwise lift data. -/

variable {O₁ O₂ A : Sheaf J CommRingCat.{u}}
variable (φ : O₁ ⟶ O₂) (ψ : O₁ ⟶ A) (π : A ⟶ O₂)

/-- A section of `π` compatible with the `O₁`-algebra structures on `A` and `O₂`. -/
abbrev IsAlgebraSection (s : O₂ ⟶ A) : Prop :=
  s ≫ π = 𝟙 O₂ ∧ φ ≫ s = ψ

variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

private abbrev structureSheafQuotient (π : A ⟶ O₂) :
    SheafOfModules.unit (ringSheaf J A) ⟶
      (SheafOfModules.pushforward (ringedSiteStructureMap π)).obj
        (SheafOfModules.unit (ringSheaf J O₂)) :=
  SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap π)

/-- The sectionwise inclusion of `Ker π` into `A`. -/
private abbrev kernelIdealInclusionApp
    (π : A ⟶ O₂)
    (U : Cᵒᵖ) (x : (kernelIdealSheaf π).val.obj U) : A.obj.obj U :=
  show A.obj.obj U from (kernelIdealSheafInclusion π).val.app U x

/-- The descended kernel module includes canonically into `A` by restricting scalars along the
fixed section `s`. -/
private abbrev kernelIdealSheafModuleInclusion
    (π : A ⟶ O₂) (s : O₂ ⟶ A) :
    kernelIdealSheafModule π s ⟶
      (restrictionAlong s).obj (SheafOfModules.unit (ringSheaf J A)) :=
  (restrictionAlong s).map (kernelIdealSheafInclusion π)

/-- The sectionwise inclusion of the descended kernel module into `A`. -/
private abbrev kernelIdealSheafModuleInclusionApp
    (π : A ⟶ O₂) (s : O₂ ⟶ A)
    (U : Cᵒᵖ) (x : (kernelIdealSheafModule π s).val.obj U) : A.obj.obj U :=
  show A.obj.obj U from (kernelIdealSheafModuleInclusion π s).val.app U x

/-- A section `s'` differs from `s` by the derivation `D` when their local sections satisfy the
pointwise formula `s' = s + D` through the canonical inclusion `Ker π ↪ A`. -/
abbrev IsSectionPerturbation
    (φ : O₁ ⟶ O₂) (π : A ⟶ O₂)
    (s s' : O₂ ⟶ A)
    (D : Der[φ ; kernelIdealSheafModule π s]) : Prop :=
  ∀ U : Cᵒᵖ, ∀ x : O₂.obj.obj U,
    s'.hom.app U x = s.hom.app U x +
      kernelIdealSheafModuleInclusionApp π s U (D.d x)

/-- Helper for Lemma 18.33.9: the descended kernel inclusion sends zero to zero on every object. -/
private theorem kernel_module_inclusion_app_zero
    (π : A ⟶ O₂) (s : O₂ ⟶ A)
    (U : Cᵒᵖ) :
    kernelIdealSheafModuleInclusionApp π s U 0 = 0 := by
  -- The inclusion is a morphism of sheaves of modules, hence each component is linear.
  simpa [kernelIdealSheafModuleInclusionApp] using
    (ModuleCat.Hom.hom ((kernelIdealSheafModuleInclusion π s).val.app U)).map_zero

/-- Helper for Lemma 18.33.9: the descended kernel inclusion preserves addition objectwise. -/
private theorem kernel_module_inclusion_app_add
    (π : A ⟶ O₂) (s : O₂ ⟶ A)
    (U : Cᵒᵖ)
    (x y : (kernelIdealSheafModule π s).val.obj U) :
    kernelIdealSheafModuleInclusionApp π s U (x + y) =
      kernelIdealSheafModuleInclusionApp π s U x +
        kernelIdealSheafModuleInclusionApp π s U y := by
  -- This is the additive part of the linearity of the kernel inclusion.
  simpa [kernelIdealSheafModuleInclusionApp] using
    (ModuleCat.Hom.hom ((kernelIdealSheafModuleInclusion π s).val.app U)).map_add x y

/-- Helper for Lemma 18.33.9: scalar multiplication in the descended kernel module is realized in
`A` by multiplication with the chosen section. -/
private theorem kernel_module_inclusion_app_smul
    (π : A ⟶ O₂) (s : O₂ ⟶ A)
    (U : Cᵒᵖ)
    (a : O₂.obj.obj U) (x : (kernelIdealSheafModule π s).val.obj U) :
    kernelIdealSheafModuleInclusionApp π s U (a • x) =
      s.hom.app U a * kernelIdealSheafModuleInclusionApp π s U x := by
  -- Restriction of scalars turns the `O₂(U)`-action into multiplication through `s(U)`.
  simpa [kernelIdealSheafModuleInclusionApp] using
    (ModuleCat.Hom.hom ((kernelIdealSheafModuleInclusion π s).val.app U)).map_smul a x

/-- Helper for Lemma 18.33.9: after applying `π`, every included kernel section vanishes. -/
private theorem kernel_module_inclusion_app_pi_eq_zero
    (π : A ⟶ O₂) (s : O₂ ⟶ A)
    (U : Cᵒᵖ) (x : (kernelIdealSheafModule π s).val.obj U) :
    π.hom.app U (kernelIdealSheafModuleInclusionApp π s U x) = 0 := by
  -- Route correction: use the canonical kernel identity after restricting scalars, then evaluate
  -- objectwise instead of unfolding the descended kernel module by hand.
  have hcomp :
      kernelIdealSheafModuleInclusion π s ≫
          (restrictionAlong s).map (structureSheafQuotient π) = 0 := by
    -- Mapping the intrinsic kernel condition through `restrictionAlong s` preserves the zero
    -- composite on the descended kernel module.
    rw [kernelIdealSheafModuleInclusion, ← Functor.map_comp, kernel.condition, Functor.map_zero]
  have hval :
      (kernelIdealSheafModuleInclusion π s ≫
          (restrictionAlong s).map (structureSheafQuotient π)).val = 0 := by
    -- Pass from the equality of module-sheaf morphisms to the underlying natural transformations.
    exact congrArg SheafOfModules.Hom.val hcomp
  have happ :
      ((kernelIdealSheafModuleInclusion π s).val.app U) ≫
          (((restrictionAlong s).map (structureSheafQuotient π)).val.app U) = 0 := by
    -- Evaluating the composite equality at `U` gives the zero map on local sections.
    change
      ((kernelIdealSheafModuleInclusion π s ≫
          (restrictionAlong s).map (structureSheafQuotient π)).val.app U) = 0
    simpa using congrArg (fun f ↦ f.app U) hval
  -- Apply the evaluated zero composite to the chosen kernel section.
  simpa [kernelIdealSheafModuleInclusionApp, structureSheafQuotient, ringedSiteStructureMap] using
    congrArg
      (fun g :
          (kernelIdealSheafModule π s).val.obj U ⟶
            ((restrictionAlong s).obj
              ((SheafOfModules.pushforward (ringedSiteStructureMap π)).obj
                (SheafOfModules.unit (ringSheaf J O₂)))).val.obj U ↦
        ModuleCat.Hom.hom g x)
      happ

/-- Helper for Lemma 18.33.9: the square-zero hypothesis kills products of two included kernel
sections. -/
private theorem kernel_module_inclusion_app_mul_eq_zero
    (π : A ⟶ O₂) (s : O₂ ⟶ A)
    (hzero : KernelSquareZero π)
    (U : Cᵒᵖ)
    (x y : (kernelIdealSheafModule π s).val.obj U) :
    kernelIdealSheafModuleInclusionApp π s U x *
      kernelIdealSheafModuleInclusionApp π s U y = 0 := by
  -- Restriction of scalars does not change the underlying local kernel sections.
  simpa [KernelSquareZero, kernelIdealSheafModuleInclusionApp, kernelIdealInclusionApp,
    kernelIdealSheafModule, kernelIdealSheaf] using hzero U x y

variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the descended kernel inclusion is injective on every object. -/
private theorem kernel_module_inclusion_app_injective
    (π : A ⟶ O₂) (s : O₂ ⟶ A)
    (U : Cᵒᵖ) :
    Function.Injective (kernelIdealSheafModuleInclusionApp π s U) := by
  -- Pass to the underlying presheaf of abelian groups, where monicity is checked objectwise.
  have hmono :
      Mono (((SheafOfModules.toSheaf (ringSheaf J A)).map
        (kernelIdealSheafInclusion π)).hom) :=
    (sheafToPresheaf J AddCommGrpCat.{u}).map_mono
      ((SheafOfModules.toSheaf (ringSheaf J A)).map
        (kernelIdealSheafInclusion π))
  have hmonoApp :
      Mono ((((SheafOfModules.toSheaf (ringSheaf J A)).map
        (kernelIdealSheafInclusion π)).hom.app U)) :=
    (NatTrans.mono_iff_mono_app _).1 hmono U
  simpa [kernelIdealSheafModuleInclusionApp, kernelIdealSheafModuleInclusion, kernelIdealSheafModule]
    using
    (AddCommGrpCat.mono_iff_injective _).1 hmonoApp

/-- Helper for Lemma 18.33.9: an ambient local section of `A` killed by `π` determines a
local section of the descended kernel module. -/
private noncomputable def ambient_zero_to_kernel_section
    (π : A ⟶ O₂) (s : O₂ ⟶ A)
    (U : Cᵒᵖ) (a : A.obj.obj U) (ha : π.hom.app U a = 0) :
    (kernelIdealSheafModule π s).val.obj U := by
  let ka : (((structureSheafQuotient π).val.app U).hom).ker := by
    refine ⟨a, ?_⟩
    simpa [structureSheafQuotient, ringedSiteStructureMap] using ha
  let z :=
    (ModuleCat.kernelIsoKer ((structureSheafQuotient π).val.app U)).inv ka
  let y :=
    (PreservesKernel.iso (PresheafOfModules.evaluation (ringSheaf J A).obj U)
      ((structureSheafQuotient π).val)).inv z
  -- Route correction: first lift the objectwise kernel element through the presheaf kernel, and
  -- only then transport it back to the sheaf-level kernel owner.
  simpa [kernelIdealSheafModule, kernelIdealSheaf] using
    ((PreservesKernel.iso (SheafOfModules.forget (ringSheaf J A))
      (structureSheafQuotient π)).inv.app U y)

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the kernel lift constructed from a section annihilated by `π`
includes back into `A(U)` as the original ambient section. -/
private theorem ambient_zero_to_kernel_section_inclusion
    (π : A ⟶ O₂) (s : O₂ ⟶ A)
    (U : Cᵒᵖ) (a : A.obj.obj U) (ha : π.hom.app U a = 0) :
    kernelIdealSheafModuleInclusionApp π s U
        (ambient_zero_to_kernel_section (π := π) (s := s) U a ha) = a := by
  let ka : (((structureSheafQuotient π).val.app U).hom).ker := by
    refine ⟨a, ?_⟩
    simpa [structureSheafQuotient, ringedSiteStructureMap] using ha
  let z :=
    (ModuleCat.kernelIsoKer ((structureSheafQuotient π).val.app U)).inv ka
  let y :=
    (PreservesKernel.iso (PresheafOfModules.evaluation (ringSheaf J A).obj U)
      ((structureSheafQuotient π).val)).inv z
  have h₁ :=
    ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.app U)
        (PreservesKernel.iso_inv_ι (SheafOfModules.forget (ringSheaf J A))
          (structureSheafQuotient π)))
      y
  have h₂ :=
    ConcreteCategory.congr_hom
      (PreservesKernel.iso_inv_ι (PresheafOfModules.evaluation (ringSheaf J A).obj U)
        ((structureSheafQuotient π).val))
      z
  have h₃ :=
    ConcreteCategory.congr_hom
      (ModuleCat.kernelIsoKer_inv_kernel_ι (f := (structureSheafQuotient π).val.app U))
      ka
  -- The three kernel comparison isomorphisms compose to the original ambient section `a`.
  simpa [ambient_zero_to_kernel_section, kernelIdealSheafModuleInclusionApp,
    kernelIdealSheafModuleInclusion, kernelIdealSheafModule, kernelIdealSheaf, y, z, ka]
    using h₁.trans (h₂.trans h₃)

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the descended kernel inclusion is natural in the object of the
site. -/
private theorem kernel_module_inclusion_app_naturality
    (π : A ⟶ O₂) (s : O₂ ⟶ A)
    {U V : Cᵒᵖ} (ρ : U ⟶ V)
    (y : (kernelIdealSheafModule π s).val.obj U) :
    kernelIdealSheafModuleInclusionApp π s V
        ((kernelIdealSheafModule π s).val.map ρ y) =
      A.obj.map ρ (kernelIdealSheafModuleInclusionApp π s U y) := by
  -- Evaluate the naturality square of the canonical inclusion on the chosen section.
  simpa [kernelIdealSheafModuleInclusionApp] using
    congrArg (fun k ↦ ModuleCat.Hom.hom k y)
      ((kernelIdealSheafModuleInclusion π s).val.naturality ρ)

/-- Helper for Lemma 18.33.9: the pointwise difference `s' - s` lifts canonically to the
descended kernel module because both sections split `π`. -/
private noncomputable def section_difference_to_kernel_app
    (s s' : O₂ ⟶ A)
    (hs : IsAlgebraSection φ ψ π s)
    (hs' : IsAlgebraSection φ ψ π s')
    (U : Cᵒᵖ) (x : O₂.obj.obj U) :
    (kernelIdealSheafModule π s).val.obj U :=
  ambient_zero_to_kernel_section (π := π) (s := s) U
    (s'.hom.app U x - s.hom.app U x) (by
      have hsU :
          s.hom.app U ≫ π.hom.app U = 𝟙 _ := by
        simpa using congrArg (fun k ↦ k.hom.app U) hs.1
      have hs'U :
          s'.hom.app U ≫ π.hom.app U = 𝟙 _ := by
        simpa using congrArg (fun k ↦ k.hom.app U) hs'.1
      have hsx : π.hom.app U (s.hom.app U x) = x := by
        simpa using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hsU) x
      have hs'x : π.hom.app U (s'.hom.app U x) = x := by
        simpa using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hs'U) x
      rw [map_sub, hs'x, hsx, sub_self])

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: including the kernel-valued difference section back into `A(U)`
recovers the raw ambient difference `s' - s`. -/
private theorem section_difference_to_kernel_app_eq
    (s s' : O₂ ⟶ A)
    (hs : IsAlgebraSection φ ψ π s)
    (hs' : IsAlgebraSection φ ψ π s')
    (U : Cᵒᵖ) (x : O₂.obj.obj U) :
    kernelIdealSheafModuleInclusionApp π s U
        (section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x) =
      s'.hom.app U x - s.hom.app U x := by
  -- This is exactly the defining property of the objectwise kernel lift.
  exact ambient_zero_to_kernel_section_inclusion (π := π) (s := s) U
    (s'.hom.app U x - s.hom.app U x) (by
      have hsU :
          s.hom.app U ≫ π.hom.app U = 𝟙 _ := by
        simpa using congrArg (fun k ↦ k.hom.app U) hs.1
      have hs'U :
          s'.hom.app U ≫ π.hom.app U = 𝟙 _ := by
        simpa using congrArg (fun k ↦ k.hom.app U) hs'.1
      have hsx : π.hom.app U (s.hom.app U x) = x := by
        simpa using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hsU) x
      have hs'x : π.hom.app U (s'.hom.app U x) = x := by
        simpa using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hs'U) x
      rw [map_sub, hs'x, hsx, sub_self])

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the kernel-valued differences commute with restriction maps, so
they form a presheaf-level family of local sections. -/
private theorem section_difference_to_kernel_naturality
    (s s' : O₂ ⟶ A)
    (hs : IsAlgebraSection φ ψ π s)
    (hs' : IsAlgebraSection φ ψ π s')
    {U V : Cᵒᵖ} (ρ : U ⟶ V) (x : O₂.obj.obj U) :
    section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' V
        (O₂.obj.map ρ x) =
      (kernelIdealSheafModule π s).val.map ρ
        (section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x) := by
  -- Compare both candidate kernel sections after including them into `A(V)`.
  apply kernel_module_inclusion_app_injective (π := π) (s := s) V
  rw [section_difference_to_kernel_app_eq,
    kernel_module_inclusion_app_naturality (π := π) (s := s) ρ,
    section_difference_to_kernel_app_eq]
  have hsρ :
      A.obj.map ρ (s.hom.app U x) =
        s.hom.app V (O₂.obj.map ρ x) := by
    simpa only using
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (s.hom.naturality ρ)).symm x
  have hs'ρ :
      A.obj.map ρ (s'.hom.app U x) =
        s'.hom.app V (O₂.obj.map ρ x) := by
    simpa only using
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (s'.hom.naturality ρ)).symm x
  rw [map_sub, hs'ρ, hsρ]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the pointwise section difference is additive on each object. -/
private theorem section_difference_to_kernel_app_add
    (s s' : O₂ ⟶ A)
    (hs : IsAlgebraSection φ ψ π s)
    (hs' : IsAlgebraSection φ ψ π s')
    (U : Cᵒᵖ) (x y : O₂.obj.obj U) :
    section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U (x + y) =
      section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x +
        section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U y := by
  -- Compare additivity after including both sides into `A(U)`, where the difference formula
  -- is just the additive identity for `s' - s`.
  apply kernel_module_inclusion_app_injective (π := π) (s := s) U
  rw [section_difference_to_kernel_app_eq, kernel_module_inclusion_app_add,
    section_difference_to_kernel_app_eq, section_difference_to_kernel_app_eq]
  have hs'add : s'.hom.app U (x + y) = s'.hom.app U x + s'.hom.app U y := by
    exact (s'.hom.app U).hom.map_add x y
  have hsadd : s.hom.app U (x + y) = s.hom.app U x + s.hom.app U y := by
    exact (s.hom.app U).hom.map_add x y
  rw [hs'add, hsadd]
  abel_nf

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the pointwise section difference satisfies the Leibniz rule on each
object. -/
private theorem section_difference_to_kernel_app_mul
    (s s' : O₂ ⟶ A)
    (hs : IsAlgebraSection φ ψ π s)
    (hs' : IsAlgebraSection φ ψ π s')
    (hzero : KernelSquareZero π)
    (U : Cᵒᵖ) (x y : O₂.obj.obj U) :
    section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U (x * y) =
      x • section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U y +
        y • section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x := by
  -- Expand `s' = s + (s' - s)` in `A(U)` and kill the quadratic term by square-zero.
  apply kernel_module_inclusion_app_injective (π := π) (s := s) U
  have hs'mul : s'.hom.app U (x * y) = s'.hom.app U x * s'.hom.app U y := by
    exact (s'.hom.app U).hom.map_mul x y
  have hsmul : s.hom.app U (x * y) = s.hom.app U x * s.hom.app U y := by
    exact (s.hom.app U).hom.map_mul x y
  let dx : A.obj.obj U :=
    kernelIdealSheafModuleInclusionApp π s U
      (section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x)
  let dy : A.obj.obj U :=
    kernelIdealSheafModuleInclusionApp π s U
      (section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U y)
  have hdx : dx = s'.hom.app U x - s.hom.app U x := by
    simpa [dx] using
      section_difference_to_kernel_app_eq (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x
  have hdy : dy = s'.hom.app U y - s.hom.app U y := by
    simpa [dy] using
      section_difference_to_kernel_app_eq (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U y
  have hdx' : s'.hom.app U x = s.hom.app U x + dx := by
    rw [hdx]
    abel
  have hdy' : s'.hom.app U y = s.hom.app U y + dy := by
    rw [hdy]
    abel
  have hdxdy : dx * dy = 0 := by
    simpa [dx, dy] using
      kernel_module_inclusion_app_mul_eq_zero (π := π) (s := s) hzero U
        (section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x)
        (section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U y)
  have hsmul_y :
      kernelIdealSheafModuleInclusionApp π s U
          (x • section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U y) =
        s.hom.app U x * dy := by
    simpa [dy] using
      kernel_module_inclusion_app_smul (π := π) (s := s) U x
        (section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U y)
  have hsmul_x :
      kernelIdealSheafModuleInclusionApp π s U
          (y • section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x) =
        s.hom.app U y * dx := by
    simpa [dx] using
      kernel_module_inclusion_app_smul (π := π) (s := s) U y
        (section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x)
  calc
    kernelIdealSheafModuleInclusionApp π s U
        (section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U (x * y))
        = s'.hom.app U (x * y) - s.hom.app U (x * y) := by
            exact section_difference_to_kernel_app_eq
              (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U (x * y)
    _ = (s.hom.app U x + dx) * (s.hom.app U y + dy) - s.hom.app U x * s.hom.app U y := by
          rw [hs'mul, hsmul, hdx', hdy']
    _ = s.hom.app U x * dy + s.hom.app U y * dx + dx * dy := by
          ring
    _ = s.hom.app U x * dy + s.hom.app U y * dx := by
          rw [hdxdy, add_zero]
    _ = kernelIdealSheafModuleInclusionApp π s U
          (x • section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U y) +
        kernelIdealSheafModuleInclusionApp π s U
          (y • section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x) := by
          rw [hsmul_y, hsmul_x]
    _ = kernelIdealSheafModuleInclusionApp π s U
          (x • section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U y +
            y • section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x) := by
          rw [kernel_module_inclusion_app_add]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the pointwise section difference vanishes on the image of
`φ(U)`. -/
private theorem section_difference_to_kernel_app_map
    (s s' : O₂ ⟶ A)
    (hs : IsAlgebraSection φ ψ π s)
    (hs' : IsAlgebraSection φ ψ π s')
    (U : Cᵒᵖ) (a : O₁.obj.obj U) :
    section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U
      (φ.hom.app U a) = 0 := by
  -- On the image of `φ(U)`, both sections agree with the fixed `O₁`-algebra structure.
  apply kernel_module_inclusion_app_injective (π := π) (s := s) U
  rw [section_difference_to_kernel_app_eq, kernel_module_inclusion_app_zero]
  have hsU :
      φ.hom.app U ≫ s.hom.app U = ψ.hom.app U := by
    simpa using congrArg (fun k ↦ k.hom.app U) hs.2
  have hs'U :
      φ.hom.app U ≫ s'.hom.app U = ψ.hom.app U := by
    simpa using congrArg (fun k ↦ k.hom.app U) hs'.2
  have hsx : s.hom.app U (φ.hom.app U a) = ψ.hom.app U a := by
    simpa using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hsU) a
  have hs'x : s'.hom.app U (φ.hom.app U a) = ψ.hom.app U a := by
    simpa using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hs'U) a
  calc
    s'.hom.app U (φ.hom.app U a) - s.hom.app U (φ.hom.app U a)
        = ψ.hom.app U a - ψ.hom.app U a := by rw [hs'x, hsx]
    _ = 0 := sub_self _

/-- Helper for Lemma 18.33.9: on each object `U`, the kernel-valued pointwise difference
`x ↦ s'(x) - s(x)` is the source derivation attached to the two sections. -/
private noncomputable def section_difference_derivation_app
    (s s' : O₂ ⟶ A)
    (hs : IsAlgebraSection φ ψ π s)
    (hs' : IsAlgebraSection φ ψ π s')
    (hzero : KernelSquareZero π)
    (U : Cᵒᵖ) :
    ((kernelIdealSheafModule π s).val.obj U).Derivation (φ.hom.app U) :=
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := (φ.hom.app U).hom.toAlgebra
  ModuleCat.Derivation.mk
    (fun x ↦ section_difference_to_kernel_app
      (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x)
    (fun x y ↦ section_difference_to_kernel_app_add
      (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x y)
    (fun x y ↦ section_difference_to_kernel_app_mul
      (φ := φ) (ψ := ψ) (π := π) s s' hs hs' hzero U x y)
    (fun a ↦ section_difference_to_kernel_app_map
      (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U a)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the objectwise derivation attached to `s' - s` evaluates to the
kernel-valued pointwise difference. -/
private theorem section_difference_derivation_app_apply
    (s s' : O₂ ⟶ A)
    (hs : IsAlgebraSection φ ψ π s)
    (hs' : IsAlgebraSection φ ψ π s')
    (hzero : KernelSquareZero π)
    (U : Cᵒᵖ) (x : O₂.obj.obj U) :
    (section_difference_derivation_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' hzero U).d x =
      section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x := by
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the perturbation formula still sends `0` to `0`. -/
private theorem section_perturbation_app_map_zero
    (s : O₂ ⟶ A)
    (D : Der[φ ; kernelIdealSheafModule π s])
    (U : Cᵒᵖ) :
    s.hom.app U (0 : O₂.obj.obj U) +
        kernelIdealSheafModuleInclusionApp π s U ((D.app U).d (0 : O₂.obj.obj U)) = 0 := by
  -- The perturbation vanishes at `0` because both `s` and the derivation do.
  have hD0 : (D.app U).d (0 : O₂.obj.obj U) = 0 := by
    have h : (D.app U).d 0 = (D.app U).d 0 + (D.app U).d 0 := by
      calc
        (D.app U).d 0 = (D.app U).d (0 + 0 : O₂.obj.obj U) := by
          exact (congrArg (fun z : O₂.obj.obj U ↦ (D.app U).d z) (zero_add 0)).symm
        _ = (D.app U).d 0 + (D.app U).d 0 := by
          exact ModuleCat.Derivation.d_add (D.app U) (0 : O₂.obj.obj U) 0
    have h' : (D.app U).d 0 + (D.app U).d 0 = (D.app U).d 0 + 0 := by
      calc
        (D.app U).d 0 + (D.app U).d 0 = (D.app U).d 0 := by exact h.symm
        _ = (D.app U).d 0 + 0 := by rw [add_zero]
    exact add_left_cancel h'
  have hs0 : s.hom.app U (0 : O₂.obj.obj U) = 0 := by
    exact (s.hom.app U).hom.map_zero
  rw [hs0, hD0, kernel_module_inclusion_app_zero, zero_add]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the perturbation formula still sends `1` to `1`. -/
private theorem section_perturbation_app_map_one
    (s : O₂ ⟶ A)
    (D : Der[φ ; kernelIdealSheafModule π s])
    (U : Cᵒᵖ) :
    s.hom.app U (1 : O₂.obj.obj U) +
        kernelIdealSheafModuleInclusionApp π s U ((D.app U).d (1 : O₂.obj.obj U)) = 1 := by
  -- The derivation term at `1` is zero, so the perturbed map still sends `1` to `1`.
  have hD1 : (D.app U).d (1 : O₂.obj.obj U) = 0 := by
    have h : (D.app U).d 1 = (D.app U).d 1 + (D.app U).d 1 := by
      calc
        (D.app U).d 1 = (D.app U).d (1 * 1 : O₂.obj.obj U) := by
          exact (congrArg (fun z : O₂.obj.obj U ↦ (D.app U).d z) (one_mul 1)).symm
        _ = (1 : O₂.obj.obj U) • (D.app U).d 1 + (1 : O₂.obj.obj U) • (D.app U).d 1 := by
          exact ModuleCat.Derivation.d_mul (D.app U) (1 : O₂.obj.obj U) 1
        _ = (D.app U).d 1 + (D.app U).d 1 := by
          have hsmul : (1 : O₂.obj.obj U) • (D.app U).d 1 = (D.app U).d 1 := by
            exact one_smul (O₂.obj.obj U) ((D.app U).d 1)
          calc
            (1 : O₂.obj.obj U) • (D.app U).d 1 + (1 : O₂.obj.obj U) • (D.app U).d 1
                = (D.app U).d 1 + (1 : O₂.obj.obj U) • (D.app U).d 1 := by rw [hsmul]
            _ = (D.app U).d 1 + (D.app U).d 1 := by rw [hsmul]
    have h' : (D.app U).d 1 + (D.app U).d 1 = (D.app U).d 1 + 0 := by
      calc
        (D.app U).d 1 + (D.app U).d 1 = (D.app U).d 1 := by exact h.symm
        _ = (D.app U).d 1 + 0 := by rw [add_zero]
    exact add_left_cancel h'
  have hs1 : s.hom.app U (1 : O₂.obj.obj U) = 1 := by
    exact (s.hom.app U).hom.map_one
  rw [hs1, hD1, kernel_module_inclusion_app_zero, add_zero]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the perturbation formula is additive on each object. -/
private theorem section_perturbation_app_map_add
    (s : O₂ ⟶ A)
    (D : Der[φ ; kernelIdealSheafModule π s])
    (U : Cᵒᵖ) (x y : O₂.obj.obj U) :
    s.hom.app U (x + y) + kernelIdealSheafModuleInclusionApp π s U ((D.app U).d (x + y)) =
      (s.hom.app U x + kernelIdealSheafModuleInclusionApp π s U ((D.app U).d x)) +
        (s.hom.app U y + kernelIdealSheafModuleInclusionApp π s U ((D.app U).d y)) := by
  -- Additivity is inherited from the ring map `s`, the additive derivation `D`, and the linear
  -- kernel inclusion.
  have hsadd : s.hom.app U (x + y) = s.hom.app U x + s.hom.app U y := by
    exact (s.hom.app U).hom.map_add x y
  have hDadd : (D.app U).d (x + y) = (D.app U).d x + (D.app U).d y := by
    exact ModuleCat.Derivation.d_add (D.app U) x y
  rw [hsadd, hDadd, kernel_module_inclusion_app_add]
  abel_nf

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the perturbation formula is multiplicative on each object. -/
private theorem section_perturbation_app_map_mul
    (s : O₂ ⟶ A)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s])
    (U : Cᵒᵖ) (x y : O₂.obj.obj U) :
    s.hom.app U (x * y) + kernelIdealSheafModuleInclusionApp π s U ((D.app U).d (x * y)) =
      (s.hom.app U x + kernelIdealSheafModuleInclusionApp π s U ((D.app U).d x)) *
        (s.hom.app U y + kernelIdealSheafModuleInclusionApp π s U ((D.app U).d y)) := by
  -- Expand `D(xy)` by Leibniz, realize the scalar actions through `s`, and kill the quadratic
  -- kernel term by the square-zero hypothesis.
  have hsmul : s.hom.app U (x * y) = s.hom.app U x * s.hom.app U y := by
    exact (s.hom.app U).hom.map_mul x y
  have hDmul :
      (D.app U).d (x * y) = x • (D.app U).d y + y • (D.app U).d x := by
    exact ModuleCat.Derivation.d_mul (D.app U) x y
  calc
    s.hom.app U (x * y) + kernelIdealSheafModuleInclusionApp π s U ((D.app U).d (x * y))
        = s.hom.app U x * s.hom.app U y +
            kernelIdealSheafModuleInclusionApp π s U (x • (D.app U).d y + y • (D.app U).d x) := by
              rw [hsmul, hDmul]
    _ = s.hom.app U x * s.hom.app U y +
          (kernelIdealSheafModuleInclusionApp π s U (x • (D.app U).d y) +
            kernelIdealSheafModuleInclusionApp π s U (y • (D.app U).d x)) := by
            rw [kernel_module_inclusion_app_add]
    _ = s.hom.app U x * s.hom.app U y +
          (s.hom.app U x * kernelIdealSheafModuleInclusionApp π s U ((D.app U).d y) +
            s.hom.app U y * kernelIdealSheafModuleInclusionApp π s U ((D.app U).d x)) := by
            rw [kernel_module_inclusion_app_smul (π := π) (s := s) U x ((D.app U).d y),
              kernel_module_inclusion_app_smul (π := π) (s := s) U y ((D.app U).d x)]
    _ = s.hom.app U x * s.hom.app U y +
          s.hom.app U x * kernelIdealSheafModuleInclusionApp π s U ((D.app U).d y) +
            s.hom.app U y * kernelIdealSheafModuleInclusionApp π s U ((D.app U).d x) := by
            rw [add_assoc]
    _ = (s.hom.app U x + kernelIdealSheafModuleInclusionApp π s U ((D.app U).d x)) *
          (s.hom.app U y + kernelIdealSheafModuleInclusionApp π s U ((D.app U).d y)) := by
            rw [add_mul, mul_add, mul_add,
              kernel_module_inclusion_app_mul_eq_zero (π := π) (s := s) hzero U
                ((D.app U).d x) ((D.app U).d y)]
            ring

/-- Helper for Lemma 18.33.9: on each object, perturbing a section by a kernel-valued derivation
produces the source formula `s + D` as a ring hom. -/
private noncomputable def section_perturbation_app
    (s : O₂ ⟶ A) (_hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s])
    (U : Cᵒᵖ) : O₂.obj.obj U →+* A.obj.obj U :=
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := (φ.hom.app U).hom.toAlgebra
  { toFun := fun x ↦ s.hom.app U x + kernelIdealSheafModuleInclusionApp π s U ((D.app U).d x)
    map_zero' := section_perturbation_app_map_zero (φ := φ) (π := π) s D U
    map_one' := section_perturbation_app_map_one (φ := φ) (π := π) s D U
    map_add' := fun x y ↦
      section_perturbation_app_map_add (φ := φ) (π := π) s D U x y
    map_mul' := fun x y ↦
      section_perturbation_app_map_mul (φ := φ) (π := π) s hzero D U x y }

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: evaluating the perturbation ring hom gives the expected formula
`s(x) + D(x)`. -/
private theorem section_perturbation_app_apply
    (s : O₂ ⟶ A) (hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s])
    (U : Cᵒᵖ) (x : O₂.obj.obj U) :
    section_perturbation_app (φ := φ) (ψ := ψ) (π := π) s hs hzero D U x =
      s.hom.app U x + kernelIdealSheafModuleInclusionApp π s U ((D.app U).d x) := by
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the objectwise perturbations `s + D` respect restriction maps, so
they assemble to a sheaf morphism. -/
private theorem section_perturbation_naturality
    (s : O₂ ⟶ A) (hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s])
    {U V : Cᵒᵖ} (ρ : U ⟶ V) (x : O₂.obj.obj U) :
    A.obj.map ρ (section_perturbation_app (φ := φ) (ψ := ψ) (π := π) s hs hzero D U x) =
      section_perturbation_app (φ := φ) (ψ := ψ) (π := π) s hs hzero D V
        (O₂.obj.map ρ x) := by
  -- Naturality comes from the naturality of `s` and the defining `d_map` axiom of the
  -- sheaf-valued derivation.
  have hsρ :
      A.obj.map ρ (s.hom.app U x) =
        s.hom.app V (O₂.obj.map ρ x) := by
    simpa only using
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (s.hom.naturality ρ)).symm x
  have hDρ :
      (D.app V).d (O₂.obj.map ρ x) =
        (kernelIdealSheafModule π s).val.map ρ ((D.app U).d x) := by
    simpa using D.d_map ρ x
  rw [section_perturbation_app_apply, section_perturbation_app_apply]
  rw [map_add, hsρ]
  refine congrArg (fun t ↦ s.hom.app V (O₂.obj.map ρ x) + t) ?_
  rw [← kernel_module_inclusion_app_naturality (π := π) (s := s) ρ ((D.app U).d x), ← hDρ]

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: perturbing a fixed compatible section by a derivation into the
square-zero kernel ideal again gives a compatible section. -/
private theorem exists_algebra_section_with_perturbation_of_derivation
    (s : O₂ ⟶ A) (hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s]) :
    ∃ s' : O₂ ⟶ A,
      IsAlgebraSection φ ψ π s' ∧
        IsSectionPerturbation φ π s s' D := by
  -- Route correction: package the textbook formula `s + D` as objectwise ring homs first, and
  -- only then assemble the sheaf morphism by a separate naturality lemma.
  let sPlusD : O₂ ⟶ A :=
    ⟨{ app := fun U ↦ CommRingCat.ofHom
          (section_perturbation_app (φ := φ) (ψ := ψ) (π := π) s hs hzero D U),
        naturality := by
          intro U V ρ
          ext x
          exact (section_perturbation_naturality (φ := φ) (ψ := ψ) (π := π)
            s hs hzero D ρ x).symm }⟩
  have hsPlusD_section : sPlusD ≫ π = 𝟙 O₂ := by
    -- After applying `π`, the kernel perturbation vanishes and we recover the original section
    -- identity for `s`.
    ext U x
    have hsU :
        s.hom.app U ≫ π.hom.app U = 𝟙 _ := by
      simpa using congrArg (fun k ↦ k.hom.app U) hs.1
    have hsx : π.hom.app U (s.hom.app U x) = x := by
      simpa using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hsU) x
    change π.hom.app U (sPlusD.hom.app U x) = x
    change π.hom.app U (section_perturbation_app (φ := φ) (ψ := ψ) (π := π) s hs hzero D U x) = x
    rw [section_perturbation_app_apply]
    rw [map_add, hsx, kernel_module_inclusion_app_pi_eq_zero, add_zero]
  have hsPlusD_alg : φ ≫ sPlusD = ψ := by
    -- The compatibility with the `O₁`-algebra structure is preserved because `D` vanishes on the
    -- image of `φ`.
    ext U x
    have hsU :
        φ.hom.app U ≫ s.hom.app U = ψ.hom.app U := by
      simpa using congrArg (fun k ↦ k.hom.app U) hs.2
    have hsx : s.hom.app U (φ.hom.app U x) = ψ.hom.app U x := by
      simpa using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hsU) x
    have hDx : (D.app U).d (φ.hom.app U x) = 0 := by
      change D.d (φ.hom.app U x) = 0
      exact D.d_app (X := U) x
    change sPlusD.hom.app U (φ.hom.app U x) = ψ.hom.app U x
    change
      section_perturbation_app (φ := φ) (ψ := ψ) (π := π) s hs hzero D U (φ.hom.app U x) =
        ψ.hom.app U x
    rw [section_perturbation_app_apply]
    rw [hsx, hDx, kernel_module_inclusion_app_zero, add_zero]
  refine ⟨sPlusD, ⟨hsPlusD_section, hsPlusD_alg⟩, ?_⟩
  -- The objectwise description of `sPlusD` is exactly the required perturbation formula.
  intro U x
  change section_perturbation_app (φ := φ) (ψ := ψ) (π := π) s hs hzero D U x =
    s.hom.app U x + kernelIdealSheafModuleInclusionApp π s U ((D.app U).d x)
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 18.33.9: the difference of two compatible sections should globalize to a
derivation into the descended kernel module. -/
private theorem exists_derivation_with_section_perturbation
    (s s' : O₂ ⟶ A)
    (hs : IsAlgebraSection φ ψ π s)
    (hs' : IsAlgebraSection φ ψ π s')
    (hzero : KernelSquareZero π) :
    ∃ D : Der[φ ; kernelIdealSheafModule π s],
      IsSectionPerturbation φ π s s' D := by
  -- Route correction: follow the source proof literally by globalizing the objectwise difference
  -- `s' - s` after it has been lifted into the descended kernel module.
  let D : Der[φ ; kernelIdealSheafModule π s] :=
    PresheafOfModules.Derivation'.mk
      (fun U ↦ section_difference_derivation_app
        (φ := φ) (ψ := ψ) (π := π) s s' hs hs' hzero U)
      (fun _ _ ρ x ↦ by
        rw [section_difference_derivation_app_apply, section_difference_derivation_app_apply]
        exact section_difference_to_kernel_naturality
          (φ := φ) (ψ := ψ) (π := π) s s' hs hs' ρ x)
  refine ⟨D, ?_⟩
  intro U x
  -- Rewrite `D.d x` to the defining pointwise difference and then rearrange `s' - s`.
  change
    s'.hom.app U x = s.hom.app U x +
      kernelIdealSheafModuleInclusionApp π s U
        (section_difference_to_kernel_app (φ := φ) (ψ := ψ) (π := π) s s' hs hs' U x)
  rw [section_difference_to_kernel_app_eq]
  abel

-- Proof sketch: define the candidate section pointwise by `s + D`; the Leibniz rule and the
-- square-zero condition show that this is again a morphism of sheaves of rings, while the
-- derivation vanishes on `O₁` and lands in `Ker π`, giving the compatibility and section
-- identities. Uniqueness follows from extensionality of sheaf morphisms.
omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Lemma 18.33.9 (1), existence-and-uniqueness form: a derivation into the intrinsic square-zero
kernel ideal determines a unique compatible section obtained by adding that derivation to a fixed
compatible section. -/
@[stacks 04BP]
theorem existsUnique_algebraSection_of_derivation
    (s : O₂ ⟶ A) (hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s]) :
    ∃! s' : O₂ ⟶ A,
      IsAlgebraSection φ ψ π s' ∧
        IsSectionPerturbation φ π s s' D := by
  obtain ⟨s', hs', hpert⟩ :=
    exists_algebra_section_with_perturbation_of_derivation
      (φ := φ) (ψ := ψ) (π := π) s hs hzero D
  refine ⟨s', ⟨hs', hpert⟩, ?_⟩
  intro s'' hs''
  -- Two perturbed sections with the same base section and derivation agree objectwise.
  ext U x
  exact (hs''.2 U x).trans (hpert U x).symm

-- Proof sketch: for a second compatible section `s'`, the pointwise difference `s' - s` lands in
-- the actual kernel ideal sheaf because both sections split `π`. The square-zero hypothesis and
-- the ring-hom identities for `s` and `s'` then show that this lifted difference is a relative
-- derivation into `Ker π`, and uniqueness follows from the monicity of `kernel.ι`.
omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Lemma 18.33.9 (2): relative to a fixed compatible section `s`, every other compatible section
arises from a unique derivation with values in the intrinsic square-zero kernel sheaf `Ker π`,
viewed as its descended canonical `O₂`-module. -/
@[stacks 04BP]
lemma existsUnique_derivation_of_algebraSection
    (s s' : O₂ ⟶ A)
    (hs : IsAlgebraSection φ ψ π s)
    (hs' : IsAlgebraSection φ ψ π s')
    (hzero : KernelSquareZero π) :
    ∃! D : Der[φ ; kernelIdealSheafModule π s],
      IsSectionPerturbation φ π s s' D := by
  obtain ⟨D, hD⟩ :=
    exists_derivation_with_section_perturbation
      (φ := φ) (ψ := ψ) (π := π) s s' hs hs' hzero
  refine ⟨D, hD, ?_⟩
  intro D' hD'
  -- Compare the two perturbation formulas and cancel the common section term.
  ext U x
  apply kernel_module_inclusion_app_injective (π := π) (s := s) U
  have hsum :
      s.hom.app U x + kernelIdealSheafModuleInclusionApp π s U (D.d x) =
        s.hom.app U x + kernelIdealSheafModuleInclusionApp π s U (D'.d x) := by
    exact (hD U x).symm.trans (hD' U x)
  exact add_left_cancel hsum.symm

end
