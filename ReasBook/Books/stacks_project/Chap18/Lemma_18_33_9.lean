import Mathlib
import stacks_project.Chap18.Lemma_18_28_15
import stacks_project.Chap18.Lemma_18_33_2

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
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

private abbrev structureSheafQuotient (π : A ⟶ O₂) :
    SheafOfModules.unit (ringSheaf J A) ⟶
      (SheafOfModules.pushforward (ringedSiteStructureMap π)).obj
        (SheafOfModules.unit (ringSheaf J O₂)) :=
  SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap π)

/-- The intrinsic kernel ideal sheaf of `π`, viewed as an `A`-module sheaf. -/
abbrev kernelIdealSheaf (π : A ⟶ O₂) : SheafOfModules (ringSheaf J A) :=
  kernel (structureSheafQuotient π)

/-- The canonical inclusion of `Ker π` into `A`. -/
abbrev kernelIdealInclusion (π : A ⟶ O₂) :
    kernelIdealSheaf π ⟶ SheafOfModules.unit (ringSheaf J A) :=
  kernel.ι (structureSheafQuotient π)

/-- The sectionwise inclusion of `Ker π` into `A`. -/
abbrev kernelIdealInclusionApp
    (π : A ⟶ O₂)
    (U : Cᵒᵖ) (x : (kernelIdealSheaf π).val.obj U) : A.obj.obj U :=
  show A.obj.obj U from (kernelIdealInclusion π).val.app U x

/-- The intrinsic kernel ideal of `π` has square zero when products of local kernel sections vanish
in `A`. -/
abbrev KernelSquareZero (π : A ⟶ O₂) : Prop :=
  ∀ U : Cᵒᵖ, ∀ x y : (kernelIdealSheaf π).val.obj U,
    kernelIdealInclusionApp π U x * kernelIdealInclusionApp π U y = 0

/-- The kernel ideal sheaf of `π`, viewed as an `O₂`-module by restricting scalars along a fixed
section `s : O₂ ⟶ A`. -/
abbrev kernelIdealSheafModule
    (π : A ⟶ O₂) (s : O₂ ⟶ A) :
    SheafOfModules (ringSheaf J O₂) :=
  (restrictionAlong s).obj (kernelIdealSheaf π)

/-- A section `s'` differs from `s` by the derivation `D` when their local sections satisfy the
pointwise formula `s' = s + D` through the canonical inclusion `Ker π ↪ A`. -/
abbrev IsSectionPerturbation
    (φ : O₁ ⟶ O₂) (π : A ⟶ O₂)
    (s s' : O₂ ⟶ A)
    (D : Der[φ ; kernelIdealSheafModule π s]) : Prop :=
  ∀ U : Cᵒᵖ, ∀ x : O₂.obj.obj U,
    s'.hom.app U x = s.hom.app U x +
      kernelIdealInclusionApp π U (show (kernelIdealSheaf π).val.obj U from D.d x)

-- Proof sketch: define the candidate section pointwise by `s + D`; the Leibniz rule and the
-- square-zero condition show that this is again a morphism of sheaves of rings, while the
-- derivation vanishes on `O₁` and lands in `Ker π`, giving the compatibility and section
-- identities. Uniqueness follows from extensionality of sheaf morphisms.
/-- Lemma 18.33.9 (1), existence-and-uniqueness form: a derivation into the intrinsic square-zero
kernel ideal determines a unique compatible section obtained by adding that derivation to a fixed
compatible section. -/
theorem existsUnique_algebraSection_of_derivation
    (s : O₂ ⟶ A) (hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s]) :
    ∃! s' : O₂ ⟶ A,
      IsAlgebraSection φ ψ π s' ∧
        IsSectionPerturbation φ π s s' D := sorry

/-- The canonical section obtained from `s` by adding the derivation `D` in the square-zero kernel
ideal of `π`. -/
noncomputable def algebraSectionOfDerivation
    (s : O₂ ⟶ A) (hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s]) :
    O₂ ⟶ A :=
  Classical.choose
    (existsUnique_algebraSection_of_derivation φ ψ π s hs hzero D)

private theorem algebraSectionOfDerivation_hasProperty
    (s : O₂ ⟶ A) (hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s]) :
    IsAlgebraSection φ ψ π (algebraSectionOfDerivation φ ψ π s hs hzero D) ∧
      IsSectionPerturbation φ π s (algebraSectionOfDerivation φ ψ π s hs hzero D) D := by
  exact (Classical.choose_spec
    (existsUnique_algebraSection_of_derivation φ ψ π s hs hzero D)).1

/-- Lemma 18.33.9 (1): starting from a compatible algebra section `s`, a derivation into the
intrinsic square-zero kernel ideal of `π` produces the actual translated section `s + D`. -/
lemma derivation_yields_algebraSection
    (s : O₂ ⟶ A) (hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s]) :
    IsAlgebraSection φ ψ π (algebraSectionOfDerivation φ ψ π s hs hzero D) ∧
      IsSectionPerturbation φ π s (algebraSectionOfDerivation φ ψ π s hs hzero D) D := by
  exact algebraSectionOfDerivation_hasProperty φ ψ π s hs hzero D

-- Proof sketch: for a second compatible section `s'`, the pointwise difference `s' - s` lands in
-- the actual kernel ideal sheaf because both sections split `π`. The square-zero hypothesis and
-- the ring-hom identities for `s` and `s'` then show that this lifted difference is a relative
-- derivation into `Ker π`, and uniqueness follows from the monicity of `kernel.ι`.
/-- Lemma 18.33.9 (2): relative to a fixed compatible section `s`, every other compatible section
arises from a unique derivation with values in the intrinsic square-zero kernel sheaf `Ker π`,
viewed as its descended canonical `O₂`-module. -/
lemma existsUnique_derivation_of_algebraSection
    (s s' : O₂ ⟶ A)
    (hs : IsAlgebraSection φ ψ π s)
    (hs' : IsAlgebraSection φ ψ π s')
    (hzero : KernelSquareZero π) :
    ∃! D : Der[φ ; kernelIdealSheafModule π s],
      IsSectionPerturbation φ π s s' D := sorry

end
