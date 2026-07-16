import StacksProject_2024.stacks_project.Chap21.Definition_21_44_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

/-
Domain-style sampling for Lemma 21.44.4:
- primary domain: strictly perfect cochain complexes of module sheaves on ringed sites, and their
  inverse-image functors;
- inspected owner declarations:
  `SheafOfModules.RingedSite.ringedSiteModuleCategory`,
  `CochainComplex.IsStrictlyPerfect`,
  `SheafOfModules.RingedSite.pullbackComplex`,
  `RingedSite.CochainComplex.IsStrictlyPerfect`;
- best owner abstraction: the public owner layer is
  `ringedSiteModuleCategory`, `CochainComplex.IsStrictlyPerfect`, and the induced pullback-complex
  owner `pullbackComplex`; the site-presented theorem should be a thin bridge to the bundled
  strict-perfectness owner surface through that Chapter 21 bridge;
- primitive data: the site-presented structure morphism of `RingCat`-valued sheaves induced by
  `φ`;
- derived API: the bundled and site-presented pullback preservation statements for strict
  perfectness.

Source/core/bridge triage:
- `source-facing`: pullback preserves strictly perfect complexes for the site-presented morphism;
- `core/canonical`: `ringedSiteModuleCategory` and `RingedSite.CochainComplex.IsStrictlyPerfect`;
- `bridge/view`: the induced pullback-complex owner `pullbackComplex F φ` from Lemma `21.18.1`.
-/
variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪D : Sheaf JC CommRingCat.{max u v}} {𝒪C : Sheaf JD CommRingCat.{max u v}}
variable (φ : 𝒪D ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} JC JD).obj 𝒪C)
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]

local notation "ModD" => ringedSiteModuleCategory JC 𝒪D
local notation "ModC" => ringedSiteModuleCategory JD 𝒪C

/-- Companion bridge for Lemma 21.44.4: the Chapter 21 pullback-complex owner preserves the
bundled strict-perfectness predicate on cochain complexes of module sheaves. -/
theorem pullbackComplex_isStrictlyPerfect
    (E : CochainComplex ModD ℤ)
    (hE : RingedSite.CochainComplex.IsStrictlyPerfect E) :
    RingedSite.CochainComplex.IsStrictlyPerfect (pullbackComplex F φ E) := by
  sorry

/-- Lemma 21.44.4: for a site-presented morphism of ringed topoi determined by `φ`, the Chapter 21
pullback complex of a strictly perfect complex of `𝒪_𝒟`-modules is a strictly perfect complex of
`𝒪_𝒞`-modules. -/
@[stacks 08H3]
theorem isStrictlyPerfect_pullback
    (E : CochainComplex ModD ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    CochainComplex.IsStrictlyPerfect (pullbackComplex F φ E) := by
  rw [CochainComplex.isStrictlyPerfect_iff_ringedSite] at hE ⊢
  simpa using pullbackComplex_isStrictlyPerfect F φ E hE

end

end SheafOfModules.RingedSite
