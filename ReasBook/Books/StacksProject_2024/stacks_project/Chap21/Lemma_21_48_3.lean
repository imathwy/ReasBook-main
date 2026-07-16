import StacksProject_2024.stacks_project.Chap21.Example_21_48_2_Core

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

open SheafOfModules.RingedSite.CochainComplex

/- Domain-style sampling for Lemma 21.48.3:
- primary domain: duality in the monoidal category of complexes of `𝒪`-modules on a ringed site,
  together with the ringed-site owner of local strict perfectness;
- sampled owner declarations:
  `CategoryTheory.ExactPairing`,
  `SheafOfModules.RingedSite.CochainComplex.IsLocallyStrictlyPerfect`;
- best owner abstraction:
  `source-facing`: the left-dual-implies-local-strictly-perfect statement for complexes;
  `core/canonical`: `ExactPairing` and
    `SheafOfModules.RingedSite.CochainComplex.IsLocallyStrictlyPerfect`;
  `bridge/view`: the explicit companion theorem for callers who want a concrete pairing argument.

This file keeps only the source-facing local strict-perfectness consequence. The previous helper
layer duplicated internal proof scaffolding rather than reusable public API. -/

-- Proof sketch: as in the Stacks argument, one extracts degreewise duality from the complex-level
-- exact pairing, applies the localized finite-free-retract criterion on each slice site, and then
-- uses the finite support of the diagonal coevaluation to obtain local boundedness.
/-- Lemma 21.48.3: if a complex `F` of `𝒪`-modules on a ringed site has a left dual in the
monoidal category of complexes of `𝒪`-modules, then `F` is locally strictly perfect, i.e. every
object `U` admits a covering on whose members the restricted complex is strictly perfect. -/
@[stacks 0FPS]
theorem exactPairing_isLocallyStrictlyPerfect
    [MonoidalCategory Cpx] {F G : Cpx} (hpair : ExactPairing G F) :
    IsLocallyStrictlyPerfect F := by
  let _ : ExactPairing G F := hpair
  sorry

end

end SheafOfModules.RingedSite
