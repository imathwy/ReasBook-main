import Mathlib
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

/- Domain-style sampling for Lemma 18.27.5:
- primary domain: left exactness of internal Hom in the monoidal closed category of sheaves of
  modules on a ringed site;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `ShortComplex`,
  `ihom`,
  `MonoidalClosed.pre`,
  `CategoryTheory.functor_leftExact_iff_maps_shortExact_to_exact_mono`;
- best owner abstraction:
  a short complex `S : ShortComplex (ringedSiteModuleCategory J 𝒪)` together with the internal-Hom
  owners `ihom ℱ` in the target variable and `pre` in the source variable;
- primitive data:
  a short exact sequence `S` of `𝒪`-modules and a fixed module in the remaining variable;
- derived API:
  the induced short complexes obtained from `S` by `ihom ℱ` and by source-variable
  precomposition.

Source/core/bridge triage:
- `source-facing`: the two exactness statements for internal Hom applied to a short exact sequence
  of `𝒪`-modules;
- `core/canonical`: `ringedSiteModuleCategory`, `ShortComplex`, `ihom`, and `pre`;
- `bridge/view`: the explicit short complexes built from the induced internal-Hom morphisms.

The local `RingedSiteModules` alias was a duplicate of the chapter owner
`ringedSiteModuleCategory`, and the split arrow data `{f₂₁, f₁, hcomp}` / `{g₀₁, g₁₂, hcomp}` was
derived from the canonical `ShortComplex` owner. This file therefore keeps the source-facing
exactness statements, but refines their public API to the canonical chapter owner and a
`ShortComplex`-first surface. -/

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: `pre` is contravariantly functorial in the source variable, so the composite
-- induced by `S.f ≫ S.g = 0` vanishes.
private theorem ringedSiteModuleInternalHom_pre_app_comp_zero
    {S : ShortComplex (ringedSiteModuleCategory J 𝒪)} (𝒢 : ringedSiteModuleCategory J 𝒪) :
    (MonoidalClosed.pre S.g).app 𝒢 ≫ (MonoidalClosed.pre S.f).app 𝒢 = 0 := by
  sorry

-- Proof sketch: functoriality of `ihom ℱ` sends the zero composite `S.f ≫ S.g = 0` to zero.
private theorem ringedSiteModuleInternalHom_map_comp_zero
    {S : ShortComplex (ringedSiteModuleCategory J 𝒪)} (ℱ : ringedSiteModuleCategory J 𝒪) :
    (ihom ℱ).map S.f ≫ (ihom ℱ).map S.g = 0 := by
  sorry

-- Proof sketch: fix `𝒢` and regard `ℱ ↦ ℋom_𝒪(ℱ, 𝒢)` as the source-variable internal-Hom owner.
-- Lemma 18.27.4 gives the relevant limit preservation, and Lemma 12.7.2 converts that to left
-- exactness on mapped short exact sequences.
/-- Lemma 18.27.5 (1): if `ℱ₂ ⟶ ℱ₁ ⟶ ℱ ⟶ 0` is a short exact sequence of `𝒪`-modules on a ringed
site, then `0 ⟶ ℋom_𝒪(ℱ, 𝒢) ⟶ ℋom_𝒪(ℱ₁, 𝒢) ⟶ ℋom_𝒪(ℱ₂, 𝒢)` is exact. -/
theorem ringedSiteModuleInternalHom_exact_in_source
    {S : ShortComplex (ringedSiteModuleCategory J 𝒪)}
    (hS : S.ShortExact) (𝒢 : ringedSiteModuleCategory J 𝒪) :
    (ShortComplex.mk
        ((MonoidalClosed.pre S.g).app 𝒢)
        ((MonoidalClosed.pre S.f).app 𝒢)
        (ringedSiteModuleInternalHom_pre_app_comp_zero J 𝒪 𝒢)).Exact ∧
      Mono ((MonoidalClosed.pre S.g).app 𝒢) := by
  sorry

-- Proof sketch: for fixed `ℱ`, the functor `𝒢 ↦ ℋom_𝒪(ℱ, 𝒢)` is the right adjoint `ihom ℱ`.
-- Lemma 18.27.4 supplies preservation of limits, and Lemma 12.7.2 converts that to left
-- exactness of the induced Hom sequence.
/-- Lemma 18.27.5 (2): if `0 ⟶ 𝒢 ⟶ 𝒢₁ ⟶ 𝒢₂` is a short exact sequence of `𝒪`-modules on a ringed
site, then `0 ⟶ ℋom_𝒪(ℱ, 𝒢) ⟶ ℋom_𝒪(ℱ, 𝒢₁) ⟶ ℋom_𝒪(ℱ, 𝒢₂)` is exact. -/
theorem ringedSiteModuleInternalHom_exact_in_target
    {S : ShortComplex (ringedSiteModuleCategory J 𝒪)}
    (hS : S.ShortExact) (ℱ : ringedSiteModuleCategory J 𝒪) :
    (ShortComplex.mk
        ((ihom ℱ).map S.f)
        ((ihom ℱ).map S.g)
        (ringedSiteModuleInternalHom_map_comp_zero J 𝒪 ℱ)).Exact ∧
      Mono ((ihom ℱ).map S.f) := by
  sorry

end
