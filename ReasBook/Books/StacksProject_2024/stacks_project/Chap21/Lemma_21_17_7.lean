import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import StacksProject_2024.stacks_project.Chap18.Lemma_18_14_2
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory
import StacksProject_2024.stacks_project.Chap21.Definition_21_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

set_option checkBinderAnnotations false

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ ℱ : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj ℱ).Additive]

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 21.17.7:
- primary domain: K-flat cochain complexes of `𝒪`-modules on a ringed site in a short
  exact sequence;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.CochainComplex.IsTermwiseFlat`,
  `CochainComplex.IsKFlat`,
  `ShortComplex.ShortExact`;
- best owner abstraction: the source-facing owner is a short complex
  `S : ShortComplex Cpx` with `hS : S.ShortExact`; the termwise-flat and K-flat hypotheses belong
  directly on the three complexes `S.Xᵢ`;
- primitive vs derived: primitive data are `S`, `hS`, the flatness of `S.X₃`, and the relevant
  K-flatness hypotheses on two of the three terms.

Source/core/bridge triage:
- `source-facing`: the ringed-site two-out-of-three K-flatness theorem from the Stacks Project,
  together with directional helper lemmas for the three consequences;
- `core/canonical`: `ringedSiteModuleCategory`, `CochainComplex.IsTermwiseFlat`,
  `CochainComplex.IsKFlat`, and `ShortComplex.ShortExact`;
- `bridge/view`: this file is the ringed-site specialization of the existing Chapter 15
  short-complex owner family
  `tensor_row_shortExact_of_termwiseFlat`,
  `tensor_shortExact_of_termwiseFlat`,
  `acyclic_X₁_of_shortExact_of_acyclic_X₂_X₃`,
  `acyclic_X₂_of_shortExact_of_acyclic_X₁_X₃`,
  `acyclic_X₃_of_shortExact_of_acyclic_X₁_X₂`,
  and `isKFlat_X₁`, `isKFlat_X₂`, `isKFlat_X₃`, transported to sheaves of modules through the
  Chapter 18 tensor-exactness comparison. Those proof-route details are intentionally kept out of
  the public theorem surface here. -/

-- Semantic recall note: `lean_leansearch` only surfaced generic tensor-exactness declarations, so
-- the source-facing owner here remains the local short-exact two-out-of-three theorem.

/-- Lemma 21.17.7: in a short exact sequence
`0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0`
of cochain complexes of `𝒪`-modules on a ringed site `(C, 𝒪)`, if every term of `K₃` is flat and
two out of `K₁`, `K₂`, `K₃` are K-flat, then so is the third. -/
@[stacks 0G7B]
theorem isKFlat_two_out_of_three_of_shortExact
    {S : ShortComplex Cpx}
    (hS : S.ShortExact)
    (hFlat₃ : IsTermwiseFlat S.X₃) :
    (S.X₁.IsKFlat ∧ S.X₂.IsKFlat → S.X₃.IsKFlat) ∧
      (S.X₁.IsKFlat ∧ S.X₃.IsKFlat → S.X₂.IsKFlat) ∧
      (S.X₂.IsKFlat ∧ S.X₃.IsKFlat → S.X₁.IsKFlat) := sorry

/-- Companion to Lemma 21.17.7: if `K₁` and `K₂` are K-flat, then `K₃` is K-flat. -/
theorem isKFlat_X₃
    {S : ShortComplex Cpx}
    (hS : S.ShortExact)
    (hFlat₃ : IsTermwiseFlat S.X₃)
    (hK₁ : S.X₁.IsKFlat)
    (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := sorry

/-- Companion to Lemma 21.17.7: if `K₁` and `K₃` are K-flat, then `K₂` is K-flat. -/
theorem isKFlat_X₂
    {S : ShortComplex Cpx}
    (hS : S.ShortExact)
    (hFlat₃ : IsTermwiseFlat S.X₃)
    (hK₁ : S.X₁.IsKFlat)
    (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := sorry

/-- Companion to Lemma 21.17.7: if `K₂` and `K₃` are K-flat, then `K₁` is K-flat. -/
theorem isKFlat_X₁
    {S : ShortComplex Cpx}
    (hS : S.ShortExact)
    (hFlat₃ : IsTermwiseFlat S.X₃)
    (hK₂ : S.X₂.IsKFlat)
    (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := sorry

end SheafOfModules.RingedSite
