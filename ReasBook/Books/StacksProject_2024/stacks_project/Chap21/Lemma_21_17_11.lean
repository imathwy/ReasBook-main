import StacksProject_2024.Chap21.Definition_21_17_2

open CategoryTheory CochainComplex
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

-- Proof sketch: choose the upper-truncation resolution tower from Lemma `21.17.10`. Each stage is
-- bounded above and has terms that are coproducts of the localized structure modules
-- `j![𝒪, U]`, hence flat by Lemma `18.28.7`; then Lemma `21.17.8` makes every stage
-- K-flat. Apply Lemma `21.17.9` to the sequential colimit of the tower. The induced comparison to
-- `𝒢` is a quasi-isomorphism and termwise epimorphic by the construction in
-- Lemma `21.17.10`, and each term of the colimit is again flat because it is a direct sum of flat
-- modules.
/-- Lemma 21.17.11: every cochain complex `𝒢` of `𝒪`-modules on a ringed site `(𝒞, 𝒪)` admits a
quasi-isomorphism from a K-flat cochain complex whose terms are flat `𝒪`-modules, expressed by
the canonical owner
`CochainComplex.IsTermwiseFlat`, and this quasi-isomorphism is termwise surjective. -/
@[stacks 06YS]
theorem exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms
    (𝒢 : CochainComplex Mod ℤ) :
    ∃ (K : CochainComplex Mod ℤ) (α : K ⟶ 𝒢),
      K.IsKFlat ∧
      IsTermwiseFlat K ∧
      QuasiIso α ∧
      ∀ n : ℤ, Epi (α.f n) := sorry

/-- Canonical morphism-level form of Lemma 21.17.11: every complex of `𝒪`-modules on a ringed
site admits a quasi-isomorphism from a K-flat termwise-flat complex whose comparison map is an
epimorphism. -/
theorem exists_epi_quasiIso_from_KFlat_complex_of_flat_terms
    (𝒢 : CochainComplex Mod ℤ) :
    ∃ (K : CochainComplex Mod ℤ) (α : K ⟶ 𝒢),
      K.IsKFlat ∧
      IsTermwiseFlat K ∧
      QuasiIso α ∧
      Epi α := by
  obtain ⟨K, α, hKFlat, hFlat, hα, hEpi⟩ :=
    exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms 𝒢
  exact ⟨K, α, hKFlat, hFlat, hα, HomologicalComplex.epi_of_epi_f α hEpi⟩

end SheafOfModules.RingedSite
