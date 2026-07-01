import Mathlib
import stacks_project.Chap18.Lemma_18_28_7
import stacks_project.Chap21.Definition_21_17_2

open CategoryTheory CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]

-- Proof sketch: choose the upper-truncation resolution tower from Lemma `21.17.10`. Each stage is
-- bounded above and has terms that are coproducts of the localized structure modules
-- `j_{U!}\mathcal O_U`, hence flat by Lemma `18.28.7`; then Lemma `21.17.8` makes every stage
-- K-flat. Apply Lemma `21.17.9` to the sequential colimit of the tower. The induced comparison to
-- `\mathcal G^\bullet` is a quasi-isomorphism and termwise epimorphic by the construction in
-- Lemma `21.17.10`, and each term of the colimit is again flat because it is a direct sum of flat
-- modules.
/-- Lemma 21.17.11: every cochain complex `\mathcal G^\bullet` of `\mathcal O`-modules on a
ringed site `(\mathcal C, \mathcal O)` admits a quasi-isomorphism from a K-flat cochain complex
whose terms are flat `\mathcal O`-modules, and this quasi-isomorphism is termwise surjective. -/
theorem exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms
    (𝒢 : CochainComplex (RingedSiteModules 𝒪) ℤ) :
    ∃ (K : CochainComplex (RingedSiteModules 𝒪) ℤ) (hK : IsKFlat K)
      (hFlat : ∀ n : ℤ,
        IsFlat 𝒪 (show SheafOfModules (ringSheaf J 𝒪) from K.X n))
      (α : K ⟶ 𝒢), QuasiIso α ∧ ∀ n : ℤ, Epi (α.f n) := sorry

end SheafOfModules.RingedSite
