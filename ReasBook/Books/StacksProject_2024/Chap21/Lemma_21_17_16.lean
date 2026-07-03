import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap21.Definition_21_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the given
ringed site. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]

-- Proof sketch: let `ℱ := kernel (K.dFrom n)`. Because `K` is acyclic, the brutal truncation
-- `\cdots ⟶ K^{n-2} ⟶ K^{n-1} ⟶ ℱ ⟶ 0` is a flat resolution of `ℱ`. Lemma `21.17.8` makes that
-- bounded-above flat complex K-flat, so it computes `Tor_1^\mathcal O(ℱ, 𝒢)` for every module
-- `𝒢`. Since `K` itself is K-flat and acyclic, derived tensoring `K` with `𝒢` is zero, forcing
-- `Tor_1^\mathcal O(ℱ, 𝒢) = 0`; then Lemma `21.17.15` yields flatness of `ℱ`.
/-- Lemma 21.17.16: if `K` is a K-flat acyclic cochain complex of flat `\mathcal O`-modules on a
ringed site, then the kernel of the differential `K^n \to K^{n+1}` is a flat
`\mathcal O`-module. -/
theorem isFlat_kernel_dFrom_of_isKFlat_of_acyclic
    (K : CochainComplex (RingedSiteModules 𝒪) ℤ) (n : ℤ)
    (hKFlat : IsKFlat K) (hAcyclic : K.Acyclic)
    (hFlat : ∀ i : ℤ, IsFlat 𝒪 (K.X i)) :
    IsFlat 𝒪 (kernel (K.dFrom n)) := sorry

end SheafOfModules.RingedSite
