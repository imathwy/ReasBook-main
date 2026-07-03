import Mathlib
import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap18.Definition_18_28_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the given
ringed site. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => RingedSiteModules 𝒪

variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]
variable [(curriedTensor (RingedSiteModules 𝒪)).Additive]
variable [∀ M : RingedSiteModules 𝒪, ((curriedTensor (RingedSiteModules 𝒪)).obj M).Additive]
variable [∀ (K L : CochainComplex (RingedSiteModules 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSiteModules 𝒪))]

-- Proof sketch: because `E` is bounded above with flat terms, Lemma `21.17.8` makes `E` K-flat,
-- so tensoring `E` with any `\mathcal O`-module computes derived tensoring with `Q(E)`. The
-- tor-amplitude hypothesis forces exactness in degree `a - 1` after tensoring with any module,
-- hence the tail ending in `cokernel(d^{a - 1})` is a flat resolution. Therefore `Tor₁` of this
-- cokernel with every module vanishes, and Lemma `21.17.15` yields flatness.
/-- Lemma 21.46.2: if `E^•` is a bounded above complex of flat `\mathcal O`-modules on a ringed
site and tensoring it with any degree-zero `\mathcal O`-module is exact outside `[a, b]`, then
the cokernel of the differential `E^{a - 1} ⟶ E^a` is a flat `\mathcal O`-module. -/
theorem isFlat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeIn
    (E : CochainComplex Mod ℤ) (a b : ℤ)
    (hbounded : IsBoundedAbove E)
    (hFlat : ∀ n : ℤ, IsFlat 𝒪 (E.X n))
    (hTor :
      ∀ (ℱ : Mod) (i : ℤ), i ∉ Set.Icc a b →
        (HomologicalComplex.tensorObj E
            ((HomologicalComplex.single Mod (ComplexShape.up ℤ) 0).obj ℱ)).ExactAt i) :
    IsFlat 𝒪 (cokernel (E.dFrom (a - 1))) := sorry

end

end SheafOfModules.RingedSite
