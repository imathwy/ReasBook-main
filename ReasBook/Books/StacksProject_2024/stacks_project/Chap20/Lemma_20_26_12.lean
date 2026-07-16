import StacksProject_2024.stacks_project.Chap17.Definition_17_17_1
import StacksProject_2024.stacks_project.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.stacks_project.Chap21.Lemma_21_17_11

open AlgebraicGeometry
open CategoryTheory HomologicalComplex
open SheafOfModules
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "SiteModX" => ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf

private theorem isFlat_iff_ringedSite_isFlat
    (ℱ : ModX) :
    SheafOfModules.IsFlat ℱ ↔ SheafOfModules.RingedSite.IsFlat X.sheaf ℱ := by
  sorry

namespace CochainComplex

/-- The opens-site owner `IsTermwiseFlat` agrees with the degreewise flatness condition for
complexes of `𝒪_X`-modules on a ringed space. -/
theorem isTermwiseFlat_iff
    (K : CochainComplex ModX ℤ) :
    IsTermwiseFlat K ↔ ∀ n : ℤ, SheafOfModules.IsFlat (K.X n) := by
  constructor
  · intro hFlat n
    exact
      (isFlat_iff_ringedSite_isFlat (K.X n)).2
        ((RingedSite.CochainComplex.isTermwiseFlat_iff K).1 hFlat n)
  · intro hFlat
    exact
      (RingedSite.CochainComplex.isTermwiseFlat_iff K).2 fun n ↦
        (isFlat_iff_ringedSite_isFlat (K.X n)).1 (hFlat n)

end CochainComplex

-- Proof sketch: specialize the Chapter 21 ringed-site resolution theorem to the opens ringed site
-- of `X`; termwise flatness is already carried by the canonical owner `IsTermwiseFlat`, and the
-- companion bridge `CochainComplex.isTermwiseFlat_iff` recovers the original degreewise wording.
/-- Lemma 20.26.12: every complex `𝒢` of `𝒪_X`-modules on a ringed space `X` admits a
quasi-isomorphism from a K-flat complex whose terms are flat `𝒪_X`-modules, and this
quasi-isomorphism is termwise surjective. The flatness condition is expressed by the canonical
owner `CochainComplex.IsTermwiseFlat`. -/
@[stacks 06YF]
theorem exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms
    (𝒢 : CochainComplex ModX ℤ) :
    ∃ (K : CochainComplex ModX ℤ) (α : K ⟶ 𝒢),
      K.IsKFlat ∧
      IsTermwiseFlat K ∧
      QuasiIso α ∧
      ∀ n : ℤ, Epi (α.f n) := by
  let 𝒢' : CochainComplex SiteModX ℤ := 𝒢
  obtain ⟨K, α, hKFlat, hFlat, hα, hEpi⟩ :=
    SheafOfModules.RingedSite.exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms 𝒢'
  exact ⟨K, α, by simpa using hKFlat, by simpa using hFlat, by simpa [𝒢'] using hα,
    by simpa using hEpi⟩

/-- Canonical morphism-level form of Lemma 20.26.12: every complex of `𝒪_X`-modules on a ringed
space admits a quasi-isomorphism from a K-flat complex with flat terms whose comparison map is an
epimorphism. -/
theorem exists_epi_quasiIso_from_KFlat_complex_of_flat_terms
    (𝒢 : CochainComplex ModX ℤ) :
    ∃ (K : CochainComplex ModX ℤ) (α : K ⟶ 𝒢),
      K.IsKFlat ∧
      IsTermwiseFlat K ∧
      QuasiIso α ∧
      Epi α := by
  obtain ⟨K, α, hKFlat, hFlat, hα, hEpi⟩ :=
    exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms 𝒢
  exact ⟨K, α, hKFlat, hFlat, hα, epi_of_epi_f α hEpi⟩

end AlgebraicGeometry.RingedSpace
