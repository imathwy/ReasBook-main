import StacksProject_2024.stacks_project.Chap22.AdmissibleShortExact

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open HomologicalComplex

universe u

namespace CochainComplex

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ

-- Source/core/bridge triage:
-- * `source-facing`: Lemma 22.7.6, asserting that the composite vanishes up to homotopy in the
--   middle admissible short exact sequence situation;
-- * `core/canonical`: strictification of homotopy-commutative squares from Lemma 22.7.3 together
--   with the canonical exact lift `ShortComplex.Exact.lift`;
-- * `bridge/view`: the Chapter 22 owner `IsAdmissibleShortExact`, rather than raw degreewise
--   splitting data.

/-- Companion bridge for Lemma 22.7.6: chosen null-homotopies of the two boundary composites
induce a chosen null-homotopy of the composite. -/
theorem comp_homotopic_zero_of_admissibleShortExact_boundaryPair_ofHomotopy
    (S₁ S₂ S₃ : ShortComplex DGMod)
    (hS₂ : IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem S₂)
    {b : S₁.X₂ ⟶ S₂.X₂}
    {b' : S₂.X₂ ⟶ S₃.X₂}
    (hb_right : Homotopy (b ≫ S₂.g) (0 : S₁.X₂ ⟶ S₂.X₃))
    (hb'_left : Homotopy (S₂.f ≫ b') (0 : S₂.X₁ ⟶ S₃.X₂)) :
    homotopic (ModuleCat A) (up ℤ) (b ≫ b') (0 : S₁.X₂ ⟶ S₃.X₂) := by
  letI : Mono S₂.f := hS₂.shortExact.mono_f
  letI : Epi S₂.g := hS₂.shortExact.epi_g
  have hExact₂ : S₂.Exact := hS₂.shortExact.exact
  have hb_right' : Homotopy ((𝟙 S₁.X₂) ≫ (0 : S₁.X₂ ⟶ S₂.X₃)) (b ≫ S₂.g) := by
    simpa using hb_right.symm
  have hb'_left' :
      Homotopy (S₂.f ≫ b') ((0 : S₂.X₁ ⟶ S₂.X₁) ≫ (0 : S₂.X₁ ⟶ S₃.X₂)) := by
    simpa using hb'_left
  obtain ⟨b₀, hb_b₀, hb₀_sq⟩ :=
    exists_homotopic_leftMap_of_admissibleEpi hb_right' hS₂.isAdmissibleEpi
  obtain ⟨b₀', hb'_b₀', hb₀'_sq⟩ :=
    exists_homotopic_rightMap_of_admissibleMono hb'_left' hS₂.isAdmissibleMono
  have hb₀_zero : b₀ ≫ S₂.g = 0 := by
    simpa using hb₀_sq.w.symm
  have hb₀'_zero : S₂.f ≫ b₀' = 0 := by
    simpa using hb₀'_sq.w
  let l : S₁.X₂ ⟶ S₂.X₁ := hExact₂.lift b₀ hb₀_zero
  have hl : l ≫ S₂.f = b₀ := by
    simpa [l] using hExact₂.lift_f b₀ hb₀_zero
  have hcomp_zero : b₀ ≫ b₀' = 0 := by
    calc
      b₀ ≫ b₀' = (l ≫ S₂.f) ≫ b₀' := by rw [hl]
      _ = l ≫ (S₂.f ≫ b₀') := by simp [Category.assoc]
      _ = 0 := by simp [hb₀'_zero]
  refine ⟨?_⟩
  simpa [hcomp_zero] using hb_b₀.comp hb'_b₀'

/-- Lemma 22.7.6: let
`x₁ ⟶ y₁ ⟶ z₁`, `x₂ ⟶ y₂ ⟶ z₂`, and `x₃ ⟶ y₃ ⟶ z₃` be morphism pairs of differential graded
`A`-modules, with the middle pair an admissible short exact sequence. If
`b : y₁ ⟶ y₂` lands in `ker(y₂ ⟶ z₂)` up to homotopy and `b' : y₂ ⟶ y₃` kills
`im(x₂ ⟶ y₂)` up to homotopy, then `b' ∘ b` is homotopic to zero. -/
@[stacks 09JY]
theorem comp_homotopic_zero_of_admissibleShortExact_boundaryPair
    (S₁ S₂ S₃ : ShortComplex DGMod)
    (hS₂ : IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem S₂)
    {b : S₁.X₂ ⟶ S₂.X₂}
    {b' : S₂.X₂ ⟶ S₃.X₂}
    (hb_right : homotopic (ModuleCat A) (up ℤ) (b ≫ S₂.g) (0 : S₁.X₂ ⟶ S₂.X₃))
    (hb'_left : homotopic (ModuleCat A) (up ℤ) (S₂.f ≫ b') (0 : S₂.X₁ ⟶ S₃.X₂))
    : homotopic (ModuleCat A) (up ℤ) (b ≫ b') (0 : S₁.X₂ ⟶ S₃.X₂) := by
  rcases hb_right with ⟨hb_right⟩
  rcases hb'_left with ⟨hb'_left⟩
  exact comp_homotopic_zero_of_admissibleShortExact_boundaryPair_ofHomotopy
    S₁ S₂ S₃ hS₂ hb_right hb'_left

end

end CochainComplex
