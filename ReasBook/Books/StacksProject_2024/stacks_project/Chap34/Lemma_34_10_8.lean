import Mathlib
import StacksProject_2024.stacks_project.Chap34.Definition_34_10_7

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the general coproduct-cover pattern around
-- `CategoryTheory.Limits.Sigma.desc`; local Chapter 34 precedent fixes `IsVCovering` as the
-- source-facing owner for `V` coverings of scheme families.

/-- Lemma 34.10.8 (1): a family of morphisms `Tᵢ ⟶ T` is a `V` covering if and only if there
exists a `V` covering family refining it. -/
@[stacks 0ETI]
theorem isVCovering_iff_exists_refinement
    {ι : Type u} {T : Scheme.{u}} (Ti : ι → Scheme.{u}) (f : ∀ i, Ti i ⟶ T) :
    IsVCovering T Ti f ↔
      ∃ (κ : Type u) (Y : κ → Scheme.{u}) (g : ∀ k, Y k ⟶ T),
        IsVCovering T Y g ∧
          ∀ k : κ, ∃ i : ι, ∃ φ : Y k ⟶ Ti i, φ ≫ f i = g k := sorry

/-- Lemma 34.10.8 (2): a family of morphisms `Tᵢ ⟶ T` is a `V` covering if and only if the
singleton family whose unique map is `∐ i, Tᵢ ⟶ T` is a `V` covering. -/
@[stacks 0ETI]
theorem isVCovering_iff_sigmaDesc
    {ι : Type u} {T : Scheme.{u}} (Ti : ι → Scheme.{u}) (f : ∀ i, Ti i ⟶ T) :
    IsVCovering T Ti f ↔
      IsVCovering T (fun _ : PUnit ↦ ∐ Ti) (fun _ ↦ Limits.Sigma.desc f) := sorry

end AlgebraicGeometry
