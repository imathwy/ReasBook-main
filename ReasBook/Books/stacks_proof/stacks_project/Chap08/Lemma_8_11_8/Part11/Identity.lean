import StacksProject_2024.Chap08.Lemma_8_11_8.Part11.IdentitySourceShell

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8: once the chosen-cover transition square is repaired, the datum-side
transition attached to `𝟙 U` should already be the identity morphism of the chosen-cover descent
datum over `U`. This isolates the remaining identity-law blocker away from the outer sheaf
transport. -/
theorem chosen_cover_descent_transition_iso_id_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) :
    -- §5.4 identity law `ρ_{𝟙 U} = id`. Post-Mathlib-refactor the defeq
    -- `overMapPullback (𝟙 U) ≅ 𝟭` is propositional, so the RHS is the canonical descended
    -- `overMapPullbackId` comparison `pulled(𝟙 U) → 𝒢_U` (the genuine "identity" here), not a
    -- literal `𝟙`.
    (chosen_cover_descent_transition_iso
      (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U)).hom =
      (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).map
        ((J.overMapPullbackId (Type (max u v)) U).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)).hom := by
  -- Reduce the datum-side identity law to the component identity above; the remaining source
  -- content is now localized at one chosen-cover member.
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  simpa [chosen_cover_descent_functor, chosen_cover_descent_transition_iso] using
    chosen_cover_descent_transition_component_iso_id_hom
      (𝒮 := 𝒮) hGerbe hAbelian U I

end CategoryTheory
