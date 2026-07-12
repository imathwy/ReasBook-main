import StacksProject_2024.Chap08.Lemma_8_11_8.Part11.TransitionSquare

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8: the chosen-cover transition component is the raw sheaf-level
pullback comparison, with the outer `overMapPullbackComp` shell and the fixed chosen-cover
counit comparison made explicit. -/
theorem chosen_cover_descent_transition_component_iso_hom_raw
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    (chosen_cover_descent_transition_component_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I).hom =
      (chosen_cover_pulled_component_composite_pullback_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I).hom ≫
        (chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ f)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).hom ≫
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian V I).inv := by
  -- Compare after the faithful chosen-cover descent functor on `I.Y`; each component then rewrites
  -- through the public Part09 normalization interface, avoiding the private transported component.
  haveI : (localizedSheafToCoverDescentEquivalence (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).faithful
  apply Functor.map_injective
    (localizedSheafToCoverDescentEquivalence (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  rw [chosen_cover_descent_transition_component_mapped_normalized]
  simp only [Functor.map_comp,
    localizedSheafToCoverDescentEquivalence_functor_map_component]
  rw [mixed_cover_secondary_cover_component_iso_eq_pullback_component,
    chosen_cover_pullback_to_local_object_component_iso_hom]
  rfl

end CategoryTheory
