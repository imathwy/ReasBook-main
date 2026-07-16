import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part11.Identity

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8: if the datum-side identity transition on the chosen cover of `U`
is already the identity, then transporting it back to the slice sheaf on `C / U` gives exactly
the canonical `overMapPullbackId` comparison. This packages the faithful-descent reduction from
`chosen_cover_transport_transition_id_reduction` into a reusable one-line bridge. -/
theorem chosen_cover_transport_transition_id_of_descent_identity
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C)
    (hidentity :
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U)).hom =
        (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).map
          ((J.overMapPullbackId (Type (max u v)) U).app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U)).hom) :
    chosen_cover_transport_transition
        (𝒮 := 𝒮) hGerbe hAbelian (f := 𝟙 U)
        (chosen_cover_descent_transition_iso
          (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U)) =
      (J.overMapPullbackId (Type (max u v)) U).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U) := by
  haveI : (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)).faithful
  apply Iso.ext
  apply Functor.map_injective (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U)
  rw [chosen_cover_transport_transition_functor_map]
  exact hidentity

/-- Helper for Lemma 8.11.8: the transported cocycle law on slice sheaves can be checked after
applying the chosen-cover descent functor on `C / W`. This isolates the remaining composition
blocker to one descent-data equality, without reopening the outer transport shell. -/
theorem chosen_cover_transport_transition_comp_reduction
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (J.overMapPullbackComp (Type (max u v)) g f).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U) ≪≫
      chosen_cover_transport_transition
        (𝒮 := 𝒮) hGerbe hAbelian (f := g ≫ f)
        (chosen_cover_descent_transition_iso
          (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f)) =
      (J.overMapPullback (Type (max u v)) g).mapIso
        (chosen_cover_transport_transition
          (𝒮 := 𝒮) hGerbe hAbelian (f := f)
          (chosen_cover_descent_transition_iso
            (𝒮 := 𝒮) hGerbe hAbelian f)) ≪≫
        chosen_cover_transport_transition
          (𝒮 := 𝒮) hGerbe hAbelian (f := g)
          (chosen_cover_descent_transition_iso
            (𝒮 := 𝒮) hGerbe hAbelian g) ↔
    (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
        (((J.overMapPullbackComp (Type (max u v)) g f).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U) ≪≫
          chosen_cover_transport_transition
            (𝒮 := 𝒮) hGerbe hAbelian (f := g ≫ f)
            (chosen_cover_descent_transition_iso
              (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f))).hom) =
      (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
        (((J.overMapPullback (Type (max u v)) g).mapIso
          (chosen_cover_transport_transition
            (𝒮 := 𝒮) hGerbe hAbelian (f := f)
            (chosen_cover_descent_transition_iso
              (𝒮 := 𝒮) hGerbe hAbelian f)) ≪≫
          chosen_cover_transport_transition
            (𝒮 := 𝒮) hGerbe hAbelian (f := g)
            (chosen_cover_descent_transition_iso
              (𝒮 := 𝒮) hGerbe hAbelian g)).hom) := by
  haveI : (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W)).faithful
  constructor
  · intro h
    exact congrArg
      (fun e ↦ (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map e.hom) h
  · intro h
    apply Iso.ext
    exact Functor.map_injective (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W) h

end CategoryTheory
