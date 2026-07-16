import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part11.CompositionLocalObjectCore
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part11.TransitionComponentRaw

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8: the local-object comparison transports the composite
pullback source shell to the source shell obtained by first transporting the `f`-transition and
then pulling along `I.f`, after one further pullback. -/
private theorem chosen_cover_pullback_to_local_object_iso_transport_transition_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
      (((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
          ((J.overMapPullbackComp (Type (max u v)) g f).hom.app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U)) ≫
        ((J.overMapPullbackComp (Type (max u v)) I.f (g ≫ f)).hom.app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)) ≫
        (chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g ≫ f)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom) =
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
      (((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
          (((J.overMapPullback (Type (max u v)) g).mapIso
            (chosen_cover_transport_transition
              (𝒮 := 𝒮) hGerbe hAbelian (f := f)
              (chosen_cover_descent_transition_iso
                (𝒮 := 𝒮) hGerbe hAbelian f))).hom) ≫
        ((J.overMapPullbackComp (Type (max u v)) I.f g).hom.app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian V)) ≫
    (chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom) := by
  let FK := ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor
  exact congrArg FK.map
    (chosen_cover_pullback_to_local_object_iso_transport_transition_component_core
      (𝒮 := 𝒮) hGerbe hAbelian f g I)

/-- Helper for Lemma 8.11.8: the component form of the varying-`U` cocycle source shell.  After
faithful descent on the chosen cover of `I.Y`, the cocycle adapter is exactly this equality after
pulling both composite/local-object shells by one further chosen-cover arrow `K.f`. -/
private theorem chosen_cover_descent_transition_component_comp_source_shell_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
            ((J.overMapPullbackComp (Type (max u v)) g f).hom.app
              (chosen_cover_underlying_automorphism_sheaf
                (𝒮 := 𝒮) hGerbe hAbelian U)) ≫
          (chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f) I).hom ≫
            (chosen_cover_pullback_to_local_object_iso
              (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g ≫ f)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom) =
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
            (((J.overMapPullback (Type (max u v)) g).mapIso
              (chosen_cover_transport_transition
                (𝒮 := 𝒮) hGerbe hAbelian (f := f)
                (chosen_cover_descent_transition_iso
                  (𝒮 := 𝒮) hGerbe hAbelian f))).hom) ≫
          (chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian g I).hom ≫
              (chosen_cover_pullback_to_local_object_iso
                (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom) := by
  -- Expand both pulled composites on the fixed `K`-component, then replace the terminal
  -- local-object comparisons by the mixed-cover component normal form.
  simp only [Functor.map_comp]
  rw [← chosen_cover_pullback_to_local_object_component_iso_hom
      (𝒮 := 𝒮) hGerbe hAbelian
      (q := I.f ≫ g ≫ f)
      (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I) K]
  rw [← mixed_cover_secondary_cover_component_iso_eq_pullback_component
      (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f) I K]
  rw [← chosen_cover_pullback_to_local_object_component_iso_hom
      (𝒮 := 𝒮) hGerbe hAbelian
      (q := I.f ≫ g)
      (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I) K]
  rw [← mixed_cover_secondary_cover_component_iso_eq_pullback_component
      (𝒮 := 𝒮) hGerbe hAbelian g I K]
  -- The exposed source shells are the new transport-transition comparison, after rewriting the
  -- mixed-cover components back to the generic local-object comparison.
  simpa [chosen_cover_pulled_component_composite_pullback_iso,
    mixed_cover_secondary_cover_component_iso_eq_pullback_component,
    chosen_cover_pullback_to_local_object_component_iso_hom, Functor.map_comp,
    Category.assoc] using
    chosen_cover_pullback_to_local_object_iso_transport_transition_component
      (𝒮 := 𝒮) hGerbe hAbelian f g I K

/-- Helper for Lemma 8.11.8: the cocycle source-shell comparison before the final fixed
chosen-cover counit for `W` is appended.  This is the exact point where varying-`U`
compatibility has to identify the composite pullback shell with the pullback of the transported
`f`-transition. -/
private theorem chosen_cover_descent_transition_component_comp_before_cover_inv
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
        ((J.overMapPullbackComp (Type (max u v)) g f).hom.app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)) ≫
      (chosen_cover_pulled_component_composite_pullback_iso
        (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f) I).hom ≫
      (chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g ≫ f)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom =
    ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
        (((J.overMapPullback (Type (max u v)) g).mapIso
          (chosen_cover_transport_transition
            (𝒮 := 𝒮) hGerbe hAbelian (f := f)
            (chosen_cover_descent_transition_iso
              (𝒮 := 𝒮) hGerbe hAbelian f))).hom) ≫
      (chosen_cover_pulled_component_composite_pullback_iso
        (𝒮 := 𝒮) hGerbe hAbelian g I).hom ≫
      (chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom := by
  -- Reduce the varying-`U` source-shell cocycle to one component after both local-object
  -- comparison shells have been exposed.
  let S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y
  haveI : (localizedSheafToCoverDescentEquivalence (J := J) S).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J) S).faithful
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J) S).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  simp only [localizedSheafToCoverDescentEquivalence_functor_map_component]
  -- The remaining target is the named `K.f`-pulled component comparison.
  exact chosen_cover_descent_transition_component_comp_source_shell_component
    (𝒮 := 𝒮) hGerbe hAbelian f g I K

/-- Helper for Lemma 8.11.8: the raw chosen-cover component form of the cocycle
`ρ_{g ≫ f} = g^*ρ_f · ρ_g`.  Both sides have the fixed chosen-cover counit for `W` exposed; the
remaining content is the source-faithful comparison between the composite pullback shell and the
pullback of the transported `f`-transition. -/
private theorem chosen_cover_descent_transition_component_comp_raw_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
        ((J.overMapPullbackComp (Type (max u v)) g f).hom.app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)) ≫
      (chosen_cover_pulled_component_composite_pullback_iso
        (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f) I).hom ≫
      (chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g ≫ f)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom ≫
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian W I).inv =
    ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
        (((J.overMapPullback (Type (max u v)) g).mapIso
          (chosen_cover_transport_transition
            (𝒮 := 𝒮) hGerbe hAbelian (f := f)
            (chosen_cover_descent_transition_iso
              (𝒮 := 𝒮) hGerbe hAbelian f))).hom) ≫
      (chosen_cover_pulled_component_composite_pullback_iso
        (𝒮 := 𝒮) hGerbe hAbelian g I).hom ≫
      (chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom ≫
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian W I).inv := by
  slice_lhs 1 3 =>
    rw [chosen_cover_descent_transition_component_comp_before_cover_inv
      (𝒮 := 𝒮) hGerbe hAbelian f g I]
  rfl

/-- Helper for Lemma 8.11.8: the transition cocycle after applying the chosen-cover descent
functor, reduced to a single chosen-cover component of `W`. This is the component form of the
source identity `ρ_{g ≫ f} = g^*ρ_f · ρ_g` after the `overMapPullbackComp` shell is exposed. -/
private theorem chosen_cover_descent_transition_component_iso_comp_after_functor_map
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow) :
    (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
        (((J.overMapPullbackComp (Type (max u v)) g f).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)).hom)).hom I) ≫
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f)).hom.hom I =
      (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
          (((J.overMapPullback (Type (max u v)) g).mapIso
            (chosen_cover_transport_transition
              (𝒮 := 𝒮) hGerbe hAbelian (f := f)
              (chosen_cover_descent_transition_iso
                (𝒮 := 𝒮) hGerbe hAbelian f))).hom)).hom I) ≫
        (chosen_cover_descent_transition_iso
          (𝒮 := 𝒮) hGerbe hAbelian g).hom.hom I := by
  -- DEFERRED (§5.4 component cocycle): this is the source transition composition law on one
  -- chosen-cover component. Proving it requires the same normalized component comparison data as
  -- the §5.2 square, plus the `overMapPullbackComp` coherence for the outer shell.
  simp [chosen_cover_descent_transition_iso, chosen_cover_descent_functor]
  rw [chosen_cover_descent_transition_component_iso_hom_raw]
  rw [chosen_cover_descent_transition_component_iso_hom_raw]
  exact chosen_cover_descent_transition_component_comp_raw_normalized
    (𝒮 := 𝒮) hGerbe hAbelian f g I

/-- Helper for Lemma 8.11.8: after the three
`chosen_cover_transport_transition_functor_map` rewrites in the composition branch, the remaining
descent-data equality is exactly the pullback-composition comparison on the chosen cover of `W`.
This isolates the final cocycle normalization away from the sheaf-side transport shell. -/
theorem chosen_cover_transport_transition_comp_after_functor_map
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
        (((J.overMapPullbackComp (Type (max u v)) g f).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)).hom) ≫
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f)).hom =
      (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W).map
          (((J.overMapPullback (Type (max u v)) g).mapIso
            (chosen_cover_transport_transition
              (𝒮 := 𝒮) hGerbe hAbelian (f := f)
              (chosen_cover_descent_transition_iso
                (𝒮 := 𝒮) hGerbe hAbelian f))).hom) ≫
        (chosen_cover_descent_transition_iso
          (𝒮 := 𝒮) hGerbe hAbelian g).hom := by
  -- The outer descent-data equation is faithful componentwise; the remaining source content is
  -- now the component cocycle isolated above.
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  simpa only [Pseudofunctor.DescentData.comp_hom] using
    chosen_cover_descent_transition_component_iso_comp_after_functor_map
      (𝒮 := 𝒮) hGerbe hAbelian f g I

end CategoryTheory
