import StacksProject_2024.Chap08.Lemma_8_11_8.Part11.TransportTransitionReductions

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Sheaf-level normal form for the remaining varying-`U` local-object transport paste.

This is the narrow core left after removing all fixed-cover/refinement functoriality: it compares
the composite pullback shell followed by the local-object comparison over `I.Y` with the route
that first transports the `f`-transition and then applies the `g`-side local-object comparison. -/
theorem chosen_cover_pullback_to_local_object_iso_transport_transition_base_nf_deferred
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow) :
    let P := J.pseudofunctorOver (Type (max u v))
    let AU := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
    let AV := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian V
    let τ := chosen_cover_transport_transition
      (𝒮 := 𝒮) hGerbe hAbelian (f := f)
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian f)
    let y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I
    let FI := (P.map I.f.op.toLoc).toFunctor
    let aI := FI.map (((J.overMapPullback (Type (max u v)) g).mapIso τ).hom)
    let bI := ((J.overMapPullbackComp (Type (max u v)) I.f g).hom.app AV)
    FI.map ((J.overMapPullbackComp (Type (max u v)) g f).hom.app AU) ≫
      ((J.overMapPullbackComp (Type (max u v)) I.f (g ≫ f)).hom.app AU) ≫
      (chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g ≫ f) y).hom =
    aI ≫ bI ≫
      (chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g) y).hom := by
  intro P AU AV τ y FI aI bI
  -- NARROW DEFERRED (§5.4 sheaf-level varying-`U` normal form): this is the
  -- core naturality/associativity paste before any fixed-cover or refinement functors are
  -- applied.  Proving it should use the `chosen_cover_transport_transition` component normal form
  -- and the two `overMapPullbackComp` shells, without reopening downstream mixed-cover data.
  sorry

/-- Small adapter for the remaining varying-`U` local-object transport paste.

The common-refinement membership data is intentionally not part of this interface: the remaining
calculation only uses the final restriction arrow `r : R₀ ⟶ K.Y`.  This keeps the blocker focused
on the associativity/naturality paste between the two `overMapPullbackComp` shells and the
pullback-to-local-object comparison. -/
theorem chosen_cover_pullback_to_local_object_iso_transport_transition_component_refined_deferred
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow)
    {R₀ : C} (r : R₀ ⟶ K.Y) :
    let P := J.pseudofunctorOver (Type (max u v))
    let AU := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
    let AV := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian V
    let τ := chosen_cover_transport_transition
      (𝒮 := 𝒮) hGerbe hAbelian (f := f)
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian f)
    let FI := (P.map I.f.op.toLoc).toFunctor
    let FK := (P.map K.f.op.toLoc).toFunctor
    let FR := (P.map r.op.toLoc).toFunctor
    let aR := FI.map (((J.overMapPullback (Type (max u v)) g).mapIso τ).hom)
    let bR := ((J.overMapPullbackComp (Type (max u v)) I.f g).hom.app AV)
    FR.map (FK.map (FI.map
        ((J.overMapPullbackComp (Type (max u v)) g f).hom.app AU))) ≫
      FR.map (FK.map
        ((J.overMapPullbackComp (Type (max u v)) I.f (g ≫ f)).hom.app AU)) ≫
      FR.map (FK.map ((chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g ≫ f)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom)) =
    FR.map (FK.map aR ≫ FK.map bR ≫
      FK.map ((chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom)) := by
  intro P AU AV τ FI FK FR aR bR
  simpa [P, AU, AV, τ, FI, FK, FR, aR, bR, Functor.map_comp, Category.assoc] using
    congrArg (fun m => FR.map (FK.map m))
      (chosen_cover_pullback_to_local_object_iso_transport_transition_base_nf_deferred
        (𝒮 := 𝒮) hGerbe hAbelian f g I)

/-- Mixed-cover wrapper for the remaining varying-`U` local-object transport paste.

This is the narrow interface between the mixed-cover component normal form and the sheaf-level
refined adapter above.  It only needs the final restriction arrow `r : R₀ ⟶ K.Y`; membership in
the common-refinement cover stays in the caller.  It keeps the dependent rewriting of the two
`mixed_cover_secondary_cover_component_iso` terms out of `CompositionLocalObjectCore`. -/
theorem chosen_cover_pullback_to_local_object_iso_transport_transition_component_refined_mixed_deferred
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow)
    {R₀ : C} (r : R₀ ⟶ K.Y) :
    let P := J.pseudofunctorOver (Type (max u v))
    let AU := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
    let AV := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian V
    let τ := chosen_cover_transport_transition
      (𝒮 := 𝒮) hGerbe hAbelian (f := f)
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian f)
    let FI := (P.map I.f.op.toLoc).toFunctor
    let FK := (P.map K.f.op.toLoc).toFunctor
    let FR := (P.map r.op.toLoc).toFunctor
    let aR := FI.map (((J.overMapPullback (Type (max u v)) g).mapIso τ).hom)
    let bR := ((J.overMapPullbackComp (Type (max u v)) I.f g).hom.app AV)
    FR.map (FK.map (FI.map
        ((J.overMapPullbackComp (Type (max u v)) g f).hom.app AU))) ≫
      FR.map (FK.map
        ((J.overMapPullbackComp (Type (max u v)) I.f (g ≫ f)).hom.app AU)) ≫
      FR.map ((mixed_cover_secondary_cover_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f) I K).hom) =
    FR.map (FK.map aR ≫ FK.map bR ≫
      (mixed_cover_secondary_cover_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian g I K).hom) := by
  intro P AU AV τ FI FK FR aR bR
  -- NARROW DEFERRED (§5.4 mixed-cover wrapper): reduce both mixed-cover components to the
  -- pullback-to-local-object normal form, then apply the refined sheaf-level adapter.
  sorry

end CategoryTheory
