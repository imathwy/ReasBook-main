import StacksProject_2024.Chap12.Definition_12_19_3

open CategoryTheory
open CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasImages 𝒜] [HasPullbacks 𝒜]
  [HasBinaryBiproducts 𝒜]

namespace FilteredObject.Hom

open FilteredObject

variable {A B C : FilteredObject 𝒜}

/- 
Source/core/bridge triage for Lemma 12.19.5:
- source-facing: strictness of the filtered biproduct lift attached to a strict monomorphism
- core/canonical owner: `FilteredObject.Hom.strict_iff_quotient_eq_inf`
- bridge/view: compare the source filtration with the pullback filtration along `biprod.lift f g`
-/

/-- Helper for Lemma 12.19.5: the underlying lift to the biproduct has left component `f`. -/
private theorem biprod_lift_hom_comp_fst (f : A ⟶ B) (g : A ⟶ C) :
    (biprod.lift f g).hom ≫ ((biprod.fst : (B ⊞ C : FilteredObject 𝒜) ⟶ B).hom) = f.hom := by
  -- Read the filtered biproduct identity on underlying morphisms.
  exact congrArg (fun k => k.hom) (biprod.lift_fst f g)

/-- Helper for Lemma 12.19.5: a strict monomorphism identifies the source filtration with the
pullback of the target filtration. -/
private theorem filtration_eq_pullback_of_strict_mono {X Y : FilteredObject 𝒜} (h : X ⟶ Y)
    [Mono h.hom] (hh : Strict h) :
    X.filtration = (Subobject.pullback h.hom).toOrderHom.comp Y.filtration := by
  refine OrderHom.ext _ _ ?_
  funext i
  -- Pull back the stagewise strictness identity along the monomorphism.
  have hi := congrArg ((Subobject.pullback h.hom).obj) ((strict_iff_quotient_eq_inf h).1 hh i)
  -- For a mono, pulling back the image recovers the original stage and distributes over `⊓`.
  simpa [DecreasingFiltration.quotient, Subobject.exists_iso_map, Limits.imageSubobject_mono,
    Subobject.inf_pullback, Subobject.pullback_self] using hi

/-- Helper for Lemma 12.19.5: for a monomorphism, equality with the pullback filtration implies
strictness. -/
private theorem strict_of_filtration_eq_pullback_mono {X Y : FilteredObject 𝒜} (h : X ⟶ Y)
    [Mono h.hom]
    (hh : X.filtration = (Subobject.pullback h.hom).toOrderHom.comp Y.filtration) :
    Strict h := by
  refine (strict_iff_quotient_eq_inf h).2 ?_
  intro i
  -- Evaluate the pullback-filtration equality at stage `i`.
  have hi := congrArg (fun F ↦ F i) hh
  calc
    X.filtration.quotient h.hom i
        = (Subobject.map h.hom).obj ((Subobject.pullback h.hom).obj (Y.filtration i)) := by
            -- Rewrite the quotient stage using the induced pullback description.
            simpa [DecreasingFiltration.quotient, Subobject.exists_iso_map] using
              congrArg ((Subobject.«exists» h.hom).obj) hi
    _ = Limits.imageSubobject h.hom ⊓ Y.filtration i := by
          -- Mapping a pullback stage along a mono gives the expected intersection.
          simpa [Subobject.inf_def, Limits.imageSubobject_mono] using
            (Subobject.inf_eq_map_pullback' (MonoOver.mk h.hom) (Y.filtration i)).symm

/-- Helper for Lemma 12.19.5: the filtration induced on `A` by `biprod.lift f g` is computed from
the left projection, hence agrees with the original filtration when `f` is strict mono. -/
private theorem biprod_lift_filtration_eq_pullback (f : A ⟶ B) (g : A ⟶ C)
    [Mono f.hom] (hf : Strict f) :
    A.filtration =
      (Subobject.pullback (biprod.lift f g).hom).toOrderHom.comp
        ((B ⊞ C : FilteredObject 𝒜).filtration) := by
  refine OrderHom.ext _ _ ?_
  funext i
  -- The easy direction is just filtration preservation of the biproduct lift.
  refine le_antisymm ?_ ?_
  · refine Subobject.le_of_factors ?_
    exact Limits.pullback_factors (biprod.lift f g).hom
      (((B ⊞ C : FilteredObject 𝒜)).filtration i) (A.filtration i).arrow
      ((biprod.lift f g).preserves i)
  · -- Route correction: instead of importing the later mono criterion, compute the pullback stage
    -- through `biprod.fst` and then substitute the strictness-induced pullback identity for `f`.
    have hstage :
        ((B ⊞ C : FilteredObject 𝒜)).filtration i ≤
          (Subobject.pullback ((biprod.fst : (B ⊞ C : FilteredObject 𝒜) ⟶ B).hom)).obj
            (B.filtration i) := by
      refine Subobject.le_of_factors ?_
      exact Limits.pullback_factors ((biprod.fst : (B ⊞ C : FilteredObject 𝒜) ⟶ B).hom)
        (B.filtration i) (((B ⊞ C : FilteredObject 𝒜)).filtration i).arrow
        ((biprod.fst : (B ⊞ C : FilteredObject 𝒜) ⟶ B).preserves i)
    have hf_stage :
        (Subobject.pullback f.hom).obj (B.filtration i) = A.filtration i := by
      simpa using (congrArg (fun F ↦ F i) (filtration_eq_pullback_of_strict_mono f hf)).symm
    calc
      (Subobject.pullback (biprod.lift f g).hom).obj
          (((B ⊞ C : FilteredObject 𝒜)).filtration i)
          ≤ (Subobject.pullback (biprod.lift f g).hom).obj
              ((Subobject.pullback ((biprod.fst : (B ⊞ C : FilteredObject 𝒜) ⟶ B).hom)).obj
                (B.filtration i)) :=
            (Subobject.pullback (biprod.lift f g).hom).monotone hstage
      _ = (Subobject.pullback f.hom).obj (B.filtration i) := by
            calc
              (Subobject.pullback (biprod.lift f g).hom).obj
                  ((Subobject.pullback ((biprod.fst : (B ⊞ C : FilteredObject 𝒜) ⟶ B).hom)).obj
                    (B.filtration i))
                  =
                    (Subobject.pullback
                      ((biprod.lift f g).hom ≫
                        ((biprod.fst : (B ⊞ C : FilteredObject 𝒜) ⟶ B).hom))).obj
                      (B.filtration i) := by
                        symm
                        exact Subobject.pullback_comp (biprod.lift f g).hom
                          ((biprod.fst : (B ⊞ C : FilteredObject 𝒜) ⟶ B).hom) (B.filtration i)
              _ = (Subobject.pullback f.hom).obj (B.filtration i) := by
                    rw [biprod_lift_hom_comp_fst]
      _ = A.filtration i := hf_stage

/-- Lemma 12.19.5: if `f : A ⟶ B` is a strict monomorphism of filtered objects and
`g : A ⟶ C` is any filtered morphism, then the induced morphism
`A ⟶ B ⊞ C` is strict. -/
theorem strict_biprodLift (f : A ⟶ B) (g : A ⟶ C) [Mono f.hom] (hf : Strict f) :
    Strict (biprod.lift f g) := by
  letI : Mono (biprod.lift f g).hom := mono_of_mono_fac (biprod_lift_hom_comp_fst f g)
  -- Compute the induced filtration along the lift from the left summand, then invoke the
  -- mono-side strictness criterion re-derived locally above.
  exact strict_of_filtration_eq_pullback_mono (biprod.lift f g)
    (biprod_lift_filtration_eq_pullback f g hf)

end FilteredObject.Hom

end CategoryTheory
