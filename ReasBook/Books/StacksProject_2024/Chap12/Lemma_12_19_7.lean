import stacks_project.Chap12.Definition_12_19_3

open CategoryTheory
open CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory
namespace FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C]
variable {A B : FilteredObject C} (f : A ⟶ B)

-- Proof sketch: pull back the stagewise strictness identity along the monomorphism `f.hom`.
-- Because pullback along a mono inverts the forward-map functor on subobjects, the left side
-- becomes the source filtration stage; the right side becomes the pullback of the target stage.
/-- Lemma 12.19.7 (1): for an injective morphism of filtered objects, strictness is equivalent to
the source filtration agreeing stagewise with the induced filtration. We keep the right-hand side
on `A.obj`, so it is written in the pullback form underlying `DecreasingFiltration.induced`. -/
theorem strict_iff_induced_filtration_of_mono [Mono f.hom] :
    Strict f ↔
      A.filtration = (Subobject.pullback f.hom).toOrderHom.comp B.filtration := by
  constructor
  · intro hf
    refine OrderHom.ext _ _ ?_
    funext i
    have hi := congrArg ((Subobject.pullback f.hom).obj) ((strict_iff_quotient_eq_inf f).1 hf i)
    simpa [DecreasingFiltration.quotient, Subobject.exists_iso_map,
      Limits.imageSubobject_mono, Subobject.inf_pullback, Subobject.pullback_self] using hi
  · intro h
    refine (strict_iff_quotient_eq_inf f).2 ?_
    intro i
    have hi := congrArg (fun F ↦ F i) h
    calc
      A.filtration.quotient f.hom i
          = (Subobject.map f.hom).obj ((Subobject.pullback f.hom).obj (B.filtration i)) := by
              simpa [DecreasingFiltration.quotient, Subobject.exists_iso_map] using
                congrArg ((Subobject.«exists» f.hom).obj) hi
      _ = Limits.imageSubobject f.hom ⊓ B.filtration i := by
              simpa [Subobject.inf_def, Limits.imageSubobject_mono] using
                (Subobject.inf_eq_map_pullback' (MonoOver.mk f.hom) (B.filtration i)).symm

-- Proof sketch: when `f.hom` is epi, `imageSubobject f.hom = ⊤`, so the stagewise strictness
-- equality becomes the statement that each target filtration stage is the image of the
-- corresponding source filtration stage under `f.hom`.
/-- Lemma 12.19.7 (2): for a surjective morphism of filtered objects, strictness is equivalent to
the target filtration agreeing stagewise with the quotient filtration. -/
theorem strict_iff_quotient_filtration_of_epi [Balanced C] [Epi f.hom] :
    Strict f ↔ B.filtration = A.filtration.quotient f.hom :=
  by
    constructor
    · intro hf
      refine OrderHom.ext _ _ ?_
      funext i
      simpa [Limits.imageSubobject_eq_top_of_epi f.hom] using
        ((strict_iff_quotient_eq_inf f).1 hf i).symm
    · intro h
      refine (strict_iff_quotient_eq_inf f).2 ?_
      intro i
      have hi := congrArg (fun F ↦ F i) h
      simpa [Limits.imageSubobject_eq_top_of_epi f.hom] using hi.symm

end FilteredObject.Hom
end CategoryTheory
