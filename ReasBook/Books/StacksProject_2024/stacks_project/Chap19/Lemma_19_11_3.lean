import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Limits

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C}

/-- Pushing forward the pullback of a subobject along an epimorphism recovers the original
subobject. -/
lemma exists_pullback_eq_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (P : Subobject Y) :
    (Subobject.exists f).obj ((Subobject.pullback f).obj P) = P := by
  have hImage : imageSubobject (((Subobject.pullback f).obj P).arrow ≫ f) = P := by
    rw [← (Subobject.isPullback f P).w]
    haveI : Epi (Subobject.pullbackπ f P) :=
      Abelian.epi_fst_of_isLimit P.arrow f (Subobject.isPullback f P).isLimit
    have hle :
        imageSubobject (Subobject.pullbackπ f P ≫ P.arrow) ≤ imageSubobject P.arrow :=
      imageSubobject_comp_le (Subobject.pullbackπ f P) P.arrow
    haveI : Epi (Subobject.ofLE _ _ hle) :=
      imageSubobject_comp_le_epi_of_epi (Subobject.pullbackπ f P) P.arrow
    haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi (Subobject.ofLE _ _ hle)
    have hEq :
        imageSubobject (Subobject.pullbackπ f P ≫ P.arrow) = imageSubobject P.arrow :=
      Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) (by simp)
    simpa [imageSubobject_mono] using hEq
  apply Subobject.eq_of_comm
    (Subobject.existsIsoImage f ((Subobject.pullback f).obj P) ≪≫
      (imageSubobjectIso _).symm ≪≫
      Subobject.isoOfEq _ _ hImage)
  calc
    ((Subobject.existsIsoImage f ((Subobject.pullback f).obj P)).hom ≫
        (imageSubobjectIso (((Subobject.pullback f).obj P).arrow ≫ f)).inv ≫
        (Subobject.isoOfEq _ _ hImage).hom) ≫
        P.arrow
        = (Subobject.existsIsoImage f ((Subobject.pullback f).obj P)).hom ≫
            image.ι (((Subobject.pullback f).obj P).arrow ≫ f) := by
              simp [Category.assoc]
    _ = ((Subobject.exists f).obj ((Subobject.pullback f).obj P)).arrow := by
          simpa [MonoOver.exists] using
            Over.w ((Subobject.existsCompRepresentativeIso f).app
              ((Subobject.pullback f).obj P)).hom.hom

/-- Lemma 19.11.3 (1): in a short exact sequence in an abelian category,
`#(Subobject M') ≤ #(Subobject M)`. -/
-- Proof sketch: a subobject of `M'` is also a subobject of `M` by composing with the mono
-- `M' ⟶ M`, giving an injection `Subobject M' ↪ Subobject M` and hence the desired cardinal
-- inequality.
lemma subobject_cardinal_subobject_le_of_shortExact (hS : S.ShortExact) :
    Cardinal.mk (Subobject S.X₁) ≤ Cardinal.mk (Subobject S.X₂) := by
  letI := hS.mono_f
  exact Cardinal.mk_le_of_injective (Subobject.map_obj_injective S.f)

/-- Lemma 19.11.3 (2): in a short exact sequence in an abelian category,
`#(Subobject M'') ≤ #(Subobject M)`. -/
-- Proof sketch: pull back subobjects of `M''` along the epimorphism `M ⟶ M''`; this gives an
-- injection `Subobject M'' ↪ Subobject M`, so the cardinality of `Subobject M''` is bounded by
-- that of `Subobject M`.
lemma subobject_cardinal_quotient_le_of_shortExact (hS : S.ShortExact) :
    Cardinal.mk (Subobject S.X₃) ≤ Cardinal.mk (Subobject S.X₂) := by
  letI := hS.epi_g
  have hleft :
      Function.LeftInverse (Subobject.exists S.g).obj (Subobject.pullback S.g).obj :=
    fun A ↦ exists_pullback_eq_of_epi S.g A
  exact Cardinal.mk_le_of_injective hleft.injective

end CategoryTheory
