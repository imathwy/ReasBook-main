import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Limits

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C}

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
  let pull : Subobject S.X₃ → Subobject S.X₂ := fun A ↦ (Subobject.pullback S.g).obj A
  have h_pullback : Function.Injective pull := by
    change ∀ A B, pull A = pull B → A = B
    intro A B hAB
    have h_exists_pullback (A : Subobject S.X₃) :
        (Subobject.exists S.g).obj (pull A) = A := by
      have hImage : imageSubobject ((pull A).arrow ≫ S.g) = A := by
        rw [← (Subobject.isPullback S.g A).w]
        haveI : Epi (Subobject.pullbackπ S.g A) :=
          Abelian.epi_fst_of_isLimit A.arrow S.g (Subobject.isPullback S.g A).isLimit
        have hle :
            imageSubobject (Subobject.pullbackπ S.g A ≫ A.arrow) ≤ imageSubobject A.arrow :=
          imageSubobject_comp_le (Subobject.pullbackπ S.g A) A.arrow
        haveI : Epi (Subobject.ofLE _ _ hle) :=
          imageSubobject_comp_le_epi_of_epi (Subobject.pullbackπ S.g A) A.arrow
        haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi (Subobject.ofLE _ _ hle)
        have hEq :
            imageSubobject (Subobject.pullbackπ S.g A ≫ A.arrow) = imageSubobject A.arrow :=
          Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) (by simp)
        simpa [imageSubobject_mono] using hEq
      apply Subobject.eq_of_comm
        (Subobject.existsIsoImage S.g (pull A) ≪≫
          (imageSubobjectIso _).symm ≪≫
            Subobject.isoOfEq _ _ hImage)
      calc
        ((Subobject.existsIsoImage S.g (pull A)).hom ≫
            (imageSubobjectIso ((pull A).arrow ≫ S.g)).inv ≫
            (Subobject.isoOfEq _ _ hImage).hom) ≫
            A.arrow
            = (Subobject.existsIsoImage S.g (pull A)).hom ≫
                image.ι ((pull A).arrow ≫ S.g) := by
                  simp [Category.assoc]
        _ = ((Subobject.exists S.g).obj (pull A)).arrow := by
              simpa [MonoOver.exists] using
                Over.w ((Subobject.existsCompRepresentativeIso S.g).app (pull A)).hom.hom
    calc
      A = (Subobject.exists S.g).obj (pull A) :=
        (h_exists_pullback A).symm
      _ = (Subobject.exists S.g).obj (pull B) := by simp [hAB]
      _ = B := h_exists_pullback B
  exact Cardinal.mk_le_of_injective h_pullback

end CategoryTheory
