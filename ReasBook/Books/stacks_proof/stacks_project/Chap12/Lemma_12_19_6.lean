import stacks_proof.stacks_project.Chap12.Definition_12_19_3
import Mathlib.Tactic.StacksAttribute

open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasImages 𝒜] [HasPullbacks 𝒜]
  [HasBinaryBiproducts 𝒜] [Balanced 𝒜]

namespace FilteredObject.Hom

open FilteredObject

variable {X Y Z : FilteredObject 𝒜}

/-!
Source/core/bridge triage for Lemma 12.19.6:
- source-facing statement: strictness of the filtered biproduct descent map
- core owner API: `FilteredObject.Hom.Strict` and
  `FilteredObject.Hom.strict_iff_quotient_eq_inf`
- bridge objects: the canonical descent `biprod.desc f g` and the stagewise image subobjects
- governing idea from the source proof: compare the image of the biproduct-stage arrow with the
  target filtration stage, using the left summand for the lower bound and filtration preservation
  for the upper bound
-/

/-- Helper for Lemma 12.19.6: if the left summand map is epi, then the induced biproduct descent
is epi on the underlying object map. -/
theorem biprod_desc_hom_epi (f : X ⟶ Z) (g : Y ⟶ Z) [Epi f.hom] :
    Epi (biprod.desc f g).hom := by
  -- The descent map factors the known epi `f.hom` through the left biproduct inclusion.
  have hinl : (biprod.inl : X ⟶ X ⊞ Y).hom ≫ (biprod.desc f g).hom = f.hom := by
    exact congrArg FilteredObject.Hom.hom (biprod.inl_desc f g)
  exact epi_of_epi_fac hinl

/-- Helper for Lemma 12.19.6: a strict epi identifies each target filtration stage with the image
of the corresponding source stage. -/
theorem strict_stage_eq_image_of_epi (f : X ⟶ Z) [Epi f.hom] (hf : Strict f) (i : ℤ) :
    Z.filtration i = imageSubobject ((X.filtration i).arrow ≫ f.hom) := by
  -- For an epi, the infimum term in the strictness criterion collapses to the stage itself.
  simpa [DecreasingFiltration.quotient_eq_imageSubobject_comp,
    Limits.imageSubobject_eq_top_of_epi f.hom] using
    (((strict_iff_quotient_eq_inf f).1 hf i).symm)

/-- Helper for Lemma 12.19.6: the image coming from the left summand stage maps into the image of
the biproduct-stage arrow under the descent map. -/
theorem left_stage_image_le_biprod_desc_stage_image (f : X ⟶ Z) (g : Y ⟶ Z) (i : ℤ) :
    imageSubobject ((X.filtration i).arrow ≫ f.hom) ≤
      imageSubobject (((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom) := by
  -- The left stage factors through the biproduct stage because `biprod.inl` preserves filtrations.
  have hstage :
      ((X ⊞ Y).filtration i).Factors
        ((X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom) := by
    simpa using (biprod.inl : X ⟶ X ⊞ Y).preserves i
  let α :=
    ((X ⊞ Y).filtration i).factorThru
      ((X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom) hstage
  have hα :
      α ≫ ((X ⊞ Y).filtration i).arrow =
        (X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom := by
    simpa [α] using
      Subobject.factorThru_arrow ((X ⊞ Y).filtration i)
        ((X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom) hstage
  have hinl : (biprod.inl : X ⟶ X ⊞ Y).hom ≫ (biprod.desc f g).hom = f.hom := by
    exact congrArg FilteredObject.Hom.hom (biprod.inl_desc f g)
  have hcomp :
      (X.filtration i).arrow ≫ f.hom =
        α ≫ ((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom := by
    -- Rewrite the source-stage composite through the left inclusion and then through its factor.
    calc
      (X.filtration i).arrow ≫ f.hom =
          (X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom ≫ (biprod.desc f g).hom := by
            simpa [Category.assoc] using
              (congrArg (fun t ↦ (X.filtration i).arrow ≫ t) hinl).symm
      _ = (α ≫ ((X ⊞ Y).filtration i).arrow) ≫ (biprod.desc f g).hom := by
            simpa [hα]
      _ = α ≫ ((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom := by
            simp [Category.assoc]
  -- Taking images now gives the desired lower bound by functoriality of image subobjects.
  calc
    imageSubobject ((X.filtration i).arrow ≫ f.hom) =
        imageSubobject (α ≫ ((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom) := by
          simpa [hcomp]
    _ ≤ imageSubobject (((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom) := by
          simpa [Category.assoc] using
            (imageSubobject_comp_le α
              (((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom))

-- Route correction: the earlier proof imported the later file `Lemma_12_19_7` only to use the
-- epi-side strictness reformulation. This proof keeps the same mathematics but works directly from
-- `strict_iff_quotient_eq_inf`, so it stays within the owner API for this earlier item.
/-- Lemma 12.19.6: if `f : X ⟶ Z` is a strict epimorphism of filtered objects and `g : Y ⟶ Z` is
any filtered morphism, then the induced morphism `X ⊞ Y ⟶ Z` is again strict. -/
@[stacks 05SL]
theorem strict_biprodDesc (f : X ⟶ Z) (g : Y ⟶ Z) [Epi f.hom] (hf : Strict f) :
    Strict (biprod.desc f g) := by
  letI : Epi (biprod.desc f g).hom := biprod_desc_hom_epi f g
  refine (strict_iff_quotient_eq_inf (biprod.desc f g)).2 ?_
  intro i
  -- The quotient filtration is the image of the stage arrow, and epi strictness removes the infimum.
  rw [DecreasingFiltration.quotient_eq_imageSubobject_comp,
    Limits.imageSubobject_eq_top_of_epi (biprod.desc f g).hom, top_inf_eq]
  refine le_antisymm ?_ ?_
  · -- The descent map preserves filtration stages, so its stage image lands in the target stage.
    simpa using
      imageSubobject_le _ _ (Subobject.factorThru_arrow _ _ ((biprod.desc f g).preserves i))
  · -- The left summand already covers the target stage because `f` is a strict epi.
    calc
      Z.filtration i = imageSubobject ((X.filtration i).arrow ≫ f.hom) :=
        strict_stage_eq_image_of_epi f hf i
      _ ≤ imageSubobject (((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom) :=
        left_stage_image_le_biprod_desc_stage_image f g i

end FilteredObject.Hom

end CategoryTheory
