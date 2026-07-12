import StacksProject_2024.Chap12.Aux_12_20_2_1
import StacksProject_2024.Chap12.Definition_12_19_3
import StacksProject_2024.Chap12.Lemma_12_19_7
import StacksProject_2024.Chap12.Lemma_12_9_6

open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredObject

open FilteredObject.Hom

variable (A : FilteredObject C)
variable {X Y : Subobject A.obj}

/-- Helper for Lemma 12.19.9: the induced filtered object on a subobject `X ⊆ A`. -/
def subobjectFilteredObject (X : Subobject A.obj) : FilteredObject C where
  obj := X
  filtration := A.filtration.induced X

/-- Helper for Lemma 12.19.9: the quotient filtered object `A / X`. -/
def quotientFilteredObject (X : Subobject A.obj) : FilteredObject C where
  obj := cokernel X.arrow
  filtration := A.filtration.quotient (cokernel.π X.arrow)

/-- Helper for Lemma 12.19.9: the canonical filtered object representing `Y / X` inside `A / X`.
-/
abbrev subobjectSubquotientFilteredObject (hXY : X ≤ Y) :
    FilteredObject C :=
  (A.quotientFilteredObject X).subobjectFilteredObject (subobjectSubquotientSubobject hXY)

/-- Helper for Lemma 12.19.9: the induced stage on a subobject maps into the ambient stage. -/
private theorem subobjectInclusion_preserves (S : Subobject A.obj) (i : ℤ) :
    (A.filtration i).Factors
      (((A.subobjectFilteredObject S).filtration i).arrow ≫ S.arrow) := by
  rw [show (A.subobjectFilteredObject S).filtration i =
      (Subobject.pullback S.arrow).obj (A.filtration i) by
    rfl]
  exact (pullback_factors_iff S.arrow (A.filtration i)
      (((A.subobjectFilteredObject S).filtration i).arrow)).1
    (Subobject.factors_self ((A.subobjectFilteredObject S).filtration i))

/-- Helper for Lemma 12.19.9: the ambient quotient map `Y ⟶ A / X` factors through the canonical
subquotient `Y / X`. -/
private theorem subobjectSubquotientProjection_condition (hXY : X ≤ Y) :
    (Y.arrow ≫ cokernel.π X.arrow) ≫ subobjectQuotientMap hXY = 0 := by
  simpa [subobjectQuotientMap, Category.assoc] using cokernel.condition Y.arrow

/-- Helper for Lemma 12.19.9: mapping an image subobject along a monomorphism identifies it with
the image of the composite. -/
private theorem imageSubobject_comp_eq_map_of_mono {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    [Mono g] :
    imageSubobject (f ≫ g) = (Subobject.map g).obj (imageSubobject f) := by
  calc
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
      rw [CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction f g]
    _ = Subobject.mk ((imageSubobject f).arrow ≫ g) := by
          simpa using (Limits.imageSubobject_mono ((imageSubobject f).arrow ≫ g))
    _ = (Subobject.map g).obj (Subobject.mk (imageSubobject f).arrow) := by
          rw [Subobject.map_mk]
    _ = (Subobject.map g).obj (imageSubobject f) := by
          rw [Subobject.mk_arrow]

/-- Helper for Lemma 12.19.9: the canonical inclusion of `Y / X` into `A / X` is mono. -/
private instance subobjectSubquotientSubobject_arrow_mono (hXY : X ≤ Y) :
    Mono (subobjectSubquotientSubobject hXY).arrow := by
  change Mono (kernelSubobject (subobjectQuotientMap hXY)).arrow
  infer_instance

/-- Helper for Lemma 12.19.9: the quotient stage maps into the ambient quotient filtration stage.
-/
private theorem subobjectToSubquotient_preserves (hXY : X ≤ Y) (i : ℤ) :
    ((A.subobjectSubquotientFilteredObject hXY).filtration i).Factors
      (((A.subobjectFilteredObject Y).filtration i).arrow ≫
        factorThruKernelSubobject
          (subobjectQuotientMap hXY)
          (Y.arrow ≫ cokernel.π X.arrow)
          (subobjectSubquotientProjection_condition A hXY)) := by
  rw [show (A.subobjectSubquotientFilteredObject hXY).filtration i =
      (Subobject.pullback (subobjectSubquotientSubobject hXY).arrow).obj
        ((A.quotientFilteredObject X).filtration i) by
    rfl]
  let u :=
    (A.filtration i).factorThru
      (((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow)
      (subobjectInclusion_preserves A Y i)
  let k : (A.filtration i : C) ⟶ cokernel X.arrow :=
    (A.filtration i).arrow ≫ cokernel.π X.arrow
  refine
    (pullback_factors_iff (subobjectSubquotientSubobject hXY).arrow
      ((A.quotientFilteredObject X).filtration i)
      (((A.subobjectFilteredObject Y).filtration i).arrow ≫
        factorThruKernelSubobject
          (subobjectQuotientMap hXY)
          (Y.arrow ≫ cokernel.π X.arrow)
          (subobjectSubquotientProjection_condition A hXY))).2 ?_
  rw [show (A.quotientFilteredObject X).filtration i = imageSubobject k by
    simpa [quotientFilteredObject, k] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration
        (cokernel.π X.arrow) i)]
  simpa [u, k, Category.assoc, imageSubobject_arrow_comp,
    subobjectSubquotientProjection_condition] using
    (Subobject.factors_comp_arrow (u ≫ factorThruImageSubobject k))

/-- Helper for Lemma 12.19.9: the canonical filtered map `Y ⟶ Y / X` inside `A / X`. -/
def subobjectToSubquotient (hXY : X ≤ Y) :
    A.subobjectFilteredObject Y ⟶ A.subobjectSubquotientFilteredObject hXY where
  hom :=
    factorThruKernelSubobject
      (subobjectQuotientMap hXY)
      (Y.arrow ≫ cokernel.π X.arrow)
      (subobjectSubquotientProjection_condition A hXY)
  preserves := subobjectToSubquotient_preserves A hXY

/-- Helper for Lemma 12.19.9: the canonical filtered map `Y ⟶ Y / X` followed by the ambient
inclusion into `A / X` is the usual quotient map from `Y`. -/
theorem subobjectToSubquotient_comp_subobjectSubquotientInclusion (hXY : X ≤ Y) :
    (A.subobjectToSubquotient hXY).hom ≫ (subobjectSubquotientSubobject hXY).arrow =
      Y.arrow ≫ cokernel.π X.arrow := by
  change
    factorThruKernelSubobject
      (subobjectQuotientMap hXY)
      (Y.arrow ≫ cokernel.π X.arrow)
      (subobjectSubquotientProjection_condition A hXY) ≫
        (subobjectSubquotientSubobject hXY).arrow =
      Y.arrow ≫ cokernel.π X.arrow
  rw [factorThruKernelSubobject_comp_arrow]

/-- Helper for Lemma 12.19.9: the canonical subquotient map is an epimorphism. -/
private theorem subobjectToSubquotient_epi (hXY : X ≤ Y) :
    Epi (A.subobjectToSubquotient hXY).hom := by
  let e :
      (imageSubobject (Y.arrow ≫ cokernel.π X.arrow) : C) ≅ subobjectSubquotient hXY :=
    Subobject.isoOfEq _ _ (Subobject.image_subobject_toQuotient_eq_subobjectSubquotient hXY)
  have hComp :
      factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫ e.hom =
        (A.subobjectToSubquotient hXY).hom := by
    have he_arrow :
        e.hom ≫ (subobjectSubquotientSubobject hXY).arrow =
          (imageSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow := by
      change
        Subobject.ofLE (imageSubobject (Y.arrow ≫ cokernel.π X.arrow))
            (subobjectSubquotientSubobject hXY)
            (Subobject.image_subobject_toQuotient_eq_subobjectSubquotient hXY).le ≫
          (subobjectSubquotientSubobject hXY).arrow =
        (imageSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow
      exact
        Subobject.ofLE_arrow
          (h := (Subobject.image_subobject_toQuotient_eq_subobjectSubquotient hXY).le)
    refine (cancel_mono (subobjectSubquotientSubobject hXY).arrow).1 ?_
    calc
      (factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫ e.hom) ≫
          (subobjectSubquotientSubobject hXY).arrow =
        factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫
          (imageSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow := by
            rw [Category.assoc, he_arrow]
      _ = Y.arrow ≫ cokernel.π X.arrow := by
            rw [imageSubobject_arrow_comp]
      _ = (A.subobjectToSubquotient hXY).hom ≫
            (subobjectSubquotientSubobject hXY).arrow := by
            symm
            exact subobjectToSubquotient_comp_subobjectSubquotientInclusion A hXY
  letI : HasEqualizers C := by infer_instance
  letI : Epi (factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow)) := inferInstance
  letI : Epi e.hom := inferInstance
  haveI : Epi (factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫ e.hom) := inferInstance
  simpa [hComp]

/-- Lemma 12.19.9: the quotient filtration on `Y / X` coming from the induced filtration on `Y`
agrees with the filtration induced from `A / X`. -/
theorem subquotient_quotient_filtration_eq_induced_filtration (hXY : X ≤ Y) :
    ((A.subobjectFilteredObject Y).filtration.quotient (A.subobjectToSubquotient hXY).hom) =
      (A.subobjectSubquotientFilteredObject hXY).filtration := by
  apply OrderHom.ext
  funext i
  -- Compare both stages after mapping them into the ambient quotient object `A / X`.
  apply Subobject.map_obj_injective (subobjectSubquotientSubobject hXY).arrow
  simp [DecreasingFiltration.quotient_eq_imageSubobject_comp]
  sorry

/-- Lemma 12.19.9: after embedding `Y / X` into `A / X`, its `i`-th filtered stage is the image
of the `i`-th stage of `Y` under the ambient quotient map. -/
theorem subobjectSubquotient_stage_map_eq_image_stage_toQuotient (hXY : X ≤ Y) (i : ℤ) :
    (Subobject.map (subobjectSubquotientSubobject hXY).arrow).obj
        ((A.subobjectSubquotientFilteredObject hXY).filtration i) =
      imageSubobject
        ((((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow) ≫
          cokernel.π X.arrow) := by
  sorry

/-- Helper for Lemma 12.19.9: the canonical subquotient inclusion is strict. -/
theorem strict_subobjectToSubquotient (hXY : X ≤ Y) :
    Hom.Strict (A.subobjectToSubquotient hXY) := by
  letI : Epi (A.subobjectToSubquotient hXY).hom := subobjectToSubquotient_epi A hXY
  refine (Hom.strict_iff_quotient_filtration_of_epi (A.subobjectToSubquotient hXY)).2 ?_
  exact (subquotient_quotient_filtration_eq_induced_filtration A hXY).symm

end FilteredObject

end CategoryTheory
