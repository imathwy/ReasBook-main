import stacks_proof.stacks_project.Chap12.Aux_12_20_2_1
import stacks_proof.stacks_project.Chap12.Definition_12_19_3
import stacks_proof.stacks_project.Chap12.Lemma_12_19_7
import stacks_proof.stacks_project.Chap12.Lemma_12_9_6
import Mathlib.Tactic.StacksAttribute

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
  simp [subobjectQuotientMap, Category.assoc]

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

/-- Helper for Lemma 12.19.9: the kernel of a composite is the pullback of the later kernel. -/
private theorem kernelSubobject_comp_eq_pullback {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelSubobject (f ≫ g) = (Subobject.pullback f).obj (kernelSubobject g) := by
  -- Compare both subobjects by the pullback characterization of kernels.
  apply le_antisymm
  · refine Subobject.le_of_comm
      (((Subobject.pullback f).obj (kernelSubobject g)).factorThru (kernelSubobject (f ≫ g)).arrow
        ?_)
      ?_
    · exact
        (pullback_factors_iff (f := f) (kernelSubobject g) (kernelSubobject (f ≫ g)).arrow).2 <| by
          rw [kernelSubobject_factors_iff, Category.assoc]
          exact kernelSubobject_arrow_comp (f ≫ g)
    · exact Subobject.factorThru_arrow _ _ _
  · exact le_kernelSubobject _ _ <| by
      have hpb := (Subobject.isPullback f (kernelSubobject g)).w
      rw [← reassoc_of% hpb, kernelSubobject_arrow_comp, comp_zero]

/-- Helper for Lemma 12.19.9: every subobject arrow is the kernel of its cokernel projection. -/
private theorem subobject_eq_kernel_cokernel (X : Subobject A.obj) :
    X = kernelSubobject (cokernel.π X.arrow) := by
  -- Rewrite the subobject through its image and use exactness of the cokernel sequence.
  calc
    X = imageSubobject X.arrow := by
      symm
      simpa using (Limits.imageSubobject_mono X.arrow)
    _ = kernelSubobject (cokernel.π X.arrow) := by
      simpa using
        (ShortComplex.exact_iff_image_eq_kernel
          (ShortComplex.mk X.arrow (cokernel.π X.arrow) (cokernel.condition X.arrow))).1
          (ShortComplex.exact_cokernel X.arrow)

/-- Helper for Lemma 12.19.9: applying `Subobject.exists` computes the image of the composite
with the ambient map. -/
private theorem existsObjEqImageSubobject_comp {X Y : C} (f : X ⟶ Y) (S : Subobject X) :
    (Subobject.exists f).obj S = imageSubobject (S.arrow ≫ f) := by
  -- Both sides are represented by the same image mono in the codomain.
  apply Subobject.eq_of_comm
    (Subobject.existsIsoImage f S ≪≫ (imageSubobjectIso _).symm)
  calc
    ((Subobject.existsIsoImage f S).hom ≫ (imageSubobjectIso (S.arrow ≫ f)).inv) ≫
        (imageSubobject (S.arrow ≫ f)).arrow
        = (Subobject.existsIsoImage f S).hom ≫ image.ι (S.arrow ≫ f) := by
            simp [Category.assoc]
    _ = ((Subobject.exists f).obj S).arrow := by
          simpa [Subobject.existsIsoImage] using
            (Over.w ((Subobject.existsCompRepresentativeIso f).app S).hom.hom)

/-- Helper for Lemma 12.19.9: pushing forward a pullback along an epimorphism recovers the
original subobject. -/
private theorem existsPullbackEqOfEpi {X Y : C} (f : X ⟶ Y) [Epi f] (P : Subobject Y) :
    (Subobject.exists f).obj ((Subobject.pullback f).obj P) = P := by
  have hImage : imageSubobject (((Subobject.pullback f).obj P).arrow ≫ f) = P := by
    -- The pullback projection is epi, so its image agrees with the original subobject.
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
  -- Compare the pushed-forward pullback with the original subobject by their arrows into `Y`.
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
          simpa [Subobject.existsIsoImage] using
            (Over.w ((Subobject.existsCompRepresentativeIso f).app
              ((Subobject.pullback f).obj P)).hom.hom)

/-- Helper for Lemma 12.19.9: pulling a canonical subquotient `Z / X` back along
`A ⟶ A / X` recovers the ambient subobject `Z`. -/
private theorem pullbackSubobjectSubquotientEqSubobject {Z : Subobject A.obj} (hXZ : X ≤ Z) :
    (Subobject.pullback (cokernel.π X.arrow)).obj (subobjectSubquotientSubobject hXZ) = Z := by
  -- Rewrite the canonical subquotient as a kernel and compute the pullback of that kernel.
  change (Subobject.pullback (cokernel.π X.arrow)).obj
      (kernelSubobject (subobjectQuotientMap hXZ)) = Z
  calc
    (Subobject.pullback (cokernel.π X.arrow)).obj (kernelSubobject (subobjectQuotientMap hXZ))
        = kernelSubobject (cokernel.π X.arrow ≫ subobjectQuotientMap hXZ) := by
            symm
            exact
              kernelSubobject_comp_eq_pullback (cokernel.π X.arrow) (subobjectQuotientMap hXZ)
    _ = kernelSubobject (cokernel.π Z.arrow) := by
          simp [subobjectQuotientMap]
    _ = Z := by
          rw [← subobject_eq_kernel_cokernel A Z]

/-- Helper for Lemma 12.19.9: under an epimorphism, a subobject is determined by its pullback. -/
private theorem pullback_obj_injective_of_epi {B D : C} (f : B ⟶ D) [Epi f] :
    Function.Injective fun P : Subobject D => (Subobject.pullback f).obj P := by
  intro P Q hPQ
  -- Proof comment: `Subobject.exists` is a left inverse to pullback along an epi.
  calc
    P = (Subobject.exists f).obj ((Subobject.pullback f).obj P) := by
          symm
          exact existsPullbackEqOfEpi f P
    _ = (Subobject.exists f).obj ((Subobject.pullback f).obj Q) := by
          exact congrArg (Subobject.exists f).obj hPQ
    _ = Q := by
          exact existsPullbackEqOfEpi f Q

/-- Helper for Lemma 12.19.9: the image of `Y ⟶ A / X` only depends on the join `X ⊔ Y`. -/
private theorem imageSubobjectToQuotientEqSubobjectSubquotientSup
    (X Y : Subobject A.obj) :
    imageSubobject (Y.arrow ≫ cokernel.π X.arrow) =
      subobjectSubquotientSubobject (show X ≤ X ⊔ Y from _root_.le_sup_left) := by
  let π : A.obj ⟶ cokernel X.arrow := cokernel.π X.arrow
  have hExistsX :
      (Subobject.exists π).obj X = (⊥ : Subobject (cokernel X.arrow)) := by
    -- The `X`-part dies under the quotient map `A ⟶ A / X`.
    calc
      (Subobject.exists π).obj X = imageSubobject (X.arrow ≫ π) := by
        exact existsObjEqImageSubobject_comp π X
      _ = ⊥ := by
        simp [π]
  have hExistsSup :
      (Subobject.exists π).obj (X ⊔ Y) = (Subobject.exists π).obj X ⊔ (Subobject.exists π).obj Y := by
    -- The left adjoint `exists π` preserves joins.
    simpa using (Subobject.existsPullbackAdj π).gc.l_sup
  calc
    imageSubobject (Y.arrow ≫ π) = (Subobject.exists π).obj Y := by
      symm
      exact existsObjEqImageSubobject_comp π Y
    _ = (Subobject.exists π).obj X ⊔ (Subobject.exists π).obj Y := by
          rw [hExistsX]
          simp
    _ = (Subobject.exists π).obj (X ⊔ Y) := by
          symm
          exact hExistsSup
    _ = imageSubobject ((X ⊔ Y).arrow ≫ π) := by
          exact existsObjEqImageSubobject_comp π (X ⊔ Y)
    _ = subobjectSubquotientSubobject (show X ≤ X ⊔ Y from _root_.le_sup_left) := by
          simpa [π] using
            (Subobject.image_subobject_toQuotient_eq_subobjectSubquotient
              (A := A.obj) (X := X) (Y := X ⊔ Y) (_root_.le_sup_left : X ≤ X ⊔ Y))

/-- Helper for Lemma 12.19.9: the `i`-th induced stage on a subobject `Y` has ambient image
`Y ⊓ F^i A`. -/
private theorem subobjectStageImage_eq_inf (Y : Subobject A.obj) (i : ℤ) :
    imageSubobject (((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow) =
      Y ⊓ A.filtration i := by
  -- Proof comment: the stage inside `Y` is a pullback of the ambient stage, and mapping that
  -- pullback along the mono `Y.arrow` produces the ambient intersection.
  rw [show (A.subobjectFilteredObject Y).filtration i =
      (Subobject.pullback Y.arrow).obj (A.filtration i) by
    rfl]
  calc
    imageSubobject (((Subobject.pullback Y.arrow).obj (A.filtration i)).arrow ≫ Y.arrow)
        = (Subobject.map Y.arrow).obj
            (imageSubobject ((Subobject.pullback Y.arrow).obj (A.filtration i)).arrow) := by
            exact imageSubobject_comp_eq_map_of_mono
              ((Subobject.pullback Y.arrow).obj (A.filtration i)).arrow Y.arrow
    _ = (Subobject.map Y.arrow).obj ((Subobject.pullback Y.arrow).obj (A.filtration i)) := by
          rw [Limits.imageSubobject_mono, Subobject.mk_arrow]
    _ = Y ⊓ A.filtration i := by
          symm
          exact Subobject.inf_eq_map_pullback Y (A.filtration i)

/-- Helper for Lemma 12.19.9: pulling the ambient quotient stage back along `A ⟶ A / X`
recovers `X ⊔ F^i A`. -/
private theorem pullbackQuotientFilteredStage_eq_sup (X : Subobject A.obj) (i : ℤ) :
    (Subobject.pullback (cokernel.π X.arrow)).obj ((A.quotientFilteredObject X).filtration i) =
      X ⊔ A.filtration i := by
  let π : A.obj ⟶ cokernel X.arrow := cokernel.π X.arrow
  -- Rewrite the quotient stage through its defining image in `A / X`, then pull the canonical
  -- subquotient back to the ambient join.
  calc
    (Subobject.pullback π).obj ((A.quotientFilteredObject X).filtration i) =
      (Subobject.pullback π).obj (imageSubobject ((A.filtration i).arrow ≫ π)) := by
        rw [show (A.quotientFilteredObject X).filtration i =
            imageSubobject ((A.filtration i).arrow ≫ π) by
          simpa [quotientFilteredObject, π] using
            (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration π i)]
    _ = (Subobject.pullback π).obj
          (subobjectSubquotientSubobject
            (show X ≤ X ⊔ A.filtration i from _root_.le_sup_left)) := by
          rw [imageSubobjectToQuotientEqSubobjectSubquotientSup A X (A.filtration i)]
    _ = X ⊔ A.filtration i := by
          exact pullbackSubobjectSubquotientEqSubobject A
            (_root_.le_sup_left : X ≤ X ⊔ A.filtration i)

/-- Helper for Lemma 12.19.9: pulling back the quotient image of a subobject `Z ⟶ A / X`
recovers the ambient join `X ⊔ Z`. -/
private theorem pullbackImageSubobjectToQuotient_eq_sup (Z : Subobject A.obj) :
    (Subobject.pullback (cokernel.π X.arrow)).obj
      (imageSubobject (Z.arrow ≫ cokernel.π X.arrow)) =
        X ⊔ Z := by
  let π : A.obj ⟶ cokernel X.arrow := cokernel.π X.arrow
  -- Proof comment: rewrite the quotient image through the canonical kernel-model subquotient
  -- `(X ⊔ Z) / X`, then pull that subquotient back along the ambient quotient map.
  calc
    (Subobject.pullback π).obj (imageSubobject (Z.arrow ≫ π))
        = (Subobject.pullback π).obj
            (subobjectSubquotientSubobject
              (show X ≤ X ⊔ Z from _root_.le_sup_left)) := by
            rw [imageSubobjectToQuotientEqSubobjectSubquotientSup A X Z]
    _ = X ⊔ Z := by
          exact pullbackSubobjectSubquotientEqSubobject A
            (_root_.le_sup_left : X ≤ X ⊔ Z)

/-- Helper for Lemma 12.19.9: the kernel of `Z ⟶ A / W` is `(W ⊓ Z) ⊆ Z`. -/
private theorem kernelSubobjectToQuotientEqInfSubobject
    (W Z : Subobject A.obj) :
    kernelSubobject (Z.arrow ≫ cokernel.π W.arrow) =
      Subobject.mk (Subobject.ofLE (W ⊓ Z) Z (_root_.inf_le_right : W ⊓ Z ≤ Z)) := by
  -- Proof comment: compare the two subobjects of `Z` after mapping them back into the ambient
  -- object `A`; there they both become the same intersection `W ⊓ Z`.
  apply Subobject.map_obj_injective Z.arrow
  calc
    (Subobject.map Z.arrow).obj (kernelSubobject (Z.arrow ≫ cokernel.π W.arrow))
        = (Subobject.map Z.arrow).obj
            ((Subobject.pullback Z.arrow).obj (kernelSubobject (cokernel.π W.arrow))) := by
              rw [kernelSubobject_comp_eq_pullback Z.arrow (cokernel.π W.arrow)]
    _ = Z ⊓ kernelSubobject (cokernel.π W.arrow) := by
          symm
          simpa [inf_comm] using
            (Subobject.inf_eq_map_pullback Z (kernelSubobject (cokernel.π W.arrow)))
    _ = Z ⊓ W := by
          rw [← subobject_eq_kernel_cokernel A W]
    _ = W ⊓ Z := by
          rw [inf_comm]
    _ = (Subobject.map Z.arrow).obj
          (Subobject.mk (Subobject.ofLE (W ⊓ Z) Z (_root_.inf_le_right : W ⊓ Z ≤ Z))) := by
          change W ⊓ Z = Subobject.mk
            (Subobject.ofLE (W ⊓ Z) Z (_root_.inf_le_right : W ⊓ Z ≤ Z) ≫ Z.arrow)
          simpa [Subobject.ofLE_arrow]

/-- Helper for Lemma 12.19.9: a known kernel presentation makes the induced map to the image
kill the corresponding subobject inclusion. -/
private theorem factorThruImageSubobjectCompZeroOfKernelEqSubobjectOfLE
    {B D : C} {K Y : Subobject B} (hKY : K ≤ Y) (f : (Y : C) ⟶ D)
    (hKernel : kernelSubobject f = Subobject.mk (Subobject.ofLE K Y hKY)) :
    Subobject.ofLE K Y hKY ≫ factorThruImageSubobject f = 0 := by
  -- Proof comment: postcompose with the image inclusion, where the claim reduces to the kernel
  -- factorization criterion for `f`.
  refine (cancel_mono (imageSubobject f).arrow).1 ?_
  calc
    (Subobject.ofLE K Y hKY ≫ factorThruImageSubobject f) ≫ (imageSubobject f).arrow
        = Subobject.ofLE K Y hKY ≫ f := by
            rw [Category.assoc, imageSubobject_arrow_comp]
    _ = 0 := by
          have hFactors : (kernelSubobject f).Factors (Subobject.ofLE K Y hKY) := by
            simpa [hKernel] using
              (Subobject.mk_factors_self (Subobject.ofLE K Y hKY) :
                (Subobject.mk (Subobject.ofLE K Y hKY)).Factors (Subobject.ofLE K Y hKY))
          exact (kernelSubobject_factors_iff f (Subobject.ofLE K Y hKY)).1 hFactors
    _ = 0 ≫ (imageSubobject f).arrow := by
          simp

/-- Helper for Lemma 12.19.9: a morphism with identified kernel presents its image as the
cokernel of that kernel inclusion. -/
private noncomputable def factorThruImageSubobjectIsCokernelOfKernelEqSubobjectOfLE
    {B D : C} {K Y : Subobject B} (hKY : K ≤ Y) (f : (Y : C) ⟶ D)
    (hKernel : kernelSubobject f = Subobject.mk (Subobject.ofLE K Y hKY)) :
    IsColimit (CokernelCofork.ofπ (factorThruImageSubobject f)
      (factorThruImageSubobjectCompZeroOfKernelEqSubobjectOfLE hKY f hKernel)) := by
  -- Proof comment: exactness of `K ⟶ Y ⟶ D` identifies the image factorization of `f` with the
  -- cokernel of the kernel inclusion.
  have hZero : Subobject.ofLE K Y hKY ≫ f = 0 := by
    have hFactors : (kernelSubobject f).Factors (Subobject.ofLE K Y hKY) := by
      simpa [hKernel] using
        (Subobject.mk_factors_self (Subobject.ofLE K Y hKY) :
          (Subobject.mk (Subobject.ofLE K Y hKY)).Factors (Subobject.ofLE K Y hKY))
    exact (kernelSubobject_factors_iff f (Subobject.ofLE K Y hKY)).1 hFactors
  have hExact : (ShortComplex.mk (Subobject.ofLE K Y hKY) f hZero).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    calc
      imageSubobject (Subobject.ofLE K Y hKY) = Subobject.mk (Subobject.ofLE K Y hKY) := by
        simpa using (Limits.imageSubobject_mono (Subobject.ofLE K Y hKY))
      _ = kernelSubobject f := by
        simpa using hKernel.symm
  let cImage : CokernelCofork (Subobject.ofLE K Y hKY) :=
    CokernelCofork.ofπ (Limits.factorThruImage f) (comp_factorThruImage_eq_zero hZero)
  have hImage : IsColimit cImage := ShortComplex.Exact.isColimitImage hExact
  exact IsColimit.ofIsoColimit hImage <|
    Cofork.ext (imageSubobjectIso f).symm

/-- Helper for Lemma 12.19.9: under `X ≤ Y`, the quotient image of `Y ∩ Z` is the intersection
of the quotient images of `Y` and `Z`. -/
private theorem imageSubobjectToQuotient_inf_eq_infImages
    (hXY : X ≤ Y) (Z : Subobject A.obj) :
    imageSubobject ((Y ⊓ Z).arrow ≫ cokernel.π X.arrow) =
      imageSubobject (Y.arrow ≫ cokernel.π X.arrow) ⊓
        imageSubobject (Z.arrow ≫ cokernel.π X.arrow) := by
  let πX : A.obj ⟶ cokernel X.arrow := cokernel.π X.arrow
  let πY : A.obj ⟶ cokernel Y.arrow := cokernel.π Y.arrow
  let qXY : cokernel X.arrow ⟶ cokernel Y.arrow := subobjectQuotientMap hXY
  let fZ : (Z : C) ⟶ cokernel X.arrow := Z.arrow ≫ πX
  let gZ : (Z : C) ⟶ cokernel Y.arrow := Z.arrow ≫ πY
  let s : ((Y ⊓ Z : Subobject A.obj) : C) ⟶ imageSubobject fZ :=
    Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫ factorThruImageSubobject fZ
  let m : (imageSubobject fZ : C) ⟶ cokernel Y.arrow := (imageSubobject fZ).arrow ≫ qXY
  have hComp : fZ ≫ qXY = gZ := by
    dsimp [fZ, gZ, qXY, πX, πY]
    simp [subobjectQuotientMap, Category.assoc]
  have hImageY :
      imageSubobject (Y.arrow ≫ πX) = kernelSubobject qXY := by
    simpa [qXY, πX, subobjectSubquotientSubobject] using
      (Subobject.image_subobject_toQuotient_eq_subobjectSubquotient
        (A := A.obj) (X := X) (Y := Y) hXY)
  have hKernelF :
      kernelSubobject fZ =
        Subobject.mk (Subobject.ofLE (X ⊓ Z) Z (_root_.inf_le_right : X ⊓ Z ≤ Z)) := by
    simpa [fZ] using kernelSubobjectToQuotientEqInfSubobject (A := A) X Z
  have hKernelG :
      kernelSubobject gZ =
        Subobject.mk (Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z)) := by
    simpa [gZ] using kernelSubobjectToQuotientEqInfSubobject (A := A) Y Z
  have hZeroF :
      Subobject.ofLE (X ⊓ Z) Z (_root_.inf_le_right : X ⊓ Z ≤ Z) ≫
        factorThruImageSubobject fZ = 0 :=
    factorThruImageSubobjectCompZeroOfKernelEqSubobjectOfLE
      (_root_.inf_le_right : X ⊓ Z ≤ Z) fZ hKernelF
  have hZeroG :
      Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
        factorThruImageSubobject gZ = 0 :=
    factorThruImageSubobjectCompZeroOfKernelEqSubobjectOfLE
      (_root_.inf_le_right : Y ⊓ Z ≤ Z) gZ hKernelG
  have hCokernelF :
      IsColimit (CokernelCofork.ofπ (factorThruImageSubobject fZ) hZeroF) :=
    factorThruImageSubobjectIsCokernelOfKernelEqSubobjectOfLE
      (_root_.inf_le_right : X ⊓ Z ≤ Z) fZ hKernelF
  have hCokernelG :
      IsColimit (CokernelCofork.ofπ (factorThruImageSubobject gZ) hZeroG) :=
    factorThruImageSubobjectIsCokernelOfKernelEqSubobjectOfLE
      (_root_.inf_le_right : Y ⊓ Z ≤ Z) gZ hKernelG
  have hXZ_le : X ⊓ Z ≤ Y ⊓ Z := inf_le_inf hXY le_rfl
  have hZeroXG :
      Subobject.ofLE (X ⊓ Z) Z (_root_.inf_le_right : X ⊓ Z ≤ Z) ≫
        factorThruImageSubobject gZ = 0 := by
    calc
      Subobject.ofLE (X ⊓ Z) Z (_root_.inf_le_right : X ⊓ Z ≤ Z) ≫
          factorThruImageSubobject gZ =
        (Subobject.ofLE (X ⊓ Z) (Y ⊓ Z) hXZ_le ≫
            Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z)) ≫
          factorThruImageSubobject gZ := by
              rw [Subobject.ofLE_comp_ofLE (X ⊓ Z) (Y ⊓ Z) Z hXZ_le
                (_root_.inf_le_right : Y ⊓ Z ≤ Z)]
      _ = Subobject.ofLE (X ⊓ Z) (Y ⊓ Z) hXZ_le ≫
          (Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
            factorThruImageSubobject gZ) := by
              simp
      _ = 0 := by
            rw [hZeroG]
            simp
  let t : (imageSubobject fZ : C) ⟶ imageSubobject gZ :=
    hCokernelF.desc (CokernelCofork.ofπ (factorThruImageSubobject gZ) hZeroXG)
  have ht_fac : factorThruImageSubobject fZ ≫ t = factorThruImageSubobject gZ := by
    simpa [t] using
      hCokernelF.fac (CokernelCofork.ofπ (factorThruImageSubobject gZ) hZeroXG)
        WalkingParallelPair.one
  have hs_zero : s ≫ t = 0 := by
    calc
      s ≫ t = Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
          (factorThruImageSubobject fZ ≫ t) := by
            simp [s, Category.assoc]
      _ = Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
          factorThruImageSubobject gZ := by
            rw [ht_fac]
      _ = 0 := hZeroG
  have ht_arrow : t ≫ (imageSubobject gZ).arrow = m := by
    apply (cancel_epi (factorThruImageSubobject fZ)).1
    calc
      factorThruImageSubobject fZ ≫ (t ≫ (imageSubobject gZ).arrow)
          = (factorThruImageSubobject fZ ≫ t) ≫ (imageSubobject gZ).arrow := by
              simp [Category.assoc]
      _ = factorThruImageSubobject gZ ≫ (imageSubobject gZ).arrow := by
            rw [ht_fac]
      _ = gZ := by
            rw [imageSubobject_arrow_comp]
      _ = factorThruImageSubobject fZ ≫ ((imageSubobject fZ).arrow ≫ qXY) := by
            simpa [fZ, gZ, m, hComp, Category.assoc]
      _ = factorThruImageSubobject fZ ≫ m := by
            rfl
  have hCokernelT : IsColimit (CokernelCofork.ofπ t hs_zero) := by
    refine Cofork.IsColimit.mk _ (fun S => ?_) ?_ ?_
    ·
      have hScond : s ≫ Cofork.π S = 0 := by
        simpa using Cofork.condition S
      have hScond' :
          Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
            factorThruImageSubobject fZ ≫ Cofork.π S = 0 := by
        calc
          Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
              factorThruImageSubobject fZ ≫ Cofork.π S
              = (Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
                  factorThruImageSubobject fZ) ≫ Cofork.π S := by
                    rw [Category.assoc]
          _ = s ≫ Cofork.π S := by
                rfl
          _ = 0 := hScond
      refine hCokernelG.desc <| CokernelCofork.ofπ (factorThruImageSubobject fZ ≫ Cofork.π S) ?_
      exact hScond'
    · intro S
      have hScond : s ≫ Cofork.π S = 0 := by
        simpa using Cofork.condition S
      have hScond' :
          Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
            factorThruImageSubobject fZ ≫ Cofork.π S = 0 := by
        calc
          Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
              factorThruImageSubobject fZ ≫ Cofork.π S
              = (Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
                  factorThruImageSubobject fZ) ≫ Cofork.π S := by
                    rw [Category.assoc]
          _ = s ≫ Cofork.π S := by
                rfl
          _ = 0 := hScond
      apply (cancel_epi (factorThruImageSubobject fZ)).1
      calc
        factorThruImageSubobject fZ ≫
            (t ≫ hCokernelG.desc (CokernelCofork.ofπ (factorThruImageSubobject fZ ≫ Cofork.π S)
              hScond')
            )
            = factorThruImageSubobject gZ ≫
                hCokernelG.desc (CokernelCofork.ofπ (factorThruImageSubobject fZ ≫ Cofork.π S)
                  hScond') := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun k =>
                          k ≫ hCokernelG.desc
                            (CokernelCofork.ofπ (factorThruImageSubobject fZ ≫ Cofork.π S)
                              hScond'))
                        ht_fac
        _ = factorThruImageSubobject fZ ≫ Cofork.π S := by
              simpa using
                hCokernelG.fac (CokernelCofork.ofπ (factorThruImageSubobject fZ ≫ Cofork.π S)
                  hScond') WalkingParallelPair.one
    · intro S u hu
      have hScond : s ≫ Cofork.π S = 0 := by
        simpa using Cofork.condition S
      have hScond' :
          Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
            factorThruImageSubobject fZ ≫ Cofork.π S = 0 := by
        calc
          Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
              factorThruImageSubobject fZ ≫ Cofork.π S
              = (Subobject.ofLE (Y ⊓ Z) Z (_root_.inf_le_right : Y ⊓ Z ≤ Z) ≫
                  factorThruImageSubobject fZ) ≫ Cofork.π S := by
                    rw [Category.assoc]
          _ = s ≫ Cofork.π S := by
                rfl
          _ = 0 := hScond
      apply hCokernelG.hom_ext
      intro j
      cases j with
      | zero =>
          simpa [Category.assoc, hZeroG]
      | one =>
          calc
            factorThruImageSubobject gZ ≫ u
                = (factorThruImageSubobject fZ ≫ t) ≫ u := by
                    rw [ht_fac]
            _ = factorThruImageSubobject fZ ≫ (t ≫ u) := by
                  simp [Category.assoc]
            _ = factorThruImageSubobject fZ ≫ Cofork.π S := by
                  simpa using congrArg (fun k => factorThruImageSubobject fZ ≫ k) hu
            _ = factorThruImageSubobject gZ ≫
                hCokernelG.desc (CokernelCofork.ofπ (factorThruImageSubobject fZ ≫ Cofork.π S)
                  hScond') := by
                    symm
                    simpa using
                      hCokernelG.fac (CokernelCofork.ofπ (factorThruImageSubobject fZ ≫ Cofork.π S)
                        hScond') WalkingParallelPair.one
  have hExactT : (ShortComplex.mk s t hs_zero).Exact := by
    exact ShortComplex.exact_of_g_is_cokernel _ hCokernelT
  have hImageKernelT : imageSubobject s = kernelSubobject t := by
    exact (ShortComplex.exact_iff_image_eq_kernel _).1 hExactT
  have hKernelM : kernelSubobject m = imageSubobject s := by
    calc
      kernelSubobject m = kernelSubobject (t ≫ (imageSubobject gZ).arrow) := by
        simpa [ht_arrow]
      _ = kernelSubobject t := by
            simpa using (kernelSubobject_comp_mono t (imageSubobject gZ).arrow)
      _ = imageSubobject s := by
            symm
            exact hImageKernelT
  -- Proof comment: compute the intersection as the image, inside `imageSubobject fZ`, of the
  -- kernel of the restricted quotient map to `A / Y`.
  symm
  calc
    imageSubobject (Y.arrow ≫ πX) ⊓ imageSubobject (Z.arrow ≫ πX)
        = kernelSubobject qXY ⊓ imageSubobject fZ := by
            simpa [fZ] using congrArg (fun T => T ⊓ imageSubobject (Z.arrow ≫ πX)) hImageY
    _ = imageSubobject fZ ⊓ kernelSubobject qXY := by
          rw [inf_comm]
    _ = (Subobject.map (imageSubobject fZ).arrow).obj
          ((Subobject.pullback (imageSubobject fZ).arrow).obj (kernelSubobject qXY)) := by
            exact Subobject.inf_eq_map_pullback (imageSubobject fZ) (kernelSubobject qXY)
    _ = (Subobject.map (imageSubobject fZ).arrow).obj
          (kernelSubobject ((imageSubobject fZ).arrow ≫ qXY)) := by
            rw [← kernelSubobject_comp_eq_pullback (imageSubobject fZ).arrow qXY]
    _ = (Subobject.map (imageSubobject fZ).arrow).obj (imageSubobject s) := by
          rw [hKernelM]
    _ = imageSubobject (s ≫ (imageSubobject fZ).arrow) := by
          symm
          exact imageSubobject_comp_eq_map_of_mono s (imageSubobject fZ).arrow
    _ = imageSubobject ((Y ⊓ Z).arrow ≫ πX) := by
          dsimp [s, fZ]
          rw [Category.assoc, imageSubobject_arrow_comp]
          simpa

/-- Helper for Lemma 12.19.9: under `X ≤ Y`, quotient-image comparison recovers the modular
identity `Y ⊓ (X ⊔ Z) = X ⊔ (Y ⊓ Z)`. -/
private theorem subobjectInfSup_eq_supInf_of_le (hXY : X ≤ Y) (Z : Subobject A.obj) :
    Y ⊓ (X ⊔ Z) = X ⊔ (Y ⊓ Z) := by
  let π : A.obj ⟶ cokernel X.arrow := cokernel.π X.arrow
  letI : Epi π := by
    dsimp [π]
    infer_instance
  have hLeftImage :
      imageSubobject ((Y ⊓ (X ⊔ Z)).arrow ≫ π) =
        imageSubobject (Y.arrow ≫ π) ⊓ imageSubobject (Z.arrow ≫ π) := by
    have hSupImage :
        imageSubobject ((X ⊔ Z).arrow ≫ π) = imageSubobject (Z.arrow ≫ π) := by
      rw [imageSubobjectToQuotientEqSubobjectSubquotientSup A X Z]
      simpa [π] using
        (Subobject.image_subobject_toQuotient_eq_subobjectSubquotient
          (A := A.obj) (X := X) (Y := X ⊔ Z)
          (_root_.le_sup_left : X ≤ X ⊔ Z))
    -- Proof comment: rewrite the second factor through `(X ⊔ Z) / X = Z / (X ⊓ Z)`.
    calc
      imageSubobject ((Y ⊓ (X ⊔ Z)).arrow ≫ π)
          = imageSubobject (Y.arrow ≫ π) ⊓ imageSubobject ((X ⊔ Z).arrow ≫ π) := by
              exact imageSubobjectToQuotient_inf_eq_infImages (A := A) (X := X)
                (Y := Y) hXY (X ⊔ Z)
      _ = imageSubobject (Y.arrow ≫ π) ⊓ imageSubobject (Z.arrow ≫ π) := by
            rw [hSupImage]
  have hRightImage :
      imageSubobject ((X ⊔ (Y ⊓ Z)).arrow ≫ π) =
        imageSubobject (Y.arrow ≫ π) ⊓ imageSubobject (Z.arrow ≫ π) := by
    -- Proof comment: the added `X` disappears in the quotient, so the right-hand side reduces
    -- to the quotient image of `Y ⊓ Z`, which is the common quotient-side intersection.
    calc
      imageSubobject ((X ⊔ (Y ⊓ Z)).arrow ≫ π) = imageSubobject ((Y ⊓ Z).arrow ≫ π) := by
        rw [imageSubobjectToQuotientEqSubobjectSubquotientSup A X (Y ⊓ Z)]
        simpa [π] using
          (Subobject.image_subobject_toQuotient_eq_subobjectSubquotient
            (A := A.obj) (X := X) (Y := X ⊔ (Y ⊓ Z))
            (_root_.le_sup_left : X ≤ X ⊔ (Y ⊓ Z)))
      _ = imageSubobject (Y.arrow ≫ π) ⊓ imageSubobject (Z.arrow ≫ π) := by
            exact imageSubobjectToQuotient_inf_eq_infImages (A := A) (X := X)
              (Y := Y) hXY Z
  -- Proof comment: both subobjects contain `X`, so equality of their quotient images implies
  -- equality after pulling back along the epi `A ⟶ A / X`.
  calc
    Y ⊓ (X ⊔ Z)
        = (Subobject.pullback π).obj (imageSubobject ((Y ⊓ (X ⊔ Z)).arrow ≫ π)) := by
            symm
            simpa [π, sup_eq_right.2 (le_inf hXY le_sup_left)] using
              pullbackImageSubobjectToQuotient_eq_sup
                (A := A) (X := X) (Z := Y ⊓ (X ⊔ Z))
    _ = (Subobject.pullback π).obj (imageSubobject ((X ⊔ (Y ⊓ Z)).arrow ≫ π)) := by
          rw [hLeftImage, hRightImage]
    _ = X ⊔ (Y ⊓ Z) := by
          simpa [π, sup_assoc, sup_left_idem, sup_comm] using
            pullbackImageSubobjectToQuotient_eq_sup
              (A := A) (X := X) (Z := X ⊔ (Y ⊓ Z))

/-- Helper for Lemma 12.19.9: mapping the induced stage on `Y / X` into `A / X` gives the
intersection with the ambient quotient stage. -/
private theorem mappedSubobjectSubquotientStage_eq_inf (hXY : X ≤ Y) (i : ℤ) :
    (Subobject.map (subobjectSubquotientSubobject hXY).arrow).obj
      ((A.subobjectSubquotientFilteredObject hXY).filtration i) =
        subobjectSubquotientSubobject hXY ⊓ (A.quotientFilteredObject X).filtration i := by
  -- Unfold the induced filtration stage and rewrite the mapped pullback with the standard
  -- `map/pullback = inf` formula.
  rw [show (A.subobjectSubquotientFilteredObject hXY).filtration i =
      (Subobject.pullback (subobjectSubquotientSubobject hXY).arrow).obj
        ((A.quotientFilteredObject X).filtration i) by
    rfl]
  rw [← Subobject.inf_eq_map_pullback (subobjectSubquotientSubobject hXY)
    ((A.quotientFilteredObject X).filtration i)]

/-- Helper for Lemma 12.19.9: the quotient-side image of the `i`-th stage of `Y` is the
canonical subquotient of `X ⊔ (Y ⊓ F^i A)`. -/
private theorem imageStageToQuotient_eq_subobjectSubquotient_supInf (i : ℤ) :
    imageSubobject
      ((((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow) ≫ cokernel.π X.arrow) =
        subobjectSubquotientSubobject
          (show X ≤ X ⊔ (Y ⊓ A.filtration i) from _root_.le_sup_left) := by
  let π : A.obj ⟶ cokernel X.arrow := cokernel.π X.arrow
  let S : Subobject A.obj :=
    imageSubobject (((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow)
  -- Proof comment: rewrite through the ambient stage image in `A`, then identify its quotient
  -- image with the canonical subquotient of `X ⊔ (Y ⊓ F^i A)`.
  calc
    imageSubobject
        ((((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow) ≫ π)
        = imageSubobject (S.arrow ≫ π) := by
        dsimp [S]
        rw [CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction
          (((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow) π]
    _ = subobjectSubquotientSubobject (show X ≤ X ⊔ S from _root_.le_sup_left) := by
          rw [imageSubobjectToQuotientEqSubobjectSubquotientSup A X S]
    _ = subobjectSubquotientSubobject
          (show X ≤ X ⊔ (Y ⊓ A.filtration i) from _root_.le_sup_left) := by
            rw [show S = Y ⊓ A.filtration i by
              exact subobjectStageImage_eq_inf A Y i]

/-- Helper for Lemma 12.19.9: pulling back the quotient-side intersection
`(Y / X) ⊓ F^i(A / X)` is the same canonical subquotient of `X ⊔ (Y ⊓ F^i A)`. -/
private theorem subobjectSubquotient_inf_eq_subobjectSubquotient_supInf
    (hXY : X ≤ Y) (i : ℤ) :
    subobjectSubquotientSubobject hXY ⊓ (A.quotientFilteredObject X).filtration i =
      subobjectSubquotientSubobject
        (show X ≤ X ⊔ (Y ⊓ A.filtration i) from _root_.le_sup_left) := by
  let π : A.obj ⟶ cokernel X.arrow := cokernel.π X.arrow
  letI : Epi π := by
    dsimp [π]
    infer_instance
  -- Proof comment: pull back the intersection in `A / X` and simplify each factor separately.
  exact pullback_obj_injective_of_epi (f := π) <| by
    calc
    (Subobject.pullback π).obj
        (subobjectSubquotientSubobject hXY ⊓ (A.quotientFilteredObject X).filtration i)
        =
      (Subobject.pullback π).obj (subobjectSubquotientSubobject hXY) ⊓
        (Subobject.pullback π).obj ((A.quotientFilteredObject X).filtration i) := by
          rw [Subobject.inf_pullback]
    _ = Y ⊓ (X ⊔ A.filtration i) := by
          rw [pullbackSubobjectSubquotientEqSubobject A hXY,
            pullbackQuotientFilteredStage_eq_sup A X i]
    _ = X ⊔ (Y ⊓ A.filtration i) := by
          exact subobjectInfSup_eq_supInf_of_le (A := A) hXY (A.filtration i)
    _ = (Subobject.pullback π).obj
          (subobjectSubquotientSubobject
            (show X ≤ X ⊔ (Y ⊓ A.filtration i) from _root_.le_sup_left)) := by
          symm
          exact pullbackSubobjectSubquotientEqSubobject A
            (_root_.le_sup_left : X ≤ X ⊔ (Y ⊓ A.filtration i))

/-- Helper for Lemma 12.19.9: inside `A / X`, the image of the `i`-th stage of `Y` is the
intersection `(Y / X) ⊓ F^i(A / X)`. -/
private theorem imageStageToQuotient_eq_inf (hXY : X ≤ Y) (i : ℤ) :
    imageSubobject
      ((((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow) ≫ cokernel.π X.arrow) =
        subobjectSubquotientSubobject hXY ⊓ (A.quotientFilteredObject X).filtration i := by
  calc
    imageSubobject
        ((((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow) ≫ cokernel.π X.arrow)
        =
      subobjectSubquotientSubobject
        (show X ≤ X ⊔ (Y ⊓ A.filtration i) from _root_.le_sup_left) := by
          exact imageStageToQuotient_eq_subobjectSubquotient_supInf A i
    _ = subobjectSubquotientSubobject hXY ⊓ (A.quotientFilteredObject X).filtration i := by
          symm
          exact subobjectSubquotient_inf_eq_subobjectSubquotient_supInf A hXY i

/-- Helper for Lemma 12.19.9: the mapped induced stage on `Y / X` is exactly the image of the
corresponding stage of `Y` inside `A / X`. -/
private theorem mappedSubobjectSubquotientStage_eq_imageStageInAmbientQuotient
    (hXY : X ≤ Y) (i : ℤ) :
    (Subobject.map (subobjectSubquotientSubobject hXY).arrow).obj
      ((A.subobjectSubquotientFilteredObject hXY).filtration i) =
        imageSubobject
          ((((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow) ≫
            cokernel.π X.arrow) := by
  -- Route correction: first normalize both sides to the common quotient-side intersection
  -- `(Y / X) ⊓ F^i(A / X)`.
  calc
    (Subobject.map (subobjectSubquotientSubobject hXY).arrow).obj
        ((A.subobjectSubquotientFilteredObject hXY).filtration i) =
      subobjectSubquotientSubobject hXY ⊓ (A.quotientFilteredObject X).filtration i := by
        exact mappedSubobjectSubquotientStage_eq_inf A hXY i
    _ = imageSubobject
          ((((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow) ≫
            cokernel.π X.arrow) := by
          symm
          exact imageStageToQuotient_eq_inf A hXY i

/-- Lemma 12.19.9: the quotient filtration on `Y / X` coming from the induced filtration on `Y`
agrees with the filtration induced from `A / X`. -/
@[stacks 0129]
theorem subquotient_quotient_filtration_eq_induced_filtration (hXY : X ≤ Y) :
    ((A.subobjectFilteredObject Y).filtration.quotient (A.subobjectToSubquotient hXY).hom) =
      (A.subobjectSubquotientFilteredObject hXY).filtration := by
  -- Route correction: compare stages after mapping them into `A / X`, where both sides become
  -- the same ambient image subobject of `((F^i Y) ⟶ A / X)`.
  letI : Mono (subobjectSubquotientSubobject hXY).arrow :=
    subobjectSubquotientSubobject_arrow_mono (A := A) hXY
  refine OrderHom.ext _ _ ?_
  funext i
  apply (Subobject.map_obj_injective (subobjectSubquotientSubobject hXY).arrow)
  rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
  calc
    (Subobject.map (subobjectSubquotientSubobject hXY).arrow).obj
        (imageSubobject
          (((A.subobjectFilteredObject Y).filtration i).arrow ≫
            (A.subobjectToSubquotient hXY).hom))
        = imageSubobject
          ((((A.subobjectFilteredObject Y).filtration i).arrow ≫
            (A.subobjectToSubquotient hXY).hom) ≫
              (subobjectSubquotientSubobject hXY).arrow) := by
            have hMono : Mono (subobjectSubquotientSubobject hXY).arrow :=
              subobjectSubquotientSubobject_arrow_mono (A := A) hXY
            have hImageComp :=
              @imageSubobject_comp_eq_map_of_mono C _ _ _ _ _
                (((A.subobjectFilteredObject Y).filtration i).arrow ≫
                  (A.subobjectToSubquotient hXY).hom)
                (subobjectSubquotientSubobject hXY).arrow hMono
            simpa [Category.assoc] using hImageComp.symm
    _ = imageSubobject
          ((((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow) ≫
            cokernel.π X.arrow) := by
            simpa [Category.assoc] using
              congrArg (fun k =>
                imageSubobject (((A.subobjectFilteredObject Y).filtration i).arrow ≫ k))
                (subobjectToSubquotient_comp_subobjectSubquotientInclusion A hXY)
    _ = (Subobject.map (subobjectSubquotientSubobject hXY).arrow).obj
          ((A.subobjectSubquotientFilteredObject hXY).filtration i) := by
            symm
            exact mappedSubobjectSubquotientStage_eq_imageStageInAmbientQuotient A hXY i

/-- Lemma 12.19.9: after embedding `Y / X` into `A / X`, its `i`-th filtered stage is the image
of the `i`-th stage of `Y` under the ambient quotient map. -/
@[stacks 0129]
theorem subobjectSubquotient_stage_map_eq_image_stage_toQuotient (hXY : X ≤ Y) (i : ℤ) :
    (Subobject.map (subobjectSubquotientSubobject hXY).arrow).obj
        ((A.subobjectSubquotientFilteredObject hXY).filtration i) =
      imageSubobject
        ((((A.subobjectFilteredObject Y).filtration i).arrow ≫ Y.arrow) ≫
          cokernel.π X.arrow) := by
  -- This is the stagewise bridge proved once above for both public statements.
  exact mappedSubobjectSubquotientStage_eq_imageStageInAmbientQuotient A hXY i

/-- Helper for Lemma 12.19.9: the canonical subquotient inclusion is strict. -/
theorem strict_subobjectToSubquotient (hXY : X ≤ Y) :
    Hom.Strict (A.subobjectToSubquotient hXY) := by
  letI : Epi (A.subobjectToSubquotient hXY).hom := subobjectToSubquotient_epi A hXY
  refine (Hom.strict_iff_quotient_filtration_of_epi (A.subobjectToSubquotient hXY)).2 ?_
  exact (subquotient_quotient_filtration_eq_induced_filtration A hXY).symm

end FilteredObject

end CategoryTheory
