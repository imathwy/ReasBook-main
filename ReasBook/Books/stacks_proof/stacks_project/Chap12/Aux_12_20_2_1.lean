import Mathlib
import Mathlib.CategoryTheory.Subobject.Lattice

-- Auxiliary Chapter 12 subquotient constructions used for later `E_∞`-style statements.

open CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section QuotientMap

variable [HasZeroMorphisms C] [HasCokernels C]

-- The inclusion `X ≤ Y` identifies `X.arrow` with `Subobject.ofLE X Y hXY ≫ Y.arrow`, so the
-- cokernel projection of `Y.arrow` annihilates `X.arrow`.
private theorem subobjectQuotientMapCondition {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    X.arrow ≫ cokernel.π Y.arrow = 0 := by
  -- Rewrite `X.arrow` through the inclusion `X ⟶ Y`, then apply the cokernel relation for `Y`.
  rw [← Subobject.ofLE_arrow (X := X) (Y := Y) hXY, Category.assoc]
  simp

/-- The canonical morphism `A / X ⟶ A / Y` induced by an inclusion `X ≤ Y` of subobjects. -/
def subobjectQuotientMap {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    cokernel X.arrow ⟶ cokernel Y.arrow :=
  cokernel.desc X.arrow (cokernel.π Y.arrow) (subobjectQuotientMapCondition hXY)

end QuotientMap

section Subquotients

variable [HasZeroMorphisms C] [HasKernels C] [HasCokernels C]

/-- The subquotient `Y / X`, realized as the kernel subobject of the canonical map
`A / X ⟶ A / Y`. -/
def subobjectSubquotient {A : C} {X Y : Subobject A} (hXY : X ≤ Y) : C :=
  kernelSubobject (subobjectQuotientMap hXY)

/-- The canonical subobject of `A / X` whose underlying object is the subquotient
`subobjectSubquotient hXY = Y / X`. -/
abbrev subobjectSubquotientSubobject {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    Subobject (cokernel X.arrow) :=
  kernelSubobject (subobjectQuotientMap hXY)

end Subquotients

section IsSubquotient

variable [Abelian C]

/-- An object `X` is a subquotient of `Y` if it is isomorphic to `Y₂ / Y₁` for some subobjects
`Y₁ ≤ Y₂ ≤ Y`. -/
def IsSubquotient (X Y : C) : Prop :=
  ∃ (Y₁ Y₂ : Subobject Y) (hY₁Y₂ : Y₁ ≤ Y₂), Nonempty (X ≅ subobjectSubquotient hY₁Y₂)

namespace IsSubquotient

/-- Transport `IsSubquotient` along an isomorphism on the left object. -/
theorem of_iso {X X' Y : C} (e : X ≅ X') :
    IsSubquotient X' Y → IsSubquotient X Y := by
  rintro ⟨Y₁, Y₂, hY₁Y₂, ⟨i⟩⟩
  exact ⟨Y₁, Y₂, hY₁Y₂, ⟨e ≪≫ i⟩⟩

end IsSubquotient

/-- Helper for Chap12 Aux 12 20 2 1: the kernel of a composite is the pullback of the later
kernel along the earlier morphism. -/
private theorem kernelSubobject_comp_eq_pullback {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelSubobject (f ≫ g) = (Subobject.pullback f).obj (kernelSubobject g) := by
  -- Compare both sides by the universal pullback characterization of kernels.
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

/-- Helper for Chap12 Aux 12 20 2 1: every subobject arrow is the kernel of its quotient
projection. -/
private theorem subobject_eq_kernel_cokernel {A : C} (X : Subobject A) :
    X = kernelSubobject (cokernel.π X.arrow) := by
  -- Rewrite the subobject through its image and use exactness of the cokernel row.
  calc
    X = imageSubobject X.arrow := by
      symm
      simpa using (Limits.imageSubobject_mono X.arrow)
    _ = kernelSubobject (cokernel.π X.arrow) := by
      simpa using
        (ShortComplex.exact_iff_image_eq_kernel
          (ShortComplex.mk X.arrow (cokernel.π X.arrow) (cokernel.condition X.arrow))).1
          (ShortComplex.exact_cokernel X.arrow)

/-- Helper for Chap12 Aux 12 20 2 1: pushing a subobject forward along a morphism gives the image
of the composite with the ambient arrow. -/
private theorem exists_obj_eq_imageSubobject_comp {X Y : C} (f : X ⟶ Y) (S : Subobject X) :
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

/-- Helper for Chap12 Aux 12 20 2 1: pushing forward a pullback along an epimorphism recovers the
original subobject. -/
private theorem exists_pullback_eq_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (P : Subobject Y) :
    (Subobject.exists f).obj ((Subobject.pullback f).obj P) = P := by
  have hImage : imageSubobject (((Subobject.pullback f).obj P).arrow ≫ f) = P := by
    -- The pullback arrow is epi, so its image agrees with the original subobject.
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
  -- Compare both subobjects by their arrows into the codomain.
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

/-- Helper for Chap12 Aux 12 20 2 1: quotient maps along a chain of subobjects compose to the
direct quotient map. -/
private theorem subobjectQuotientMap_comp {A : C} {W X Y : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) :
    subobjectQuotientMap hWX ≫ subobjectQuotientMap hXY =
      subobjectQuotientMap (hWX.trans hXY) := by
  -- Compare the two candidates after postcomposing with the epi `A ⟶ A / W`.
  apply (cancel_epi (cokernel.π W.arrow)).1
  simp [subobjectQuotientMap]

/-- Helper for Chap12 Aux 12 20 2 1: pulling the canonical subquotient `Y / X` back along the
quotient map `A ⟶ A / X` recovers the original subobject `Y ⊆ A`. -/
private theorem pullback_subobjectSubquotient_eq_subobject {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    (Subobject.pullback (cokernel.π X.arrow)).obj (subobjectSubquotientSubobject hXY) = Y := by
  -- Rewrite the subquotient as a kernel and then pull it back through the quotient map.
  change (Subobject.pullback (cokernel.π X.arrow)).obj
      (kernelSubobject (subobjectQuotientMap hXY)) = Y
  calc
    (Subobject.pullback (cokernel.π X.arrow)).obj (kernelSubobject (subobjectQuotientMap hXY))
        = kernelSubobject (cokernel.π X.arrow ≫ subobjectQuotientMap hXY) := by
            symm
            exact
              kernelSubobject_comp_eq_pullback (cokernel.π X.arrow) (subobjectQuotientMap hXY)
    _ = kernelSubobject (cokernel.π Y.arrow) := by
          simp [subobjectQuotientMap]
    _ = Y := by
          rw [← subobject_eq_kernel_cokernel Y]

/-- Helper for Chap12 Aux 12 20 2 1: the image of `Y ⟶ A / X` is exactly the canonical
subobject representing `Y / X`. -/
private theorem imageSubobjectToQuotient_eq_subobjectSubquotient {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    imageSubobject (Y.arrow ≫ cokernel.π X.arrow) = subobjectSubquotientSubobject hXY := by
  let π : A ⟶ cokernel X.arrow := cokernel.π X.arrow
  letI : Epi π := by
    dsimp [π]
    infer_instance
  -- Push the pullback description of `Y / X` forward along the quotient map.
  calc
    imageSubobject (Y.arrow ≫ π) = (Subobject.exists π).obj Y := by
      symm
      exact exists_obj_eq_imageSubobject_comp π Y
    _ = (Subobject.exists π).obj
          ((Subobject.pullback π).obj (subobjectSubquotientSubobject hXY)) := by
            rw [pullback_subobjectSubquotient_eq_subobject hXY]
    _ = subobjectSubquotientSubobject hXY := by
          exact exists_pullback_eq_of_epi π (subobjectSubquotientSubobject hXY)

/-- Helper for Chap12 Aux 12 20 2 1: inside the ambient quotient `A / W`, the stage `X / W`
lies below the stage `Y / W`. -/
private theorem subobjectSubquotientSubobject_le {A : C} {W X Y : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) :
    subobjectSubquotientSubobject hWX ≤
      subobjectSubquotientSubobject (show W ≤ Y from hWX.trans hXY) := by
  -- The composite through the larger quotient map vanishes by the chain relation.
  refine le_kernelSubobject _ _ ?_
  rw [← subobjectQuotientMap_comp (hWX := hWX) (hXY := hXY)]
  have hzero := kernelSubobject_arrow_comp (subobjectQuotientMap hWX)
  rw [← Category.assoc, hzero]
  simp

/-- Helper for Chap12 Aux 12 20 2 1: the canonical quotient map from `Y` to `Y / X`. -/
private noncomputable abbrev subobjectToSubquotient {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    (Y : C) ⟶ subobjectSubquotient (A := A) (X := X) (Y := Y) hXY :=
  factorThruKernelSubobject
    (subobjectQuotientMap hXY)
    (Y.arrow ≫ cokernel.π X.arrow)
    (by
      -- The image of `Y` in `A / X` is killed by the quotient map to `A / Y`.
      calc
        (Y.arrow ≫ cokernel.π X.arrow) ≫ subobjectQuotientMap hXY
            = Y.arrow ≫ (cokernel.π X.arrow ≫ subobjectQuotientMap hXY) := by
                simp [Category.assoc]
        _ = Y.arrow ≫ cokernel.π Y.arrow := by
              simp [subobjectQuotientMap]
        _ = 0 := cokernel.condition Y.arrow)

/-- Helper for Chap12 Aux 12 20 2 1: the canonical map `Y ⟶ Y / X` followed by the subobject
inclusion into `A / X` is the usual quotient map out of `Y`. -/
private theorem subobjectToSubquotient_comp_subobjectSubquotientInclusion {A : C}
    {X Y : Subobject A} (hXY : X ≤ Y) :
    subobjectToSubquotient hXY ≫ (subobjectSubquotientSubobject hXY).arrow =
      Y.arrow ≫ cokernel.π X.arrow := by
  -- This is the defining property of the factor-through-kernel map.
  change
    factorThruKernelSubobject
      (subobjectQuotientMap hXY)
      (Y.arrow ≫ cokernel.π X.arrow)
      (by
        calc
          (Y.arrow ≫ cokernel.π X.arrow) ≫ subobjectQuotientMap hXY
              = Y.arrow ≫ (cokernel.π X.arrow ≫ subobjectQuotientMap hXY) := by
                  simp [Category.assoc]
          _ = Y.arrow ≫ cokernel.π Y.arrow := by
                simp [subobjectQuotientMap]
          _ = 0 := cokernel.condition Y.arrow) ≫
        (subobjectSubquotientSubobject hXY).arrow =
      Y.arrow ≫ cokernel.π X.arrow
  rw [factorThruKernelSubobject_comp_arrow]

/-- Helper for Chap12 Aux 12 20 2 1: the canonical inclusion of `Y / X` into `A / X` is a
monomorphism. -/
private instance subobjectSubquotientSubobject_arrow_mono {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) : Mono (subobjectSubquotientSubobject hXY).arrow := by
  change Mono (kernelSubobject (subobjectQuotientMap hXY)).arrow
  infer_instance

/-- Helper for Chap12 Aux 12 20 2 1: inside `Y`, the kernel of `Y ⟶ A / X` is exactly the
subobject `X ⊆ Y`. -/
private theorem kernelSubobject_toQuotient_eq_subobjectOfLE {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    kernelSubobject (Y.arrow ≫ cokernel.π X.arrow) = Subobject.mk (Subobject.ofLE X Y hXY) := by
  -- Compare the two subobjects of `Y` by their arrows.
  apply le_antisymm
  · rw [← Subobject.mk_arrow (kernelSubobject (Y.arrow ≫ cokernel.π X.arrow))]
    refine Subobject.mk_le_mk_of_comm
      (X.factorThru ((kernelSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow ≫ Y.arrow) ?_) ?_
    · have hFactorsKernel : (kernelSubobject (cokernel.π X.arrow)).Factors
          ((kernelSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow ≫ Y.arrow) := by
        rw [kernelSubobject_factors_iff]
        simpa [Category.assoc] using kernelSubobject_arrow_comp (Y.arrow ≫ cokernel.π X.arrow)
      have hXkernel : X = kernelSubobject (cokernel.π X.arrow) := by
        exact subobject_eq_kernel_cokernel X
      simpa [hXkernel] using hFactorsKernel
    · -- Cancel the mono `Y.arrow` to identify the induced morphism with the kernel arrow.
      apply (cancel_mono Y.arrow).1
      simpa [Category.assoc, Subobject.ofLE_arrow] using
        (Subobject.factorThru_arrow X
          ((kernelSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow ≫ Y.arrow) _)
  · rw [← Subobject.mk_arrow (kernelSubobject (Y.arrow ≫ cokernel.π X.arrow))]
    refine Subobject.mk_le_mk_of_comm
      (factorThruKernelSubobject (Y.arrow ≫ cokernel.π X.arrow) (Subobject.ofLE X Y hXY) ?_) ?_
    · simpa [Category.assoc, Subobject.ofLE_arrow] using cokernel.condition X.arrow
    · rw [factorThruKernelSubobject_comp_arrow]

/-- Helper for Chap12 Aux 12 20 2 1: the canonical map `Y ⟶ Y / X` kills the subobject
`X ⊆ Y`. -/
private theorem subobjectToSubquotient_comp_zero {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    Subobject.ofLE X Y hXY ≫ subobjectToSubquotient hXY = 0 := by
  -- Postcompose with the mono inclusion into `A / X` and use the ambient cokernel relation.
  refine (cancel_mono (subobjectSubquotientSubobject hXY).arrow).1 ?_
  calc
    (Subobject.ofLE X Y hXY ≫ subobjectToSubquotient hXY) ≫
        (subobjectSubquotientSubobject hXY).arrow
        = Subobject.ofLE X Y hXY ≫ (Y.arrow ≫ cokernel.π X.arrow) := by
            rw [Category.assoc, subobjectToSubquotient_comp_subobjectSubquotientInclusion]
    _ = X.arrow ≫ cokernel.π X.arrow := by
          simp
    _ = 0 := cokernel.condition X.arrow
    _ = 0 ≫ (subobjectSubquotientSubobject hXY).arrow := by
          simp

/-- Helper for Chap12 Aux 12 20 2 1: the canonical quotient map `Y ⟶ Y / X` is an epimorphism.
-/
private theorem subobjectToSubquotient_epi {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    Epi (subobjectToSubquotient hXY) := by
  let e :
      (imageSubobject (Y.arrow ≫ cokernel.π X.arrow) : C) ≅ subobjectSubquotient hXY :=
    Subobject.isoOfEq _ _ (imageSubobjectToQuotient_eq_subobjectSubquotient hXY)
  have hComp :
      factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫ e.hom =
        subobjectToSubquotient hXY := by
    -- Compare the two quotient maps after composing into `A / X`.
    have he_arrow :
        e.hom ≫ (subobjectSubquotientSubobject hXY).arrow =
          (imageSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow := by
      change
        Subobject.ofLE (imageSubobject (Y.arrow ≫ cokernel.π X.arrow))
            (subobjectSubquotientSubobject hXY)
            (imageSubobjectToQuotient_eq_subobjectSubquotient hXY).le ≫
          (subobjectSubquotientSubobject hXY).arrow =
        (imageSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow
      exact
        Subobject.ofLE_arrow
          (h := (imageSubobjectToQuotient_eq_subobjectSubquotient hXY).le)
    refine (cancel_mono (subobjectSubquotientSubobject hXY).arrow).1 ?_
    calc
      (factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫ e.hom) ≫
          (subobjectSubquotientSubobject hXY).arrow
          = factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫
              (imageSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow := by
                rw [Category.assoc, he_arrow]
      _ = Y.arrow ≫ cokernel.π X.arrow := by
            rw [imageSubobject_arrow_comp]
      _ = subobjectToSubquotient hXY ≫ (subobjectSubquotientSubobject hXY).arrow := by
            symm
            exact subobjectToSubquotient_comp_subobjectSubquotientInclusion hXY
  letI : Epi (factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow)) := inferInstance
  letI : Epi e.hom := inferInstance
  haveI : Epi (factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫ e.hom) := inferInstance
  simpa [hComp]

/-- Helper for Chap12 Aux 12 20 2 1: the canonical sequence
`0 ⟶ X ⟶ Y ⟶ Y / X ⟶ 0` is short exact. -/
private theorem subobjectToSubquotient_shortExact {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    (ShortComplex.mk (Subobject.ofLE X Y hXY) (subobjectToSubquotient hXY)
      (subobjectToSubquotient_comp_zero hXY)).ShortExact := by
  letI : Epi (subobjectToSubquotient hXY) := subobjectToSubquotient_epi hXY
  letI : Mono (subobjectSubquotientSubobject hXY).arrow :=
    subobjectSubquotientSubobject_arrow_mono hXY
  -- Prove exactness by identifying the kernel of `Y ⟶ Y / X` with the inclusion `X ⟶ Y`.
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [ShortComplex.exact_iff_image_eq_kernel]
  have hKernel :
      kernelSubobject (subobjectToSubquotient hXY) = Subobject.mk (Subobject.ofLE X Y hXY) := by
    calc
      kernelSubobject (subobjectToSubquotient hXY)
          = kernelSubobject
              (subobjectToSubquotient hXY ≫ (subobjectSubquotientSubobject hXY).arrow) := by
                have hMono : Mono (subobjectSubquotientSubobject hXY).arrow :=
                  subobjectSubquotientSubobject_arrow_mono hXY
                symm
                exact
                  @Limits.kernelSubobject_comp_mono _ _ _ _ _ (subobjectToSubquotient hXY)
                    inferInstance _ (subobjectSubquotientSubobject hXY).arrow hMono
      _ = kernelSubobject (Y.arrow ≫ cokernel.π X.arrow) := by
            rw [subobjectToSubquotient_comp_subobjectSubquotientInclusion]
      _ = Subobject.mk (Subobject.ofLE X Y hXY) := by
            exact kernelSubobject_toQuotient_eq_subobjectOfLE hXY
  calc
    imageSubobject (Subobject.ofLE X Y hXY) = Subobject.mk (Subobject.ofLE X Y hXY) := by
      simpa using (Limits.imageSubobject_mono (Subobject.ofLE X Y hXY))
    _ = kernelSubobject (subobjectToSubquotient hXY) := by
      symm
      exact hKernel

/-- Helper for Chap12 Aux 12 20 2 1: the canonical map `Y ⟶ Y / X` is a cokernel of the
inclusion `X ⟶ Y`. -/
private noncomputable def subobjectToSubquotient_isCokernel {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    IsColimit (CokernelCofork.ofπ (subobjectToSubquotient hXY)
      (subobjectToSubquotient_comp_zero hXY)) := by
  -- Route correction: the short exact row already identifies the right map as the cokernel,
  -- so no extra coimage transport is needed here.
  exact (subobjectToSubquotient_shortExact hXY).gIsCokernel

/-- Helper for Chap12 Aux 12 20 2 1: any epi `Y ⟶ T` with kernel `X ⊆ Y` identifies `T` with
the canonical subquotient `Y / X`. -/
private theorem subobjectSubquotientIsoOfEpi {A : C} {X Y : Subobject A} (hXY : X ≤ Y)
    {T : C} (f : (Y : C) ⟶ T) [Epi f]
    (hKernel : kernelSubobject f = Subobject.mk (Subobject.ofLE X Y hXY)) :
    Nonempty (subobjectSubquotient hXY ≅ T) := by
  have hFactors : (kernelSubobject f).Factors (Subobject.ofLE X Y hXY) := by
    -- The kernel equality turns the inclusion `X ⟶ Y` into a canonical kernel factorization.
    simpa [hKernel] using
      (Subobject.mk_factors_self (Subobject.ofLE X Y hXY) :
        (Subobject.mk (Subobject.ofLE X Y hXY)).Factors (Subobject.ofLE X Y hXY))
  have hzero : Subobject.ofLE X Y hXY ≫ f = 0 := by
    -- A morphism factoring through the kernel is exactly a morphism annihilated by `f`.
    exact (kernelSubobject_factors_iff f (Subobject.ofLE X Y hXY)).1 hFactors
  have hExact :
      (ShortComplex.mk (Subobject.ofLE X Y hXY) f hzero).Exact := by
    -- The identified kernel shows that the image of `X ⟶ Y` is precisely `kernelSubobject f`.
    rw [ShortComplex.exact_iff_image_eq_kernel]
    calc
      imageSubobject (Subobject.ofLE X Y hXY) = Subobject.mk (Subobject.ofLE X Y hXY) := by
        simpa using (Limits.imageSubobject_mono (Subobject.ofLE X Y hXY))
      _ = kernelSubobject f := by
        simpa using hKernel.symm
  have hShort :
      (ShortComplex.mk (Subobject.ofLE X Y hXY) f hzero).ShortExact := by
    -- Exactness, monicity of the inclusion, and epicity of `f` give the comparison short exact
    -- row on the common fork `X ⟶ Y ⟶ T`.
    exact ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  -- Compare the canonical quotient `Y / X` and the target `T` as cokernels of the same arrow.
  exact ⟨IsColimit.coconePointUniqueUpToIso (subobjectToSubquotient_isCokernel hXY)
    (ShortComplex.ShortExact.gIsCokernel hShort)⟩

/-- Helper for Chap12 Aux 12 20 2 1: an epi from a subobject `Q ≤ S` presents its codomain as a
subquotient of `S`. -/
private theorem isSubquotient_of_epi_of_le {B T : C} {Q S : Subobject B}
    (hQS : Q ≤ S) (f : (Q : C) ⟶ T) [Epi f] :
    IsSubquotient T (S : C) := by
  let QS : Subobject (S : C) := Subobject.mk (Subobject.ofLE Q S hQS)
  let KS : Subobject (S : C) := Subobject.mk ((kernelSubobject f).arrow ≫ Subobject.ofLE Q S hQS)
  have hKSQS : KS ≤ QS := by
    -- The transported kernel stage lands inside the transported upper stage by construction.
    change Subobject.mk ((kernelSubobject f).arrow ≫ Subobject.ofLE Q S hQS) ≤
        Subobject.mk (Subobject.ofLE Q S hQS)
    exact Subobject.mk_le_mk_of_comm (kernelSubobject f).arrow (by simp)
  let eQ : (QS : C) ≅ (Q : C) := Subobject.underlyingIso (Subobject.ofLE Q S hQS)
  let g : (QS : C) ⟶ T := eQ.hom ≫ f
  letI : Epi g := by
    dsimp [g]
    infer_instance
  let eK : (KS : C) ≅ (kernelSubobject f : C) :=
    Subobject.underlyingIso ((kernelSubobject f).arrow ≫ Subobject.ofLE Q S hQS)
  have hKernel' : Subobject.mk (Subobject.ofLE KS QS hKSQS) = kernelSubobject g := by
    -- Route correction: realize both stages directly inside `(S : C)` and compare them after
    -- postcomposing with the mono `QS.arrow`, avoiding any `Subobject.subobjectOrderIso`.
    refine Subobject.mk_eq_of_comm (Subobject.ofLE KS QS hKSQS)
      (eK ≪≫ (kernelSubobjectIsoComp eQ.hom f).symm) ?_
    apply (cancel_mono QS.arrow).1
    calc
      ((eK ≪≫ (kernelSubobjectIsoComp eQ.hom f).symm).hom ≫
          (kernelSubobject g).arrow) ≫
          QS.arrow
          = eK.hom ≫ (((kernelSubobjectIsoComp eQ.hom f).symm).hom ≫
              (kernelSubobject g).arrow) ≫
              QS.arrow := by
                simp [Category.assoc]
      _ = eK.hom ≫ ((kernelSubobject f).arrow ≫ eQ.inv) ≫ QS.arrow := by
            simpa [g, Category.assoc] using
              congrArg (fun k => eK.hom ≫ k ≫ QS.arrow)
                (kernelSubobjectIsoComp_inv_arrow (f := eQ.hom) (g := f))
      _ = eK.hom ≫ (kernelSubobject f).arrow ≫ (eQ.inv ≫ QS.arrow) := by
            simp [Category.assoc]
      _ = eK.hom ≫ (kernelSubobject f).arrow ≫ Subobject.ofLE Q S hQS := by
            rw [Subobject.underlyingIso_arrow]
      _ = KS.arrow := by
            simpa [eK, KS] using
              (Subobject.underlyingIso_hom_comp_eq_mk
                ((kernelSubobject f).arrow ≫ Subobject.ofLE Q S hQS))
      _ = Subobject.ofLE KS QS hKSQS ≫ QS.arrow := by
            rw [Subobject.ofLE_arrow]
  have hKernel : kernelSubobject g = Subobject.mk (Subobject.ofLE KS QS hKSQS) := hKernel'.symm
  obtain ⟨e⟩ := subobjectSubquotientIsoOfEpi hKSQS g hKernel
  have hBase : IsSubquotient (subobjectSubquotient hKSQS) (S : C) := by
    -- The explicit stages `KS ≤ QS ≤ S` already witness the canonical subquotient.
    exact ⟨KS, QS, hKSQS, ⟨Iso.refl _⟩⟩
  -- Transport the canonical subquotient witness across the cokernel comparison isomorphism.
  exact IsSubquotient.of_iso e.symm hBase

/-- Helper for Chap12 Aux 12 20 2 1: the quotient map `Y ⟶ Y / X` already kills the smaller
subobject `W ⊆ Y` whenever `W ≤ X ≤ Y`. -/
private theorem subobjectToSubquotient_comp_zero_of_le_chain {A : C} {W X Y : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) :
    Subobject.ofLE W Y (show W ≤ Y from hWX.trans hXY) ≫ subobjectToSubquotient hXY = 0 := by
  -- Factor the smaller inclusion through `X ⟶ Y` and use that `X` already maps to zero.
  calc
    Subobject.ofLE W Y (show W ≤ Y from hWX.trans hXY) ≫ subobjectToSubquotient hXY
        = (Subobject.ofLE W X hWX ≫ Subobject.ofLE X Y hXY) ≫ subobjectToSubquotient hXY := by
              rw [Subobject.ofLE_comp_ofLE W X Y hWX hXY]
    _ = Subobject.ofLE W X hWX ≫
            (Subobject.ofLE X Y hXY ≫ subobjectToSubquotient hXY) := by
          rw [Category.assoc]
    _ = Subobject.ofLE W X hWX ≫ 0 := by
          rw [subobjectToSubquotient_comp_zero hXY]
    _ = 0 := by
          simp

/-- Helper for Chap12 Aux 12 20 2 1: the quotient map `Y ⟶ Y / X` descends along the quotient
`Y ⟶ Y / W` when `W ≤ X ≤ Y`. -/
private noncomputable def stageToSubobjectSubquotient {A : C} {W X Y : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) :
    subobjectSubquotient (show W ≤ Y from hWX.trans hXY) ⟶ subobjectSubquotient hXY :=
  (subobjectToSubquotient_isCokernel (show W ≤ Y from hWX.trans hXY)).desc <|
    CokernelCofork.ofπ (subobjectToSubquotient hXY)
      (subobjectToSubquotient_comp_zero_of_le_chain hWX hXY)

/-- Helper for Chap12 Aux 12 20 2 1: the descended map from `Y / W` to `Y / X` composes with the
canonical quotient `Y ⟶ Y / W` to recover the map `Y ⟶ Y / X`. -/
private theorem subobjectToSubquotient_comp_stageToSubobjectSubquotient {A : C}
    {W X Y : Subobject A} (hWX : W ≤ X) (hXY : X ≤ Y) :
    subobjectToSubquotient (show W ≤ Y from hWX.trans hXY) ≫
        stageToSubobjectSubquotient hWX hXY =
      subobjectToSubquotient hXY := by
  simpa [stageToSubobjectSubquotient] using
    (subobjectToSubquotient_isCokernel (show W ≤ Y from hWX.trans hXY)).fac
      (CokernelCofork.ofπ (subobjectToSubquotient hXY)
        (subobjectToSubquotient_comp_zero_of_le_chain hWX hXY))
      WalkingParallelPair.one

/-- Helper for Chap12 Aux 12 20 2 1: the descended map `Y / W ⟶ Y / X` is an epimorphism. -/
private theorem stageToSubobjectSubquotient_epi {A : C} {W X Y : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) :
    Epi (stageToSubobjectSubquotient hWX hXY) := by
  letI : Epi (subobjectToSubquotient hXY) := subobjectToSubquotient_epi hXY
  exact epi_of_epi_fac (subobjectToSubquotient_comp_stageToSubobjectSubquotient hWX hXY)

-- Proof sketch: inside the ambient quotient `A / W`, the subquotients `X / W` and `Y / W`
-- define nested subobjects of `Z / W`; the quotient of these two stages recovers `Y / X`.
/-- Chap12 Aux 12 20 2 1: if `W ≤ X ≤ Y ≤ Z` are subobjects of `A`, then the intermediate
quotient `Y / X` is a subquotient of the larger quotient `Z / W`. -/
theorem subobjectSubquotient_isSubquotient_of_le_chain {A : C} {W X Y Z : Subobject A}
    (hWX : W ≤ X) (hXY : X ≤ Y) (hYZ : Y ≤ Z) :
    IsSubquotient (subobjectSubquotient hXY)
      (subobjectSubquotient (hWX.trans <| hXY.trans hYZ)) := by
  let hWY : W ≤ Y := show W ≤ Y from hWX.trans hXY
  let hWZ : W ≤ Z := show W ≤ Z from hWX.trans (hXY.trans hYZ)
  have hEpi : Epi (stageToSubobjectSubquotient hWX hXY) := stageToSubobjectSubquotient_epi hWX hXY
  -- Route correction: package the target as a quotient of the stage `Y / W`, then view that
  -- stage as a subobject of `Z / W`.
  exact
    @isSubquotient_of_epi_of_le C _ _ (cokernel W.arrow) (subobjectSubquotient hXY)
      (subobjectSubquotientSubobject hWY) (subobjectSubquotientSubobject hWZ)
      (subobjectSubquotientSubobject_le hWY hYZ)
      (stageToSubobjectSubquotient hWX hXY) hEpi

end IsSubquotient

end CategoryTheory
