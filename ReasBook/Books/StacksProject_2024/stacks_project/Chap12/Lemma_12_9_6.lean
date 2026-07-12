import Mathlib
import StacksProject_2024.Chap12.Aux_12_20_2_1
import StacksProject_2024.Chap12.Lemma_12_9_4
import StacksProject_2024.Chap12.Lemma_12_9_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Subobject

variable {A : C}

/- Domain triage:
- primary domain: Jordan-Hölder theory for the subobject lattice of an object in an abelian
  category;
- sampled owner API:
  `JordanHolderLattice`,
  `CompositionSeries.jordan_holder`,
  `JordanHolderModule.instJordanHolderLattice`,
  `subobjectSubquotient`;
- `core/canonical`: the ambient owner is `JordanHolderLattice (Subobject A)`;
- `bridge/view`: `iso_iff_nonempty_subobjectSubquotient_iso` and `CompositionSeries.factor`
  translate the generic Jordan-Hölder owner back to canonical subquotients `Y / X`.
-/

/-- Helper for Lemma 12.9.6: the kernel of a composite is the pullback of the second kernel
along the first morphism. -/
private theorem kernelSubobject_comp_eq_pullback {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelSubobject (f ≫ g) = (Subobject.pullback f).obj (kernelSubobject g) := by
  -- Compare both sides by the universal property of the pullback description of the kernel.
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

/-- Helper for Lemma 12.9.6: a subobject arrow is the kernel of its cokernel projection. -/
private theorem subobject_eq_kernel_cokernel (X : Subobject A) :
    X = kernelSubobject (cokernel.π X.arrow) := by
  -- Rewrite the subobject as the image of its mono arrow, then invoke exactness of a cokernel.
  calc
    X = imageSubobject X.arrow := by
      symm
      simpa using (Limits.imageSubobject_mono X.arrow)
    _ = kernelSubobject (cokernel.π X.arrow) := by
      simpa using
        (ShortComplex.exact_iff_image_eq_kernel
          (ShortComplex.mk X.arrow (cokernel.π X.arrow) (cokernel.condition X.arrow))).1
          (ShortComplex.exact_cokernel X.arrow)

/-- Helper for Lemma 12.9.6: applying `Subobject.exists` to a subobject recovers the image of
its arrow followed by the ambient morphism. -/
private theorem exists_obj_eq_imageSubobject_comp {X Y : C} (f : X ⟶ Y) (S : Subobject X) :
    (Subobject.exists f).obj S = imageSubobject (S.arrow ≫ f) := by
  -- Both subobjects are represented by the same image mono inside the codomain.
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

/-- Helper for Lemma 12.9.6: pushing forward a pullback along an epimorphism recovers the
original subobject. -/
private theorem exists_pullback_eq_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (P : Subobject Y) :
    (Subobject.exists f).obj ((Subobject.pullback f).obj P) = P := by
  have hImage : imageSubobject (((Subobject.pullback f).obj P).arrow ≫ f) = P := by
    -- The pullback projection is epi, so the image of the pulled-back arrow is the original
    -- subobject.
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

/-- Helper for Lemma 12.9.6: inside `A / X`, the kernel-model subquotient `Y / X` pulls back to
the original subobject `Y ⊆ A`. -/
private theorem pullback_subobjectSubquotient_eq_subobject {X Y : Subobject A} (hXY : X ≤ Y) :
    (Subobject.pullback (cokernel.π X.arrow)).obj (subobjectSubquotientSubobject hXY) = Y := by
  -- Rewrite the canonical subquotient as a kernel and pull it back along the quotient map.
  change (Subobject.pullback (cokernel.π X.arrow)).obj
      (kernelSubobject (subobjectQuotientMap hXY)) = Y
  calc
    (Subobject.pullback (cokernel.π X.arrow)).obj (kernelSubobject (subobjectQuotientMap hXY))
        = kernelSubobject (cokernel.π X.arrow ≫ subobjectQuotientMap hXY) := by
            symm
            exact kernelSubobject_comp_eq_pullback (cokernel.π X.arrow) (subobjectQuotientMap hXY)
    _ = kernelSubobject (cokernel.π Y.arrow) := by
          simp [subobjectQuotientMap]
    _ = Y := by
          rw [← subobject_eq_kernel_cokernel Y]

/-- Helper for Lemma 12.9.6: the image of `Y ⟶ A / X` is exactly the canonical subobject
representing `Y / X` inside `A / X`. -/
theorem image_subobject_toQuotient_eq_subobjectSubquotient {X Y : Subobject A}
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

-- Proof sketch: a cover `X ⋖ Y` means the interval `[X, Y]` has exactly two points, and in an
-- abelian category the subobjects of the canonical subquotient `Y / X` correspond to this
-- interval. Hence the quotient is simple.
private theorem simple_subobjectSubquotient_of_covBy {X Y : Subobject A} (h : X ⋖ Y) :
    Simple (subobjectSubquotient (CovBy.le h)) := by
  let hXY : X ≤ Y := CovBy.le h
  let π : A ⟶ cokernel X.arrow := cokernel.π X.arrow
  let e :
      Subobject (subobjectSubquotient hXY) ≃o Set.Iic (subobjectSubquotientSubobject hXY) :=
    Subobject.subobjectOrderIso (subobjectSubquotientSubobject hXY)
  have hQuotient_ne_bot :
      subobjectSubquotientSubobject hXY ≠ (⊥ : Subobject (cokernel X.arrow)) := by
    intro hbot
    have hZero : Y.arrow ≫ π = 0 := by
      have hImage :
          imageSubobject (Y.arrow ≫ π) = (⊥ : Subobject (cokernel X.arrow)) := by
        simpa [π] using
          (image_subobject_toQuotient_eq_subobjectSubquotient (A := A) (X := X) (Y := Y) hXY).trans
            hbot
      have hArrow : (imageSubobject (Y.arrow ≫ π)).arrow = 0 := by
        rw [hImage]
        simp
      -- If the image is zero, then the quotient map kills all of `Y`.
      calc
        Y.arrow ≫ π =
            factorThruImageSubobject (Y.arrow ≫ π) ≫
              (imageSubobject (Y.arrow ≫ π)).arrow := by
              symm
              exact imageSubobject_arrow_comp (Y.arrow ≫ π)
        _ = factorThruImageSubobject (Y.arrow ≫ π) ≫ 0 := by
              rw [hArrow]
        _ = 0 := by
              simp
    have hYX : Y ≤ X := by
      -- The ambient quotient map `A ⟶ A / X` has kernel exactly `X`.
      have hXkernel : X = kernelSubobject π := by
        simpa [π] using subobject_eq_kernel_cokernel X
      rw [hXkernel]
      exact le_kernelSubobject _ _ hZero
    exact (CovBy.lt h).not_ge hYX
  haveI : Nontrivial (Set.Iic (subobjectSubquotientSubobject hXY)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro hEq
    exact hQuotient_ne_bot <| by
      simpa [eq_comm] using congrArg Subtype.val hEq
  refine (simple_iff_subobject_isSimpleOrder _).2 <|
    (OrderIso.isSimpleOrder_iff e).2 ?_
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro P hPbot
  let R : Subobject A := (Subobject.pullback π).obj (P : Subobject (cokernel X.arrow))
  have hXleR : X ≤ R := by
    have hExistsX :
        (Subobject.exists π).obj X = (⊥ : Subobject (cokernel X.arrow)) := by
      calc
        (Subobject.exists π).obj X = imageSubobject (X.arrow ≫ π) := by
          exact exists_obj_eq_imageSubobject_comp π X
        _ = ⊥ := by
          simp [π]
    -- Route correction: use the `exists ⊣ pullback` Galois connection instead of an explicit
    -- pullback-lift term, so the kernel inclusion is carried by the adjunction.
    exact ((Subobject.existsPullbackAdj π).gc X (P : Subobject (cokernel X.arrow))).1 <| by
      simpa [hExistsX]
  have hRleY : R ≤ Y := by
    -- Pulling back a subobject of `Y / X` stays inside `Y`.
    have hPullback_le :
        R ≤ (Subobject.pullback π).obj (subobjectSubquotientSubobject hXY) := by
      exact
        (Functor.monotone (Subobject.pullback π))
          (show (P : Subobject (cokernel X.arrow)) ≤ subobjectSubquotientSubobject hXY from P.2)
    rw [pullback_subobjectSubquotient_eq_subobject (A := A) (X := X) (Y := Y) hXY] at hPullback_le
    exact hPullback_le
  have hReq : R = X ∨ R = Y := h.eq_or_eq hXleR hRleY
  cases hReq with
  | inl hRX =>
      have hPzero : (P : Subobject (cokernel X.arrow)) = ⊥ := by
      -- When the pullback is exactly `X`, pushing forward gives the zero subobject of `A / X`.
        calc
          (P : Subobject (cokernel X.arrow)) = (Subobject.exists π).obj R := by
            symm
            simpa [R] using exists_pullback_eq_of_epi π (P : Subobject (cokernel X.arrow))
          _ = (Subobject.exists π).obj X := by
                rw [hRX]
          _ = imageSubobject (X.arrow ≫ π) := by
                exact exists_obj_eq_imageSubobject_comp π X
          _ = ⊥ := by
                simp [π]
      exact (hPbot <| Subtype.ext hPzero).elim
  | inr hRY =>
      -- If the pullback is `Y`, the subobject must be the whole canonical quotient.
      apply Subtype.ext
      calc
        (P : Subobject (cokernel X.arrow)) = (Subobject.exists π).obj R := by
          symm
          simpa [R] using exists_pullback_eq_of_epi π (P : Subobject (cokernel X.arrow))
        _ = (Subobject.exists π).obj Y := by
              rw [hRY]
        _ = imageSubobject (Y.arrow ≫ π) := by
              exact exists_obj_eq_imageSubobject_comp π Y
        _ = subobjectSubquotientSubobject hXY := by
              simpa [π] using
                image_subobject_toQuotient_eq_subobjectSubquotient (A := A) (X := X) (Y := Y) hXY

-- Proof sketch: this is the second isomorphism theorem for subquotients in an abelian category.
private theorem subquotient_sup_iso_subquotient_inf (X Y : Subobject A) :
    Nonempty (subobjectSubquotient (show X ≤ X ⊔ Y from _root_.le_sup_left) ≅
      subobjectSubquotient (show X ⊓ Y ≤ Y from _root_.inf_le_right)) := by
  -- TODO: identify both quotients with the image/coimage of `Y ⟶ A / X`:
  -- `(X ⊔ Y)/X` is its image in `A / X`, while `Y/(X ⊓ Y)` is its coimage because the kernel is
  -- `X ⊓ Y`. Then apply `Abelian.coimageIsoImage'`.
  sorry

open scoped Classical in
/-- The Jordan-Hölder lattice structure on the subobject lattice of an object in an abelian
category, with factors given by canonical subquotients. -/
instance : JordanHolderLattice (Subobject A) where
  IsMaximal := (· ⋖ ·)
  lt_of_isMaximal := CovBy.lt
  sup_eq_of_isMaximal hxz hyz := WCovBy.sup_eq hxz.wcovBy hyz.wcovBy
  isMaximal_inf_left_of_isMaximal_sup := by
    intro X Y hX hY
    -- TODO: prove the subobject-lattice cover step directly, or expose the missing modular-lattice
    -- bridge for `Subobject A`.
    sorry
  Iso X Y := Nonempty
    (subobjectSubquotient (show X.1 ⊓ X.2 ≤ X.2 from _root_.inf_le_right) ≅
      subobjectSubquotient (show Y.1 ⊓ Y.2 ≤ Y.2 from _root_.inf_le_right))
  iso_symm := fun ⟨e⟩ ↦ ⟨e.symm⟩
  iso_trans := fun ⟨e₁⟩ ⟨e₂⟩ ↦ ⟨e₁.trans e₂⟩
  second_iso := by
    intro X Y h
    simpa [inf_eq_left.2 (_root_.le_sup_left : X ≤ X ⊔ Y), inf_assoc] using
      subquotient_sup_iso_subquotient_inf X Y

/-- For comparable pairs of subobjects, the `Iso` relation in the Jordan-Hölder lattice structure
is exactly isomorphism of the canonical subquotients. -/
theorem iso_iff_nonempty_subobjectSubquotient_iso {X₁ X₂ Y₁ Y₂ : Subobject A}
    (hX : X₁ ≤ X₂) (hY : Y₁ ≤ Y₂) :
    JordanHolderLattice.Iso (X₁, X₂) (Y₁, Y₂) ↔
      Nonempty (subobjectSubquotient hX ≅ subobjectSubquotient hY) := by
  change Nonempty
      (subobjectSubquotient (show X₁ ⊓ X₂ ≤ X₂ from _root_.inf_le_right) ≅
        subobjectSubquotient (show Y₁ ⊓ Y₂ ≤ Y₂ from _root_.inf_le_right)) ↔
    Nonempty (subobjectSubquotient hX ≅ subobjectSubquotient hY)
  simp [inf_eq_left.2 hX, inf_eq_left.2 hY]

end Subobject

end CategoryTheory

namespace CompositionSeries

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : C}

/-- The `i`-th successive canonical subquotient in a composition series of subobjects. -/
noncomputable abbrev factor (s : CompositionSeries (Subobject A)) (i : Fin s.length) :=
  subobjectSubquotient (s.step i).le

-- Proof sketch: apply `Subobject.simple_subobjectSubquotient_of_covBy` to the `i`-th cover
-- relation.
/-- Each successive canonical subquotient `s (i + 1) / s i` of a composition series in
`Subobject A` is simple. -/
theorem factor_simple (s : CompositionSeries (Subobject A)) (i : Fin s.length) :
    Simple (s.factor i) := by
  exact Subobject.simple_subobjectSubquotient_of_covBy (s.step i)

end CompositionSeries

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

-- This is the exact order-theoretic owner construction used for finite-length modules, applied to
-- the well-founded subobject lattice of an Artinian and Noetherian object.
/-- If an object in an abelian category is Artinian and Noetherian, then its subobject lattice
admits a composition series from `0` to the whole object. -/
theorem exists_compositionSeries_of_isArtinianObject_isNoetherianObject (A : C)
    [IsArtinianObject A] [IsNoetherianObject A] :
    ∃ s : CompositionSeries (Subobject A), s.head = ⊥ ∧ s.last = ⊤ := by
  obtain ⟨f, f0, n, hn⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (Subobject A)
  exact ⟨⟨n, fun i ↦ f i, fun i ↦ hn.2 i i.2⟩, f0.eq_bot, hn.1.eq_top⟩

/-- Helper for Lemma 12.9.6: the ambient quotient map `Y ⟶ A / X` factors through the kernel
model of `Y / X`. -/
private theorem subobjectSubquotientProjection_condition {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    (Y.arrow ≫ cokernel.π X.arrow) ≫ subobjectQuotientMap hXY = 0 := by
  -- Expand the canonical quotient map `A / X ⟶ A / Y` and use the cokernel relation for `Y`.
  simp [subobjectQuotientMap, Category.assoc]

/-- Helper for Lemma 12.9.6: the image-factor quotient map `Y ⟶ Y / X` landing in the canonical
subquotient object. -/
private noncomputable abbrev subobjectToSubquotient {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    (Y : C) ⟶ subobjectSubquotient hXY :=
  factorThruKernelSubobject (subobjectQuotientMap hXY) (Y.arrow ≫ cokernel.π X.arrow)
    (subobjectSubquotientProjection_condition hXY)

/-- Helper for Lemma 12.9.6: the quotient map `Y ⟶ Y / X` followed by the canonical inclusion into
`A / X` is the ambient quotient map `Y ⟶ A / X`. -/
private theorem subobjectToSubquotient_comp_subobjectSubquotientInclusion {A : C}
    {X Y : Subobject A} (hXY : X ≤ Y) :
    subobjectToSubquotient hXY ≫ (subobjectSubquotientSubobject hXY).arrow =
      Y.arrow ≫ cokernel.π X.arrow := by
  -- The quotient map is defined by the universal kernel factorization of `Y ⟶ A / X`.
  change
    factorThruKernelSubobject (subobjectQuotientMap hXY) (Y.arrow ≫ cokernel.π X.arrow)
      (subobjectSubquotientProjection_condition hXY) ≫
        (subobjectSubquotientSubobject hXY).arrow =
      Y.arrow ≫ cokernel.π X.arrow
  rw [Limits.factorThruKernelSubobject_comp_arrow]

/-- Helper for Lemma 12.9.6: the canonical inclusion of `Y / X` into `A / X` is mono. -/
private instance subobjectSubquotientSubobject_arrow_mono {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) : Mono (subobjectSubquotientSubobject hXY).arrow := by
  change Mono (kernelSubobject (subobjectQuotientMap hXY)).arrow
  infer_instance

/-- Helper for Lemma 12.9.6: the kernel of `Y ⟶ A / X` is exactly the subobject `X ⊆ Y`. -/
private theorem kernel_subobject_toQuotient_eq_subobject_ofLE {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    kernelSubobject (Y.arrow ≫ cokernel.π X.arrow) = Subobject.mk (Subobject.ofLE X Y hXY) := by
  -- Route correction: compare both subobjects of `Y` through their arrows, instead of pushing the
  -- whole goal through a pullback transport in `Subobject Y`.
  apply le_antisymm
  · rw [← Subobject.mk_arrow (kernelSubobject (Y.arrow ≫ cokernel.π X.arrow))]
    -- The kernel arrow lands in `X` because it is killed by the quotient `A ⟶ A / X`.
    refine Subobject.mk_le_mk_of_comm
      (X.factorThru ((kernelSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow ≫ Y.arrow) ?_) ?_
    · have hFactorsKernel : (kernelSubobject (cokernel.π X.arrow)).Factors
          ((kernelSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow ≫ Y.arrow) := by
        rw [kernelSubobject_factors_iff]
        simpa [Category.assoc] using kernelSubobject_arrow_comp (Y.arrow ≫ cokernel.π X.arrow)
      have hXkernel : X = kernelSubobject (cokernel.π X.arrow) := by
        calc
          X = imageSubobject X.arrow := by
            symm
            simpa using (Limits.imageSubobject_mono X.arrow)
          _ = kernelSubobject (cokernel.π X.arrow) := by
              simpa using
                (ShortComplex.exact_iff_image_eq_kernel
                  (ShortComplex.mk X.arrow (cokernel.π X.arrow)
                    (cokernel.condition X.arrow))).1
                  (ShortComplex.exact_cokernel X.arrow)
      simpa [hXkernel] using hFactorsKernel
    · -- Cancel the mono `Y.arrow` to identify the induced morphism with the kernel inclusion.
      apply (cancel_mono Y.arrow).1
      simpa [Category.assoc, Subobject.ofLE_arrow] using
        (Subobject.factorThru_arrow X
          ((kernelSubobject (Y.arrow ≫ cokernel.π X.arrow)).arrow ≫ Y.arrow) _)
  · rw [← Subobject.mk_arrow (kernelSubobject (Y.arrow ≫ cokernel.π X.arrow))]
    -- Conversely, the inclusion `X ⟶ Y` is killed by `Y ⟶ A / X`, so it factors through the
    -- kernel subobject.
    refine Subobject.mk_le_mk_of_comm
      (factorThruKernelSubobject (Y.arrow ≫ cokernel.π X.arrow) (Subobject.ofLE X Y hXY) ?_) ?_
    · simpa [Category.assoc, Subobject.ofLE_arrow] using cokernel.condition X.arrow
    · rw [factorThruKernelSubobject_comp_arrow]

/-- Helper for Lemma 12.9.6: the canonical quotient map `Y ⟶ Y / X` kills the subobject
`X ⊆ Y`. -/
private theorem subobject_to_subquotient_comp_zero {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    Subobject.ofLE X Y hXY ≫ subobjectToSubquotient hXY = 0 := by
  -- Postcompose with the mono inclusion `Y / X ↪ A / X` and use the ambient cokernel relation.
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

/-- Helper for Lemma 12.9.6: the canonical quotient map `Y ⟶ Y / X` is an epimorphism. -/
private theorem subobjectToSubquotient_epi {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    Epi (subobjectToSubquotient hXY) := by
  let e :
      (imageSubobject (Y.arrow ≫ cokernel.π X.arrow) : C) ≅ subobjectSubquotient hXY :=
    Subobject.isoOfEq _ _ (Subobject.image_subobject_toQuotient_eq_subobjectSubquotient hXY)
  have hComp :
      factorThruImageSubobject (Y.arrow ≫ cokernel.π X.arrow) ≫ e.hom =
        subobjectToSubquotient hXY := by
    -- Compare the two quotients after composing with the mono inclusion into `A / X`.
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
  rw [← hComp]
  infer_instance

/-- Helper for Lemma 12.9.6: the canonical sequence `0 → X → Y → Y / X → 0` is short exact. -/
private theorem subobject_to_subquotient_shortExact {A : C} {X Y : Subobject A} (hXY : X ≤ Y) :
    (ShortComplex.mk (Subobject.ofLE X Y hXY) (subobjectToSubquotient hXY)
      (subobject_to_subquotient_comp_zero hXY)).ShortExact := by
  letI : Epi (subobjectToSubquotient hXY) := subobjectToSubquotient_epi hXY
  letI : Mono (subobjectSubquotientSubobject hXY).arrow :=
    subobjectSubquotientSubobject_arrow_mono hXY
  -- Route correction: prove exactness entirely inside `Subobject Y`, then use the new epi bridge.
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [ShortComplex.exact_iff_image_eq_kernel]
  have hKernel :
      kernelSubobject (subobjectToSubquotient hXY) = Subobject.mk (Subobject.ofLE X Y hXY) := by
    -- Postcomposing with the mono inclusion into `A / X` does not change the kernel.
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
            exact kernel_subobject_toQuotient_eq_subobject_ofLE hXY
  -- The left map is mono, so its image is exactly the source subobject.
  calc
    imageSubobject (Subobject.ofLE X Y hXY) = Subobject.mk (Subobject.ofLE X Y hXY) := by
      simpa using (Limits.imageSubobject_mono (Subobject.ofLE X Y hXY))
    _ = kernelSubobject (subobjectToSubquotient hXY) := by
      symm
      exact hKernel

/-- Helper for Lemma 12.9.6: a simple object is both Artinian and Noetherian. -/
private theorem simple_isArtinianObject_and_isNoetherianObject {B : C} (hB : Simple B) :
    IsArtinianObject B ∧ IsNoetherianObject B := by
  letI : IsSimpleOrder (Subobject B) := (simple_iff_subobject_isSimpleOrder B).1 hB
  constructor
  · -- In a two-point subobject order, a strictly descending chain would already fail by stage `2`.
    rw [isArtinianObject_iff_not_strictAnti B]
    intro f hf
    have h1 : f 1 = (⊥ : Subobject B) ∨ f 1 = ⊤ := IsSimpleOrder.eq_bot_or_eq_top (f 1)
    cases h1 with
    | inl hbot =>
        have h21 : f 2 < f 1 := hf (show 1 < 2 by decide)
        exact (not_lt_bot (a := f 2)) (by simpa [hbot] using h21)
    | inr htop =>
        have h10 : f 1 < f 0 := hf (show 0 < 1 by decide)
        exact (not_top_lt (a := f 0)) (by simpa [htop] using h10)
  · -- The same two-point argument rules out strictly ascending chains as well.
    rw [isNoetherianObject_iff_not_strictMono B]
    intro f hf
    have h1 : f 1 = (⊥ : Subobject B) ∨ f 1 = ⊤ := IsSimpleOrder.eq_bot_or_eq_top (f 1)
    cases h1 with
    | inl hbot =>
        have h01 : f 0 < f 1 := hf (show 0 < 1 by decide)
        exact (not_lt_bot (a := f 0)) (by simpa [hbot] using h01)
    | inr htop =>
        have h12 : f 1 < f 2 := hf (show 1 < 2 by decide)
        exact (not_top_lt (a := f 2)) (by simpa [htop] using h12)

/-- Helper for Lemma 12.9.6: every stage of a composition series from `⊥` to `⊤` is Artinian and
Noetherian. -/
private theorem stage_isArtinianObject_and_isNoetherianObject (A : C)
    (s : CompositionSeries (Subobject A)) (hhead : s.head = ⊥) :
    ∀ i : Fin (s.length + 1), IsArtinianObject (s i : C) ∧ IsNoetherianObject (s i : C) := by
  -- Follow the source proof: start at the zero stage, then pass from `s i` to `s (i + 1)` using
  -- the short exact row with simple quotient `s.factor i`.
  intro i
  refine Fin.induction ?_ ?_ i
  · have hzero : s (0 : Fin (s.length + 1)) = ⊥ := by
      simpa using hhead
    let eZero : (s (0 : Fin (s.length + 1)) : C) ≅ ((⊥ : Subobject A) : C) :=
      Subobject.isoOfEq _ _ hzero
    have hBotZero : IsZero (((⊥ : Subobject A) : C)) :=
      (isZero_zero C).of_iso Subobject.botCoeIsoZero
    constructor
    · -- Transport the zero-object Artinian statement to the initial stage of the series.
      have hArtBot : IsArtinianObject (((⊥ : Subobject A) : C)) :=
        isArtinianObject_of_isZero hBotZero
      simpa [ObjectProperty.is_iff] using
        (isArtinianObject.prop_iff_of_iso eZero).2
          (by simpa [ObjectProperty.is_iff] using hArtBot)
    · -- The same transport gives the Noetherian base case.
      have hNoethBot : IsNoetherianObject (((⊥ : Subobject A) : C)) :=
        isNoetherianObject_of_isZero hBotZero
      simpa [ObjectProperty.is_iff] using
        (isNoetherianObject.prop_iff_of_iso eZero).2
          (by simpa [ObjectProperty.is_iff] using hNoethBot)
  · intro j hj
    have hShort : (ShortComplex.mk (Subobject.ofLE (s (Fin.castSucc j)) (s (Fin.succ j))
        (s.step j).le) (subobjectToSubquotient (s.step j).le)
        (subobject_to_subquotient_comp_zero (s.step j).le)).ShortExact :=
      subobject_to_subquotient_shortExact (s.step j).le
    have hFactor :
        IsArtinianObject (s.factor j) ∧ IsNoetherianObject (s.factor j) :=
      simple_isArtinianObject_and_isNoetherianObject (CompositionSeries.factor_simple s j)
    constructor
    · -- Lemma 12.9.4 upgrades the induction hypothesis across the successor short exact row.
      exact (ShortComplex.isArtinianObject_iff_of_shortExact hShort).2 ⟨hj.1, hFactor.1⟩
    · -- Lemma 12.9.5 does the same for Noetherianity.
      exact (ShortComplex.isNoetherianObject_iff_of_shortExact hShort).2 ⟨hj.2, hFactor.2⟩

-- Proof sketch: if `A` is Artinian and Noetherian, refine a maximal strict chain in `Subobject A`
-- from `⊥` to `⊤` into a composition series. Conversely, such a composition series bounds strict
-- ascending and descending chains of subobjects.
/-- Lemma 12.9.6: an object of an abelian category is Artinian and Noetherian if and only if it
admits a composition series of subobjects from `0` to itself. -/
lemma isArtinianObject_and_isNoetherianObject_iff_exists_compositionSeries (A : C) :
    (IsArtinianObject A ∧ IsNoetherianObject A) ↔
      ∃ s : CompositionSeries (Subobject A), s.head = ⊥ ∧ s.last = ⊤ := by
  constructor
  · rintro ⟨hArtinian, hNoetherian⟩
    letI : IsArtinianObject A := hArtinian
    letI : IsNoetherianObject A := hNoetherian
    exact exists_compositionSeries_of_isArtinianObject_isNoetherianObject A
  · rintro ⟨s, hhead, hlast⟩
    have hLastStage : IsArtinianObject (s.last : C) ∧ IsNoetherianObject (s.last : C) := by
      simpa using stage_isArtinianObject_and_isNoetherianObject A s hhead (Fin.last s.length)
    let eTop : (s.last : C) ≅ A :=
      Subobject.isoOfEq _ _ hlast ≪≫ asIso ((⊤ : Subobject A).arrow)
    constructor
    · -- Evaluate the stage induction at the terminal subobject and transport along `s.last = ⊤`.
      simpa [ObjectProperty.is_iff] using (isArtinianObject.prop_iff_of_iso eTop).1
        (by simpa [ObjectProperty.is_iff] using hLastStage.1)
    · -- The same top-stage transport yields the Noetherian statement.
      simpa [ObjectProperty.is_iff] using (isNoetherianObject.prop_iff_of_iso eTop).1
        (by simpa [ObjectProperty.is_iff] using hLastStage.2)

end CategoryTheory
