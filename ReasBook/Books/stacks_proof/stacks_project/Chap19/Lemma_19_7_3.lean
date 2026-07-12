import Mathlib
import StacksProject_2024.Chap18.Definition_18_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.IsGrothendieckAbelian
open CategoryTheory.MorphismProperty
open ZeroObject
open Opposite
open scoped CategoryTheory.FreeAbelianSheaf

universe u v w

noncomputable section

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
variable [HasWeakSheafify K AddCommGrpCat]

/-- Helper for Lemma 19.7.3: morphisms from the free abelian sheaf on `X` to `𝒢` identify with
sections of `𝒢` over `X` via the canonical 19.7.2.1 equivalence. -/
abbrev free_representable_hom_equiv (X : C) (𝒢 : Sheaf K AddCommGrpCat) :
    ((ℤ_ (yoneda.obj X))^#[K] ⟶ 𝒢) ≃ 𝒢.obj.obj (op X) :=
  ((((sheafificationAdjunction K AddCommGrpCat).homEquiv _ _).trans
      ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)).trans yonedaEquiv)

/-- Helper for Lemma 19.7.3: the free-representable Hom-sections equivalence is natural in the
codomain sheaf. -/
lemma free_representable_hom_equiv_naturality
    (X : C) {𝒢 ℋ : Sheaf K AddCommGrpCat} (f : 𝒢 ⟶ ℋ)
    (ψ : (ℤ_ (yoneda.obj X))^#[K] ⟶ 𝒢) :
    free_representable_hom_equiv (K := K) X ℋ (ψ ≫ f) =
      f.hom.app (op X) (free_representable_hom_equiv (K := K) X 𝒢 ψ) := by
  rfl

/-- Helper for Lemma 19.7.3: a monomorphism of abelian sheaves is injective on each section
group. -/
lemma sheaf_app_injective_of_mono {𝒢 ℋ : Sheaf K AddCommGrpCat} (f : 𝒢 ⟶ ℋ) [Mono f]
    (X : C) :
    Function.Injective (f.hom.app (op X)) := by
  have hfhom : Mono f.hom := (sheafToPresheaf K AddCommGrpCat).map_mono f
  exact (AddCommGrpCat.mono_iff_injective _).1
    ((NatTrans.mono_iff_mono_app f.hom).1 hfhom (op X))

/-- Helper for Lemma 19.7.3: a proper subobject of a sheaf is missed by some map from a free
abelian sheaf on a representable. -/
lemma exists_free_representable_not_factors_of_ne_top
    {𝒢 : Sheaf K AddCommGrpCat} (A : Subobject 𝒢) (hA : A ≠ ⊤) :
    ∃ (X : C) (ψ : (ℤ_ (yoneda.obj X))^#[K] ⟶ 𝒢), ¬ A.Factors ψ := by
  by_contra h
  have hsurj :
      ∀ X : C,
        Function.Surjective (A.arrow.hom.app (op X)) := by
    intro X s
    -- Use 19.7.2.1 to realize the chosen section as a map from the free representable.
    let ψ : (ℤ_ (yoneda.obj X))^#[K] ⟶ 𝒢 :=
      (free_representable_hom_equiv (K := K) X 𝒢).symm s
    have hfac : A.Factors ψ := by
      by_contra hψ
      exact h ⟨X, ψ, hψ⟩
    let ψA : (ℤ_ (yoneda.obj X))^#[K] ⟶ (A : Sheaf K AddCommGrpCat) := A.factorThru ψ hfac
    refine ⟨free_representable_hom_equiv (K := K) X (A : Sheaf K AddCommGrpCat) ψA, ?_⟩
    -- Naturality identifies postcomposition with `A.arrow` and application of `A.arrow` to
    -- sections.
    calc
      A.arrow.hom.app (op X)
          (free_representable_hom_equiv (K := K) X (A : Sheaf K AddCommGrpCat) ψA) =
          free_representable_hom_equiv (K := K) X 𝒢 (ψA ≫ A.arrow) := by
            simpa using
              (free_representable_hom_equiv_naturality (K := K) X A.arrow ψA).symm
      _ = free_representable_hom_equiv (K := K) X 𝒢 ψ := by
            rw [Subobject.factorThru_arrow]
      _ = s := by
            simp [ψ]
  have hbij :
      ∀ X : C, Function.Bijective (A.arrow.hom.app (op X)) := by
    intro X
    refine ⟨?_, hsurj X⟩
    exact sheaf_app_injective_of_mono (K := K) A.arrow X
  have hIsoHom : IsIso A.arrow.hom := by
    -- Pointwise bijectivity upgrades the underlying natural transformation to an isomorphism.
    refine (NatTrans.isIso_iff_isIso_app _).2 ?_
    intro U
    exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2 (hbij U.unop)
  have hIsoArrow : IsIso A.arrow := by
    -- The sheaf forgetful functor reflects isomorphisms.
    letI : IsIso ((sheafToPresheaf K AddCommGrpCat).map A.arrow) := by
      simpa using hIsoHom
    exact isIso_of_reflects_iso A.arrow (sheafToPresheaf K AddCommGrpCat)
  exact hA ((Subobject.isIso_arrow_iff_eq_top A).1 hIsoArrow)

/-- Helper for Lemma 19.7.3: the kernel of `ψ` lies in the pullback of any subobject along `ψ`.
-/
lemma kernelSubobject_le_pullback
    {X : Sheaf K AddCommGrpCat} {𝒢 : Sheaf K AddCommGrpCat}
    (A : Subobject 𝒢) (ψ : X ⟶ 𝒢) :
    kernelSubobject ψ ≤ (Subobject.pullback ψ).obj A := by
  -- The source route first isolates the formal claim `ker ψ ⊆ ψ⁻¹(A)`.
  apply Subobject.le_of_comm
    (((Subobject.pullback ψ).obj A).factorThru (kernelSubobject ψ).arrow <| by
      -- The kernel arrow composes to zero, and the zero map factors through every subobject.
      rw [pullback_factors_iff]
      simpa [kernelSubobject_arrow_comp] using
        (Subobject.factors_zero :
          A.Factors (0 : (kernelSubobject ψ : Sheaf K AddCommGrpCat) ⟶ 𝒢)))
  -- The chosen comparison morphism is the canonical factorization through the pullback.
  simp [Subobject.factorThru_arrow]

/-- Helper for Lemma 19.7.3: if the subobject-kernel arrow kills `η`, then the ordinary kernel
arrow also kills `η`. -/
lemma kernel_comp_zero_of_kernelSubobject_comp_zero
    {D : Type u} [Category.{v} D] [Abelian D]
    {P Q J : D} (ψ : P ⟶ Q) (η : P ⟶ J)
    (hη : (kernelSubobject ψ).arrow ≫ η = 0) :
    kernel.ι ψ ≫ η = 0 := by
  let e := kernelSubobjectIso ψ
  have hs : (kernelSubobject ψ).arrow = e.hom ≫ kernel.ι ψ := by
    -- Rewrite the subobject kernel arrow through the actual kernel object.
    simp [e]
  have hη' : e.inv ≫ ((kernelSubobject ψ).arrow ≫ η) = e.inv ≫ 0 :=
    congrArg (fun k ↦ e.inv ≫ k) hη
  -- Cancel the isomorphism to recover the zero-composite on `kernel.ι ψ`.
  simpa [hs, Category.assoc] using hη'

/-- Helper for Lemma 19.7.3: the coimage-image comparison for `ψ` identifies the image inclusion
with the coimage factorization map. -/
lemma coimageIsoImage'_hom_comp_image_ι
    {D : Type u} [Category.{v} D] [Abelian D]
    {P Q : D} (ψ : P ⟶ Q) :
    (Abelian.coimageIsoImage' ψ).hom ≫ image.ι ψ = Abelian.factorThruCoimage ψ := by
  -- The abelian `coimageIsoImage'` is built from the canonical image comparison lift.
  simpa [Abelian.coimageIsoImage', Abelian.coimageStrongEpiMonoFactorisation_m] using
    (Abelian.coimageStrongEpiMonoFactorisation ψ).toMonoIsImage.lift_fac
      (Image.monoFactorisation ψ)

/-- Helper for Lemma 19.7.3: after transporting through `coimageIsoImage'`, the cokernel
projection of `kernel.ι ψ` is the usual image factorization map of `ψ`. -/
lemma cokernel_pi_comp_coimageIsoImage'_hom
    {D : Type u} [Category.{v} D] [Abelian D]
    {P Q : D} (ψ : P ⟶ Q) :
    cokernel.π (kernel.ι ψ) ≫ (Abelian.coimageIsoImage' ψ).hom = factorThruImage ψ := by
  refine (cancel_mono (image.ι ψ)).1 ?_
  calc
    (cokernel.π (kernel.ι ψ) ≫ (Abelian.coimageIsoImage' ψ).hom) ≫ image.ι ψ
        = cokernel.π (kernel.ι ψ) ≫ Abelian.factorThruCoimage ψ := by
            -- First replace the abstract comparison isomorphism by the concrete coimage map.
            rw [Category.assoc, coimageIsoImage'_hom_comp_image_ι (ψ := ψ)]
    _ = ψ := by
          -- Then use the cokernel computation rule for the descended map.
          simpa [Abelian.factorThruCoimage] using
            (cokernel.π_desc (kernel.ι ψ) ψ (by simp))
    _ = factorThruImage ψ ≫ image.ι ψ := by
          -- Finally compare with the usual image factorization of `ψ`.
          symm
          exact image.fac ψ

/-- Helper for Lemma 19.7.3: the map to the image subobject agrees with the ordinary image
factorization after transporting along `imageSubobjectIso`. -/
lemma factorThruImageSubobject_comp_imageSubobjectIso_hom
    {D : Type u} [Category.{v} D] [Abelian D]
    {P Q : D} (ψ : P ⟶ Q) :
    factorThruImageSubobject ψ ≫ (imageSubobjectIso ψ).hom = factorThruImage ψ := by
  -- Both morphisms become equal after postcomposing with `image.ι ψ`.
  exact (cancel_mono (image.ι ψ)).1 (by simp [Category.assoc])

/-- Helper for Lemma 19.7.3: transporting the image factorization map back across
`coimageIsoImage'` recovers the cokernel projection of `kernel.ι ψ`. -/
lemma factorThruImage_comp_coimageIsoImage'_inv
    {D : Type u} [Category.{v} D] [Abelian D]
    {P Q : D} (ψ : P ⟶ Q) :
    factorThruImage ψ ≫ (Abelian.coimageIsoImage' ψ).inv = cokernel.π (kernel.ι ψ) := by
  refine (cancel_mono ((Abelian.coimageIsoImage' ψ).hom)).1 ?_
  calc
    (factorThruImage ψ ≫ (Abelian.coimageIsoImage' ψ).inv) ≫
        (Abelian.coimageIsoImage' ψ).hom = factorThruImage ψ := by
          -- Cancel the inverse/hom pair before comparing with the cokernel projection.
          simpa [Category.assoc] using
            congrArg (fun t ↦ factorThruImage ψ ≫ t)
              (Iso.inv_hom_id (Abelian.coimageIsoImage' ψ))
    _ = cokernel.π (kernel.ι ψ) ≫ (Abelian.coimageIsoImage' ψ).hom := by
          rw [cokernel_pi_comp_coimageIsoImage'_hom (ψ := ψ)]

/-- Helper for Lemma 19.7.3: a morphism out of the source of `ψ` that vanishes on `ker ψ`
descends to the image subobject of `ψ`. -/
lemma desc_to_image_of_zero_on_kernel
    {D : Type u} [Category.{v} D] [Abelian D]
    {P Q J : D} (ψ : P ⟶ Q) (η : P ⟶ J)
    (hη : (kernelSubobject ψ).arrow ≫ η = 0) :
    ∃ ηim : (imageSubobject ψ : D) ⟶ J,
      factorThruImageSubobject ψ ≫ ηim = η := by
  have hη' : kernel.ι ψ ≫ η = 0 :=
    kernel_comp_zero_of_kernelSubobject_comp_zero (ψ := ψ) (η := η) hη
  let ηcok : cokernel (kernel.ι ψ) ⟶ J :=
    cokernel.desc (kernel.ι ψ) η hη'
  let ηim' : image ψ ⟶ J := (Abelian.coimageIsoImage' ψ).inv ≫ ηcok
  let ηim : (imageSubobject ψ : D) ⟶ J := (imageSubobjectIso ψ).hom ≫ ηim'
  refine ⟨ηim, ?_⟩
  calc
    factorThruImageSubobject ψ ≫ ηim
        = factorThruImageSubobject ψ ≫ (imageSubobjectIso ψ).hom ≫ ηim' := by
            rfl
    _ = factorThruImage ψ ≫ ηim' := by
          -- Move from the image subobject model to the ordinary image object.
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ ηim')
              (factorThruImageSubobject_comp_imageSubobjectIso_hom (ψ := ψ))
    _ = factorThruImage ψ ≫ (Abelian.coimageIsoImage' ψ).inv ≫ ηcok := by
          rfl
    _ = cokernel.π (kernel.ι ψ) ≫ ηcok := by
          -- Replace the transported image factorization by the cokernel projection.
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ ηcok)
              (factorThruImage_comp_coimageIsoImage'_inv (ψ := ψ))
    _ = η := by
          -- The remaining equality is the defining computation rule for `cokernel.desc`.
          simpa [ηcok] using cokernel.π_desc (kernel.ι ψ) η hη'

/-- Helper for Lemma 19.7.3: the pullback of `A` along `ψ` maps canonically to the pullback of
`A` along the image inclusion of `ψ`. -/
noncomputable def pullback_to_pullback_of_image_arrow
    {X 𝒢 : Sheaf K AddCommGrpCat}
    (A : Subobject 𝒢) (ψ : X ⟶ 𝒢) :
    ((Subobject.pullback ψ).obj A : Sheaf K AddCommGrpCat) ⟶
      ((Subobject.pullback (imageSubobject ψ).arrow).obj A : Sheaf K AddCommGrpCat) :=
  ((Subobject.pullback (imageSubobject ψ).arrow).obj A).factorThru
    (((Subobject.pullback ψ).obj A).arrow ≫ factorThruImageSubobject ψ) <| by
      -- The source route compares the two overlap objects through the factorization of `ψ`
      -- through its image, so first prove that the composite still lands in `A`.
      rw [pullback_factors_iff, Subobject.factors_iff]
      refine ⟨Subobject.pullbackπ ψ A, ?_⟩
      calc
        Subobject.pullbackπ ψ A ≫ A.arrow = ((Subobject.pullback ψ).obj A).arrow ≫ ψ := by
          simpa using (Subobject.isPullback ψ A).w
        _ = (((Subobject.pullback ψ).obj A).arrow ≫ factorThruImageSubobject ψ) ≫
              (imageSubobject ψ).arrow := by
              simp [Category.assoc, imageSubobject_arrow_comp]

/-- Helper for Lemma 19.7.3: the comparison morphism into the image-level pullback is defined by
the expected factorization through `factorThruImageSubobject ψ`. -/
lemma pullback_to_pullback_of_image_arrow_arrow
    {X 𝒢 : Sheaf K AddCommGrpCat}
    (A : Subobject 𝒢) (ψ : X ⟶ 𝒢) :
    pullback_to_pullback_of_image_arrow (K := K) A ψ ≫
        ((Subobject.pullback (imageSubobject ψ).arrow).obj A).arrow =
      ((Subobject.pullback ψ).obj A).arrow ≫ factorThruImageSubobject ψ := by
  -- This is the defining equation of the chosen `factorThru`.
  simp [pullback_to_pullback_of_image_arrow, Subobject.factorThru_arrow]

/-- Helper for Lemma 19.7.3: after passing to the image-level pullback, the `A`-projection agrees
with the original pullback projection along `ψ`. -/
lemma pullback_to_pullback_of_image_arrow_π
    {X 𝒢 : Sheaf K AddCommGrpCat}
    (A : Subobject 𝒢) (ψ : X ⟶ 𝒢) :
    pullback_to_pullback_of_image_arrow (K := K) A ψ ≫
        Subobject.pullbackπ (imageSubobject ψ).arrow A =
      Subobject.pullbackπ ψ A := by
  -- Compare both morphisms after postcomposing with the mono `A.arrow`.
  apply (cancel_mono A.arrow).1
  calc
    (pullback_to_pullback_of_image_arrow (K := K) A ψ ≫
        Subobject.pullbackπ (imageSubobject ψ).arrow A) ≫ A.arrow
        = pullback_to_pullback_of_image_arrow (K := K) A ψ ≫
            (Subobject.pullbackπ (imageSubobject ψ).arrow A ≫ A.arrow) := by
              simp [Category.assoc]
    _ = pullback_to_pullback_of_image_arrow (K := K) A ψ ≫
          (((Subobject.pullback (imageSubobject ψ).arrow).obj A).arrow ≫
            (imageSubobject ψ).arrow) := by
            rw [(Subobject.isPullback (imageSubobject ψ).arrow A).w]
    _ = (pullback_to_pullback_of_image_arrow (K := K) A ψ ≫
          ((Subobject.pullback (imageSubobject ψ).arrow).obj A).arrow) ≫
            (imageSubobject ψ).arrow := by
            simp [Category.assoc]
    _ = (((Subobject.pullback ψ).obj A).arrow ≫ factorThruImageSubobject ψ) ≫
          (imageSubobject ψ).arrow := by
            rw [pullback_to_pullback_of_image_arrow_arrow]
    _ = ((Subobject.pullback ψ).obj A).arrow ≫ ψ := by
          simp [Category.assoc, imageSubobject_arrow_comp]
    _ = Subobject.pullbackπ ψ A ≫ A.arrow := by
          simpa using (Subobject.isPullback ψ A).w.symm

/-- Helper for Lemma 19.7.3: once both candidate maps are precomposed with the comparison from
the source pullback, the original compatibility on `pullback ψ A` transfers to the image-level
pullback. -/
lemma maps_agree_after_precompose_pullback_to_pullback_of_image_arrow
    {X 𝒢 𝒥 : Sheaf K AddCommGrpCat}
    (A : Subobject 𝒢) (ψ : X ⟶ 𝒢)
    (σA : (A : Sheaf K AddCommGrpCat) ⟶ 𝒥)
    (η : X ⟶ 𝒥)
    (ηim : (imageSubobject ψ : Sheaf K AddCommGrpCat) ⟶ 𝒥)
    (hηim : factorThruImageSubobject ψ ≫ ηim = η)
    (hcomm : Subobject.pullbackπ ψ A ≫ σA = ((Subobject.pullback ψ).obj A).arrow ≫ η) :
    pullback_to_pullback_of_image_arrow (K := K) A ψ ≫
        Subobject.pullbackπ (imageSubobject ψ).arrow A ≫ σA =
      pullback_to_pullback_of_image_arrow (K := K) A ψ ≫
        ((Subobject.pullback (imageSubobject ψ).arrow).obj A).arrow ≫ ηim := by
  -- The only remaining gap after this rewrite is to cancel the comparison morphism.
  calc
    pullback_to_pullback_of_image_arrow (K := K) A ψ ≫
        Subobject.pullbackπ (imageSubobject ψ).arrow A ≫ σA
        = Subobject.pullbackπ ψ A ≫ σA := by
            rw [← Category.assoc, pullback_to_pullback_of_image_arrow_π]
    _ = ((Subobject.pullback ψ).obj A).arrow ≫ η := hcomm
    _ = ((Subobject.pullback ψ).obj A).arrow ≫ factorThruImageSubobject ψ ≫ ηim := by
          rw [hηim]
    _ = (pullback_to_pullback_of_image_arrow (K := K) A ψ ≫
          ((Subobject.pullback (imageSubobject ψ).arrow).obj A).arrow) ≫ ηim := by
          rw [pullback_to_pullback_of_image_arrow_arrow]
          simp [Category.assoc]
    _ = pullback_to_pullback_of_image_arrow (K := K) A ψ ≫
          ((Subobject.pullback (imageSubobject ψ).arrow).obj A).arrow ≫ ηim := by
          simp [Category.assoc]

/-- Helper for Lemma 19.7.3: the comparison morphism from the original pullback to the
image-level pullback is itself a pullback of `factorThruImageSubobject ψ`. -/
lemma isPullback_pullback_to_pullback_of_image_arrow
    {X 𝒢 : Sheaf K AddCommGrpCat}
    (A : Subobject 𝒢) (ψ : X ⟶ 𝒢) :
    IsPullback (((Subobject.pullback ψ).obj A).arrow)
      (pullback_to_pullback_of_image_arrow (K := K) A ψ)
      (factorThruImageSubobject ψ)
      (((Subobject.pullback (imageSubobject ψ).arrow).obj A).arrow) := by
  have hright :
      IsPullback (((Subobject.pullback (imageSubobject ψ).arrow).obj A).arrow)
        (Subobject.pullbackπ (imageSubobject ψ).arrow A)
        (imageSubobject ψ).arrow
        A.arrow :=
    (Subobject.isPullback (imageSubobject ψ).arrow A).flip
  have houter :
      IsPullback (((Subobject.pullback ψ).obj A).arrow)
        (pullback_to_pullback_of_image_arrow (K := K) A ψ ≫
          Subobject.pullbackπ (imageSubobject ψ).arrow A)
        (factorThruImageSubobject ψ ≫ (imageSubobject ψ).arrow)
        A.arrow := by
    -- The outer rectangle is the original pullback square for `ψ`.
    simpa [Category.assoc, pullback_to_pullback_of_image_arrow_π, imageSubobject_arrow_comp] using
      (Subobject.isPullback ψ A).flip
  -- Route correction: deduce the left square by vertically unpasting the image-level pullback.
  exact (IsPullback.paste_vert_iff
      (s := hright)
      (e := (pullback_to_pullback_of_image_arrow_arrow (K := K) A ψ).symm)).1 houter

/-- Helper for Lemma 19.7.3: the comparison morphism into the image-level pullback is an
epimorphism because it is the pullback of the epi `factorThruImageSubobject ψ`. -/
lemma epi_pullback_to_pullback_of_image_arrow
    {X 𝒢 : Sheaf K AddCommGrpCat}
    (A : Subobject 𝒢) (ψ : X ⟶ 𝒢) :
    Epi (pullback_to_pullback_of_image_arrow (K := K) A ψ) := by
  -- The structural pullback lemma identifies the comparison map as the second projection.
  simpa using
    (Abelian.epi_snd_of_isLimit
      (f := factorThruImageSubobject ψ)
      (g := (((Subobject.pullback (imageSubobject ψ).arrow).obj A).arrow))
      (isPullback_pullback_to_pullback_of_image_arrow (K := K) A ψ).isLimit)

/-- Helper for Lemma 19.7.3: once the comparison map is known to be epi, the precomposed
compatibility on `pullback ψ A` upgrades to actual agreement on the image-level pullback. -/
lemma maps_agree_on_pullback_of_image_arrow
    {X 𝒢 𝒥 : Sheaf K AddCommGrpCat}
    (A : Subobject 𝒢) (ψ : X ⟶ 𝒢)
    (σA : (A : Sheaf K AddCommGrpCat) ⟶ 𝒥)
    (η : X ⟶ 𝒥)
    (ηim : (imageSubobject ψ : Sheaf K AddCommGrpCat) ⟶ 𝒥)
    (hηim : factorThruImageSubobject ψ ≫ ηim = η)
    (hcomm : Subobject.pullbackπ ψ A ≫ σA = ((Subobject.pullback ψ).obj A).arrow ≫ η) :
    Subobject.pullbackπ (imageSubobject ψ).arrow A ≫ σA =
      ((Subobject.pullback (imageSubobject ψ).arrow).obj A).arrow ≫ ηim := by
  letI : Epi (pullback_to_pullback_of_image_arrow (K := K) A ψ) :=
    epi_pullback_to_pullback_of_image_arrow (K := K) A ψ
  -- Cancel the epi comparison morphism in the already-proved precomposed equality.
  apply (cancel_epi (pullback_to_pullback_of_image_arrow (K := K) A ψ)).1
  simpa [Category.assoc] using
    maps_agree_after_precompose_pullback_to_pullback_of_image_arrow
      (K := K) A ψ σA η ηim hηim hcomm

/-- Helper for Lemma 19.7.3: if the image of `ψ` is contained in `A`, then `ψ` factors through
`A`. -/
lemma factors_of_imageSubobject_le
    {X : Sheaf K AddCommGrpCat} {𝒢 : Sheaf K AddCommGrpCat}
    (ψ : X ⟶ 𝒢) (A : Subobject 𝒢) (h : imageSubobject ψ ≤ A) :
    A.Factors ψ := by
  -- This is the strictness bridge used later: `Im(ψ) ≤ A` forces a factorization through `A`.
  rw [Subobject.factors_iff]
  refine ⟨factorThruImageSubobject ψ ≫ Subobject.ofLE _ _ h, ?_⟩
  -- Rewrite through the image factorization and then through the comparison `Im(ψ) ≤ A`.
  simp [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]

/-- Helper for Lemma 19.7.3: if `ψ` does not factor through `A`, then its image subobject is not
contained in `A`. -/
lemma not_imageSubobject_le_of_not_factors
    {X : Sheaf K AddCommGrpCat} {𝒢 : Sheaf K AddCommGrpCat}
    (A : Subobject 𝒢) (ψ : X ⟶ 𝒢) (hψ : ¬ A.Factors ψ) :
    ¬ imageSubobject ψ ≤ A := by
  intro himage
  exact hψ (factors_of_imageSubobject_le (K := K) (X := X) (𝒢 := 𝒢) (ψ := ψ) (A := A) himage)

/-- Helper for Lemma 19.7.3: if a map `η : X ⟶ 𝒥` extends the pullback restriction of a map
`τ : A ⟶ 𝒥`, then `η` vanishes on `ker ψ`. -/
lemma kernel_comp_zero_of_pullback_extension
    {X 𝒢 𝒥 : Sheaf K AddCommGrpCat}
    (A : Subobject 𝒢) (ψ : X ⟶ 𝒢)
    (τ : (A : Sheaf K AddCommGrpCat) ⟶ 𝒥)
    (η : X ⟶ 𝒥)
    (hη :
      ((Subobject.pullback ψ).obj A).arrow ≫ η =
        Subobject.pullbackπ ψ A ≫ τ) :
    (kernelSubobject ψ).arrow ≫ η = 0 := by
  let hker : kernelSubobject ψ ≤ (Subobject.pullback ψ).obj A :=
    kernelSubobject_le_pullback (K := K) A ψ
  let κ :
      (kernelSubobject ψ : Sheaf K AddCommGrpCat) ⟶
        ((Subobject.pullback ψ).obj A : Sheaf K AddCommGrpCat) :=
    Subobject.ofLE _ _ hker
  have hπzero : κ ≫ Subobject.pullbackπ ψ A = 0 := by
    -- Compare after postcomposing with `A.arrow`, where the pullback equation reduces to
    -- `ker ψ ≫ ψ = 0`.
    apply (cancel_mono A.arrow).1
    calc
      (κ ≫ Subobject.pullbackπ ψ A) ≫ A.arrow
          = κ ≫ (Subobject.pullbackπ ψ A ≫ A.arrow) := by
              simp [Category.assoc]
      _ = κ ≫ (((Subobject.pullback ψ).obj A).arrow ≫ ψ) := by
            rw [(Subobject.isPullback ψ A).w]
      _ = (κ ≫ ((Subobject.pullback ψ).obj A).arrow) ≫ ψ := by
            simp [Category.assoc]
      _ = (kernelSubobject ψ).arrow ≫ ψ := by
            rw [Subobject.ofLE_arrow]
      _ = 0 ≫ A.arrow := by
            simp [kernelSubobject_arrow_comp ψ]
  -- Restrict the extension identity to `ker ψ` and use the vanishing of the pullback projection.
  calc
    (kernelSubobject ψ).arrow ≫ η
        = (κ ≫ ((Subobject.pullback ψ).obj A).arrow) ≫ η := by
            rw [Subobject.ofLE_arrow]
    _ = κ ≫ (((Subobject.pullback ψ).obj A).arrow ≫ η) := by
          simp [Category.assoc]
    _ = κ ≫ (Subobject.pullbackπ ψ A ≫ τ) := by
          rw [hη]
    _ = (κ ≫ Subobject.pullbackπ ψ A) ≫ τ := by
          simp [Category.assoc]
    _ = 0 := by
          simp [hπzero]

/-- Helper for Lemma 19.7.3: a partial extension consists of an intermediate subobject of `𝒢`
containing the image of `i`, together with a morphism to `𝒥` extending `φ` across that
intermediate subobject. -/
structure PartialExtension
    {𝒥 ℱ 𝒢 : Sheaf K AddCommGrpCat}
    (i : ℱ ⟶ 𝒢) [Mono i] (φ : ℱ ⟶ 𝒥) where
  subobject : Subobject 𝒢
  le_subobject : Subobject.mk i ≤ subobject
  map : (subobject : Sheaf K AddCommGrpCat) ⟶ 𝒥
  comm : (Subobject.underlyingIso i).inv ≫ Subobject.ofLE _ _ le_subobject ≫ map = φ

namespace PartialExtensionAux

variable {𝒥 ℱ 𝒢 : Sheaf K AddCommGrpCat}
variable {i : ℱ ⟶ 𝒢} [Mono i] {φ : ℱ ⟶ 𝒥}

/-- Helper for Lemma 19.7.3: `e ≤ e'` means that `e'` extends `e` on the smaller chosen
subobject. -/
def CompatibleLE (e e' : PartialExtension (K := K) i φ) : Prop :=
  ∃ h : e.subobject ≤ e'.subobject, Subobject.ofLE _ _ h ≫ e'.map = e.map

/-- Helper for Lemma 19.7.3: compatible enlargement is the ambient order on partial extensions. -/
instance partialExtensionLE : LE (PartialExtension (K := K) i φ) where
  le := CompatibleLE (K := K) (i := i) (φ := φ)

/-- Helper for Lemma 19.7.3: the comparison identity for the initial partial extension is the
tautological `Subobject.underlyingIso` cancellation. -/
lemma initial_comm :
    (Subobject.underlyingIso i).inv ≫
        Subobject.ofLE _ _ (le_rfl : Subobject.mk i ≤ Subobject.mk i) ≫
        ((Subobject.underlyingIso i).hom ≫ φ) = φ := by
  -- The initial domain is exactly `Subobject.mk i`, so both comparison maps cancel.
  simp [Subobject.ofLE_refl]

/-- Helper for Lemma 19.7.3: the original morphism `φ` is the initial partial extension on the
subobject represented by `i`. -/
def initial : PartialExtension (K := K) i φ :=
  { subobject := Subobject.mk i
    le_subobject := le_rfl
    map := (Subobject.underlyingIso i).hom ≫ φ
    comm := initial_comm (K := K) (i := i) (φ := φ) }

/-- Helper for Lemma 19.7.3: every partial extension is compatibly contained in itself. -/
lemma compatibleLE_rfl (e : PartialExtension (K := K) i φ) :
    CompatibleLE (K := K) (i := i) (φ := φ) e e := by
  refine ⟨le_rfl, ?_⟩
  -- Restricting along the identity subobject map changes nothing.
  simp [Subobject.ofLE_refl]

/-- Helper for Lemma 19.7.3: compatible enlargements compose along nested subobjects. -/
lemma compatibleLE_trans
    {e₁ e₂ e₃ : PartialExtension (K := K) i φ}
    (h₁₂ : CompatibleLE (K := K) (i := i) (φ := φ) e₁ e₂)
    (h₂₃ : CompatibleLE (K := K) (i := i) (φ := φ) e₂ e₃) :
    CompatibleLE (K := K) (i := i) (φ := φ) e₁ e₃ := by
  rcases h₁₂ with ⟨h₁₂sub, h₁₂map⟩
  rcases h₂₃ with ⟨h₂₃sub, h₂₃map⟩
  refine ⟨h₁₂sub.trans h₂₃sub, ?_⟩
  -- Compose the two restriction identities using the canonical `Subobject.ofLE` composition law.
  calc
    Subobject.ofLE _ _ (h₁₂sub.trans h₂₃sub) ≫ e₃.map
        = (Subobject.ofLE _ _ h₁₂sub ≫ Subobject.ofLE _ _ h₂₃sub) ≫ e₃.map := by
            simp [Subobject.ofLE_comp_ofLE]
    _ = Subobject.ofLE _ _ h₁₂sub ≫ (Subobject.ofLE _ _ h₂₃sub ≫ e₃.map) := by
          simp
    _ = Subobject.ofLE _ _ h₁₂sub ≫ e₂.map := by rw [h₂₃map]
    _ = e₁.map := h₁₂map

/-- Helper for Lemma 19.7.3: unpacking a compatible enlargement recovers the expected restriction
identity on the smaller subobject. -/
lemma partial_extension_restrict_eq_of_le
    {e e' : PartialExtension (K := K) i φ}
    (h : CompatibleLE (K := K) (i := i) (φ := φ) e e') :
    ∃ hsub : e.subobject ≤ e'.subobject, Subobject.ofLE _ _ hsub ≫ e'.map = e.map := h

/-- Helper for Lemma 19.7.3: the compatible-extension relation is reflexive and transitive, so it
can be used as the Zorn order on partial extensions. -/
instance partialExtensionPreorder : Preorder (PartialExtension (K := K) i φ) where
  le := CompatibleLE (K := K) (i := i) (φ := φ)
  le_refl := compatibleLE_rfl (K := K) (i := i) (φ := φ)
  le_trans := fun _ _ _ ↦ compatibleLE_trans (K := K) (i := i) (φ := φ)

/-- Helper for Lemma 19.7.3: any partial extension whose chosen subobject is not top can be
strictly enlarged while preserving the extension of `φ`. -/
lemma existsStrictlyLargerPartialExtension
    {C : Type u} [Category.{v} C]
    {K : GrothendieckTopology C}
    [HasWeakSheafify K AddCommGrpCat]
    {𝒥 ℱ 𝒢 : Sheaf K AddCommGrpCat}
    (h𝒥 : ∀ (X : C) {𝒮 : Sheaf K AddCommGrpCat}
      (i : 𝒮 ⟶ (ℤ_ (yoneda.obj X))^#[K]) [Mono i] (φ : 𝒮 ⟶ 𝒥),
        ∃ ψ : (ℤ_ (yoneda.obj X))^#[K] ⟶ 𝒥,
          i ≫ ψ = φ)
    {i : ℱ ⟶ 𝒢} [Mono i] {φ : ℱ ⟶ 𝒥}
    (e : PartialExtension (K := K) i φ) (hne : e.subobject ≠ ⊤) :
    ∃ e' : PartialExtension (K := K) i φ, e ≤ e' ∧ e.subobject < e'.subobject := by
  -- TODO for Lemma 19.7.3: this older strict-enlargement proof should be rebuilt through the
  -- binary-sup/image-descent API from the re-plan, or removed entirely once the separator-based
  -- proof route is completed.
  sorry

/-- Helper for Lemma 19.7.3: once a partial extension reaches the top subobject, its map descends
to an honest extension on the ambient sheaf. -/
lemma extensionOfTopPartialExtension
    {𝒥 ℱ 𝒢 : Sheaf K AddCommGrpCat}
    {i : ℱ ⟶ 𝒢} [Mono i] {φ : ℱ ⟶ 𝒥}
    (e : PartialExtension (K := K) i φ) (htop : e.subobject = ⊤) :
    ∃ ψ : 𝒢 ⟶ 𝒥, i ≫ ψ = φ := by
  cases e with
  | mk subobject le_subobject map comm =>
      cases htop
      letI : IsIso ((⊤ : Subobject 𝒢).arrow) := (Subobject.isIso_arrow_iff_eq_top _).2 rfl
      have hcompare :
          (Subobject.underlyingIso i).inv ≫ Subobject.ofLE _ _ le_subobject =
            i ≫ inv ((⊤ : Subobject 𝒢).arrow) := by
        -- Compare both maps after postcomposing with the top inclusion and cancel the mono.
        apply (cancel_mono ((⊤ : Subobject 𝒢).arrow)).1
        calc
          ((Subobject.underlyingIso i).inv ≫ Subobject.ofLE _ _ le_subobject) ≫
              (⊤ : Subobject 𝒢).arrow
              = (Subobject.underlyingIso i).inv ≫
                  (Subobject.ofLE _ _ le_subobject ≫ (⊤ : Subobject 𝒢).arrow) := by
                    simp [Category.assoc]
          _ = i := by
                calc
                  (Subobject.underlyingIso i).inv ≫
                      (Subobject.ofLE _ _ le_subobject ≫ (⊤ : Subobject 𝒢).arrow)
                      = (Subobject.underlyingIso i).inv ≫ (Subobject.mk i).arrow := by
                          exact congrArg (fun k ↦ (Subobject.underlyingIso i).inv ≫ k)
                            (Subobject.ofLE_arrow le_subobject)
                  _ = i := by
                        simpa using (Subobject.underlyingIso_arrow i)
          _ = (i ≫ inv ((⊤ : Subobject 𝒢).arrow)) ≫ (⊤ : Subobject 𝒢).arrow := by
                simp [Category.assoc]
      refine ⟨inv ((⊤ : Subobject 𝒢).arrow) ≫ map, ?_⟩
      -- Once the top arrow is inverted, the stored commutativity is exactly the desired extension.
      calc
        i ≫ (inv ((⊤ : Subobject 𝒢).arrow) ≫ map)
            = (Subobject.underlyingIso i).inv ≫
                Subobject.ofLE _ _ le_subobject ≫ map := by
                  simpa [Category.assoc] using
                    congrArg (fun k ↦ k ≫ map) hcompare.symm
        _ = φ := comm

end PartialExtensionAux

end

end CategoryTheory

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
variable [HasWeakSheafify K AddCommGrpCat]

local instance : Abelian (Sheaf K AddCommGrpCat) := sheafIsAbelian

/-- Helper for Lemma 19.7.3: the additive group `ℤ` is a separator in `AddCommGrpCat`. -/
lemma intIsSeparator :
    IsSeparator (AddCommGrpCat.of ℤ) := by
  rw [isSeparator_def]
  intro A B f g hfg
  simp only [AddCommGrpCat.ext_iff, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    Function.comp_apply, forall_eq'] at hfg ⊢
  intro x
  specialize hfg
    (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y : ℤ ↦ y • x) (fun y z ↦ by simp only [add_smul])))
    1
  simpa using hfg

/-- Helper for Lemma 19.7.3: extending maps from subobjects of a fixed object `U` is equivalent
to the right lifting property against a morphism into a chosen zero object. -/
lemma subobjectExtension_iff_rlpGeneratingMonomorphismsZero
    {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasZeroObject D]
    {U I : D} :
    (∀ (M : Subobject U) (φ : (M : D) ⟶ I), ∃ ψ : U ⟶ I, M.arrow ≫ ψ = φ) ↔
      (generatingMonomorphisms U).rlp (0 : I ⟶ 0) := by
  constructor
  · intro h A B g hg
    rcases hg with ⟨M⟩
    -- A lift for the square against `M.arrow` is exactly an extension of the top map.
    refine ⟨fun {f b} _ ↦ ?_⟩
    rcases h M f with ⟨l, hl⟩
    refine ⟨⟨{ l := l, fac_left := hl, fac_right := ?_ }⟩⟩
    exact (isZero_zero D).eq_of_tgt _ _
  · intro h M φ
    -- Repackage `φ` as a square against the chosen zero-target map `p`.
    let _ : HasLiftingProperty M.arrow (0 : I ⟶ 0) := h _ ⟨M⟩
    let sq : CommSq φ M.arrow (0 : I ⟶ 0) 0 := ⟨by simp⟩
    exact ⟨sq.lift, sq.fac_left⟩

/-- Helper for Lemma 19.7.3: in a Grothendieck abelian category, it is enough to extend maps from
subobjects of a separator in order to prove injectivity. -/
lemma injective_iff_separatorSubobjectExtension
    {D : Type u} [Category.{v} D] [Abelian D] [IsGrothendieckAbelian.{w} D]
    {U I : D} (hU : IsSeparator U) :
    Injective I ↔
      ∀ (M : Subobject U) (φ : (M : D) ⟶ I), ∃ ψ : U ⟶ I, M.arrow ≫ ψ = φ := by
  -- Normalize injectivity through the canonical zero-map lifting criterion for a separator.
  rw [injective_iff_rlp_monomorphisms_zero,
    ← generatingMonomorphisms_rlp hU,
    ← subobjectExtension_iff_rlpGeneratingMonomorphismsZero (D := D) (U := U) (I := I)]

/-- Helper for Lemma 19.7.3: the family of free abelian sheaves on representables is separating,
because the established Hom-sections equivalence detects equality sectionwise. -/
lemma freeAbelianRepresentableFamilyIsSeparating :
    ObjectProperty.IsSeparating
      (.ofObj (fun X : C ↦ ((ℤ_ (yoneda.obj X))^#[K] : Sheaf K AddCommGrpCat))) := by
  intro 𝒢 ℋ f g hfg
  ext X x
  let ψ : ((ℤ_ (yoneda.obj X.unop))^#[K] : Sheaf K AddCommGrpCat) ⟶ 𝒢 :=
    (free_representable_hom_equiv (K := K) X.unop 𝒢).symm x
  have hψ : ψ ≫ f = ψ ≫ g := hfg _ (ObjectProperty.ofObj_apply _ X.unop) ψ
  -- Compare the two composites on the representing object to recover equality of sections.
  calc
    f.hom.app X x
        = free_representable_hom_equiv (K := K) X.unop ℋ (ψ ≫ f) := by
            symm
            simpa [ψ] using
              free_representable_hom_equiv_naturality (K := K) X.unop f ψ
    _ = free_representable_hom_equiv (K := K) X.unop ℋ (ψ ≫ g) := by rw [hψ]
    _ = g.hom.app X x := by
          simpa [ψ] using
            free_representable_hom_equiv_naturality (K := K) X.unop g ψ

/-- Helper for Lemma 19.7.3: the componentwise extension hypothesis for the free abelian sheaves
on representables should be repackaged as the separator-level extension property used by the
Grothendieck-category injectivity criterion. -/
lemma separatorSubobjectExtensionOfRepresentableFreeAbelianExtension
    (𝒥 : Sheaf K AddCommGrpCat)
    (h𝒥 : ∀ (X : C) {𝒮 : Sheaf K AddCommGrpCat}
      (i : 𝒮 ⟶ (ℤ_ (yoneda.obj X))^#[K]) [Mono i] (φ : 𝒮 ⟶ 𝒥),
        ∃ ψ : (ℤ_ (yoneda.obj X))^#[K] ⟶ 𝒥,
          i ≫ ψ = φ) :
    ∃ U : Sheaf K AddCommGrpCat, IsSeparator U ∧
      ∀ (M : Subobject U) (φ : (M : Sheaf K AddCommGrpCat) ⟶ 𝒥), ∃ ψ : U ⟶ 𝒥, M.arrow ≫ ψ = φ := by
  -- Route correction: replace the local partial-extension/Zorn construction by the canonical
  -- Grothendieck-category criterion once the family of free representable abelian sheaves has been
  -- bundled into a single separator object.
  let U : Sheaf K AddCommGrpCat := ∐ fun X : C ↦
    ((ℤ_ (yoneda.obj X))^#[K] : Sheaf K AddCommGrpCat)
  have hU : IsSeparator U := by
    -- The chosen coproduct packages the separating family of free representable abelian sheaves
    -- into one separator object.
    simpa [U] using
      (CategoryTheory.ObjectProperty.IsSeparating.isSeparator_coproduct
        (f := fun X : C ↦ ((ℤ_ (yoneda.obj X))^#[K] : Sheaf K AddCommGrpCat))
        (freeAbelianRepresentableFamilyIsSeparating (K := K)))
  refine ⟨U, hU, ?_⟩
  intro M φ
  -- TODO for Lemma 19.7.3: the remaining blocker is the coherent extension step on subobjects of
  -- the separator coproduct. The finite-support factorization route should first reduce `M` to
  -- finite subcoproduct stages, prove extension there, and then compare the assembled map against
  -- `φ` on `M` using the separating family of free representables.
  sorry

/- Domain-style sampling for Lemma 19.7.3:
- primary domain: injective objects in the category of abelian sheaves on a site, tested on the
  source-facing family of free abelian sheaves on representables;
- sampled owner declarations:
  `Injective`,
  `Injective.factors`,
  `freeAbelianSheaf`,
  `(ℤ_ (yoneda.obj X))^#[K]`;
- best owner abstraction: the canonical class `Injective`; the free abelian sheaves on
  representables are the source-facing test objects, not a second owner abstraction;
- primitive data: an object `X`, a monomorphism `i : 𝒮 ⟶ (ℤ_ (yoneda.obj X))^#`, and a morphism
  `φ : 𝒮 ⟶ 𝒥`;
- derived API: the restricted `Injective.factors`-style extension morphism `ψ` across `i`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project test family `(ℤ_ (yoneda.obj X))^#`;
- `core/canonical`: `Injective` and its extension owner `Injective.factors`;
- `bridge/view`: this theorem, which proves injectivity from the source-facing extension test. -/

-- Proof sketch: argue by Baer's criterion as in More on Algebra, Lemma 15.54.1. For a strict
-- monomorphism of abelian sheaves and a map into `𝒥`, choose an object `X` and a section of the
-- larger sheaf not coming from the smaller one; the associated map from `Z_X^#`, formalized as
-- the free abelian sheaf on `yoneda.obj X`, and the assumed extension property produce a strictly
-- larger intermediate subsheaf to which the map extends, contradicting maximality.
/-- Lemma 19.7.3: if every morphism from an abelian subsheaf of `Z_X^#`, formalized as a
monomorphism into `(ℤ_ (yoneda.obj X))^#[K]`,
extends to `𝒥`, then `𝒥` is an injective abelian sheaf on `(C, K)`. -/
@[stacks 01DO]
theorem injective_of_representable_free_abelian_extension_property
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
    [HasWeakSheafify K AddCommGrpCat]
    (𝒥 : Sheaf K AddCommGrpCat)
    (h𝒥 : ∀ (X : C) {𝒮 : Sheaf K AddCommGrpCat}
      (i : 𝒮 ⟶ (ℤ_ (yoneda.obj X))^#[K]) [Mono i] (φ : 𝒮 ⟶ 𝒥),
        ∃ ψ : (ℤ_ (yoneda.obj X))^#[K] ⟶ 𝒥,
          i ≫ ψ = φ) :
    Injective 𝒥 := by
  letI : EssentiallySmall.{max u v} C := CategoryTheory.essentiallySmallSelf (C := C)
  -- Install the standard Grothendieck-abelian structure on abelian sheaves over the site.
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall K AddCommGrpCat.{max u v}
  rcases
      separatorSubobjectExtensionOfRepresentableFreeAbelianExtension (K := K) 𝒥 h𝒥 with
    ⟨U, hU, hExt⟩
  -- The separator-level extension property is exactly the local injectivity criterion.
  exact (injective_iff_separatorSubobjectExtension (K := K) (D := Sheaf K AddCommGrpCat) hU).2 hExt

end

end CategoryTheory
