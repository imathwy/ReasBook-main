import StacksProject_2024.Chap12.Definition_12_19_1

open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C]

namespace Limits

/-- In a balanced category, an epimorphism has full image, so its image subobject is the top
subobject. This bridge is used by the strictness criterion for epimorphisms. -/
theorem imageSubobject_eq_top_of_epi [Balanced C] {X Y : C} (g : X ⟶ Y) [Epi g] :
    imageSubobject g = (⊤ : Subobject Y) := by
  let e : X ⟶ imageSubobject g := factorThruImageSubobject g
  letI : Epi (e ≫ (imageSubobject g).arrow) := by
    simpa [e] using (inferInstance : Epi g)
  letI : Epi (imageSubobject g).arrow := epi_of_epi e (imageSubobject g).arrow
  letI : IsIso (imageSubobject g).arrow := isIso_of_mono_of_epi (imageSubobject g).arrow
  exact Subobject.eq_top_of_isIso_arrow (imageSubobject g)

/-
The balanced hypothesis is essential here: the conclusion identifies the image mono of an epi
with an isomorphism, which is exactly the mono+epi-to-iso step provided by `Balanced`.
-/

/-- In a balanced category with equalizers, the image of a composite `f ≫ g` is exactly the image
of `g` restricted to the image subobject of `f`. -/
theorem imageSubobject_comp_eq_imageSubobject_restriction [HasEqualizers C] [Balanced C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
  let h := imageSubobject_comp_le (factorThruImageSubobject f) ((imageSubobject f).arrow ≫ g)
  let φ := Subobject.ofLE _ _ h
  haveI : Epi φ := by
    dsimp [φ, h]
    infer_instance
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  have :
      imageSubobject (factorThruImageSubobject f ≫ (imageSubobject f).arrow ≫ g) =
        imageSubobject ((imageSubobject f).arrow ≫ g) :=
    Subobject.eq_of_comm (asIso φ) (by simp [φ])
  simpa [Category.assoc] using this

end Limits

namespace DecreasingFiltration

variable {X Y : C}

/-- The quotient filtration is computed stagewise by the image of the composite into the target.
-/
theorem quotient_eq_imageSubobject_comp (F : DecreasingFiltration X) (g : X ⟶ Y) (i : ℤ) :
    F.quotient g i = imageSubobject ((F i).arrow ≫ g) := by
  change (Subobject.«exists» g).obj (F i) = _
  apply Subobject.eq_of_comm
    (Subobject.existsIsoImage g (F i) ≪≫ (imageSubobjectIso _).symm)
  calc
    ((Subobject.existsIsoImage g (F i)).hom ≫
        (imageSubobjectIso ((F i).arrow ≫ g)).inv) ≫
        (imageSubobject ((F i).arrow ≫ g)).arrow
        = (Subobject.existsIsoImage g (F i)).hom ≫ image.ι ((F i).arrow ≫ g) := by
            simp [Category.assoc]
    _ = ((Subobject.«exists» g).obj (F i)).arrow := by
          simpa [Subobject.existsIsoImage] using
            (Over.w ((Subobject.existsCompRepresentativeIso g).app (F i)).hom.hom)

end DecreasingFiltration

namespace FilteredObject.Hom

variable [HasPullbacks C]
variable {A B : FilteredObject C}

/-
Source/core/bridge triage for Definition 12.19.3:
- sampled owner declarations in this domain:
  `Subobject.existsIsoImage`, `DecreasingFiltration.quotient`,
  `Limits.imageSubobject_mono`, `Subobject.eq_top_of_isIso_arrow`
- source-facing owner: strictness of a filtered morphism
- core/canonical owner: `FilteredObject.Hom.Strict`
- primitive data: the stagewise image subobject of `(A.filtration i).arrow ≫ f.hom`
- bridge/view: the quotient filtration `A.filtration.quotient f.hom`
- derived API: the quotient-filtration reformulation and the identity map is strict
-/

/-- Definition 12.19.3: a morphism of filtered objects is strict when, for every integer `i`, the
image of the `i`-th filtration step is exactly the intersection of the total image with the
`i`-th filtration step of the target. -/
def Strict (f : A ⟶ B) : Prop :=
  ∀ i : ℤ, imageSubobject ((A.filtration i).arrow ≫ f.hom) = imageSubobject f.hom ⊓ B.filtration i

/-- Bridge/view reformulation of strictness in terms of the quotient filtration. -/
theorem strict_iff_quotient_eq_inf (f : A ⟶ B) :
    Strict f ↔ ∀ i : ℤ, A.filtration.quotient f.hom i = imageSubobject f.hom ⊓ B.filtration i := by
  constructor <;> intro hf i <;>
    simpa [DecreasingFiltration.quotient_eq_imageSubobject_comp] using hf i

/-- The identity morphism of a filtered object is strict. -/
@[simp] theorem strict_id (A : FilteredObject C) : Strict (𝟙 A) := by
  intro i
  change imageSubobject ((A.filtration i).arrow ≫ 𝟙 A.obj) =
      imageSubobject (𝟙 A.obj) ⊓ A.filtration i
  rw [Limits.imageSubobject_mono]
  rw [Limits.imageSubobject_mono, ← Subobject.top_eq_id A.obj]
  simp

end FilteredObject.Hom

end CategoryTheory
