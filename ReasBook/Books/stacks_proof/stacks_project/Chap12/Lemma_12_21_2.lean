import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap12.Definition_12_19_3
import StacksProject_2024.Chap12.Definition_12_21_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

-- Proof sketch: the kernel of a composite is characterized by the universal property of the
-- pullback of the second kernel along the first map.
/-- The kernel of a composite `f ≫ g` is the inverse image of `Ker(g)` under `f`. -/
private theorem kernelSubobject_comp_eq_pullback {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelSubobject (f ≫ g) = (Subobject.pullback f).obj (kernelSubobject g) := by
  apply le_antisymm
  · refine Subobject.le_of_comm
      (((Subobject.pullback f).obj (kernelSubobject g)).factorThru (kernelSubobject (f ≫ g)).arrow ?_)
      ?_
    · exact (pullback_factors_iff f (kernelSubobject g) (kernelSubobject (f ≫ g)).arrow).2 <| by
        rw [kernelSubobject_factors_iff, Category.assoc]
        exact kernelSubobject_arrow_comp (f ≫ g)
    · exact Subobject.factorThru_arrow _ _ _
  · exact le_kernelSubobject _ _ <| by
      have hpb := (Subobject.isPullback f (kernelSubobject g)).w
      rw [← reassoc_of% hpb, kernelSubobject_arrow_comp, comp_zero]

namespace ExactCouple

local notation "ExactCoupleCat" => @ExactCouple C _ _

/- Domain-style sampling for Lemma 12.21.2:
- primary domain: exact couples in an abelian category, viewed through the kernel and image
  subobjects of the three exact short complexes and of the page-one differential;
- sampled owner declarations in the immediate chapter/mathlib ecosystem:
  `ExactCouple.d`,
  `ExactCouple.page`,
  `ShortComplex.exact_iff_image_eq_kernel`,
  `ExactCouple.derived`;
- best owner abstraction: the chapter owner `ExactCouple`, with the page-one differential and the
  derived exact couple recovered from `ExactCouple.d`, `ExactCouple.page`, and
  `ExactCouple.derived`;
- primitive data: an exact couple `T` with maps `α`, `f`, `g`;
- derived API in this file: the kernel/image comparisons for `d = f ≫ g` and the canonical recall
  that the derived data are already owned upstream by `ExactCouple.derived`;
- source/core/bridge triage:
  `source-facing`: the textbook identifications in Lemma 12.21.2;
  `core/canonical`: `ExactCouple`, `ShortComplex.exact_iff_image_eq_kernel`,
  `kernelSubobject`, `imageSubobject`, and `ExactCouple.derived`;
  `bridge/view`: the pullback/image descriptions of `kernelSubobject T.d` and
  `imageSubobject T.d`.

This file should therefore expose only the source-facing equalities and reuse the existing exact
couple owners, rather than introducing parallel derived-data wrappers. -/
variable (T : ExactCoupleCat)

-- Proof sketch: exactness of `A --α--> A --g--> E` identifies `imageSubobject α` with
-- `kernelSubobject g` via `ShortComplex.exact_iff_image_eq_kernel`.
/-- The image of `α` agrees with the kernel of `g`. -/
theorem image_alpha_eq_kernel_g :
    imageSubobject T.α = kernelSubobject T.g :=
  (ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk T.α T.g T.α_comp_g)).mp T.exact_α_g

-- Proof sketch: exactness of `A --g--> E --f--> A` identifies `imageSubobject g` with
-- `kernelSubobject f`.
/-- The image of `g` agrees with the kernel of `f`. -/
theorem image_g_eq_kernel_f :
    imageSubobject T.g = kernelSubobject T.f :=
  (ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk T.g T.f T.g_comp_f)).mp T.exact_g_f

-- Proof sketch: exactness of `E --f--> A --α--> A` identifies `imageSubobject f` with
-- `kernelSubobject α`.
/-- The image of `f` agrees with the kernel of `α`. -/
theorem image_f_eq_kernel_alpha :
    imageSubobject T.f = kernelSubobject T.α :=
  (ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk T.f T.α T.f_comp_α)).mp T.exact_f_α

-- Proof sketch: identify `Ker(d)` with the pullback of `Ker(g)` along `f` by unraveling the
-- kernel of `d = f ≫ g`.
/-- Lemma 12.21.2 (1): the kernel of `d = f ≫ g` is the inverse image of `Ker(g)` under `f`. -/
@[stacks 011R]
theorem kernel_differential_eq_preimage_kernel_g :
    kernelSubobject T.d = (Subobject.pullback T.f).obj (kernelSubobject T.g) :=
  kernelSubobject_comp_eq_pullback T.f T.g

-- Proof sketch: replace `kernelSubobject g` by `imageSubobject α` using exactness of
-- `A --α--> A --g--> E`, then pull back along `f`.
/-- Lemma 12.21.2 (2): the inverse image of `Ker(g)` under `f` equals the inverse image of
`Im(α)` under `f`. -/
@[stacks 011R]
theorem preimage_kernel_g_eq_preimage_image_alpha :
    (Subobject.pullback T.f).obj (kernelSubobject T.g) =
      (Subobject.pullback T.f).obj (imageSubobject T.α) :=
  congrArg ((Subobject.pullback T.f).obj) (image_alpha_eq_kernel_g T).symm

-- Proof sketch: the image of `d = f ≫ g` is the image of the restriction of `g` to
-- `imageSubobject f`.
/-- Lemma 12.21.2 (3): the image of `d = f ≫ g` is the image of `g` applied to `Im(f)`. -/
@[stacks 011R]
theorem image_differential_eq_image_restricted_g_on_image_f :
    imageSubobject T.d = imageSubobject ((imageSubobject T.f).arrow ≫ T.g) :=
  Limits.imageSubobject_comp_eq_imageSubobject_restriction T.f T.g

-- Proof sketch: replace `imageSubobject f` by `kernelSubobject α` using exactness of
-- `E --f--> A --α--> A`, then compare the induced images under `g`.
/-- Lemma 12.21.2 (4): the image of `g` applied to `Im(f)` equals the image of `g` applied to
`Ker(α)`. -/
@[stacks 011R]
theorem image_restricted_g_on_image_f_eq_image_restricted_g_on_kernel_alpha
    :
    imageSubobject ((imageSubobject T.f).arrow ≫ T.g) =
      imageSubobject ((kernelSubobject T.α).arrow ≫ T.g) :=
  congrArg (fun S : Subobject T.A ↦ imageSubobject (S.arrow ≫ T.g)) (image_f_eq_kernel_alpha T)

/- Lemma 12.21.2 (5): the derived data
`(A', E', α', f', g') = (Im(α), Ker(d) / Im(d), α', f', g')`
form an exact couple. In this chapter the owner construction is the canonical declaration
`ExactCouple.derived`, built from `ExactCouple.d` and `ExactCouple.page`. -/
recall ExactCouple.derived

end ExactCouple
end CategoryTheory
