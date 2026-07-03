import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Idempotents
open Limits

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/- Domain-style sampling for Lemma 12.4.3:
- primary domain: idempotent completeness of preadditive categories via kernels and cokernels of
  split morphisms;
- sampled owner API:
  `IsIdempotentComplete`,
  `isIdempotentComplete_iff_idempotents_have_kernels`,
  `isIdempotentComplete_iff_opposite`,
  `CokernelCofork.IsColimit.ofπOp`;
- source/core/bridge triage:
  `core/canonical`: `IsIdempotentComplete C`;
  `source-facing`: countable products/coproducts together with existence of kernels/cokernels for
  split epis/monos;
  `bridge/view`: the countable-product swindle realizing a kernel of an idempotent as the kernel
  of a split epimorphism on `X^ℕ`.

Primitive data are only the ambient preadditive category, the countable product/coproduct
hypothesis, and the existence of kernels/cokernels for split morphisms. The swindle endomorphisms
on the countable power are internal proof data, while the public API of this file remains the
owner-level bridge to `IsIdempotentComplete C`.
-/
private abbrev powerFamily (X : C) : ℕ → C := fun _ ↦ X

section CountableProducts

variable [HasCountableProducts C]

private noncomputable abbrev countablePower (X : C) : C :=
  ∏ᶜ powerFamily X

private noncomputable abbrev proj (X : C) (n : ℕ) :
    countablePower X ⟶ X :=
  Pi.π (powerFamily X) n

private noncomputable def leftShift (X : C) :
    countablePower X ⟶ countablePower X :=
  Pi.lift fun n ↦ proj X (n + 1)

private noncomputable def rightShift (X : C) :
    countablePower X ⟶ countablePower X :=
  Pi.lift fun
    | 0 => (0 : countablePower X ⟶ X)
    | n + 1 => proj X n

private noncomputable def coordMap {X Y : C} (f : X ⟶ Y) :
    countablePower X ⟶ countablePower Y :=
  Limits.Pi.map (fun _ : ℕ ↦ f)

omit [Preadditive C] in
private lemma leftShift_comp_proj (X : C) (n : ℕ) :
    leftShift X ≫ proj X n = proj X (n + 1) := by
  rw [leftShift, Pi.lift_π]

private lemma rightShift_comp_proj_zero (X : C) :
    rightShift X ≫ proj X 0 = 0 := by
  rw [rightShift, Pi.lift_π]

private lemma rightShift_comp_proj_succ (X : C) (n : ℕ) :
    rightShift X ≫ proj X (n + 1) = proj X n := by
  rw [rightShift, Pi.lift_π]

omit [Preadditive C] in
private lemma coordMap_comp_proj {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    coordMap f ≫ proj Y n = proj X n ≫ f := by
  simp [coordMap, proj]

private noncomputable def swindleMap {X : C} (p : X ⟶ X) :
    countablePower X ⟶ countablePower X :=
  coordMap p + leftShift X ≫ coordMap (𝟙 X - p)

private noncomputable def swindleSection {X : C} (p : X ⟶ X) :
    countablePower X ⟶ countablePower X :=
  coordMap p + rightShift X ≫ coordMap (𝟙 X - p)

private lemma swindleMap_comp_proj {X : C} (p : X ⟶ X) (n : ℕ) :
    swindleMap p ≫ proj X n = proj X n ≫ p + proj X (n + 1) ≫ (𝟙 X - p) := by
  rw [swindleMap, Preadditive.add_comp]
  rw [coordMap_comp_proj]
  rw [Category.assoc, coordMap_comp_proj, ← Category.assoc, leftShift_comp_proj]

private lemma swindleSection_comp_proj_zero {X : C} (p : X ⟶ X) :
    swindleSection p ≫ proj X 0 = proj X 0 ≫ p := by
  rw [swindleSection, Preadditive.add_comp]
  rw [coordMap_comp_proj]
  rw [Category.assoc, coordMap_comp_proj, ← Category.assoc, rightShift_comp_proj_zero]
  simp

private lemma swindleSection_comp_proj_succ {X : C} (p : X ⟶ X) (n : ℕ) :
    swindleSection p ≫ proj X (n + 1) = proj X (n + 1) ≫ p + proj X n ≫ (𝟙 X - p) := by
  rw [swindleSection, Preadditive.add_comp]
  rw [coordMap_comp_proj]
  rw [Category.assoc, coordMap_comp_proj, ← Category.assoc, rightShift_comp_proj_succ]

private lemma swindleSection_comp_swindleMap {X : C} (p : X ⟶ X) (hp : p ≫ p = p) :
    swindleSection p ≫ swindleMap p = 𝟙 (countablePower X) := by
  ext n
  cases n with
  | zero =>
      rw [Category.assoc, swindleMap_comp_proj, Preadditive.comp_add]
      rw [← Category.assoc, swindleSection_comp_proj_zero]
      rw [← Category.assoc, swindleSection_comp_proj_succ]
      simp [hp, Category.assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  | succ n =>
      rw [Category.assoc, swindleMap_comp_proj, Preadditive.comp_add]
      rw [← Category.assoc, swindleSection_comp_proj_succ]
      rw [← Category.assoc, swindleSection_comp_proj_succ]
      simp [hp, Category.assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

private noncomputable def liftToPower {X W : C} (k : W ⟶ X) :
    W ⟶ countablePower X :=
  Pi.lift fun
    | 0 => k
    | _ + 1 => 0

private lemma liftToPower_comp_proj_zero {X W : C} (k : W ⟶ X) :
    liftToPower k ≫ proj X 0 = k := by
  rw [liftToPower, Pi.lift_π]

private lemma liftToPower_comp_proj_succ {X W : C} (k : W ⟶ X) (n : ℕ) :
    liftToPower k ≫ proj X (n + 1) = 0 := by
  rw [liftToPower, Pi.lift_π]

private lemma liftToPower_comp_swindleMap {X W : C} (p : X ⟶ X) (k : W ⟶ X)
    (hk : k ≫ p = 0) :
    liftToPower k ≫ swindleMap p = 0 := by
  ext n
  cases n with
  | zero =>
      rw [Category.assoc, swindleMap_comp_proj, Preadditive.comp_add]
      rw [← Category.assoc, liftToPower_comp_proj_zero]
      rw [← Category.assoc, liftToPower_comp_proj_succ]
      simp [hk]
  | succ n =>
      rw [Category.assoc, swindleMap_comp_proj, Preadditive.comp_add]
      rw [← Category.assoc, liftToPower_comp_proj_succ]
      rw [← Category.assoc, liftToPower_comp_proj_succ]
      simp

private lemma firstCoord_comp_p_eq_zero {X W : C} (p : X ⟶ X) (hp : p ≫ p = p)
    (u : W ⟶ countablePower X)
    (hu : u ≫ swindleMap p = 0) :
    (u ≫ proj X 0) ≫ p = 0 := by
  have h0 : u ≫ swindleMap p ≫ proj X 0 = 0 := by
    simpa [Category.assoc] using congrArg (fun g ↦ g ≫ proj X 0) hu
  have h0' : (u ≫ proj X 0) ≫ p + (u ≫ proj X 1) ≫ (𝟙 X - p) = 0 := by
    simpa [Category.assoc, swindleMap_comp_proj] using h0
  have hp' := congrArg (fun g ↦ g ≫ p) h0'
  simpa [hp, Category.assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp'

private lemma succCoord_comp_one_sub_eq_zero {X W : C} (p : X ⟶ X) (hp : p ≫ p = p)
    (u : W ⟶ countablePower X)
    (hu : u ≫ swindleMap p = 0) (n : ℕ) :
    (u ≫ proj X (n + 1)) ≫ (𝟙 X - p) = 0 := by
  have hn : u ≫ swindleMap p ≫ proj X n = 0 := by
    simpa [Category.assoc] using congrArg (fun g ↦ g ≫ proj X n) hu
  have hn' : (u ≫ proj X n) ≫ p + (u ≫ proj X (n + 1)) ≫ (𝟙 X - p) = 0 := by
    simpa [Category.assoc, swindleMap_comp_proj] using hn
  have hq := congrArg (fun g ↦ g ≫ (𝟙 X - p)) hn'
  simpa [hp, Category.assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hq

private lemma succCoord_comp_p_eq_zero {X W : C} (p : X ⟶ X) (hp : p ≫ p = p)
    (u : W ⟶ countablePower X)
    (hu : u ≫ swindleMap p = 0) (n : ℕ) :
    (u ≫ proj X (n + 1)) ≫ p = 0 := by
  have hn : u ≫ swindleMap p ≫ proj X (n + 1) = 0 := by
    simpa [Category.assoc] using congrArg (fun g ↦ g ≫ proj X (n + 1)) hu
  have hn' : (u ≫ proj X (n + 1)) ≫ p + (u ≫ proj X (n + 2)) ≫ (𝟙 X - p) = 0 := by
    simpa [Category.assoc, swindleMap_comp_proj] using hn
  have hp' := congrArg (fun g ↦ g ≫ p) hn'
  simpa [hp, Category.assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp'

private lemma succCoord_eq_zero {X W : C} (p : X ⟶ X) (hp : p ≫ p = p)
    (u : W ⟶ countablePower X)
    (hu : u ≫ swindleMap p = 0) (n : ℕ) :
    u ≫ proj X (n + 1) = 0 := by
  have hp' := succCoord_comp_p_eq_zero p hp u hu n
  have hq := succCoord_comp_one_sub_eq_zero p hp u hu n
  calc
    u ≫ proj X (n + 1) = (u ≫ proj X (n + 1)) ≫ p + (u ≫ proj X (n + 1)) ≫ (𝟙 X - p) := by
      simp [Category.assoc, sub_eq_add_neg, add_left_comm, add_comm]
    _ = 0 := by simp [hp', hq]

private theorem hasKernel_idempotent_of_splitEpiKernels
    (hkernel : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [IsSplitEpi f], HasKernel f)
    (X : C) (p : X ⟶ X) (hp : p ≫ p = p) : HasKernel p := by
  let f : countablePower X ⟶ countablePower X := swindleMap p
  let s : countablePower X ⟶ countablePower X := swindleSection p
  have hs : s ≫ f = 𝟙 (countablePower X) := by
    simpa [f, s] using swindleSection_comp_swindleMap p hp
  letI : IsSplitEpi f := IsSplitEpi.mk' ⟨s, hs⟩
  letI : HasKernel f := hkernel f
  refine ⟨⟨KernelFork.ofι (kernel.ι f ≫ proj X 0) ?_, ?_⟩⟩
  · exact firstCoord_comp_p_eq_zero p hp (kernel.ι f) (kernel.condition f)
  · refine KernelFork.IsLimit.ofι (kernel.ι f ≫ proj X 0)
        (firstCoord_comp_p_eq_zero p hp (kernel.ι f) (kernel.condition f))
        (fun {W} k hk ↦ kernel.lift f (liftToPower k) (by simpa [f] using liftToPower_comp_swindleMap p k hk))
        (fun {W} k hk ↦ by
          change kernel.lift f (liftToPower k)
              (by simpa [f] using liftToPower_comp_swindleMap p k hk) ≫
                kernel.ι f ≫ proj X 0 = k
          rw [← Category.assoc, kernel.lift_ι, liftToPower_comp_proj_zero]
        )
        (fun {W} k hk m hm ↦ by
          apply (cancel_mono (kernel.ι f)).1
          ext n
          cases n with
          | zero =>
              simpa [Category.assoc, liftToPower_comp_proj_zero] using hm
          | succ n =>
              have hm' : (m ≫ kernel.ι f) ≫ f = 0 := by
                rw [Category.assoc, kernel.condition, comp_zero]
              simpa [Category.assoc, liftToPower_comp_proj_succ] using
                succCoord_eq_zero p hp (m ≫ kernel.ι f) hm' n)

end CountableProducts

/-- Lemma 12.4.3 (1): if a preadditive category has countable products and every morphism with a
right inverse has a kernel, then the category is Karoubian. -/
-- Proof sketch: for an idempotent endomorphism `p`, use the Stacks countable-product construction
-- to realize `ker p` as the kernel of a split epimorphism on a countable product. The hypothesis
-- then gives a kernel for `p`, and `isIdempotentComplete_iff_idempotents_have_kernels` finishes.
lemma isIdempotentComplete_of_countableProducts_of_splitEpi_kernels
    [HasCountableProducts C]
    (hkernel : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [IsSplitEpi f], HasKernel f) :
    IsIdempotentComplete C := by
  rw [isIdempotentComplete_iff_idempotents_have_kernels]
  intro X p hp
  exact hasKernel_idempotent_of_splitEpiKernels hkernel X p hp

/-- Lemma 12.4.3 (2): if a preadditive category has countable coproducts and every morphism with a
left inverse has a cokernel, then the category is Karoubian. -/
-- Proof sketch: apply part (1) to `Cᵒᵖ`. Countable coproducts in `C` become countable products in
-- `Cᵒᵖ`, split monomorphisms become split epimorphisms after passing to opposites, and a cokernel
-- in `C` yields a kernel in `Cᵒᵖ` via the standard opposite-category kernel/cokernel conversion.
lemma isIdempotentComplete_of_countableCoproducts_of_splitMono_cokernels
    [HasCountableCoproducts C]
    (hcokernel : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [IsSplitMono f], HasCokernel f) :
    IsIdempotentComplete C := by
  letI : HasCountableProducts Cᵒᵖ :=
    ⟨fun J _ ↦ by infer_instance⟩
  have hkernel_op : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) [IsSplitEpi f], HasKernel f := by
    intro X Y f _
    letI : IsSplitMono f.unop := IsSplitMono.mk' {
      retraction := (section_ f).unop
      id := by
        change (section_ f ≫ f).unop = (𝟙 Y).unop
        exact congrArg Quiver.Hom.unop (IsSplitEpi.id f) }
    letI : HasCokernel f.unop := hcokernel f.unop
    refine ⟨⟨KernelFork.ofι (cokernel.π f.unop).op ?_, ?_⟩⟩
    · have h := congrArg Quiver.Hom.op (cokernel.condition f.unop)
      change (cokernel.π f.unop).op ≫ f = 0 at h
      simpa using h
    · exact CokernelCofork.IsColimit.ofπOp (cokernel.π f.unop) (cokernel.condition f.unop)
        (cokernelIsCokernel f.unop)
  exact isIdempotentComplete_of_isIdempotentComplete_opposite <|
    isIdempotentComplete_of_countableProducts_of_splitEpi_kernels hkernel_op

end

end CategoryTheory
