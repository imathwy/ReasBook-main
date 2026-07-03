import Mathlib
import stacks_project.Chap04.Example_4_22_6

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory.Limits

universe u v

namespace CategoryTheory

/-- High-reuse core vocabulary for a sequential inverse system in `A`, namely a functor
`ℕᵒᵖ ⥤ A`. -/
abbrev SequentialInverseSystem (A : Type u) [Category.{v} A] := ℕᵒᵖ ⥤ A

namespace SequentialInverseSystem

variable {A : Type u} [Category.{v} A]

/-
Domain-style sampling for Definition 12.31.2 in the inverse-system / Mittag-Leffler domain:
- sampled mathlib owner declarations in the concrete `Type`-valued setting:
  * `CategoryTheory.Functor.IsMittagLeffler`
  * `CategoryTheory.Functor.isMittagLeffler_iff_eventualRange`
  * `CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp`
- source/core/bridge triage:
  * `source-facing`: the textbook stabilization of image subobjects for a sequential inverse system
    in an abelian category
  * `core/canonical`: mathlib's `Functor.IsMittagLeffler` for `Type`-valued cofiltered systems
  * `bridge/view`: faithful/concrete comparisons between the image-subobject formulation here and
    the range-stabilization owner in concrete categories

The present item therefore stays `source-facing`: its primitive data are only the inverse system
`F`, while the transition morphisms are derived from that owner object. The broader categorical
image-subobject formulation carries genuinely more semantics than the `Type`-valued owner, so this
file should define it directly rather than disguise it as a wrapper around the concrete mathlib
predicate.
-/

/-- Derived API: the transition morphism `F_j ⟶ F_i` attached to an inequality `i ≤ j`. -/
abbrev transitionMap (F : SequentialInverseSystem A) {i j : ℕ} (hij : i ≤ j) :
    F.obj (op j) ⟶ F.obj (op i) :=
  F.map ((homOfLE hij).op)

/-- Derived API: the successor transition morphism `F_{n + 1} ⟶ F_n` of a sequential inverse
system. -/
abbrev stepMap (F : SequentialInverseSystem A) (n : ℕ) :
    F.obj (op (n + 1)) ⟶ F.obj (op n) :=
  F.transitionMap (Nat.le_add_right n 1)

/-- The tail of a sequential inverse system obtained by shifting the index by `n`. -/
abbrev shift (F : SequentialInverseSystem A) (n : ℕ) : SequentialInverseSystem A :=
  ({ toFun := fun i ↦ n + i
     monotone' := fun _ _ hij ↦ Nat.add_le_add_left hij n } : ℕ →o ℕ).toFunctor.op ⋙ F

@[simp] theorem shift_obj (F : SequentialInverseSystem A) (n i : ℕ) :
    (F.shift n).obj (op i) = F.obj (op (n + i)) :=
  rfl

@[simp] theorem shift_transitionMap (F : SequentialInverseSystem A) (n : ℕ) {i j : ℕ}
    (hij : i ≤ j) :
    (F.shift n).transitionMap hij = F.transitionMap (Nat.add_le_add_left hij n) :=
  rfl

/-- The sequential inverse system obtained by taking countable coproducts stagewise. -/
noncomputable def countableCoproduct [HasCountableCoproducts A] (F : SequentialInverseSystem A) :
    SequentialInverseSystem A :=
  F ⋙ ((Functor.const (Discrete ℕ)) ⋙ colim)

/-- Evaluating the stagewise countable-coproduct inverse system at `n` gives the canonical
countable coproduct of copies of `F.obj n`. -/
@[simp] theorem countableCoproduct_obj [HasCountableCoproducts A]
    (F : SequentialInverseSystem A) (n : ℕᵒᵖ) :
    F.countableCoproduct.obj n = ∐ fun _ : ℕ ↦ F.obj n :=
  rfl

/-- Definition 12.31.2: the textbook Mittag-Leffler condition for a sequential inverse system in
an abelian category only uses the image subobjects of the transition morphisms, so the owner-level
Lean predicate is stated in any category with images. -/
def IsMittagLeffler [HasImages A] (F : SequentialInverseSystem A) : Prop :=
  ∀ i : ℕ, ∃ (c : ℕ) (hic : i ≤ c),
    ∀ ⦃k : ℕ⦄ (hck : c ≤ k),
      imageSubobject (F.transitionMap (hic.trans hck)) =
        imageSubobject (F.transitionMap hic)

end SequentialInverseSystem

namespace SequentialProObjectMorphismRep

variable {A : Type u} [Category.{v} A] {X Y : SequentialInverseSystem A}

/-- Build a sequential pro-object representative from a natural transformation out of a shifted
source inverse system. -/
def ofShiftNatTrans (c : ℕ) (α : X.shift c ⟶ Y) :
    SequentialProObjectMorphismRep X Y where
  reindex :=
    { toFun := fun n ↦ c + n
      monotone' := fun _ _ h ↦ Nat.add_le_add_left h c }
  hom := by
    simpa [SequentialInverseSystem.shift] using α

end SequentialProObjectMorphismRep

end CategoryTheory
