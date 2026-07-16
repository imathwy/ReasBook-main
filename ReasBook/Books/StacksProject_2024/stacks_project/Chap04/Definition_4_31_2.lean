import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
import Mathlib.CategoryTheory.Bicategory.Extension
import Mathlib.CategoryTheory.Bicategory.Strict.Basic
import Mathlib.CategoryTheory.CatCommSq
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
import StacksProject_2024.stacks_project.Chap04.Definition_4_31_1

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Bicategory
open Limits
open Limits.CategoricalPullback
open Limits.CategoricalPullback.CatCommSqOver
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} (f : x ⟶ z) (g : y ⟶ z)

/- Domain-style sampling for Definition 4.31.2:
- `Bicategory.IsFinal` from Definition `4.31.1` is the canonical owner abstraction for the
  universal property of a `2`-fibre product square.
- `LeftLift` from mathlib is the canonical owner for the lower-triangle data and for the ordinary
  morphism category on the apex maps.
- `Bicategory.IsLocallyGroupoid` from Definition `4.30.1` is only bridge-level input: in the
  source `(2,1)` setting it upgrades those ordinary ambient `2`-morphisms to invertible ones; it
  should not be hardwired into the square owner itself.
- The categorical prototype is `CategoricalPullback.CatCommSqOver`, where the primitive data are a
  commutative square and the pullback universal property is derived API.

Primitive-vs-derived split:
- primitive data: the apex object, the two projection `1`-morphisms, and the invertible
  comparison `2`-morphism.
- derived API: the bicategory structure on squares with ordinary ambient `2`-morphisms in each
  hom-category, the inherited local-groupoid and strictness instances, and the
  existence-and-uniqueness reformulation of finality available in the `(2,1)` setting. -/

/- Source/core/bridge triage for Definition 4.31.2:
- `source-facing`: the square data `BicategoricalTwoCommutativeSquare f g`.
- `core/canonical`: for `P : BicategoricalTwoCommutativeSquare f g`, the universal property
  `Bicategory.IsFinal P`.
- `bridge/view`: the inherited `(2,1)`-category specialization, already owned upstream by
  `Bicategory.isFinal_iff_existsUnique_hom₂`. -/

/-- A `2`-commutative square over a bicategorical cospan `x ⟶ z ← y`. -/
@[ext]
structure BicategoricalTwoCommutativeSquare where
  /-- The apex object of the square. -/
  obj : B
  /-- The projection to the left object. -/
  p : obj ⟶ x
  /-- The projection to the right object. -/
  q : obj ⟶ y
  /-- The invertible `2`-morphism witnessing `2`-commutativity. -/
  ψ : p ≫ f ≅ q ≫ g

namespace BicategoricalTwoCommutativeSquare

variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Swap the two legs of a `2`-commutative square. -/
@[simps]
def symm (S : BicategoricalTwoCommutativeSquare f g) :
    BicategoricalTwoCommutativeSquare g f where
  obj := S.obj
  p := S.q
  q := S.p
  ψ := S.ψ.symm

/-- The symmetry operation on `2`-commutative squares is involutive. -/
@[simp] theorem symm_symm (S : BicategoricalTwoCommutativeSquare f g) :
    S.symm.symm = S := by
  cases S
  rfl

/-- The lower triangle of a `2`-commutative square, viewed as the canonical left-lift owner. -/
abbrev toLeftLift (S : BicategoricalTwoCommutativeSquare f g) :
    LeftLift f (S.q ≫ g) :=
  LeftLift.mk S.p S.ψ.inv

noncomputable instance (S : BicategoricalTwoCommutativeSquare f g) :
    IsIso S.toLeftLift.unit := by
  change IsIso S.ψ.inv
  infer_instance

end BicategoricalTwoCommutativeSquare

namespace Limits.CategoricalPullback.CatCommSqOver

universe vCat uCat

variable {X : Type uCat} [Category.{vCat} X]
variable {A : Type uCat} [Category.{vCat} A]
variable {B' : Type uCat} [Category.{vCat} B']
variable {C : Type uCat} [Category.{vCat} C]

/-- A categorical commutative square over `F` and `G`, viewed in the chapter's bicategorical
owner of `2`-commutative squares in `Cat`. -/
abbrev toBicategoricalSquare
    {F : A ⥤ C} {G : B' ⥤ C}
    (P : CatCommSqOver F G X) :
    BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom where
  obj := Cat.of X
  p := P.fst.toCatHom
  q := P.snd.toCatHom
  ψ := Cat.Hom.isoMk P.iso

end Limits.CategoricalPullback.CatCommSqOver

namespace BicategoricalTwoCommutativeSquare

variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

local notation "Square" => BicategoricalTwoCommutativeSquare f g

section

variable {S S₁ S₂ S₃ : Square}

/-- A `1`-morphism between `2`-commutative squares over the fixed cospan `x ⟶ z ← y`. -/
@[ext]
structure Hom (S₁ S₂ : Square) where
  /-- The map between the apex objects. -/
  hom : S₁.obj ⟶ S₂.obj
  /-- The comparison `2`-morphism on the left leg. -/
  left : hom ≫ S₂.p ⟶ S₁.p
  /-- The comparison `2`-morphism on the right leg. -/
  right : hom ≫ S₂.q ⟶ S₁.q
  /-- Compatibility with the chosen `2`-commutativity witnesses. -/
  comm :
    (left ▷ f) ≫ S₁.ψ.hom =
      (α_ hom S₂.p f).hom ≫ hom ◁ S₂.ψ.hom ≫ (α_ hom S₂.q g).inv ≫ (right ▷ g)

/-- A `2`-morphism between morphisms of `2`-commutative squares. -/
@[ext]
structure TwoHom
    {S₁ S₂ : Square}
    (u v : Hom S₁ S₂) where
  /-- The ambient `2`-morphism between the apex maps. -/
  hom : u.hom ⟶ v.hom
  /-- Compatibility with the left-leg comparison `2`-morphisms. -/
  left_comm : (hom ▷ S₂.p) ≫ v.left = u.left
  /-- Compatibility with the right-leg comparison `2`-morphisms. -/
  right_comm : (hom ▷ S₂.q) ≫ v.right = u.right

private def idHom (S : Square) :
    Hom S S where
  hom := 𝟙 S.obj
  left := (λ_ S.p).hom
  right := (λ_ S.q).hom
  comm := by
    sorry

private def compHom
    {S₁ S₂ S₃ : Square}
    (u : Hom S₁ S₂)
    (v : Hom S₂ S₃) :
    Hom S₁ S₃ where
  hom := u.hom ≫ v.hom
  left := (α_ u.hom v.hom S₃.p).hom ≫ u.hom ◁ v.left ≫ u.left
  right := (α_ u.hom v.hom S₃.q).hom ≫ u.hom ◁ v.right ≫ u.right
  comm := by
    sorry

private def idHom₂
    {S₁ S₂ : Square}
    (u : Hom S₁ S₂) :
    TwoHom u u where
  hom := 𝟙 u.hom
  left_comm := by
    sorry
  right_comm := by
    sorry

private def compHom₂
    {S₁ S₂ : Square}
    {u v w : Hom S₁ S₂}
    (η : TwoHom u v)
    (θ : TwoHom v w) :
    TwoHom u w where
  hom := η.hom ≫ θ.hom
  left_comm := by
    sorry
  right_comm := by
    sorry

private def whiskerLeftTwoHom
    {S₁ S₂ S₃ : Square}
    (u : Hom S₁ S₂)
    {v w : Hom S₂ S₃}
    (η : TwoHom v w) :
    TwoHom (compHom u v) (compHom u w) where
  hom := u.hom ◁ η.hom
  left_comm := by
    sorry
  right_comm := by
    sorry

private def whiskerRightTwoHom
    {S₁ S₂ S₃ : Square}
    {u v : Hom S₁ S₂}
    (η : TwoHom u v)
    (w : Hom S₂ S₃) :
    TwoHom (compHom u w) (compHom v w) where
  hom := η.hom ▷ w.hom
  left_comm := by
    sorry
  right_comm := by
    sorry

instance (S₁ S₂ : Square) : Category (Hom S₁ S₂) where
  Hom u v := TwoHom u v
  id := idHom₂
  comp := compHom₂
  id_comp := by
    sorry
  comp_id := by
    sorry
  assoc := by
    sorry

noncomputable instance
    [IsLocallyGroupoid B]
    (S₁ S₂ : Square) :
    Groupoid (Hom S₁ S₂) where
  toCategory := inferInstance
  inv η :=
    { hom := inv η.hom
      left_comm := by
        sorry
      right_comm := by
        sorry }
  inv_comp := by
    sorry
  comp_inv := by
    sorry

instance : Bicategory (BicategoricalTwoCommutativeSquare f g) where
  Hom S₁ S₂ := Hom S₁ S₂
  homCategory S₁ S₂ := inferInstance
  id := idHom
  comp := compHom
  whiskerLeft := whiskerLeftTwoHom
  whiskerRight := whiskerRightTwoHom
  associator {a b c d} S₁ S₂ S₃ := by
    let _ : Category (Hom a d) := inferInstance
    refine
      { hom :=
          { hom :=
              (α_ S₁.hom S₂.hom S₃.hom).hom
            left_comm := by
              sorry
            right_comm := by
              sorry
            }
        inv :=
          { hom :=
              (α_ S₁.hom S₂.hom S₃.hom).inv
            left_comm := by
              sorry
            right_comm := by
              sorry
            } }
  leftUnitor {a b} S := by
    let _ : Category (Hom a b) := inferInstance
    refine
      { hom :=
          { hom := (λ_ S.hom).hom
            left_comm := by
              sorry
            right_comm := by
              sorry
            }
        inv :=
          { hom := (λ_ S.hom).inv
            left_comm := by
              sorry
            right_comm := by
              sorry
            } }
  rightUnitor {a b} S := by
    let _ : Category (Hom a b) := inferInstance
    refine
      { hom :=
          { hom := (ρ_ S.hom).hom
            left_comm := by
              sorry
            right_comm := by
              sorry
            }
        inv :=
          { hom := (ρ_ S.hom).inv
            left_comm := by
              sorry
            right_comm := by
              sorry
            } }
  whisker_exchange := by
    sorry
  whiskerLeft_id := by
    sorry
  whiskerLeft_comp := by
    sorry
  id_whiskerLeft := by
    sorry
  comp_whiskerLeft := by
    sorry
  id_whiskerRight := by
    sorry
  comp_whiskerRight := by
    sorry
  whiskerRight_id := by
    sorry
  whiskerRight_comp := by
    sorry
  whisker_assoc := by
    sorry
  pentagon := by
    sorry
  triangle := by
    sorry

instance [IsLocallyGroupoid B] :
    IsLocallyGroupoid (BicategoricalTwoCommutativeSquare f g) :=
  fun S₁ S₂ ↦ by
    change IsGroupoid (Hom S₁ S₂)
    infer_instance

instance [Strict B] : Strict (BicategoricalTwoCommutativeSquare f g) where
  id_comp := by
    sorry
  comp_id := by
    sorry
  assoc := by
    sorry
  leftUnitor_eqToIso := by
    sorry
  rightUnitor_eqToIso := by
    sorry
  associator_eqToIso := by
    sorry

end

end BicategoricalTwoCommutativeSquare

variable (P : BicategoricalTwoCommutativeSquare f g)

/- Definition 4.31.2: a `2`-fibre product square over `f : x ⟶ z` and `g : y ⟶ z` is a final
object `P` of the bicategory of `2`-commutative squares over that cospan. This core owner
statement is intrinsic to the square bicategory itself. -/
#check (IsFinal P : Prop)

section LocallyGroupoid

variable [IsLocallyGroupoid B]

/- Companion bridge: under the inherited `(2,1)` hypothesis, the textbook
existence-and-uniqueness formulation is the canonical specialization of
`Bicategory.isFinal_iff_existsUnique_hom₂` to the bicategory
`BicategoricalTwoCommutativeSquare f g`. -/
#check Bicategory.isFinal_iff_existsUnique_hom₂ P

end LocallyGroupoid

end CategoryTheory
