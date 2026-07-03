import Mathlib
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_31_1 (from Chap04) -/
universe w v u

namespace CategoryTheory

open Bicategory
open Limits
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/- Domain-style sampling for Definition 4.31.1:
- `CategoryTheory.Limits.HasTerminal` is the canonical owner abstraction for “there exists a
  terminal object” in a category.
- `CategoryTheory.Limits.IsTerminal` is the canonical owner abstraction for a chosen terminal
  object.
- `CategoryTheory.Limits.IsTerminal.ofUnique` is the canonical constructor when a chosen object is
  shown terminal by a `Unique`-morphism API.
- `CategoryTheory.Bicategory.IsLocallyGroupoid` from Definition `4.30.1` is the project owner
  abstraction for the `(2,1)` condition that every `2`-morphism is invertible.

Primitive-vs-derived split:
- primitive data: for each `y : B`, terminal-object structure on the hom-category `y ⟶ x`.
- derived API: the chosen terminal `1`-morphism `⊤_ (y ⟶ x)`, the canonical comparison
  `2`-morphism `terminal.from _` in each hom-category, the induced uniqueness of `2`-morphisms in
  the locally groupoidal case, and the textbook existence-and-uniqueness reformulation. -/

/- Source/core/bridge triage for Definition 4.31.1:
- `source-facing`: `Bicategory.IsFinal x`.
- `core/canonical`: `HasTerminal (y ⟶ x)` and `IsTerminal f` in the hom-categories.
- `bridge/view`: `Bicategory.isFinal_iff_existsUnique_hom₂`. Its public surface is the Prop-valued
  existence-and-subsingleton restatement, while the reverse construction is driven internally by
  the canonical owner `Unique (f ⟶ g)`. -/

/-- Definition 4.31.1: an object `x` is bicategorically final if every hom-category `y ⟶ x` has a
terminal object. The textbook Stacks definition is only stated for `(2,1)`-categories, but this
owner notion itself is intrinsic to any bicategory. -/
class Bicategory.IsFinal (x : B) : Prop where
  /-- For every object `y`, the hom-category `y ⟶ x` has a terminal object. -/
  hasTerminal (y : B) : HasTerminal (y ⟶ x)

attribute [instance] Bicategory.IsFinal.hasTerminal

/-- A family of terminal hom-categories into `x` packages into bicategorical finality. -/
instance (x : B) [∀ y : B, HasTerminal (y ⟶ x)] : Bicategory.IsFinal x where
  hasTerminal _ := inferInstance

section

variable [IsLocallyGroupoid B]

namespace Bicategory.IsFinal

/-- In a locally groupoidal bicategory, every `1`-morphism into a final object is terminal in the
corresponding hom-category. -/
noncomputable def homIsTerminal {x y : B} [IsFinal x] (f : y ⟶ x) : IsTerminal f :=
  IsTerminal.ofIso terminalIsTerminal (asIso (terminal.from f)).symm

end Bicategory.IsFinal

/-- Any pair of `1`-morphisms into a final object has a unique `2`-morphism between them. -/
noncomputable instance {x y : B} [IsFinal x] (f g : y ⟶ x) : Unique (f ⟶ g) :=
  (isTerminalEquivUnique (Functor.empty (y ⟶ x)) g).toFun (IsFinal.homIsTerminal g) f

namespace Bicategory

/-- Definition 4.31.1 in textbook form: if every `2`-morphism is invertible, then `x` is final iff
for each object `y` there is a `1`-morphism `y ⟶ x`, and between any two such `1`-morphisms there
is a unique `2`-morphism. In the Stacks `(2,1)`-category setting, this local-groupoid hypothesis is
automatic, while strictness does not enter the statement. The theorem is Prop-valued, so the
existence-and-uniqueness clause is stated as `Nonempty` plus `Subsingleton`, while the reverse
construction uses the canonical owner `Unique (f ⟶ g)` internally. -/
theorem isFinal_iff_existsUnique_hom₂ (x : B) :
    IsFinal x ↔
      ∀ y : B, Nonempty (y ⟶ x) ∧
        ∀ f g : y ⟶ x, Nonempty (f ⟶ g) ∧ Subsingleton (f ⟶ g) := by
  constructor
  · intro _ y
    refine ⟨⟨⊤_ (y ⟶ x)⟩, ?_⟩
    intro f g
    let _ : Unique (f ⟶ g) := inferInstance
    exact ⟨⟨default⟩, inferInstance⟩
  · intro hx
    classical
    refine ⟨fun y ↦ ?_⟩
    rcases (hx y).1 with ⟨f⟩
    letI : ∀ g : y ⟶ x, Nonempty (g ⟶ f) := fun g ↦ ((hx y).2 g f).1
    letI : ∀ g : y ⟶ x, Subsingleton (g ⟶ f) := fun g ↦ ((hx y).2 g f).2
    exact hasTerminal_of_unique f

end Bicategory

end

end CategoryTheory

/-! ### Definition_4_31_2 (from Chap04) -/
open scoped Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

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
  hom-category, the inherited local-groupoid instance, and the
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

/-- A `1`-morphism between `2`-commutative squares over the fixed cospan `x ⟶ z ← y`.
The leg comparison cells are intentionally oriented toward the source square: this is the
cone-morphism direction used by the final-object universal property of a `2`-fibre product. -/
@[ext]
structure Hom (S₁ S₂ : Square) where
  /-- The map between the apex objects. -/
  hom : S₁.obj ⟶ S₂.obj
  /-- The comparison `2`-morphism on the left leg, oriented toward the source cone. -/
  left : hom ≫ S₂.p ⟶ S₁.p
  /-- The comparison `2`-morphism on the right leg, oriented toward the source cone. -/
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
    -- The identity square condition is exactly the ambient left-unitor whiskering formula.
    simpa using (Bicategory.id_whiskerLeft (η := S.ψ.hom)).symm

private def compHom
    {S₁ S₂ S₃ : Square}
    (u : Hom S₁ S₂)
    (v : Hom S₂ S₃) :
    Hom S₁ S₃ where
  hom := u.hom ≫ v.hom
  left := (α_ u.hom v.hom S₃.p).hom ≫ u.hom ◁ v.left ≫ u.left
  right := (α_ u.hom v.hom S₃.q).hom ≫ u.hom ◁ v.right ≫ u.right
  comm := by
    -- Route correction: first rewrite the outer square relation `u.comm`, then whisker `v.comm`
    -- through `u.hom`; the remaining associator bookkeeping is pure ambient bicategory coherence.
    simp only [comp_whiskerRight, Category.assoc]
    rw [u.comm]
    have hv :
        (u.hom ◁ v.left) ▷ f ≫ (α_ u.hom S₂.p f).hom ≫ u.hom ◁ S₂.ψ.hom =
          (α_ u.hom (v.hom ≫ S₃.p) f).hom ≫
            u.hom ◁
              ((α_ v.hom S₃.p f).hom ≫ v.hom ◁ S₃.ψ.hom ≫
                (α_ v.hom S₃.q g).inv ≫ v.right ▷ g) := by
      -- Transport the middle square relation through left whiskering by `u.hom`, then align the
      -- resulting source with the displayed composite-leg parenthesization.
      rw [associator_naturality_middle_assoc]
      simpa [Category.assoc] using congrArg (fun β ↦ u.hom ◁ β) v.comm
    have hv' :=
      congrArg
        (fun α ↦
          (α_ u.hom v.hom S₃.p).hom ▷ f ≫ α ≫ (α_ u.hom S₂.q g).inv ≫ u.right ▷ g)
        hv
    simpa [Category.assoc] using hv'

private def idHom₂
    {S₁ S₂ : Square}
    (u : Hom S₁ S₂) :
    TwoHom u u where
  hom := 𝟙 u.hom
  left_comm := by
    -- Identity `2`-cells act trivially on the left leg.
    simp
  right_comm := by
    -- Identity `2`-cells act trivially on the right leg.
    simp

private def compHom₂
    {S₁ S₂ : Square}
    {u v w : Hom S₁ S₂}
    (η : TwoHom u v)
    (θ : TwoHom v w) :
    TwoHom u w where
  hom := η.hom ≫ θ.hom
  left_comm := by
    -- Vertical composition preserves the left-leg compatibility by associativity.
    simpa [Category.assoc, η.left_comm, θ.left_comm]
  right_comm := by
    -- Vertical composition preserves the right-leg compatibility by associativity.
    simpa [Category.assoc, η.right_comm, θ.right_comm]

private def whiskerLeftTwoHom
    {S₁ S₂ S₃ : Square}
    (u : Hom S₁ S₂)
    {v w : Hom S₂ S₃}
    (η : TwoHom v w) :
    TwoHom (compHom u v) (compHom u w) where
  hom := u.hom ◁ η.hom
  left_comm := by
    -- Transport the left leg relation through left whiskering and then reattach `u.left`.
    simpa [compHom, Category.assoc] using
      (show
        ((u.hom ◁ η.hom ▷ S₃.p ≫ u.hom ◁ w.left) ≫ u.left =
          u.hom ◁ v.left ≫ u.left) from
        congrArg (fun α ↦ α ≫ u.left)
          (by
            simpa [Category.assoc] using congrArg (fun β ↦ u.hom ◁ β) η.left_comm))
  right_comm := by
    -- The right leg is the same transport calculation with `q`.
    simpa [compHom, Category.assoc] using
      (show
        ((u.hom ◁ η.hom ▷ S₃.q ≫ u.hom ◁ w.right) ≫ u.right =
          u.hom ◁ v.right ≫ u.right) from
        congrArg (fun α ↦ α ≫ u.right)
          (by
            simpa [Category.assoc] using congrArg (fun β ↦ u.hom ◁ β) η.right_comm))

private def whiskerRightTwoHom
    {S₁ S₂ S₃ : Square}
    {u v : Hom S₁ S₂}
    (η : TwoHom u v)
    (w : Hom S₂ S₃) :
    TwoHom (compHom u w) (compHom v w) where
  hom := η.hom ▷ w.hom
  left_comm := by
    -- Reassociate to the final displayed left-leg shape, commute the whiskers, and substitute
    -- the square relation `η.left_comm`.
    calc
      η.hom ▷ w.hom ▷ S₃.p ≫ (compHom v w).left
          = η.hom ▷ w.hom ▷ S₃.p ≫ (α_ v.hom w.hom S₃.p).hom ≫ v.hom ◁ w.left ≫ v.left := by
              simp [compHom, Category.assoc]
      _ = (α_ u.hom w.hom S₃.p).hom ≫ η.hom ▷ (w.hom ≫ S₃.p) ≫ v.hom ◁ w.left ≫ v.left := by
            rw [associator_naturality_left_assoc]
      _ = (α_ u.hom w.hom S₃.p).hom ≫ (u.hom ◁ w.left ≫ η.hom ▷ S₂.p) ≫ v.left := by
            rw [← whisker_exchange_assoc]
            simp [Category.assoc]
      _ = (α_ u.hom w.hom S₃.p).hom ≫ u.hom ◁ w.left ≫ u.left := by
            rw [Category.assoc, η.left_comm]
      _ = (compHom u w).left := by
            simp [compHom, Category.assoc]
  right_comm := by
    -- The right leg follows from the same ambient reassociation with `q`.
    calc
      η.hom ▷ w.hom ▷ S₃.q ≫ (compHom v w).right
          = η.hom ▷ w.hom ▷ S₃.q ≫ (α_ v.hom w.hom S₃.q).hom ≫ v.hom ◁ w.right ≫ v.right := by
              simp [compHom, Category.assoc]
      _ = (α_ u.hom w.hom S₃.q).hom ≫ η.hom ▷ (w.hom ≫ S₃.q) ≫ v.hom ◁ w.right ≫ v.right := by
            rw [associator_naturality_left_assoc]
      _ = (α_ u.hom w.hom S₃.q).hom ≫ (u.hom ◁ w.right ≫ η.hom ▷ S₂.q) ≫ v.right := by
            rw [← whisker_exchange_assoc]
            simp [Category.assoc]
      _ = (α_ u.hom w.hom S₃.q).hom ≫ u.hom ◁ w.right ≫ u.right := by
            rw [Category.assoc, η.right_comm]
      _ = (compHom u w).right := by
            simp [compHom, Category.assoc]

instance (S₁ S₂ : Square) : Category (Hom S₁ S₂) where
  Hom u v := TwoHom u v
  id := idHom₂
  comp := compHom₂
  id_comp := by
    intro u v η
    -- Equality of square `2`-morphisms is detected on the ambient `2`-cell component.
    ext
    simp [compHom₂, idHom₂]
  comp_id := by
    intro u v η
    -- The right identity is the same ambient categorical identity law.
    ext
    simp [compHom₂, idHom₂]
  assoc := by
    intro u v w t η θ μ
    -- Associativity is inherited verbatim from the ambient hom-category.
    ext
    simp [compHom₂, Category.assoc]

noncomputable instance
    [IsLocallyGroupoid B]
    (S₁ S₂ : Square) :
    Groupoid (Hom S₁ S₂) where
  toCategory := inferInstance
  inv η :=
    { hom := inv η.hom
      left_comm := by
        -- Compose the left-leg relation with the inverse whisker to cancel `η.hom`.
        simpa [Category.assoc] using
          congrArg (fun α ↦ inv η.hom ▷ S₂.p ≫ α) (Eq.symm η.left_comm)
      right_comm := by
        -- The right-leg inverse calculation is identical.
        simpa [Category.assoc] using
          congrArg (fun α ↦ inv η.hom ▷ S₂.q ≫ α) (Eq.symm η.right_comm) }
  inv_comp := by
    intro X Y f_1
    -- The inverse law reduces to the ambient groupoid inverse law on `f_1.hom`.
    apply TwoHom.ext
    change inv f_1.hom ≫ f_1.hom = 𝟙 Y.hom
    simpa using Groupoid.inv_comp f_1.hom
  comp_inv := by
    intro X Y f_1
    -- The other inverse law is the same reduction.
    apply TwoHom.ext
    change f_1.hom ≫ inv f_1.hom = 𝟙 X.hom
    simpa using Groupoid.comp_inv f_1.hom

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
              -- The square associator is compatible with the left leg by pure ambient coherence.
              simp [compHom, Category.assoc]
            right_comm := by
              -- The right leg is the same ambient coherence calculation.
              simp [compHom, Category.assoc]
            }
        inv :=
          { hom :=
              (α_ S₁.hom S₂.hom S₃.hom).inv
            left_comm := by
              -- The inverse associator satisfies the same compatibility relation.
              simp [compHom, Category.assoc]
            right_comm := by
              -- The right-leg inverse compatibility is identical.
              simp [compHom, Category.assoc]
            }
        hom_inv_id := by
          -- Equality of square `2`-cells is detected on the ambient apex `2`-cell.
          apply TwoHom.ext
          change (α_ S₁.hom S₂.hom S₃.hom).hom ≫ (α_ S₁.hom S₂.hom S₃.hom).inv =
              𝟙 ((compHom (compHom S₁ S₂) S₃).hom)
          simpa [compHom] using Iso.hom_inv_id (α_ S₁.hom S₂.hom S₃.hom)
        inv_hom_id := by
          -- The opposite inverse law is the same ambient inverse identity.
          apply TwoHom.ext
          change (α_ S₁.hom S₂.hom S₃.hom).inv ≫ (α_ S₁.hom S₂.hom S₃.hom).hom =
              𝟙 ((compHom S₁ (compHom S₂ S₃)).hom)
          simpa [compHom] using Iso.inv_hom_id (α_ S₁.hom S₂.hom S₃.hom) }
  leftUnitor {a b} S := by
    let _ : Category (Hom a b) := inferInstance
    refine
      { hom :=
          { hom := (λ_ S.hom).hom
            left_comm := by
              -- The square left unitor is the ambient left unitor on the apex map.
              simp [idHom, compHom, Category.assoc]
            right_comm := by
              -- The right leg is unchanged by the same left-unitor normalization.
              simp [idHom, compHom, Category.assoc]
            }
        inv :=
          { hom := (λ_ S.hom).inv
            left_comm := by
              -- The inverse left unitor is compatible by the same ambient simplification.
              simp [idHom, compHom, Category.assoc]
            right_comm := by
              -- Likewise for the right leg.
              simp [idHom, compHom, Category.assoc]
            }
        hom_inv_id := by
          -- Reduce the inverse law to the ambient left unitor inverse identity.
          apply TwoHom.ext
          change (λ_ S.hom).hom ≫ (λ_ S.hom).inv = 𝟙 ((compHom (idHom a) S).hom)
          simpa [idHom, compHom] using Iso.hom_inv_id (λ_ S.hom)
        inv_hom_id := by
          -- The opposite inverse law is the same componentwise reduction.
          apply TwoHom.ext
          change (λ_ S.hom).inv ≫ (λ_ S.hom).hom = 𝟙 S.hom
          simpa [idHom, compHom] using Iso.inv_hom_id (λ_ S.hom) }
  rightUnitor {a b} S := by
    let _ : Category (Hom a b) := inferInstance
    refine
      { hom :=
          { hom := (ρ_ S.hom).hom
            left_comm := by
              -- The square right unitor is inherited from the ambient one.
              simp [idHom, compHom, Category.assoc]
            right_comm := by
              -- The right leg is identical after the same normalization.
              simp [idHom, compHom, Category.assoc]
            }
        inv :=
          { hom := (ρ_ S.hom).inv
            left_comm := by
              -- The inverse right unitor satisfies the same compatibility relation.
              simp [idHom, compHom, Category.assoc]
            right_comm := by
              -- Likewise on the right leg.
              simp [idHom, compHom, Category.assoc]
            }
        hom_inv_id := by
          -- Reduce the inverse law to the ambient right unitor inverse identity.
          apply TwoHom.ext
          change (ρ_ S.hom).hom ≫ (ρ_ S.hom).inv = 𝟙 ((compHom S (idHom b)).hom)
          simpa [idHom, compHom] using Iso.hom_inv_id (ρ_ S.hom)
        inv_hom_id := by
          -- The opposite inverse law is identical.
          apply TwoHom.ext
          change (ρ_ S.hom).inv ≫ (ρ_ S.hom).hom = 𝟙 S.hom
          simpa [idHom, compHom] using Iso.inv_hom_id (ρ_ S.hom) }
  whisker_exchange := by
    intro a b c f_1 g_1 h i η θ
    -- The exchange law is inherited verbatim from the ambient bicategory on apex maps.
    apply TwoHom.ext
    change f_1.hom ◁ θ.hom ≫ η.hom ▷ i.hom = η.hom ▷ h.hom ≫ g_1.hom ◁ θ.hom
    simpa using CategoryTheory.Bicategory.whisker_exchange η.hom θ.hom
  whiskerLeft_id := by
    intro a b c f_1 g_1
    -- Once the transport lemmas are exact, this is just the ambient left-whiskering identity law.
    apply TwoHom.ext
    change f_1.hom ◁ 𝟙 g_1.hom = 𝟙 ((compHom f_1 g_1).hom)
    simpa [whiskerLeftTwoHom, compHom, idHom₂] using
      Bicategory.whiskerLeft_id f_1.hom g_1.hom
  whiskerLeft_comp := by
    intro a b c f_1 g_1 h i η θ
    -- The apex `2`-cell component is exactly the ambient left-whiskering composition law.
    apply TwoHom.ext
    change f_1.hom ◁ (η.hom ≫ θ.hom) = (f_1.hom ◁ η.hom) ≫ f_1.hom ◁ θ.hom
    simpa [whiskerLeftTwoHom, compHom₂] using
      Bicategory.whiskerLeft_comp f_1.hom η.hom θ.hom
  id_whiskerLeft := by
    intro a b f_1 g_1 η
    -- After identifying the `.hom` field, the displayed square relation follows automatically.
    apply TwoHom.ext
    change (𝟙 a.obj ◁ η.hom) = (λ_ f_1.hom).hom ≫ η.hom ≫ (λ_ g_1.hom).inv
    simpa [whiskerLeftTwoHom, idHom, compHom] using Bicategory.id_whiskerLeft η.hom
  comp_whiskerLeft := by
    intro a b c d f_1 g_1 h h' η
    -- This is the ambient `comp_whiskerLeft` law on the apex `2`-cell component.
    apply TwoHom.ext
    change (f_1.hom ≫ g_1.hom) ◁ η.hom =
      (α_ f_1.hom g_1.hom h.hom).hom ≫ f_1.hom ◁ (g_1.hom ◁ η.hom) ≫
        (α_ f_1.hom g_1.hom h'.hom).inv
    simpa [whiskerLeftTwoHom, compHom] using
      Bicategory.comp_whiskerLeft f_1.hom g_1.hom η.hom
  id_whiskerRight := by
    intro a b c f_1 g_1
    -- The right-whiskering identity law is inherited from the ambient bicategory.
    apply TwoHom.ext
    change 𝟙 f_1.hom ▷ g_1.hom = 𝟙 ((compHom f_1 g_1).hom)
    simpa [whiskerRightTwoHom, compHom, idHom₂] using
      Bicategory.id_whiskerRight f_1.hom g_1.hom
  comp_whiskerRight := by
    intro a b c f_1 g_1 h η θ i
    -- Vertical composition on the apex `2`-cell is preserved by right whiskering.
    apply TwoHom.ext
    change (η.hom ≫ θ.hom) ▷ i.hom = η.hom ▷ i.hom ≫ θ.hom ▷ i.hom
    simpa [whiskerRightTwoHom, compHom₂] using
      Bicategory.comp_whiskerRight η.hom θ.hom i.hom
  whiskerRight_id := by
    intro a b f_1 g_1 η
    -- This is the ambient right-whiskering identity law transported to square `2`-cells.
    apply TwoHom.ext
    change η.hom ▷ 𝟙 b.obj = (ρ_ f_1.hom).hom ≫ η.hom ≫ (ρ_ g_1.hom).inv
    simpa [whiskerRightTwoHom, idHom, compHom] using Bicategory.whiskerRight_id η.hom
  whiskerRight_comp := by
    intro a b c d f_1 f_1' η g_1 h
    -- This is the ambient right-whiskering associativity law on the `.hom` field.
    apply TwoHom.ext
    change η.hom ▷ (g_1.hom ≫ h.hom) =
      (α_ f_1.hom g_1.hom h.hom).inv ≫ (η.hom ▷ g_1.hom) ▷ h.hom ≫
        (α_ f_1'.hom g_1.hom h.hom).hom
    simpa [whiskerRightTwoHom, compHom] using
      Bicategory.whiskerRight_comp η.hom g_1.hom h.hom
  whisker_assoc := by
    intro a b c d f_1 g_1 g_1' η h
    -- The compatibility of left and right whiskering is inherited componentwise.
    apply TwoHom.ext
    change (f_1.hom ◁ η.hom) ▷ h.hom =
      (α_ f_1.hom g_1.hom h.hom).hom ≫ f_1.hom ◁ (η.hom ▷ h.hom) ≫
        (α_ f_1.hom g_1'.hom h.hom).inv
    simpa [whiskerLeftTwoHom, whiskerRightTwoHom, compHom] using
      Bicategory.whisker_assoc f_1.hom η.hom h.hom
  pentagon := by
    intro a b c d e f_1 g_1 h i
    -- The pentagon coherence law reduces to the ambient one on apex maps.
    apply TwoHom.ext
    change (α_ f_1.hom g_1.hom h.hom).hom ▷ i.hom ≫
        (α_ f_1.hom (g_1.hom ≫ h.hom) i.hom).hom ≫ f_1.hom ◁ (α_ g_1.hom h.hom i.hom).hom =
      (α_ (f_1.hom ≫ g_1.hom) h.hom i.hom).hom ≫ (α_ f_1.hom g_1.hom (h.hom ≫ i.hom)).hom
    simpa [compHom] using Bicategory.pentagon f_1.hom g_1.hom h.hom i.hom
  triangle := by
    intro a b c f_1 g_1
    -- The triangle coherence law is likewise inherited from the ambient bicategory.
    apply TwoHom.ext
    change (α_ f_1.hom (𝟙 b.obj) g_1.hom).hom ≫ f_1.hom ◁ (λ_ g_1.hom).hom =
      (ρ_ f_1.hom).hom ▷ g_1.hom
    simpa [whiskerLeftTwoHom, whiskerRightTwoHom, idHom, compHom] using
      Bicategory.triangle f_1.hom g_1.hom

instance [IsLocallyGroupoid B] :
    IsLocallyGroupoid (BicategoricalTwoCommutativeSquare f g) :=
  fun S₁ S₂ ↦ by
    change IsGroupoid (Hom S₁ S₂)
    infer_instance


/-- Helper for Definition 4.31.2: the ambient `2`-cell component of `eqToHom` between square
`1`-morphisms is the `eqToHom` of the induced apex-map equality. -/
private theorem eqToHom_hom_component {a b : Square} {u v : a ⟶ b} (h : u = v) :
    (eqToHom h).hom = eqToHom (congrArg Hom.hom h) := by
  cases h
  rfl

/-- Helper for Definition 4.31.2: square composition with an identity on the left is strictly
unital. -/
private theorem strict_id_comp_hom [Strict B] {a b : Square} (f_1 : a ⟶ b) :
    𝟙 a ≫ f_1 = f_1 := by
  -- Reduce equality of square morphisms to the apex map and the two dependent leg `2`-cells.
  apply Hom.ext
  · -- The apex map is the ambient strict left identity.
    change 𝟙 a.obj ≫ f_1.hom = f_1.hom
    exact Strict.id_comp f_1.hom
  · -- On the left leg, the strict associator and left unitor collapse the transport to `f_1.left`.
    change ((α_ (𝟙 a.obj) f_1.hom b.p).hom ≫ (𝟙 a.obj ◁ f_1.left) ≫ (λ_ a.p).hom) ≍ f_1.left
    simp [Strict.leftUnitor_eqToIso, Strict.associator_eqToIso]
  · -- The right leg is the same normalization with `q` in place of `p`.
    change ((α_ (𝟙 a.obj) f_1.hom b.q).hom ≫ (𝟙 a.obj ◁ f_1.right) ≫ (λ_ a.q).hom) ≍
        f_1.right
    simp [Strict.leftUnitor_eqToIso, Strict.associator_eqToIso]

/-- Helper for Definition 4.31.2: square composition with an identity on the right is strictly
unital. -/
private theorem strict_comp_id_hom [Strict B] {a b : Square} (f_1 : a ⟶ b) :
    f_1 ≫ 𝟙 b = f_1 := by
  -- Reduce equality of square morphisms to the apex map and the two dependent leg `2`-cells.
  apply Hom.ext
  · -- The apex map is the ambient strict right identity.
    change f_1.hom ≫ 𝟙 b.obj = f_1.hom
    exact Strict.comp_id f_1.hom
  · -- The left leg rewrites to whiskering the ambient left unitor on `b.p`.
    change ((α_ f_1.hom (𝟙 b.obj) b.p).hom ≫ (f_1.hom ◁ (λ_ b.p).hom) ≫ f_1.left) ≍ f_1.left
    simpa [Strict.associator_eqToIso, Strict.leftUnitor_eqToIso] using
      (eqToHom_comp_heq f_1.left (congr_arg (fun k ↦ f_1.hom ≫ k) (Strict.id_comp b.p)))
  · -- The right leg is the same transport calculation for `b.q`.
    change ((α_ f_1.hom (𝟙 b.obj) b.q).hom ≫ (f_1.hom ◁ (λ_ b.q).hom) ≫ f_1.right) ≍ f_1.right
    simpa [Strict.associator_eqToIso, Strict.leftUnitor_eqToIso] using
      (eqToHom_comp_heq f_1.right (congr_arg (fun k ↦ f_1.hom ≫ k) (Strict.id_comp b.q)))

/-- Helper for Definition 4.31.2: square composition is strictly associative. -/
private theorem strict_assoc_left_leg_transport [Strict B] {a b c d : Square}
    (f_1 : a ⟶ b) (g_1 : b ⟶ c) (h : c ⟶ d) :
    ((α_ (f_1.hom ≫ g_1.hom) h.hom d.p).hom ≫ ((f_1.hom ≫ g_1.hom) ◁ h.left) ≫
        ((α_ f_1.hom g_1.hom c.p).hom ≫ f_1.hom ◁ g_1.left ≫ f_1.left)) ≍
      (f_1 ≫ g_1 ≫ h).left := by
  -- Route correction: isolate the dependent left-leg transport as its own theorem so the main
  -- strict associativity proof only has to assemble the three component equalities.
  rw [Bicategory.comp_whiskerLeft]
  -- Strict associators collapse the outer transport to the whiskering-composition normal form
  -- used by the right-associated square leg.
  simp [Category.assoc, Strict.associator_eqToIso]
  -- The remaining comparison is exactly functoriality of left whiskering over the inner
  -- composite leg of `g_1 ≫ h`.
  show
    (f_1.hom ◁ g_1.hom ◁ h.left ≫ f_1.hom ◁ g_1.left ≫ f_1.left) ≍
      ((α_ f_1.hom (g_1.hom ≫ h.hom) d.p).hom ≫
          f_1.hom ◁ ((α_ g_1.hom h.hom d.p).hom ≫ g_1.hom ◁ h.left ≫ g_1.left) ≫
            f_1.left)
  simpa [Category.assoc, Strict.associator_eqToIso] using
    congrArg (fun α ↦ α ≫ f_1.left)
      (Bicategory.whiskerLeft_comp f_1.hom
        ((α_ g_1.hom h.hom d.p).hom ≫ g_1.hom ◁ h.left) g_1.left)

/-- Helper for Definition 4.31.2: the right leg of square composition has the same strict
associativity transport as the left leg. -/
private theorem strict_assoc_right_leg_transport [Strict B] {a b c d : Square}
    (f_1 : a ⟶ b) (g_1 : b ⟶ c) (h : c ⟶ d) :
    ((α_ (f_1.hom ≫ g_1.hom) h.hom d.q).hom ≫ ((f_1.hom ≫ g_1.hom) ◁ h.right) ≫
        ((α_ f_1.hom g_1.hom c.q).hom ≫ f_1.hom ◁ g_1.right ≫ f_1.right)) ≍
      (f_1 ≫ g_1 ≫ h).right := by
  -- The right-leg proof is the same normalization, now postcomposed with `f_1.right`.
  rw [Bicategory.comp_whiskerLeft]
  -- Strict associators again collapse the dependent transport to the right-associated normal form.
  simp [Category.assoc, Strict.associator_eqToIso]
  -- The right leg is the same whiskering-compatibility statement with `q`.
  show
    (f_1.hom ◁ g_1.hom ◁ h.right ≫ f_1.hom ◁ g_1.right ≫ f_1.right) ≍
      ((α_ f_1.hom (g_1.hom ≫ h.hom) d.q).hom ≫
          f_1.hom ◁ ((α_ g_1.hom h.hom d.q).hom ≫ g_1.hom ◁ h.right ≫ g_1.right) ≫
            f_1.right)
  simpa [Category.assoc, Strict.associator_eqToIso] using
    congrArg (fun α ↦ α ≫ f_1.right)
      (Bicategory.whiskerLeft_comp f_1.hom
        ((α_ g_1.hom h.hom d.q).hom ≫ g_1.hom ◁ h.right) g_1.right)

/-- Helper for Definition 4.31.2: square composition is strictly associative. -/
private theorem strict_assoc_hom [Strict B] {a b c d : Square}
    (f_1 : a ⟶ b) (g_1 : b ⟶ c) (h : c ⟶ d) :
    (f_1 ≫ g_1) ≫ h = f_1 ≫ g_1 ≫ h := by
  -- Reduce equality of square morphisms to the apex map and the two dependent leg `2`-cells.
  apply Hom.ext
  · -- The apex map is the ambient strict associativity equality.
    change (f_1.hom ≫ g_1.hom) ≫ h.hom = f_1.hom ≫ g_1.hom ≫ h.hom
    exact Strict.assoc f_1.hom g_1.hom h.hom
  · -- Route correction: reuse the exact left-leg transport lemma so the dependent field proof is
    -- reduced to the already-normalized strict associativity calculation.
    change
      ((α_ (f_1.hom ≫ g_1.hom) h.hom d.p).hom ≫ ((f_1.hom ≫ g_1.hom) ◁ h.left) ≫
          ((α_ f_1.hom g_1.hom c.p).hom ≫ f_1.hom ◁ g_1.left ≫ f_1.left)) ≍
        (f_1 ≫ g_1 ≫ h).left
    exact strict_assoc_left_leg_transport f_1 g_1 h
  · -- The right leg is the same strict transport calculation with `q` in place of `p`.
    change
      ((α_ (f_1.hom ≫ g_1.hom) h.hom d.q).hom ≫ ((f_1.hom ≫ g_1.hom) ◁ h.right) ≫
          ((α_ f_1.hom g_1.hom c.q).hom ≫ f_1.hom ◁ g_1.right ≫ f_1.right)) ≍
        (f_1 ≫ g_1 ≫ h).right
    exact strict_assoc_right_leg_transport f_1 g_1 h

instance [Strict B] : Strict (BicategoricalTwoCommutativeSquare f g) where
  id_comp := by
    intro a b f_1
    -- Reuse the strict left-unital square equality proved just above.
    exact strict_id_comp_hom f_1
  comp_id := by
    intro a b f_1
    -- Reuse the strict right-unital square equality proved just above.
    exact strict_comp_id_hom f_1
  assoc := by
    intro a b c d f_1 g_1 h
    -- Reuse the strict associativity equality proved just above.
    exact strict_assoc_hom f_1 g_1 h
  leftUnitor_eqToIso := by
    intro a b f_1
    -- Compare isomorphisms on the underlying ambient `2`-cell component of their `hom`.
    apply Iso.ext
    apply TwoHom.ext
    -- Rewrite the `eqToIso` side to the `eqToHom` of the apex-map equality proved above.
    have hhom : congrArg Hom.hom (strict_id_comp_hom f_1) = Strict.id_comp f_1.hom := by
      exact Subsingleton.elim _ _
    rw [eqToIso.hom, eqToHom_hom_component, hhom]
    -- The remaining statement is exactly the ambient strict left-unitor compatibility.
    simpa using congrArg Iso.hom (Strict.leftUnitor_eqToIso f_1.hom)
  rightUnitor_eqToIso := by
    intro a b f_1
    -- Compare isomorphisms on the underlying ambient `2`-cell component of their `hom`.
    apply Iso.ext
    apply TwoHom.ext
    -- Rewrite the `eqToIso` side to the `eqToHom` of the apex-map equality proved above.
    have hhom : congrArg Hom.hom (strict_comp_id_hom f_1) = Strict.comp_id f_1.hom := by
      exact Subsingleton.elim _ _
    rw [eqToIso.hom, eqToHom_hom_component, hhom]
    -- The remaining statement is exactly the ambient strict right-unitor compatibility.
    simpa using congrArg Iso.hom (Strict.rightUnitor_eqToIso f_1.hom)
  associator_eqToIso := by
    intro a b c d f_1 g_1 h
    -- Compare isomorphisms on the underlying ambient `2`-cell component of their `hom`.
    apply Iso.ext
    apply TwoHom.ext
    -- Rewrite the `eqToIso` side to the `eqToHom` of the apex-map equality proved above.
    have hhom :
        congrArg Hom.hom (strict_assoc_hom f_1 g_1 h) =
          Strict.assoc f_1.hom g_1.hom h.hom := by
      exact Subsingleton.elim _ _
    rw [eqToIso.hom, eqToHom_hom_component, hhom]
    -- The remaining statement is exactly the ambient strict associator compatibility.
    simpa using congrArg Iso.hom (Strict.associator_eqToIso f_1.hom g_1.hom h.hom)

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

/-! ### Example_4_31_3 (from Chap04) -/
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

open CategoricalPullback
open scoped CategoricalPullback

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable (F : A ⥤ C) (G : B ⥤ C)

/- Domain-style sampling for Example 4.31.3:
- primary domain: categorical pullbacks of functors between categories;
- sampled owner-level declarations:
  `CategoricalPullback`,
  `CategoricalPullback.π₁`,
  `CategoricalPullback.π₂`,
  `CategoricalPullback.catCommSq`;
- best owner abstraction: the canonical pullback owner `F ⊡ G`;
- primitive data: owned by `CategoricalPullback`;
- derived API: the projection functors `π₁ F G`, `π₂ F G`, and the canonical square `catCommSq`.

Source/core/bridge triage:
- `source-facing`: the textbook `2`-fibre product category attached to `F` and `G`;
- `core/canonical`: `F ⊡ G`;
- `bridge/view`: the projection functors and their canonical commutative square. -/

/- Example 4.31.3: the textbook `2`-fibre product category attached to functors `F : A ⥤ C` and
`G : B ⥤ C` is the canonical categorical pullback `F ⊡ G`. -/
#check (F ⊡ G)

/- Companion check: the first projection `F ⊡ G ⥤ A` is the canonical functor `π₁ F G`. -/
#check (π₁ F G : F ⊡ G ⥤ A)

/- Companion check: the second projection `F ⊡ G ⥤ B` is the canonical functor `π₂ F G`. -/
#check (π₂ F G : F ⊡ G ⥤ B)

/- Companion check: the canonical commutative square
`CatCommSq (π₁ F G) (π₂ F G) F G` is the instance `catCommSq`. -/
#check (inferInstance : CatCommSq (π₁ F G) (π₂ F G) F G)

end CategoryTheory.Limits

/-! ### Lemma_4_31_4 (from Chap04) -/
open scoped Bicategory

universe w v u

namespace CategoryTheory.Limits

open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped Bicategory CategoricalPullback

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {C : Type (max u v)} [Category.{v} C]
variable (F : A ⥤ C) (G : B ⥤ C)

/- Domain-style sampling for Lemma 4.31.4:
- primary domain: bicategorical `2`-fibre products in `Cat`, presented through the categorical
  pullback model of Example `4.31.3`;
- inspected owner-level declarations:
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`,
  `CategoricalPullback.toCatCommSqOver`,
  `CatCommSqOver.toBicategoricalSquare`,
  `CategoricalPullback.functorEquiv`;
- best owner abstraction: the chapter's source-facing owner is
  `Bicategory.IsFinal (categoricalPullbackSquare F G)`, where the square itself is the canonical
  pullback square from Example `4.31.3` viewed in the bicategory of `2`-commutative squares;
- primitive data: the categorical pullback object `F ⊡ G` and its canonical square
  `toCatCommSqOver F G (F ⊡ G)`;
- derived API: the universal property equivalence `CategoricalPullback.functorEquiv F G X`,
  transferred to the chapter's square owner by `CatCommSqOver.toBicategoricalSquare`.

Source/core/bridge triage:
- `source-facing`: the square `categoricalPullbackSquare F G` and its `2`-fibre-product property;
- `core/canonical`: `Bicategory.IsFinal (categoricalPullbackSquare F G)`;
- `bridge/view`: `CategoricalPullback.functorEquiv F G X` and
  `CatCommSqOver.toBicategoricalSquare`. -/

/-- The canonical square from Example 4.31.3, viewed as an object of the chapter's bicategory of
`2`-commutative squares over `F` and `G`. -/
abbrev categoricalPullbackSquare :
    BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom :=
  ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).toBicategoricalSquare

/-- Helper for Lemma 4.31.4: reinterpret a bicategorical square in `Cat` as a categorical
commutative square over `F` and `G`. -/
abbrev as_catCommSqOver
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom) :
    CatCommSqOver F G S.obj :=
  { fst := S.p.toFunctor
    snd := S.q.toFunctor
    iso := Cat.Hom.toNatIso S.ψ }

/-- Helper for Lemma 4.31.4: the compatibility condition of a morphism in `CatCommSqOver`,
evaluated at an object, is exactly the objectwise bicategorical square equation in `Cat`. -/
lemma catCommSqOver_hom_to_square_hom_comm
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom)
    (J : S.obj ⥤ F ⊡ G)
    (φ : (toCatCommSqOver F G S.obj).obj J ⟶ as_catCommSqOver F G S)
    (x : S.obj) :
    (Cat.Hom₂.toNatTrans
        ((φ.fst.toCatHom₂ ▷ F.toCatHom) ≫ S.ψ.hom)).app x =
      (Cat.Hom₂.toNatTrans
        ((α_ J.toCatHom (categoricalPullbackSquare F G).p F.toCatHom).hom ≫
          J.toCatHom ◁ (categoricalPullbackSquare F G).ψ.hom ≫
          (α_ J.toCatHom (categoricalPullbackSquare F G).q G.toCatHom).inv ≫
          (φ.snd.toCatHom₂ ▷ G.toCatHom))).app x := by
  let mid := (((toCatCommSqOver F G S.obj).obj J).iso.hom.app x) ≫ G.map (φ.snd.app x)
  -- Route correction: compare both sides with the common `CatCommSqOver` midpoint
  -- `((toCatCommSqOver ...).obj J).iso.hom.app x ≫ G.map (φ.snd.app x)`.
  have hw :
      (Cat.Hom₂.toNatTrans ((φ.fst.toCatHom₂ ▷ F.toCatHom) ≫ S.ψ.hom)).app x = mid := by
    -- This is exactly the objectwise compatibility equation of `φ`.
    simpa [mid, as_catCommSqOver] using
      (CatCommSqOver.w_app
        (F := F) (G := G) (X := S.obj) (S := (toCatCommSqOver F G S.obj).obj J)
        (S' := as_catCommSqOver F G S) φ x)
  have hr :
      (Cat.Hom₂.toNatTrans
        ((α_ J.toCatHom (categoricalPullbackSquare F G).p F.toCatHom).hom ≫
          J.toCatHom ◁ (categoricalPullbackSquare F G).ψ.hom ≫
          (α_ J.toCatHom (categoricalPullbackSquare F G).q G.toCatHom).inv ≫
          (φ.snd.toCatHom₂ ▷ G.toCatHom))).app x = mid := by
    -- The canonical pullback square term reduces to the same midpoint after expanding the
    -- remaining ordinary natural-transformation compositions.
    repeat rw [Cat.Hom₂.comp_app]
    rw [Cat.associator_hom_app]
    have hnat :
        (J.whiskerLeft ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom ≫
            (J.associator ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).snd G).inv ≫
            Functor.whiskerRight φ.snd G).app x = mid := by
      repeat rw [NatTrans.comp_app]
      simp [mid]
    have h1 :
        𝟙 (F.obj (J.obj x).fst) ≫
          (J.whiskerLeft ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom ≫
              (J.associator ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).snd G).inv ≫
              Functor.whiskerRight φ.snd G).app x =
            (J.whiskerLeft ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom ≫
              (J.associator ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).snd G).inv ≫
              Functor.whiskerRight φ.snd G).app x := by
      simp
    exact h1.trans hnat
  exact hw.trans hr.symm

/-- Helper for Lemma 4.31.4: the compatibility field of a bicategorical square morphism into the
canonical pullback square becomes the natural-transformation equation required in
`CatCommSqOver` after applying `toNatTrans` and evaluating at an object. -/
lemma square_hom_comm_to_catCommSqOver_w
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom)
    (u : S ⟶ categoricalPullbackSquare F G)
    (x : S.obj) :
    F.map (u.left.toNatTrans.app x) ≫ S.ψ.hom.toNatTrans.app x =
      (((toCatCommSqOver F G S.obj).obj u.hom.toFunctor).iso.hom.app x) ≫
        G.map (u.right.toNatTrans.app x) := by
  -- Route correction: expand `u.comm` to an objectwise equality in `Cat`, then compare its
  -- right-hand side with the pullback object's structural isomorphism.
  have h := congrArg Cat.Hom₂.toNatTrans u.comm
  have h' := congrArg (fun τ ↦ τ.app x) h
  let rhs' :=
    (Cat.Hom₂.toNatTrans
      ((α_ u.hom (categoricalPullbackSquare F G).p F.toCatHom).hom ≫
        u.hom ◁ (categoricalPullbackSquare F G).ψ.hom ≫
        (α_ u.hom (categoricalPullbackSquare F G).q G.toCatHom).inv ≫
        (u.right ▷ G.toCatHom))).app x
  have hr :
      rhs' = (((toCatCommSqOver F G S.obj).obj u.hom.toFunctor).iso.hom.app x) ≫
        G.map (u.right.toNatTrans.app x) := by
    -- The canonical pullback square term collapses to the pullback object's internal `iso.hom`
    -- after expanding the remaining ordinary natural-transformation compositions.
    dsimp [rhs']
    have hnat :
        (u.hom.toFunctor.whiskerLeft ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom ≫
            (u.hom.toFunctor.associator ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).snd G).inv ≫
            Functor.whiskerRight u.right.toNatTrans G).app x =
          (((toCatCommSqOver F G S.obj).obj u.hom.toFunctor).iso.hom.app x) ≫
            G.map (u.right.toNatTrans.app x) := by
      repeat rw [NatTrans.comp_app]
      simp
    have h1 :
        𝟙 (F.obj (u.hom.toFunctor.obj x).fst) ≫
          (u.hom.toFunctor.whiskerLeft ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom ≫
              (u.hom.toFunctor.associator ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).snd G).inv ≫
              Functor.whiskerRight u.right.toNatTrans G).app x =
            (u.hom.toFunctor.whiskerLeft ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom ≫
              (u.hom.toFunctor.associator ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).snd G).inv ≫
              Functor.whiskerRight u.right.toNatTrans G).app x := by
      simp
    exact h1.trans hnat
  -- After the owner-level normalization, `u.comm` becomes the desired `CatCommSqOver` equation.
  simpa [rhs', Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app, Category.assoc] using h'.trans hr

/-- Helper for Lemma 4.31.4: a morphism of categorical squares over `F` and `G` yields a
`1`-morphism from the corresponding bicategorical square to the canonical pullback square. -/
abbrev catCommSqOver_hom_to_square_hom
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom)
    (J : S.obj ⥤ F ⊡ G)
    (φ : (toCatCommSqOver F G S.obj).obj J ⟶ as_catCommSqOver F G S) :
    S ⟶ categoricalPullbackSquare F G := by
  refine
    { hom := J.toCatHom
      left := φ.fst.toCatHom₂
      right := φ.snd.toCatHom₂
      comm := ?_ }
  -- The commutativity field is the objectwise square equation transported through `Cat`.
  apply Cat.Hom₂.ext
  ext x
  exact catCommSqOver_hom_to_square_hom_comm F G S J φ x

/-- Helper for Lemma 4.31.4: a morphism into the canonical pullback square is the same data as a
morphism in `CatCommSqOver` from its apex functor to the original square. -/
abbrev hom_to_catCommSqOver_hom
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom)
    (u : S ⟶ categoricalPullbackSquare F G) :
    (toCatCommSqOver F G S.obj).obj u.hom.toFunctor ⟶ as_catCommSqOver F G S := by
  refine
    { fst := u.left.toNatTrans
      snd := u.right.toNatTrans
      w := ?_ }
  -- The bicategorical square equation becomes the `CatCommSqOver` compatibility field.
  ext x
  exact square_hom_comm_to_catCommSqOver_w F G S u x

/-- Helper for Lemma 4.31.4: the textbook factorization through `A ×[C] B` obtained by sending an
object `W` to the triple `(a(W), b(W), t_W)`. -/
abbrev terminal_lift
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom) :
    S ⟶ categoricalPullbackSquare F G :=
  catCommSqOver_hom_to_square_hom F G S
    ((CatCommSqOver.toFunctorToCategoricalPullback F G S.obj).obj (as_catCommSqOver F G S))
    (((CategoricalPullback.functorEquiv F G S.obj).counitIso.app (as_catCommSqOver F G S)).hom)

/-- Helper for Lemma 4.31.4: a `2`-morphism between factorizations is equivalent to equality of the
induced morphisms in `CatCommSqOver`. -/
lemma twoHom_to_catCommSqOver_hom
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom)
    {u v : S ⟶ categoricalPullbackSquare F G}
    (η : u ⟶ v) :
    (toCatCommSqOver F G S.obj).map η.hom.toNatTrans ≫ hom_to_catCommSqOver_hom F G S v =
      hom_to_catCommSqOver_hom F G S u := by
  -- The induced equality is detected on the two projection components in `CatCommSqOver`.
  apply CatCommSqOver.hom_ext
  · ext x
    -- The first projection is exactly the left compatibility condition of `η`.
    simpa [hom_to_catCommSqOver_hom, categoricalPullbackSquare] using
      congrArg (fun τ => τ.app x) (congrArg Cat.Hom₂.toNatTrans η.left_comm)
  · ext x
    -- The second projection is exactly the right compatibility condition of `η`.
    simpa [hom_to_catCommSqOver_hom, categoricalPullbackSquare] using
      congrArg (fun τ => τ.app x) (congrArg Cat.Hom₂.toNatTrans η.right_comm)

/-- Helper for Lemma 4.31.4: the `CatCommSqOver` morphism attached to `terminal_lift` is the
counit of the categorical pullback equivalence. -/
lemma hom_to_catCommSqOver_hom_terminal_lift
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom) :
    hom_to_catCommSqOver_hom F G S (terminal_lift F G S) =
      ((CategoricalPullback.functorEquiv F G S.obj).counitIso.app
        (as_catCommSqOver F G S)).hom := by
  -- Both morphisms have the same two projection components, so `hom_ext` closes the comparison.
  apply CatCommSqOver.hom_ext <;> rfl

/-- Helper for Lemma 4.31.4: every morphism into the canonical pullback square admits a unique
`2`-morphism to the canonical factorization `terminal_lift`. -/
noncomputable abbrev hom_to_terminal_unique
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom)
    (u : S ⟶ categoricalPullbackSquare F G) :
    Unique (u ⟶ terminal_lift F G S) := by
  let E := (CategoricalPullback.functorEquiv F G S.obj).functor
  let counit := (CategoricalPullback.functorEquiv F G S.obj).counitIso.app
    (as_catCommSqOver F G S)
  let δ := E.preimage (hom_to_catCommSqOver_hom F G S u ≫ counit.inv)
  have hterminal :
      hom_to_catCommSqOver_hom F G S (terminal_lift F G S) = counit.hom := by
    simpa [counit] using hom_to_catCommSqOver_hom_terminal_lift F G S
  have hpre :
      (toCatCommSqOver F G S.obj).map δ =
        hom_to_catCommSqOver_hom F G S u ≫ counit.inv := by
    simpa [E, δ, counit] using
      (E.map_preimage (hom_to_catCommSqOver_hom F G S u ≫ counit.inv))
  have hδ :
      (toCatCommSqOver F G S.obj).map δ ≫ hom_to_catCommSqOver_hom F G S (terminal_lift F G S) =
        hom_to_catCommSqOver_hom F G S u := by
    have hδc :
        (toCatCommSqOver F G S.obj).map δ ≫ counit.hom =
          hom_to_catCommSqOver_hom F G S u := by
      rw [hpre]
      have h :
          (hom_to_catCommSqOver_hom F G S u ≫ counit.inv) ≫ counit.hom =
            hom_to_catCommSqOver_hom F G S u := by
        simp [Category.assoc]
      exact h
    simpa [hterminal] using hδc
  let η0 : u ⟶ terminal_lift F G S :=
    { hom := δ.toCatHom₂
      left_comm := by
        simpa [δ, hom_to_catCommSqOver_hom] using
          congrArg NatTrans.toCatHom₂ (congrArg CatCommSqOver.Hom.fst hδ)
      right_comm := by
        simpa [δ, hom_to_catCommSqOver_hom] using
          congrArg NatTrans.toCatHom₂ (congrArg CatCommSqOver.Hom.snd hδ) }
  refine { default := η0, uniq := ?_ }
  intro η
  apply BicategoricalTwoCommutativeSquare.TwoHom.ext
  have hη :
      (toCatCommSqOver F G S.obj).map η.hom.toNatTrans ≫
        hom_to_catCommSqOver_hom F G S (terminal_lift F G S) =
      hom_to_catCommSqOver_hom F G S u :=
    twoHom_to_catCommSqOver_hom F G S η
  have hηc :
      (toCatCommSqOver F G S.obj).map η.hom.toNatTrans ≫ counit.hom =
        hom_to_catCommSqOver_hom F G S u := by
    simpa [hterminal] using hη
  have hη' :
      (toCatCommSqOver F G S.obj).map η.hom.toNatTrans =
        hom_to_catCommSqOver_hom F G S u ≫ counit.inv := by
    exact (CategoryTheory.Iso.eq_comp_inv counit).2 hηc
  exact congrArg NatTrans.toCatHom₂ (E.map_injective (hη'.trans hpre.symm))

/-- Lemma 4.31.4: the canonical square carried by the categorical pullback `F ⊡ G` is a
`2`-fibre product square in the bicategory of `2`-commutative squares over `F` and `G`. -/
theorem categoricalPullback_isTwoFibreProduct :
    Bicategory.IsFinal (categoricalPullbackSquare F G) := by
  -- For each source square, the hom-category into the pullback square has a terminal factorization.
  refine ⟨fun S ↦ ?_⟩
  -- The chosen factorization is `terminal_lift`, and uniqueness follows from the pullback
  -- equivalence transported through `CatCommSqOver`.
  let _ : ∀ Y : S ⟶ categoricalPullbackSquare F G, Unique (Y ⟶ terminal_lift F G S) :=
    fun Y ↦ hom_to_terminal_unique F G S Y
  exact Limits.hasTerminal_of_unique (terminal_lift F G S)

/- Companion bridge/view: the universal property above is implemented by the canonical pullback
equivalence between functors into `F ⊡ G` and commutative squares over `F` and `G`. -/
recall CategoricalPullback.functorEquiv

end CategoryTheory.Limits

/-! ### Remark_4_31_5 (from Chap04) -/
namespace CategoryTheory.Limits

open CategoryTheory.Prod
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

/- Domain-style sampling for Remark 4.31.5:
- primary domain: categorical pullbacks of functors between categories;
- sampled owner-level declarations:
  `CategoricalPullback`,
  `CategoricalPullback.toCatCommSqOver`,
  `CategoricalPullback.CatCommSqOver`,
  `CatCommSqOver.toFunctorToCategoricalPullback`,
  `CategoricalPullback.functorEquiv`,
  `Functor.prod`,
  `Functor.diag`;
- best owner abstraction for the source model: the diagonal pullback
  `(F.prod G) ⊡ (Functor.diag C)`;
- core/canonical owner abstraction for the ordinary `2`-fibre product: `F ⊡ G`.

Primitive-vs-derived split:
- primitive data of the source-facing symmetric model: the canonical diagonal square
  `toCatCommSqOver (F.prod G) (Functor.diag C) ((F.prod G) ⊡ (Functor.diag C))`
  applied to `𝟭 _`;
- derived API: the projected square over `F` and `G`, the comparison functor to `F ⊡ G`, and the
  resulting equivalence.

Source/core/bridge triage:
- `source-facing`: `(F.prod G) ⊡ (Functor.diag C)`;
- `core/canonical`: `F ⊡ G`;
- `bridge/view`: `symmetricTwoFibreProductComparison` and
  `symmetricTwoFibreProductEquivalence`. -/

private abbrev SymmetricModel (F : A ⥤ C) (G : B ⥤ C) :=
  (F.prod G) ⊡ (Functor.diag C)

private abbrev diagonalSourceSquare (F : A ⥤ C) (G : B ⥤ C) :
    CatCommSqOver (F.prod G) (Functor.diag C) (SymmetricModel F G) :=
  (toCatCommSqOver (F.prod G) (Functor.diag C) (SymmetricModel F G)).obj (𝟭 _)

private def leftComponentIso
    (F : A ⥤ C) (G : B ⥤ C)
    {X : Type*} [Category X]
    {Φ : X ⥤ A × B} {Λ : X ⥤ C}
    (σ : Φ ⋙ (F.prod G) ≅ Λ ⋙ Functor.diag C) :
    Φ ⋙ fst A B ⋙ F ≅ Λ :=
  NatIso.ofComponents
    (fun X ↦ by simpa using (fst C C).mapIso (σ.app X))
    (fun {_ _} f ↦ by
      simpa using congrArg _root_.Prod.fst (σ.hom.naturality f))

private def rightComponentIso
    (F : A ⥤ C) (G : B ⥤ C)
    {X : Type*} [Category X]
    {Φ : X ⥤ A × B} {Λ : X ⥤ C}
    (σ : Φ ⋙ (F.prod G) ≅ Λ ⋙ Functor.diag C) :
    Φ ⋙ snd A B ⋙ G ≅ Λ :=
  NatIso.ofComponents
    (fun X ↦ by simpa using (snd C C).mapIso (σ.app X))
    (fun {_ _} f ↦ by
      simpa using congrArg _root_.Prod.snd (σ.hom.naturality f))

private abbrev ordinarySquare
    (F : A ⥤ C) (G : B ⥤ C)
    {X : Type*} [Category X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) :
    CatCommSqOver F G X where
  fst := P.fst ⋙ fst A B
  snd := P.fst ⋙ snd A B
  iso := leftComponentIso F G P.iso ≪≫ (rightComponentIso F G P.iso).symm

/-- Remark 4.31.5: the symmetric quintuple model
`(A, B, C, F(A) ≅ C, G(B) ≅ C)` is the canonical diagonal pullback
`(F.prod G) ⊡ (Functor.diag C)`. The functor below is its canonical comparison
to the standard pullback owner `F ⊡ G`; the `IsEquivalence` instance below expresses that this
comparison is an equivalence. -/
abbrev symmetricTwoFibreProductComparison (F : A ⥤ C) (G : B ⥤ C) :
    (F.prod G) ⊡ (Functor.diag C) ⥤ F ⊡ G :=
  (toFunctorToCategoricalPullback F G (SymmetricModel F G)).obj
    (ordinarySquare F G (diagonalSourceSquare F G))

-- Proof sketch: use the explicit quasi-inverse `symmetricInverse F G` together with the unit and
-- counit isomorphisms `symmetricUnitIso F G` and `symmetricCounitIso F G`, then apply
-- `Functor.IsEquivalence.mk'`.
private def symmetricInverse (F : A ⥤ C) (G : B ⥤ C) :
    F ⊡ G ⥤ SymmetricModel F G where
  obj X :=
    { fst := (X.fst, X.snd)
      snd := G.obj X.snd
      iso := Iso.prod X.iso (.refl _) }
  map {X Y} f :=
    { fst := f.fst ×ₘ f.snd
      snd := G.map f.snd
      w := by
        ext <;> simp [f.w] }

private def symmetricUnitIso (F : A ⥤ C) (G : B ⥤ C) :
    𝟭 (SymmetricModel F G) ≅ symmetricTwoFibreProductComparison F G ⋙ symmetricInverse F G :=
  CategoricalPullback.mkNatIso
    (NatIso.ofComponents
      (fun X ↦ (prod.etaIso X.fst).symm)
      (fun {_ _} f ↦ by
        ext <;> simp [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
          diagonalSourceSquare, leftComponentIso, rightComponentIso]))
    (NatIso.ofComponents
      (fun X ↦ ((rightComponentIso F G (diagonalSourceSquare F G).iso).app X).symm)
      (fun {_ _} f ↦ by
        simpa [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
          diagonalSourceSquare, leftComponentIso, rightComponentIso] using
          congrArg _root_.Prod.snd f.w'))
    (by
      ext X
      · simp [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
          diagonalSourceSquare, leftComponentIso, rightComponentIso]
      · suffices 𝟙 (G.obj X.fst.2) = X.iso.hom.2 ≫ X.iso.inv.2 by
          simpa [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
            diagonalSourceSquare, leftComponentIso, rightComponentIso] using this
        exact (congrArg _root_.Prod.snd X.iso.hom_inv_id).symm)

private def symmetricCounitIso (F : A ⥤ C) (G : B ⥤ C) :
    symmetricInverse F G ⋙ symmetricTwoFibreProductComparison F G ≅ 𝟭 (F ⊡ G) :=
  CategoricalPullback.mkNatIso
    (NatIso.ofComponents
      (fun X ↦ .refl _)
      (fun {_ _} f ↦ by
        simp [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
          diagonalSourceSquare, leftComponentIso, rightComponentIso]))
    (NatIso.ofComponents
      (fun X ↦ .refl _)
      (fun {_ _} f ↦ by
        simp [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
          diagonalSourceSquare, leftComponentIso, rightComponentIso]))
    (by
      ext X
      simp [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
        diagonalSourceSquare, leftComponentIso, rightComponentIso])

/-- The canonical comparison from the symmetric diagonal pullback model to the ordinary pullback
owner is an equivalence of categories. -/
theorem symmetricTwoFibreProductComparison_isEquivalence
    (F : A ⥤ C) (G : B ⥤ C) :
    (symmetricTwoFibreProductComparison F G).IsEquivalence := by
  -- The explicit inverse and the unit/counit isomorphisms already realize the comparison as an
  -- equivalence, so it remains only to package that data with `Functor.IsEquivalence.mk'`.
  exact
    Functor.IsEquivalence.mk'
      (symmetricInverse F G)
      (symmetricUnitIso F G)
      (symmetricCounitIso F G)

noncomputable instance
    (F : A ⥤ C) (G : B ⥤ C) :
    (symmetricTwoFibreProductComparison F G).IsEquivalence :=
  symmetricTwoFibreProductComparison_isEquivalence F G

end

end CategoryTheory.Limits

/-! ### Lemma_4_31_6 (from Chap04) -/
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]

/- Domain-style sampling for Lemma 4.31.6:
- primary domain: categorical pullbacks and their functoriality with respect to
  `2`-commutative cospan maps;
- sampled owner-level declarations:
  `CategoricalPullback.toCatCommSqOver`,
  `Limits.CatCospanTransform`,
  `CategoricalPullback.catCommSq`,
  `CategoricalPullback.CatCommSqOver.transform`,
  `CategoricalPullback.functorEquiv`,
  `CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback`;
- best owner abstraction: the primitive source data are a
  `Limits.CatCospanTransform H I F G`; applying `CatCommSqOver.transform` to the canonical source
  square `CategoricalPullback.catCommSq H I` produces the derived square in
  `CatCommSqOver F G (H ⊡ I)`;
- primitive data: the three component functors together with the two comparison squares, and the
  canonical source square over `H` and `I`;
- derived API: the transformed square over `F` and `G`, and then the induced functor between the
  categorical pullbacks of the source and target cospans through the owner equivalence
  `CategoricalPullback.functorEquiv`.

Source/core/bridge triage:
- `source-facing`: the textbook functor determined by isomorphisms
  `α : K ⋙ G ≅ I ⋙ M` and `β : H ⋙ M ≅ L ⋙ F`;
- `core/canonical`: `Limits.CatCospanTransform H I F G`;
- `bridge/view`: the induced square on pullback categories obtained by
  `CatCommSqOver.transform`, followed by the comparison functor
  `CatCommSqOver.toFunctorToCategoricalPullback`; the chapter's bicategorical square owner is a
  later companion view. -/

section

variable {H : X ⥤ Z} {I : Y ⥤ Z} {L : X ⥤ A} {K : Y ⥤ B}
variable {M : Z ⥤ C} {F : A ⥤ C} {G : B ⥤ C}

/- Primitive owner data for the induced map of categorical pullbacks are exactly the comparison
isomorphisms `α`, `β`, assembled directly into a `CatCospanTransform H I F G`. The public functor
`two_fibre_product_map` is then the canonical bridge obtained by transforming the canonical source
square in `CatCommSqOver H I (H ⊡ I)` and applying `toFunctorToCategoricalPullback`. -/

private abbrev two_fibre_product_cospanTransform
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) :
    CatCospanTransform H I F G :=
  { left := L
    base := M
    right := K
    squareLeft := ⟨β⟩
    squareRight := ⟨α.symm⟩ }

private abbrev two_fibre_product_sourceSquare :
    CatCommSqOver H I (H ⊡ I) :=
  (toCatCommSqOver H I (H ⊡ I)).obj (𝟭 (H ⊡ I))

private abbrev two_fibre_product_targetSquare
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) :
    CatCommSqOver F G (H ⊡ I) :=
  ((transform (H ⊡ I)).obj (two_fibre_product_cospanTransform α β)).obj
    two_fibre_product_sourceSquare

/-- Lemma 4.31.6: a `2`-commutative diagram with chosen isomorphisms
`α : K ⋙ G ≅ I ⋙ M` and `β : H ⋙ M ≅ L ⋙ F` induces a canonical functor
`X ×[Z] Y ⥤ A ×[C] B`. -/
abbrev two_fibre_product_map
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) :
    H ⊡ I ⥤ F ⊡ G :=
  (toFunctorToCategoricalPullback F G (H ⊡ I)).obj (two_fibre_product_targetSquare α β)

/-- The canonical `2`-fibre product map is obtained by applying the pullback comparison functor to
the transformed square determined by `α` and `β`. -/
theorem two_fibre_product_map_def
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) :
    two_fibre_product_map α β =
      (toFunctorToCategoricalPullback F G (H ⊡ I)).obj (two_fibre_product_targetSquare α β) :=
  rfl

@[simp] theorem two_fibre_product_map_obj_fst
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) (P : H ⊡ I) :
    ((two_fibre_product_map α β).obj P).fst = L.obj P.fst :=
  rfl

@[simp] theorem two_fibre_product_map_obj_snd
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) (P : H ⊡ I) :
    ((two_fibre_product_map α β).obj P).snd = K.obj P.snd :=
  rfl

@[simp] theorem two_fibre_product_map_obj_iso_hom
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F) (P : H ⊡ I) :
    ((two_fibre_product_map α β).obj P).iso.hom =
      β.inv.app P.fst ≫ M.map P.iso.hom ≫ α.inv.app P.snd :=
  by
    cases α
    cases β
    simp [two_fibre_product_map, two_fibre_product_targetSquare,
      two_fibre_product_cospanTransform, CatCommSq.iso]

@[simp] theorem two_fibre_product_map_map_fst
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)
    {P Q : H ⊡ I} (f : P ⟶ Q) :
    ((two_fibre_product_map α β).map f).fst = L.map f.fst :=
  rfl

@[simp] theorem two_fibre_product_map_map_snd
    (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)
    {P Q : H ⊡ I} (f : P ⟶ Q) :
    ((two_fibre_product_map α β).map f).snd = K.map f.snd :=
  rfl

end

end CategoryTheory
