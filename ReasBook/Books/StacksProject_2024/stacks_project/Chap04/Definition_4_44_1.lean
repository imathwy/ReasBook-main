import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/- Domain-style sampling for Definition 4.44.1:
- primary domain: bicategorical `2`-commutative squares together with left-lift data;
- owner abstractions inspected: `BicategoricalTwoCommutativeSquare`, `LeftLift`,
  `LeftLift.whiskering`, and the canonical morphism category on `LeftLift`;
- triage:
  `source-facing`: the dotted-arrow data attached to a chosen `2`-commutative square,
  `core/canonical`: the square owner `BicategoricalTwoCommutativeSquare` together with the
  whiskered owner category `LeftLift p (sq.p ≫ y)`,
  `bridge/view`: the dotted-arrow category and its locally-groupoidal consequences;
- primitive data: a chosen square `sq : BicategoricalTwoCommutativeSquare y p`, a lift
  `toLeftLift : LeftLift p y` with invertible unit, and an isomorphism from its whiskering along
  `sq.p` to the canonical `LeftLift` encoded by `sq`;
- derived API: the dotted morphism itself, the upper-left and lower-right comparison
  `2`-isomorphisms, the category structure on `DottedArrow sq` with canonical hom type `A ⟶ A'`,
  the postcomposition square/functor for a right square, and the groupoid structure under local
  groupoid hypotheses. -/

/-- Definition 4.44.1: for a chosen `2`-commutative square `sq` over `y : T ⟶ Y` and
`p : X ⟶ Y`, a dotted arrow consists of the canonical bicategorical left-lift datum for the right
triangle, together with an isomorphism in the whiskered owner category identifying the induced
upper-left comparison with the canonical one attached to `sq`. The source-facing Stacks condition
that the right-triangle comparison is invertible remains part of the data. -/
structure DottedArrow
    {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
    (sq : BicategoricalTwoCommutativeSquare y p) where
  /-- The canonical left-lift datum encoding the right triangle `y ⟶ arrow ≫ p`. -/
  toLeftLift : LeftLift p y
  /-- The right-triangle comparison is invertible. -/
  unit_isIso : IsIso toLeftLift.unit
  /-- The induced upper-left comparison, promoted to the whiskered owner category. -/
  comparison : (LeftLift.whiskering sq.p).obj toLeftLift ≅ sq.symm.toLeftLift

attribute [instance] DottedArrow.unit_isIso

namespace DottedArrow

variable {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
variable {sq : BicategoricalTwoCommutativeSquare y p}

/-- Construct the owner-level comparison isomorphism from a source-facing upper-left comparison. -/
noncomputable def comparisonIsoMk
    (t : LeftLift p y) [IsIso t.unit]
    (left : sq.p ≫ t.lift ≅ sq.q)
    (comm :
      sq.p ◁ t.unit ≫ (α_ sq.p t.lift p).inv ≫ left.hom ▷ p =
        sq.ψ.hom) :
    (LeftLift.whiskering sq.p).obj t ≅ sq.symm.toLeftLift :=
  { hom := LeftLift.homMk left.hom <| by
      simpa [LeftLift.whiskering] using comm
    inv := LeftLift.homMk left.inv <| by
      sorry
    hom_inv_id := by
      apply StructuredArrow.hom_ext
      exact left.hom_inv_id
    inv_hom_id := by
      apply StructuredArrow.hom_ext
      exact left.inv_hom_id }

/-- The dotted morphism `T ⟶ X`. -/
abbrev arrow (A : DottedArrow sq) : T ⟶ X :=
  A.toLeftLift.lift

/-- The comparison `2`-isomorphism for the upper-left triangle. -/
noncomputable def left (A : DottedArrow sq) : sq.p ≫ A.arrow ≅ sq.q :=
  let η := A.comparison.hom
  let θ := A.comparison.inv
  { hom := η.right
    inv := θ.right
    hom_inv_id := by
      sorry
    inv_hom_id := by
      sorry }

/-- The comparison `2`-isomorphism for the lower-right triangle. -/
noncomputable def right (A : DottedArrow sq) : y ≅ A.arrow ≫ p :=
  letI := A.unit_isIso
  asIso A.toLeftLift.unit

@[simp]
theorem right_hom (A : DottedArrow sq) :
    A.right.hom = A.toLeftLift.unit := by
  rfl

/-- The two triangular comparison `2`-isomorphisms recover the chosen outer comparison `sq.ψ`. -/
theorem comm (A : DottedArrow sq) :
    whiskerLeftIso sq.p A.right ≪≫
        (α_ sq.p A.arrow p).symm ≪≫
          whiskerRightIso A.left p =
      sq.ψ := by
  ext
  simpa [left, right] using LeftLift.w A.comparison.hom

end DottedArrow

namespace DottedArrow

variable {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
variable {sq : BicategoricalTwoCommutativeSquare y p}

/-- A morphism of dotted arrows is a morphism in the canonical left-lift category together with
compatibility with the upper-left comparison `2`-isomorphisms. The lower-right compatibility is
already owned by the underlying `LeftLift` morphism. -/
abbrev Hom (A A' : DottedArrow sq) :=
  { η : A.toLeftLift ⟶ A'.toLeftLift //
      (LeftLift.whiskering sq.p).map η ≫ A'.comparison.hom = A.comparison.hom }

namespace Hom

variable {A A' : DottedArrow sq}

/-- The underlying morphism in the canonical left-lift category. -/
private abbrev toLeftLiftHom (η : Hom A A') : A.toLeftLift ⟶ A'.toLeftLift :=
  η.1

/-- The ambient `2`-morphism between the dotted morphisms. -/
abbrev right (η : Hom A A') : A.arrow ⟶ A'.arrow :=
  η.1.right

/-- Compatibility with the upper-left comparison `2`-isomorphisms. -/
@[reassoc, simp]
theorem left_comm (η : Hom A A') :
    sq.p ◁ η.right ≫ A'.left.hom = A.left.hom :=
  by
    simpa [DottedArrow.left, LeftLift.whiskering] using
      congrArg (fun f ↦ f.right) η.2

/-- Compatibility with the lower-right comparison `2`-isomorphisms. -/
@[reassoc, simp]
theorem right_comm (η : Hom A A') :
    A.right.hom ≫ η.right ▷ p = A'.right.hom := by
  simp [LeftLift.w η.toLeftLiftHom]

@[ext]
theorem ext
    {η θ : Hom A A'}
    (h : η.right = θ.right) :
    η = θ := by
  apply Subtype.ext
  exact StructuredArrow.hom_ext η.1 θ.1 h

end Hom

/-- The identity morphism of a dotted arrow. -/
private def idHom (A : DottedArrow sq) : Hom A A :=
  ⟨𝟙 A.toLeftLift, by
    simp
  ⟩

/-- The ambient `2`-morphism of `idHom`. -/
@[simp]
private theorem idHom_right (A : DottedArrow sq) :
    (idHom A).right = 𝟙 A.arrow :=
  rfl

/-- Composition of morphisms of dotted arrows. -/
private def compHom
    {A B C : DottedArrow sq}
    (η : Hom A B) (θ : Hom B C) :
    Hom A C :=
  ⟨η.toLeftLiftHom ≫ θ.toLeftLiftHom, by
    rw [Functor.map_comp, Category.assoc, θ.2]
    exact η.2
  ⟩

/-- The ambient `2`-morphism of `compHom`. -/
@[simp]
private theorem compHom_right
    {A B C : DottedArrow sq}
    (η : Hom A B) (θ : Hom B C) :
    (compHom η θ).right = η.right ≫ θ.right :=
  rfl

private theorem id_comp
    {A B : DottedArrow sq}
    (η : Hom A B) :
    compHom (idHom A) η = η := by
  apply Hom.ext
  change (𝟙 A.toLeftLift ≫ η.toLeftLiftHom).right = η.right
  simp

private theorem comp_id
    {A B : DottedArrow sq}
    (η : Hom A B) :
    compHom η (idHom B) = η := by
  apply Hom.ext
  change (η.toLeftLiftHom ≫ 𝟙 B.toLeftLift).right = η.right
  simp

private theorem assoc
    {A B C D : DottedArrow sq}
    (η : Hom A B) (θ : Hom B C) (ι : Hom C D) :
    compHom (compHom η θ) ι = compHom η (compHom θ ι) := by
  apply Hom.ext
  change ((η.toLeftLiftHom ≫ θ.toLeftLiftHom) ≫ ι.toLeftLiftHom).right =
      (η.toLeftLiftHom ≫ (θ.toLeftLiftHom ≫ ι.toLeftLiftHom)).right
  simp

/-- The dotted arrows for a fixed `2`-commutative square form a category. -/
instance : Category (DottedArrow sq) where
  Hom A B := Hom A B
  id := idHom
  comp η θ := compHom η θ
  id_comp := id_comp
  comp_id := comp_id
  assoc η θ ι := assoc η θ ι

@[simp]
theorem id_right (A : DottedArrow sq) :
    (𝟙 A : A ⟶ A).right = 𝟙 A.arrow :=
  idHom_right A

@[simp]
theorem comp_right
    {A B C : DottedArrow sq}
    (η : A ⟶ B) (θ : B ⟶ C) :
    (η ≫ θ).right = η.right ≫ θ.right :=
  compHom_right η θ

section LocallyGroupoid

variable [Bicategory.IsLocallyGroupoid B]

/-- In a locally groupoidal bicategory, a morphism of dotted arrows has the inverse `2`-morphism
in the ambient hom-category as its inverse. -/
private noncomputable def invHom
    {A A' : DottedArrow sq}
    (η : A ⟶ A') :
    A' ⟶ A :=
  ⟨LeftLift.homMk (inv η.right) <| by
      haveI : IsIso η.right := inferInstance
      haveI : IsIso (η.right ▷ p) := inferInstance
      have hunit :
          A.toLeftLift.unit ≫ η.right ▷ p = A'.toLeftLift.unit :=
        LeftLift.w η.toLeftLiftHom
      calc
        A'.toLeftLift.unit ≫ inv η.right ▷ p =
            (A.toLeftLift.unit ≫ η.right ▷ p) ≫ inv η.right ▷ p := by
              rw [← hunit]
        _ = A.toLeftLift.unit ≫
              ((η.right ▷ p) ≫ (inv η.right ▷ p)) := by
              rw [Category.assoc]
        _ = A.toLeftLift.unit ≫ 𝟙 (A.arrow ≫ p) := by
              simp
        _ = A.toLeftLift.unit := by
              simp, by
      sorry⟩

@[simp]
private theorem invHom_right
    {A A' : DottedArrow sq}
    (η : A ⟶ A') :
    (invHom η).right = inv η.right :=
  rfl

/-- In a locally groupoidal bicategory, every morphism of dotted arrows is invertible. -/
noncomputable instance
    {A A' : DottedArrow sq}
    (η : A ⟶ A') :
    IsIso η where
  out :=
    ⟨invHom η, by
      haveI : IsIso η.right := inferInstance
      apply Hom.ext
      change (η ≫ invHom η).right = (𝟙 A : A ⟶ A).right
      simp, by
      haveI : IsIso η.right := inferInstance
      apply Hom.ext
      change (invHom η ≫ η).right = (𝟙 A' : A' ⟶ A').right
      simp⟩

/-- In a locally groupoidal bicategory, dotted arrows for a fixed square form a groupoid. -/
noncomputable instance : IsGroupoid (DottedArrow sq) where
  all_isIso η := by infer_instance

end LocallyGroupoid

end DottedArrow

namespace BicategoricalTwoCommutativeSquare

variable {T X' Y' X Y : B} {y : T ⟶ Y'} {p : X' ⟶ Y'}
variable (sq : BicategoricalTwoCommutativeSquare y p)
variable {q : X' ⟶ X} {g : Y' ⟶ Y} {f : X ⟶ Y}

/-- Postcomposing a `2`-commutative square with a right square
`p ≫ g ≅ q ≫ f` gives the outer rectangle over `y ≫ g` and `f`. -/
def postcompose (φ : p ≫ g ≅ q ≫ f) :
    BicategoricalTwoCommutativeSquare (y ≫ g) f :=
  { obj := sq.obj
    p := sq.p
    q := sq.q ≫ q
    ψ :=
      (α_ sq.p y g).symm ≪≫
        whiskerRightIso sq.ψ g ≪≫
          α_ sq.q p g ≪≫
            whiskerLeftIso sq.q φ ≪≫
              (α_ sq.q q f).symm }

section

variable {T X' X Y : B} {y : T ⟶ Y} {p : X' ⟶ Y}
variable (sq : BicategoricalTwoCommutativeSquare y p)
variable {q : X' ⟶ X} {f : X ⟶ Y}

/-- Postcomposing a `2`-commutative square with a right triangle `p ≅ q ≫ f` keeps the left edge
fixed and replaces the right edge by `f`. This is the source-facing specialization of
`postcompose` to an identity top edge, with the unitors absorbed into the square itself. -/
def postcomposeRight (φ : p ≅ q ≫ f) :
    BicategoricalTwoCommutativeSquare y f :=
  { obj := sq.obj
    p := sq.p
    q := sq.q ≫ q
    ψ := sq.ψ ≪≫ whiskerLeftIso sq.q φ ≪≫ (α_ sq.q q f).symm }

end

end BicategoricalTwoCommutativeSquare

namespace DottedArrow

section Postcompose

variable {T X' Y' X Y : B} {y : T ⟶ Y'} {p : X' ⟶ Y'}
variable {sq : BicategoricalTwoCommutativeSquare y p}
variable {q : X' ⟶ X} {g : Y' ⟶ Y} {f : X ⟶ Y}

/-- The upper-left comparison induced by postcomposing a dotted arrow with `q`. -/
private noncomputable def postcomposeLeft
    (A : DottedArrow sq) :
    sq.p ≫ (A.arrow ≫ q) ≅ sq.q ≫ q :=
  (α_ sq.p A.arrow q).symm ≪≫ whiskerRightIso A.left q

/-- The lower-right comparison induced by postcomposing a dotted arrow with a right square. -/
private noncomputable def postcomposeLowerRight
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow sq) :
    y ≫ g ≅ (A.arrow ≫ q) ≫ f :=
  whiskerRightIso A.right g ≪≫
    α_ A.arrow p g ≪≫
      whiskerLeftIso A.arrow φ ≪≫
        (α_ A.arrow q f).symm

/-- The underlying left lift of the postcomposed dotted arrow. -/
private noncomputable abbrev postcomposeToLeftLift
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow sq) :
    LeftLift f (y ≫ g) :=
  LeftLift.mk (A.arrow ≫ q) (postcomposeLowerRight φ A).hom

private theorem postcompose_comm
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow sq) :
    whiskerLeftIso sq.p (postcomposeLowerRight φ A) ≪≫
        (α_ sq.p (A.arrow ≫ q) f).symm ≪≫
          whiskerRightIso (postcomposeLeft A) f =
      (sq.postcompose φ).ψ := sorry

/-- Postcomposing a dotted arrow with a right square gives a dotted arrow for the outer
rectangle. -/
noncomputable def postcompose
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow sq) :
    DottedArrow (sq.postcompose φ) := by
  let t : LeftLift f (y ≫ g) := postcomposeToLeftLift φ A
  let _ : IsIso t.unit := by
    change IsIso (postcomposeLowerRight φ A).hom
    infer_instance
  refine
    { toLeftLift := t
      unit_isIso := inferInstance
      comparison := comparisonIsoMk t (postcomposeLeft A) ?_ }
  simpa [t] using congrArg Iso.hom (postcompose_comm φ A)

private theorem postcomposeMap_left_comm
    {A B : DottedArrow sq}
    (θ : A ⟶ B) :
    sq.p ◁ (θ.right ▷ q) ≫ (postcomposeLeft B).hom = (postcomposeLeft A).hom := sorry

private theorem postcomposeMap_right_comm
    (φ : p ≫ g ≅ q ≫ f)
    {A B : DottedArrow sq}
    (θ : A ⟶ B) :
    (postcomposeLowerRight φ A).hom ≫ (θ.right ▷ q) ▷ f =
      (postcomposeLowerRight φ B).hom := sorry

/-- The induced morphism on postcomposed dotted arrows. -/
private noncomputable def postcomposeMap
    (φ : p ≫ g ≅ q ≫ f)
    {A B : DottedArrow sq}
    (θ : A ⟶ B) :
    postcompose φ A ⟶ postcompose φ B :=
  ⟨show postcomposeToLeftLift φ A ⟶ postcomposeToLeftLift φ B from
      LeftLift.homMk (θ.right ▷ q) (postcomposeMap_right_comm φ θ), by
    sorry⟩

private theorem postcompose_map_id
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow sq) :
    postcomposeMap φ (𝟙 A) = 𝟙 (postcompose φ A) := sorry

private theorem postcompose_map_comp
    (φ : p ≫ g ≅ q ≫ f)
    {A B C : DottedArrow sq}
    (η : A ⟶ B) (θ : B ⟶ C) :
    postcomposeMap φ (η ≫ θ) = postcomposeMap φ η ≫ postcomposeMap φ θ := sorry

/-- The canonical functor on dotted-arrow categories induced by postcomposing with a right
square. -/
noncomputable def postcomposeFunctor
    (S : BicategoricalTwoCommutativeSquare y p)
    (φ : p ≫ g ≅ q ≫ f) :
    DottedArrow S ⥤ DottedArrow (S.postcompose φ) where
  obj := postcompose φ
  map := postcomposeMap φ
  map_id := postcompose_map_id φ
  map_comp := by
    intro A B C η θ
    simpa using postcompose_map_comp φ η θ

section PostcomposeRight

variable {T X' X Y : B} {y : T ⟶ Y} {p : X' ⟶ Y}
variable {sq : BicategoricalTwoCommutativeSquare y p}
variable {q : X' ⟶ X} {f : X ⟶ Y}

/-- The lower-right comparison induced by postcomposing a dotted arrow with a right triangle
`p ≅ q ≫ f`. -/
private noncomputable def postcomposeRightIso
    (φ : p ≅ q ≫ f)
    (A : DottedArrow sq) :
    y ≅ (A.arrow ≫ q) ≫ f :=
  A.right ≪≫ whiskerLeftIso A.arrow φ ≪≫ (α_ A.arrow q f).symm

private theorem postcomposeRight_comm
    (φ : p ≅ q ≫ f)
    (A : DottedArrow sq) :
    whiskerLeftIso sq.p (postcomposeRightIso φ A) ≪≫
        (α_ sq.p (A.arrow ≫ q) f).symm ≪≫
          whiskerRightIso (postcomposeLeft A) f =
      (sq.postcomposeRight φ).ψ := sorry

/-- Postcomposing a dotted arrow with a right triangle `p ≅ q ≫ f` keeps the left source fixed
and gives a dotted arrow for the resulting source-facing outer square. -/
noncomputable def postcomposeRight
    (φ : p ≅ q ≫ f)
    (A : DottedArrow sq) :
    DottedArrow (sq.postcomposeRight φ) := by
  let t : LeftLift f y := LeftLift.mk (A.arrow ≫ q) (postcomposeRightIso φ A).hom
  let _ : IsIso t.unit := by
    change IsIso (postcomposeRightIso φ A).hom
    infer_instance
  refine
    { toLeftLift := t
      unit_isIso := inferInstance
      comparison := comparisonIsoMk t (postcomposeLeft A) ?_ }
  simpa [t] using congrArg Iso.hom (postcomposeRight_comm φ A)

private theorem postcomposeRightMap_right_comm
    (φ : p ≅ q ≫ f)
    {A B : DottedArrow sq}
    (θ : A ⟶ B) :
    (postcomposeRightIso φ A).hom ≫ (θ.right ▷ q) ▷ f = (postcomposeRightIso φ B).hom := sorry

/-- The induced morphism on right-postcomposed dotted arrows. -/
private noncomputable def postcomposeRightMap
    (φ : p ≅ q ≫ f)
    {A B : DottedArrow sq}
    (θ : A ⟶ B) :
    postcomposeRight φ A ⟶ postcomposeRight φ B :=
  ⟨show LeftLift.mk (A.arrow ≫ q) (postcomposeRightIso φ A).hom ⟶
        LeftLift.mk (B.arrow ≫ q) (postcomposeRightIso φ B).hom from
      LeftLift.homMk (θ.right ▷ q) (postcomposeRightMap_right_comm φ θ), by
    sorry⟩

private theorem postcomposeRight_map_id
    (φ : p ≅ q ≫ f)
    (A : DottedArrow sq) :
    postcomposeRightMap φ (𝟙 A) = 𝟙 (postcomposeRight φ A) := sorry

private theorem postcomposeRight_map_comp
    (φ : p ≅ q ≫ f)
    {A B C : DottedArrow sq}
    (η : A ⟶ B) (θ : B ⟶ C) :
    postcomposeRightMap φ (η ≫ θ) = postcomposeRightMap φ η ≫ postcomposeRightMap φ θ := sorry

/-- The canonical functor on dotted-arrow categories induced by postcomposing with a right
triangle `p ≅ q ≫ f`. -/
noncomputable def postcomposeRightFunctor
    (S : BicategoricalTwoCommutativeSquare y p)
    (φ : p ≅ q ≫ f) :
    DottedArrow S ⥤ DottedArrow (S.postcomposeRight φ) where
  obj := postcomposeRight φ
  map := postcomposeRightMap φ
  map_id := postcomposeRight_map_id φ
  map_comp := by
    intro A B C η θ
    simpa using postcomposeRight_map_comp φ η θ

end PostcomposeRight

end Postcompose

end DottedArrow

end CategoryTheory
