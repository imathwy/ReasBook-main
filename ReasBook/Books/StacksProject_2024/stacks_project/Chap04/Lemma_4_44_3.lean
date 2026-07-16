import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_35_1
import StacksProject_2024.stacks_project.Chap04.Definition_4_35_6
import StacksProject_2024.stacks_project.Chap04.Definition_4_44_1

-- Declarations for this item will be appended below by the statement pipeline.

universe wB vB uB

namespace CategoryTheory

open scoped CategoryTheory.Bicategory

open Limits CategoricalPullback
open CategoricalPullback.CatCommSqOver
open Bicategory

/- Domain sampling for Lemma 4.44.3:
- primary domain: bicategorical dotted-arrow categories and fibred-in-groupoids projections over a
  dotted-arrow base;
- owner abstractions inspected: `BicategoricalTwoCommutativeSquare`,
  `DottedArrow.postcomposeRightFunctor`, `CategoricalPullback.π₁`, and
  `CatCommSqOver.toFunctorToCategoricalPullback`;
- triage:
  `source-facing`: the auxiliary category `D''` and the left-square comparison for a fixed middle
  dotted arrow;
  `core/canonical`: `DottedArrow`, `CategoricalPullback`, and
  `IsFibredInGroupoids`/`FibredInGroupoidsOver`;
  `bridge/view`: the transport from outer dotted arrows to middle ones, the projection
  `D'' ⥤ D'`, and the fiberwise comparison functors;
- primitive data for `D''`: an intermediate dotted arrow, an outer dotted arrow, and a
  comparison `middle.arrow ≅ outer.arrow ≫ f`, exactly the owner data of a categorical pullback in
  the hom-category `Hom(T, Y)`;
- derived API: the projection to the middle dotted-arrow category and the fiberwise equivalence
  with the dotted-arrow category of the corresponding left square. -/

section CompositionAux

variable {B : Type uB} [Bicategory.{wB, vB} B] [Bicategory.IsLocallyGroupoid B]
variable {S T X Y Z : B}
variable (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y) (g : Y ⟶ Z) (z : T ⟶ Z)
variable (γ : j ≫ z ≅ x ≫ f ≫ g)

namespace DottedArrowComposition

/-- The outer `2`-commutative square of Lemma 4.44.3. -/
abbrev outerSquare :
    BicategoricalTwoCommutativeSquare z (f ≫ g) :=
  { obj := S
    p := j
    q := x
    ψ := γ }

/-- The source-facing middle square `D'` of Lemma 4.44.3. -/
abbrev middleSquare :
    BicategoricalTwoCommutativeSquare z g :=
  BicategoricalTwoCommutativeSquare.postcomposeRight
    (outerSquare x j f g z γ) (Iso.refl (f ≫ g))

local notation "outerSq" => outerSquare x j f g z γ
local notation "middleSq" => middleSquare x j f g z γ

/-- The left square cut out by an intermediate dotted arrow. -/
noncomputable def leftSquare
    (d : DottedArrow middleSq) :
    BicategoricalTwoCommutativeSquare d.arrow f :=
  { obj := S
    p := j
    q := x
    ψ := d.left }

/-- The base category `D'` of intermediate dotted arrows. -/
private abbrev middleArrow :
    DottedArrow middleSq ⥤ (T ⟶ Y) where
  obj d := d.arrow
  map η := η.right
  map_id := by
    intro d
    rfl
  map_comp := by
    intro d d' d'' η θ
    rfl

/-- The canonical bridge from outer dotted arrows to middle dotted arrows. -/
private noncomputable abbrev middleOfOuter :
    DottedArrow outerSq ⥤ DottedArrow middleSq :=
  DottedArrow.postcomposeRightFunctor (outerSquare x j f g z γ) (Iso.refl (f ≫ g))

/-- The arrow functor from outer dotted arrows to the hom-category `Hom(T, Y)`. -/
private noncomputable abbrev outerArrow :
    DottedArrow outerSq ⥤ (T ⟶ Y) :=
  middleOfOuter x j f g z γ ⋙ middleArrow x j f g z γ

/-- The canonical projection `D'' ⥤ D'`. -/
private noncomputable abbrev auxProjection :
    ((middleArrow x j f g z γ) ⊡ (outerArrow x j f g z γ)) ⥤ DottedArrow middleSq :=
  π₁ (middleArrow x j f g z γ) (outerArrow x j f g z γ)

/-- The auxiliary projection is fibred in groupoids over the intermediate dotted-arrow category. -/
private instance auxProjection_isFibredInGroupoids :
    IsFibredInGroupoids (auxProjection x j f g z γ) := by
  sorry

/-- The canonical auxiliary category `D''` of Lemma 4.44.3. -/
noncomputable def auxOver :
    FibredInGroupoidsOver (DottedArrow middleSq) :=
  FibredInGroupoidsOver.ofFunctor (auxProjection x j f g z γ)

/-- The canonical functor from outer dotted arrows to the auxiliary category `D''`. -/
noncomputable def auxFromOuter :
    DottedArrow outerSq ⥤ (auxOver x j f g z γ).S :=
  show DottedArrow outerSq ⥤ ((middleArrow x j f g z γ) ⊡ (outerArrow x j f g z γ)) from
    (toFunctorToCategoricalPullback
        (middleArrow x j f g z γ)
        (outerArrow x j f g z γ)
        (DottedArrow outerSq)).obj
      { fst := middleOfOuter x j f g z γ
        snd := 𝟭 _
        iso := (outerArrow x j f g z γ).leftUnitor.symm }

/-- The canonical functor from outer dotted arrows to the auxiliary category `D''` is an
equivalence. -/
theorem auxFromOuter_isEquivalence :
    (auxFromOuter x j f g z γ).IsEquivalence := by
  sorry

/-- The canonical functor from the left-square dotted-arrow category to the fiber of the
auxiliary projection over a fixed intermediate dotted arrow. -/
private noncomputable def outerOfLeft
    (d : DottedArrow middleSq) :
    DottedArrow (leftSquare x j f g z γ d) ⥤ DottedArrow outerSq where
  obj A :=
    { toLeftLift := LeftLift.mk A.arrow
        ((d.right ≪≫ whiskerRightIso A.right g ≪≫ α_ A.arrow f g).hom)
      unit_isIso := by
        change IsIso
          ((d.right ≪≫ whiskerRightIso A.right g ≪≫ α_ A.arrow f g).hom)
        infer_instance
      comparison := DottedArrow.comparisonIsoMk
        (LeftLift.mk A.arrow ((d.right ≪≫ whiskerRightIso A.right g ≪≫ α_ A.arrow f g).hom))
        A.left <| by
          sorry }
  map := fun {A B} η ↦
    ⟨LeftLift.homMk η.right <| by
        sorry
      , by
        sorry⟩
  map_id := by
    intro A
    apply DottedArrow.Hom.ext
    rfl
  map_comp := by
    intro A B C η θ
    apply DottedArrow.Hom.ext
    rfl

/-- The fiberwise comparison functor from left-square dotted arrows to the auxiliary fiber. -/
noncomputable def leftToAuxFiber
    (d : DottedArrow middleSq) :
    DottedArrow (leftSquare x j f g z γ d) ⥤ ((auxOver x j f g z γ).p).Fiber d where
  obj := fun A ↦
    let obj : ((middleArrow x j f g z γ) ⊡ (outerArrow x j f g z γ)) :=
      { fst := d
        snd := (outerOfLeft x j f g z γ d).obj A
        iso := A.right }
    ⟨obj, rfl⟩
  map := fun {A A'} η ↦ by
    let source : ((middleArrow x j f g z γ) ⊡ (outerArrow x j f g z γ)) :=
      { fst := d
        snd := (outerOfLeft x j f g z γ d).obj A
        iso := A.right }
    let target : ((middleArrow x j f g z γ) ⊡ (outerArrow x j f g z γ)) :=
      { fst := d
        snd := (outerOfLeft x j f g z γ d).obj A'
        iso := A'.right }
    let θ : source ⟶ target :=
      { fst := 𝟙 d
        snd := (outerOfLeft x j f g z γ d).map η
        w := by
          sorry }
    let _ : ((auxOver x j f g z γ).p).IsHomLift (𝟙 d) θ := by
      sorry
    exact Functor.Fiber.homMk ((auxOver x j f g z γ).p) d θ
  map_id := by
    sorry
  map_comp := by
    sorry

/-- The canonical comparison functor from the dotted arrows of the left square to the fiber of
`D'' ⥤ D'` over a fixed middle dotted arrow. -/
theorem leftToAuxFiber_isEquivalence
    (d : DottedArrow middleSq) :
    (leftToAuxFiber x j f g z γ d).IsEquivalence := by
  sorry

/-- Lemma 4.44.3, fiberwise form: the fiber of `D'' ⥤ D'` over a middle dotted arrow is
canonically equivalent to the dotted-arrow category of the corresponding left square. -/
noncomputable def auxFiberEquivLeftSquare
    (d : DottedArrow middleSq) :
    ((auxOver x j f g z γ).p).Fiber d ≌ DottedArrow (leftSquare x j f g z γ d) :=
  let H := leftToAuxFiber x j f g z γ d
  letI : H.IsEquivalence := leftToAuxFiber_isEquivalence x j f g z γ d
  H.asEquivalence.symm

end DottedArrowComposition

-- Proof sketch: the explicit auxiliary category `D''` above is the one constructed in the
-- textbook proof, now expressed canonically as a categorical pullback in `Hom(T, Y)`. Its
-- projection to the middle dotted-arrow category is fibred in groupoids, the functor from outer
-- dotted arrows is the canonical pullback comparison `a ↦ (middle(a), a, 𝟙)`, and the fiber over
-- a fixed middle dotted arrow is the left-square dotted-arrow category corresponding to that
-- middle object.
/- Lemma 4.44.3: for a `2`-commutative rectangle in a `(2,1)`-category with chosen
`2`-isomorphism `γ : j ≫ z ≅ x ≫ f ≫ g`, the source-facing intermediate category `D'` is the
dotted-arrow category of the direct middle square
`DottedArrowComposition.middleSquare x j f g z γ : BicategoricalTwoCommutativeSquare z g`, and
the auxiliary category `D''` is `DottedArrowComposition.auxOver x j f g z γ`. Its projection to
`D'` is fibred in groupoids by construction, the canonical comparison functor from outer dotted
arrows is `DottedArrowComposition.auxFromOuter x j f g z γ`, and for each middle dotted arrow
`d : DottedArrow (DottedArrowComposition.middleSquare x j f g z γ)` the fiber of `D'' ⥤ D'` over
`d` is canonically equivalent to the dotted-arrow category of the corresponding left square via
`DottedArrowComposition.auxFiberEquivLeftSquare x j f g z γ d`. -/

end CompositionAux

end CategoryTheory
