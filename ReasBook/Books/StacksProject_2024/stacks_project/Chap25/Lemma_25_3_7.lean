import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Logic.Small.Basic
import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap25.Definition_25_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

-- Semantic search note: `lean_leansearch` pointed to mathlib's `OneHypercover` API, but this item
-- stays with the local Chapter 25 fixed-target `SemiRepresentableFamily`/`Hypercovering` owner and
-- mathlib's simplicial `cosk`/adjunction interface, which matches the source statement here.

namespace SemiRepresentableFamily
namespace Over
namespace Hom

/-- The fiber family of a morphism of fixed-target families over a chosen target component. -/
def fiber
    {X : C}
    {𝒰 𝒱 : SemiRepresentableFamily.Over.{v, u, w} X}
    (φ : 𝒰 ⟶ 𝒱) (j : 𝒱.index) :
    SemiRepresentableFamily.Over.{v, u, w} ((𝒱.obj j).left) where
  I := { i : 𝒰.index // φ.f i = j }
  obj := fun i ↦ by
    rcases i with ⟨i, hi⟩
    subst hi
    exact CategoryTheory.Over.mk ((φ.φ i).left)

/-- A morphism of fixed-target families is covering if each fiber family over a target component
generates a covering sieve on that target component. -/
def IsCovering
    (J : GrothendieckTopology C)
    {X : C}
    {𝒰 𝒱 : SemiRepresentableFamily.Over.{v, u, w} X}
    (φ : 𝒰 ⟶ 𝒱) : Prop :=
  ∀ j : 𝒱.index, (fiber φ j).toSieve ∈ J ((𝒱.obj j).left)

end Hom
end Over
end SemiRepresentableFamily

/-- The canonical comparison from degree `n + 1` of a simplicial object in `SR(C, X)` to degree
`n + 1` of its `n`-coskeleton. -/
noncomputable abbrev matchingMap
    {X : C}
    (K : SimplicialObject (SemiRepresentableFamily.Over.{v, u, w} X)) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SemiRepresentableFamily.Over.{v, u, w} X,
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    K.obj (op <| SimplexCategory.mk (n + 1)) ⟶
      ((SimplicialObject.cosk n).obj K).obj
        (op <| SimplexCategory.mk (n + 1)) :=
  ((SimplicialObject.coskAdj n).unit.app K).app
    (op <| SimplexCategory.mk (n + 1))

/-- Unfolding `matchingMap` gives the component in degree `n + 1` of the unit of the
`n`-coskeleton adjunction. -/
@[simp] theorem matchingMap_def
    {X : C}
    (K : SimplicialObject (SemiRepresentableFamily.Over.{v, u, w} X)) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SemiRepresentableFamily.Over.{v, u, w} X,
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    matchingMap K n =
      ((SimplicialObject.coskAdj n).unit.app K).app
        (op <| SimplexCategory.mk (n + 1)) :=
  rfl

/-- A hypercovering of `X` is a simplicial object of fixed-target families over `X` whose degree
`0` term is covering and whose canonical matching maps are covering in every positive degree. -/
structure Hypercovering (J : GrothendieckTopology C) (X : C) where
  /-- The underlying simplicial object of fixed-target families over `X`. -/
  toSimplicialObject : SimplicialObject (SemiRepresentableFamily.Over.{v, u, max u v} X)
  /-- The degree-`0` family covers `X`. -/
  zero_isCovering :
    (toSimplicialObject.obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X
  /-- Each canonical map to the `n`-coskeleton is a covering morphism in degree `n + 1`. -/
  succ_isCovering (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SemiRepresentableFamily.Over.{v, u, max u v} X,
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    Hom.IsCovering J (matchingMap toSimplicialObject n)

namespace Hypercovering

variable {X : C}

/-- A hypercovering can be used as its underlying simplicial object of fixed-target families. -/
instance instCoeToSimplicialObject :
    CoeOut (Hypercovering J X)
      (SimplicialObject (SemiRepresentableFamily.Over.{v, u, max u v} X)) where
  coe K := K.toSimplicialObject

/-- The degree-`n` fixed-target family of a hypercovering. -/
abbrev family (K : Hypercovering J X) (n : ℕ) :
    SemiRepresentableFamily.Over.{v, u, max u v} X :=
  K.toSimplicialObject.obj (op <| SimplexCategory.mk n)

/-- Unfolding `family` recovers the degree-`n` term of the underlying simplicial object. -/
@[simp] theorem family_def (K : Hypercovering J X) (n : ℕ) :
    K.family n = K.toSimplicialObject.obj (op <| SimplexCategory.mk n) :=
  rfl

end Hypercovering

/-- Lemma 25.3.7: for an object `X` of the site, the collection of all
hypercoverings of `X` is set-sized. -/
@[stacks 01G7]
theorem small_hypercoverings (X : C) :
    Small.{max (u + 1) (v + 1)} (Hypercovering J X) := by
  let _ : Small.{max (u + 1) (v + 1)}
      (SimplicialObject (SemiRepresentableFamily.Over.{v, u, max u v} X)) :=
    small_self _
  have hinj : Function.Injective (fun K : Hypercovering J X ↦ K.toSimplicialObject) := by
    intro K L hKL
    cases K
    cases L
    cases hKL
    simp
  exact small_of_injective hinj

end CategoryTheory
