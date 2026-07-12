import StacksProject_2024.Chap25.Definition_25_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

-- Semantic search note: the source-facing fixed-target singleton-coproduct replacement is exposed
-- directly at the `SemiRepresentableFamily.Over` layer, together with the local fixed-target
-- `Hypercovering` API.

namespace SemiRepresentableFamily
namespace Over

/-- The singleton fixed-target family obtained from the Chapter 25 singleton-coproduct family of
the underlying family and the induced coproduct morphism to the common target. -/
abbrev coproductSingleton {X : C} (𝒰 : SR(C, X))
    [HasCoproduct (fun i ↦ (𝒰.obj i).left)] : SR(C, X) :=
  ofArrows
    (fun _ : PUnit ↦ ∐ fun i ↦ (𝒰.obj i).left)
    (fun _ ↦ Sigma.desc fun i ↦ (𝒰.obj i).hom)

/-- Unfolding `coproductSingleton` gives the singleton fixed-target family on the coproduct of the
components of `𝒰`. -/
theorem coproductSingleton_def {X : C} (𝒰 : SR(C, X))
    [HasCoproduct (fun i ↦ (𝒰.obj i).left)] :
    𝒰.coproductSingleton =
      ofArrows
        (fun _ : PUnit ↦ ∐ fun i ↦ (𝒰.obj i).left)
        (fun _ ↦ Sigma.desc fun i ↦ (𝒰.obj i).hom) :=
  rfl

/-- Forgetting the target from the fixed-target singleton-coproduct family gives the singleton
underlying family on the coproduct object. -/
@[simp] theorem forget_obj_coproductSingleton {X : C} (𝒰 : SR(C, X))
    [HasCoproduct (fun i ↦ (𝒰.obj i).left)] :
    forget.obj 𝒰.coproductSingleton =
      ⟨PUnit, fun _ : PUnit ↦ ∐ fun i ↦ (𝒰.obj i).left⟩ :=
  rfl

end Over
end SemiRepresentableFamily

namespace SimplicialObject

section DegreewiseCoproductSingleton

open SemiRepresentableFamily.Over

variable {X : C}
variable (K L : SimplicialObject (SR(C, X)))
variable [∀ Δ : SimplexCategoryᵒᵖ,
  HasCoproduct (fun i ↦ ((K.obj Δ).obj i).left)]

/-- The simplicial object `L` is obtained degreewise from `K` by replacing each fixed-target family
with the singleton family on the coproduct of its components. -/
def IsDegreewiseCoproductSingleton : Prop :=
  ∀ Δ : SimplexCategoryᵒᵖ, (K.obj Δ).coproductSingleton = L.obj Δ

@[simp] theorem isDegreewiseCoproductSingleton_iff :
    K.IsDegreewiseCoproductSingleton L ↔
      ∀ Δ : SimplexCategoryᵒᵖ, (K.obj Δ).coproductSingleton = L.obj Δ :=
  Iff.rfl

/-- Unfolding `K.IsDegreewiseCoproductSingleton L` identifies the degree-`Δ` term of `L` with the
singleton coproduct family attached to the degree-`Δ` term of `K`. -/
@[simp] theorem isDegreewiseCoproductSingleton_obj
    (hL : K.IsDegreewiseCoproductSingleton L) (Δ : SimplexCategoryᵒᵖ) :
    (K.obj Δ).coproductSingleton = L.obj Δ :=
  hL Δ

end DegreewiseCoproductSingleton

end SimplicialObject

namespace Hypercovering

open SemiRepresentableFamily.Over

variable {X : C}

section DegreewiseCoproductSingleton

variable (K : Hypercovering J X) (L : SimplicialObject (SR(C, X)))
variable [∀ Δ : SimplexCategoryᵒᵖ,
  HasCoproduct (fun i ↦ ((K.obj Δ).obj i).left)]

/-- The degreewise singleton-coproduct relation in Remark 25.12.9 depends only on the underlying
simplicial object of the hypercovering. -/
abbrev IsDegreewiseCoproductSingleton : Prop :=
  (K : SimplicialObject (SR(C, X))).IsDegreewiseCoproductSingleton L

@[simp] theorem isDegreewiseCoproductSingleton_iff :
    K.IsDegreewiseCoproductSingleton L ↔
      ∀ Δ : SimplexCategoryᵒᵖ, (K.obj Δ).coproductSingleton = L.obj Δ :=
  Iff.rfl

/-- Unfolding `K.IsDegreewiseCoproductSingleton L` identifies the degree-`Δ` term of `L` with the
singleton coproduct family attached to the degree-`Δ` term of `K`. -/
@[simp] theorem isDegreewiseCoproductSingleton_obj
    (hL : K.IsDegreewiseCoproductSingleton L) (Δ : SimplexCategoryᵒᵖ) :
    (K.obj Δ).coproductSingleton = L.obj Δ :=
  hL Δ

end DegreewiseCoproductSingleton

/- Remark 25.12.9: once a simplicial object `L` of `SR(C, X)` is fixed, a hypercovering structure
on `L` is determined by the degree-`0` covering condition and the covering conditions for its
matching maps. The canonical owner for that structure is `Hypercovering.ofSimplicial`; the
degreewise singleton-coproduct relation to another hypercovering is recorded separately by
`IsDegreewiseCoproductSingleton`. -/
@[stacks 0DB2]
#check Hypercovering.ofSimplicial

section DegreewiseCoproductSingleton

variable (K : Hypercovering J X) (L : SimplicialObject (SR(C, X)))
variable [∀ Δ : SimplexCategoryᵒᵖ,
  HasCoproduct (fun i ↦ ((K.obj Δ).obj i).left)]

/-- Building a hypercovering from `L` via `Hypercovering.ofSimplicial` does not change the
source-facing degreewise singleton-coproduct relation to `K`; only the extra covering data is
added. -/
@[simp] theorem isDegreewiseCoproductSingleton_ofSimplicial_iff
    (hzero : toSieve (L.obj (op <| SimplexCategory.mk 0)) ∈ J X)
    (hsucc : ∀ n : ℕ,
      ∀ [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
          (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F],
        Hom.IsCovering J (matchingMap L n)) :
    K.IsDegreewiseCoproductSingleton
        (Hypercovering.ofSimplicial L hzero hsucc).toSimplicialObject ↔
      K.IsDegreewiseCoproductSingleton L :=
  by
    simp

end DegreewiseCoproductSingleton

end Hypercovering

end CategoryTheory
