import Mathlib
import StacksProject_2024.Chap25.Example_25_3_4_ech_hypercoverings

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

-- Semantic search note: `lean_leansearch` pointed to mathlib's general `Arrow.cechNerve` and
-- `SimplicialObject.cechNerve` APIs; this item stays with the local Chapter 25 fixed-target owner
-- `SemiRepresentableFamily.Over.cechSimplicial_isHypercovering`, which directly states the
-- hypercovering conditions in
-- `SR(C, X)`.

namespace SemiRepresentableFamily
namespace Over

/-- The singleton fixed-target family over `X` determined by a morphism `f : U ⟶ X`. -/
abbrev singletonFamily {X U : C} (f : U ⟶ X) : SR(C, X) :=
  ofArrows (fun _ : PUnit ↦ U) (fun _ ↦ f)

/-- The Čech simplicial object attached to the singleton family `{U ⟶ X}`. Its degree `n` term is
the singleton family whose sole object is the `(n + 1)`-fold fiber product of `U` over `X`. -/
noncomputable abbrev singletonCechSimplicial {X U : C} (f : U ⟶ X) :
    SimplicialObject (SR(C, X)) :=
  cechSimplicial (singletonFamily f)

/-- Example 25.3.6 (Čech hypercovering associated to a cover): if the singleton family
`{U ⟶ X}` is covering, then the Čech simplicial object with terms
`U ×_X ... ×_X U ⟶ X` is a hypercovering of `X`. -/
theorem singletonCechSimplicial_isHypercovering {X U : C} (f : U ⟶ X)
    (hf : (singletonFamily f).toSieve ∈ J X) :
    ((singletonCechSimplicial f).obj (Opposite.op <| SimplexCategory.mk 0)).toSieve ∈ J X ∧
      ∀ n : ℕ,
        ∀ [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
          (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F],
          Hom.IsCovering J (matchingMap (singletonCechSimplicial f) n) := by
  constructor
  · simpa [singletonCechSimplicial] using
      cechSimplicial_zero_isCovering (J := J) (singletonFamily f) hf
  · intro n _inst
    simpa [singletonCechSimplicial] using
      cechSimplicial_succ_isCovering (J := J) (singletonFamily f) n

end Over
end SemiRepresentableFamily

end CategoryTheory
