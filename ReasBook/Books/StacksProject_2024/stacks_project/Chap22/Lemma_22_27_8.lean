import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import StacksProject_2024.stacks_project.Chap22.Definition_22_26_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]

-- Semantic recall note: `Lemma_22_7_6` gives the same composition-vanishing pattern for
-- differential graded modules. Here the source-facing owner is the middle admissible short exact
-- sequence, represented canonically by `ShortComplex (Comp R A)` together with a splitting, while
-- the null-homotopy conditions are recorded by the chapter owner `Homotopic`.

/- Source/core/bridge triage:
- `source-facing`: Lemma 22.27.8, asserting that if `b : y₁ ⟶ y₂` lands in `ker(y₂ ⟶ z₂)` up to
  homotopy and `b' : y₂ ⟶ y₃` kills `im(x₂ ⟶ y₂)` up to homotopy, then `b' ∘ b` is homotopic to
  zero.
- `core/canonical`: `ShortComplex.Exact` together with the canonical exact lift
  `ShortComplex.Exact.lift`.
- `bridge/view`: the strict exactness-level boundary-pair companion theorem below; the split middle
  row is used only in the source-facing homotopy theorem to strictify the null-homotopic boundary
  composites.
-/

/-- Companion bridge for Lemma 22.27.8: in an exact middle short complex, if the two boundary
composites already vanish strictly, then the composite vanishes strictly as well. -/
theorem comp_eq_zero_of_shortComplexExact_boundaryPair
    (S₁ S₂ S₃ : ShortComplex (Comp R A))
    (hExact₂ : S₂.Exact)
    {b : S₁.X₂ ⟶ S₂.X₂}
    {b' : S₂.X₂ ⟶ S₃.X₂}
    (hb_right : b ≫ S₂.g = 0)
    (hb'_left : S₂.f ≫ b' = 0) :
    b ≫ b' = 0 := by
  sorry

/-- Lemma 22.27.8: let
`x₁ ⟶ y₁ ⟶ z₁`, `x₂ ⟶ y₂ ⟶ z₂`, and `x₃ ⟶ y₃ ⟶ z₃` be morphism pairs in `Comp(𝒜)`, with
`x₂ ⟶ y₂ ⟶ z₂` an admissible short exact sequence. If
`b : y₁ ⟶ y₂` lands in `ker(y₂ ⟶ z₂)` up to homotopy and
`b' : y₂ ⟶ y₃` kills `im(x₂ ⟶ y₂)` up to homotopy, then `b' ∘ b` is homotopic to zero. -/
@[stacks 09QP]
theorem comp_homotopic_zero_of_admissibleShortExact_boundaryPair
    (S₁ S₂ S₃ : ShortComplex (Comp R A))
    (σ₂ : S₂.Splitting)
    {b : S₁.X₂ ⟶ S₂.X₂}
    {b' : S₂.X₂ ⟶ S₃.X₂}
    (hb_right : Homotopic S₁.X₂.obj S₂.X₃.obj (b ≫ S₂.g) 0)
    (hb'_left : Homotopic S₂.X₁.obj S₃.X₂.obj (S₂.f ≫ b') 0) :
    Homotopic S₁.X₂.obj S₃.X₂.obj (b ≫ b') 0 := by
  sorry

end
