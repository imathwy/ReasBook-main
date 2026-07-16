import StacksProject_2024.stacks_project.Chap29.Definition_29_14_2
import StacksProject_2024.stacks_project.Chap29.Lemma_29_34_6
import StacksProject_2024.stacks_project.Chap29.Lemma_29_34_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- mathlib supplies the canonical open-immersion-to-smooth bridge through the instance
  `AlgebraicGeometry.instIsSmoothOfIsOpenImmersion`;
- Chapter 29 already exports the scheme-level bridge `smooth_syntomic : Smooth f →
  LocallyOfType RingHom.Syntomic f`;
- this file is therefore the source-facing composition of those two canonical owners, rather than a
  repeated affine-chart proof.
-/

/-- Lemma 29.30.5: any open immersion is syntomic. -/
theorem syntomic_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Syntomic f := by
  exact smooth_syntomic (smooth_of_isOpenImmersion f)

end AlgebraicGeometry

end
