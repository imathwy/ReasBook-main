import StacksProject_2024.stacks_project.Chap29.Definition_29_40_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_43_1
import Mathlib.AlgebraicGeometry.Morphisms.Proper

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Lemma 29.43.13 (1): over a quasi-compact and quasi-separated base, a morphism is
projective if and only if it is quasi-projective and proper. -/
@[stacks 0BCL]
theorem projective_iff_quasiProjective_and_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] :
    Projective f ↔ QuasiProjective f ∧ IsProper f := sorry

/-- Lemma 29.43.13 (2): over a quasi-compact and quasi-separated base, a morphism is
H-projective if and only if it is H-quasi-projective and proper. -/
@[stacks 0BCL]
theorem hProjective_iff_hQuasiProjective_and_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] :
    HProjective f ↔ HQuasiProjective f ∧ IsProper f := sorry

end AlgebraicGeometry
