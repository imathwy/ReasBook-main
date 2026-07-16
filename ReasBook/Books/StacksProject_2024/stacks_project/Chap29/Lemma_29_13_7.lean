import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import StacksProject_2024.stacks_project.Chap29.Definition_29_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: the canonical owners are the source-facing morphism predicate
-- `QuasiAffineHom`, the scheme property `Scheme.IsQuasiAffine`, and the affine-local criterion for
-- `QuasiCompact`.

/-- Lemma 29.13.7 (1): for a morphism `f : X ⟶ S` with affine source `X`, being quasi-affine is
equivalent to being quasi-compact. -/
theorem quasiAffineHom_iff_quasiCompact_of_isAffine
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] :
    QuasiAffineHom f ↔ QuasiCompact f := by
  sorry

/-- Lemma 29.13.7 (2): any morphism from an affine scheme to a quasi-separated scheme is
quasi-affine. -/
theorem quasiAffineHom_of_isAffine_of_quasiSeparated
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [QuasiSeparatedSpace S] :
    QuasiAffineHom f := by
  sorry

end AlgebraicGeometry
