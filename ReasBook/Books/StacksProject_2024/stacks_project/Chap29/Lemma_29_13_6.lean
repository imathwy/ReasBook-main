import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found `Scheme.IsQuasiAffine.of_isImmersion` as the
-- scheme-level result behind the proof, while local Chapter 29 precedent fixes the
-- source-facing morphism predicate as `QuasiAffineHom`.

/-- Lemma 29.13.6: a quasi-compact immersion is quasi-affine. -/
@[stacks 02JR]
theorem IsImmersion.quasiAffineHom_of_quasiCompact
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsImmersion f) (hqc : QuasiCompact f) :
    QuasiAffineHom f := sorry

end AlgebraicGeometry
