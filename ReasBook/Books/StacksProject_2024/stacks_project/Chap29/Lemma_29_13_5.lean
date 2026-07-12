import Mathlib
import StacksProject_2024.Chap29.Definition_29_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section

variable {X S S' : Scheme.{u}} {f : X ⟶ S} (g : S' ⟶ S)

-- Semantic recall: `lean_leansearch` surfaced the canonical quasi-affine-scheme owner
-- `Scheme.IsQuasiAffine` and the general affine-target-local base-change infrastructure. Local
-- Chapter 29 precedent fixes the source-facing morphism predicate as `QuasiAffineHom`, and nearby
-- base-change files use `pullback.snd f g` for the morphism after base change by `g`.

/-- Lemma 29.13.5: the base change of a quasi-affine morphism is quasi-affine. -/
@[stacks 01SO]
theorem QuasiAffineHom.baseChange (hf : QuasiAffineHom f) :
    QuasiAffineHom (pullback.snd f g) := sorry

end

end AlgebraicGeometry
