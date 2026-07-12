import StacksProject_2024.Chap28.Definition_28_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- - `Definition_28_7_1` already fixes the source-facing owner `X.isNormal`;
-- - this item is the source-facing integral-scheme reformulation that restores the source's
--   explicit "nonempty affine open" wording, with the domain part carried by `[IsIntegral X]`.

/-- Lemma 28.7.4: an integral scheme `X` is normal if and only if for every nonempty affine open
`U ⊆ X`, the ring of sections `Γ(X, U)` is a normal domain; in the project owner style, this is
expressed by `X.isNormal` and `_root_.IsNormalRing (Γ(X, U))`. -/
@[stacks 033J]
theorem isNormal_iff_forall_affineOpen_isNormalRing (X : Scheme.{u}) [IsIntegral X] :
    X.isNormal ↔
      ∀ U : X.affineOpens, Nonempty (U : X.Opens) → _root_.IsNormalRing (Γ(X, U)) := by
  sorry

end AlgebraicGeometry.Scheme
