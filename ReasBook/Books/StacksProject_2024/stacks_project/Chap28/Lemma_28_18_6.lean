import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IsQuasiAffine

-- Semantic recall: `lean_leansearch` points to `Scheme.IsQuasiAffine` and `AffineSpace`; the
-- source-facing statement is the corresponding existence theorem phrased using canonical pullbacks
-- and the relative affine-space projection `AffineSpace.over`.

/-- Lemma 28.18.6: if `X` is quasi-affine, then there exist a natural number `n`, an affine scheme
`T`, and a morphism `π : T ⟶ X` such that for every morphism `f : X' ⟶ X` with `X'` affine, the
pullback `pullback π f` is isomorphic over `X'` to the relative affine space
`AffineSpace (Fin n) X'`. -/
@[stacks 0F82]
theorem exists_affineSpacePullback {X : Scheme.{u}} (hX : X.IsQuasiAffine) :
    ∃ (n : ℕ) (T : Scheme.{u}) (π : T ⟶ X),
      IsAffine T ∧
      ∀ {X' : Scheme.{u}} (f : X' ⟶ X), IsAffine X' →
        Nonempty (Over.mk (pullback.snd π f) ≅ Over.mk (𝔸(Fin n; X') ↘ X')) := by
  sorry

end AlgebraicGeometry.Scheme.IsQuasiAffine
