import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical relative-normalization owners
-- `Scheme.Hom.normalization`, `Scheme.Hom.toNormalization`, and `Scheme.Hom.fromNormalization`,
-- but no checked relative-`Spec` owner for the pushforward algebra. The source statement is
-- therefore recorded through its affine-open section criterion: `f_* O_X` is integral over
-- `O_S` exactly when the maps `Γ(S,U) -> Γ(X,f^{-1}U)` are integral on affine opens. The Stacks
-- tag evidence is consistent: item tag `03GQ` agrees with the URL ending in `/tag/03GQ`.

/-- Lemma 29.53.11: if `f : X ⟶ S` is quasi-compact, quasi-separated, and universally closed,
then `f_* O_X` is integral over `O_S`. Affine-locally on `S`, this says that for every affine
open `U ⊆ S`, the induced section map `Γ(S, U) → Γ(X, f^{-1} U)` is an integral ring map. This
is the affine-open formulation of the statement that the relative normalization of `S` in `X`
is the Stein factorization through `Spec_S(f_* O_X)`. -/
@[stacks 03GQ]
theorem Scheme.Hom.app_isIntegral_of_universallyClosed
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f]
    (U : S.Opens) (hU : IsAffineOpen U) :
    (CommRingCat.Hom.hom (f.app U)).IsIntegral := sorry

end AlgebraicGeometry
