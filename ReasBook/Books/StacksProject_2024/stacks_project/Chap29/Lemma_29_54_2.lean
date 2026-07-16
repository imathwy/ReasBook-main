import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_54_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` recalled the canonical normalization owners
-- `Scheme.Hom.normalization`, `Scheme.Hom.fromNormalization`, and `Scheme.Hom.normalizationDesc`.
-- Local Chapter 29 precedent already packages the scheme normalization as `Scheme.normalization`
-- and `Scheme.normalizationTo`, so this item is stated as the factorization through
-- `X.nilradical.subscheme` together with the comparison isomorphism to the normalization of the
-- reduced subscheme.

/-- The reduced subscheme of a scheme with finitely many irreducible components on quasi-compact
opens again has finitely many irreducible components on quasi-compact opens. -/
instance Scheme.instHasFiniteIrreducibleComponentsOnCompactOpensReducedSubscheme
    (X : Scheme.{u}) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X.nilradical.subscheme := sorry

namespace Scheme

/-- Local shorthand for the reduced subscheme `X_red`. -/
private noncomputable abbrev redSubscheme (X : Scheme.{u}) : Scheme.{u} :=
  X.nilradical.subscheme

/-- Lemma 29.54.2 (1): if every quasi-compact open of `X` has finitely many irreducible
components, then the normalization morphism `ν : X^ν ⟶ X`, formalized as `X.normalizationTo`,
factors through the reduction `X_red`, formalized as `X.nilradical.subscheme`. -/
@[stacks 035O]
theorem normalizationTo_factorsThroughReduction (X : Scheme.{u})
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)] :
    ∃ νred : X.normalization ⟶ X.nilradical.subscheme,
      νred ≫ X.nilradical.subschemeι = X.normalizationTo := sorry

/-- Lemma 29.54.2 (2): for any factorization `ν = ν_red ≫ (X_red ⟶ X)` from
`normalizationTo_factorsThroughReduction`, the factor morphism `ν_red : X^ν ⟶ X_red` is the
normalization of `X_red`; equivalently, `X^ν` is canonically isomorphic to the normalization of
`X_red`, and under this comparison `ν_red` is the normalization morphism of `X_red`. -/
@[stacks 035O]
theorem factorThroughReduction_isNormalization (X : Scheme.{u})
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    [QuasiCompact (genericPointSpectrumCoproductTo (redSubscheme X))]
    [QuasiSeparated (genericPointSpectrumCoproductTo (redSubscheme X))]
    {νred : X.normalization ⟶ redSubscheme X}
    (hνred : νred ≫ X.nilradical.subschemeι = X.normalizationTo) :
    ∃ e : X.normalization ≅ (redSubscheme X).normalization,
      νred = e.hom ≫ (redSubscheme X).normalizationTo := sorry

end Scheme

end AlgebraicGeometry
