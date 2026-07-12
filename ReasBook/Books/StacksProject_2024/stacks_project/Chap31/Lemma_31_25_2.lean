import Mathlib
import StacksProject_2024.Chap29.Definition_29_54_1
import StacksProject_2024.Chap31.Lemma_31_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsReduced X]
variable [HasFiniteIrreducibleComponentsOnCompactOpens X]

local notation "KX" => X.toLocallyRingedSpace.meromorphicFunctionSheaf

/- Semantic recall: `lean_leansearch` recalled the canonical normalization owners
`Scheme.Hom.normalization` and `Scheme.Hom.fromNormalization`; local Chapter 29 precedent
represents relative `Spec_X` descriptions by affine-open section-ring formulas. The Stacks tag
evidence is consistent: item tag `035T` matches `https://stacks.math.columbia.edu/tag/035T`. -/

/-- Lemma 31.25.2: for a reduced scheme whose quasi-compact opens have finitely many irreducible
components, the normalization morphism `ν : X^ν ⟶ X` is the relative spectrum over `X` of the
integral closure of `𝒪_X` inside the meromorphic-function sheaf `𝒦_X`. In the current project this
relative-`Spec_X` assertion is exposed on affine opens: over `U`, the section ring of `ν⁻¹(U)` is
the integral closure of `Γ(X, U)` in `𝒦_X(U)`. -/
@[stacks 035T]
theorem reduced_normalizationTo_sections_algEquiv_integralClosure_meromorphicFunctions
    (U : X.affineOpens) :
    let _ : Algebra Γ(X, (U : X.Opens))
        Γ(X.normalization, (Opens.map (Scheme.normalizationTo X).base).obj (U : X.Opens)) :=
      ((Scheme.normalizationTo X).app (U : X.Opens)).hom.toAlgebra
    Nonempty <|
      Γ(X.normalization, (Opens.map (Scheme.normalizationTo X).base).obj (U : X.Opens)) ≃ₐ[
        Γ(X, (U : X.Opens))]
        integralClosure Γ(X, (U : X.Opens)) ((KX).presheaf.obj (op (U : X.Opens))) := sorry

end AlgebraicGeometry.Scheme
