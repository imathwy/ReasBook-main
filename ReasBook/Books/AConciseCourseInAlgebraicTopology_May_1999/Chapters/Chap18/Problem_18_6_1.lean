import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.RepresentationTheory.Rep.Iso

open CategoryTheory
open scoped FundamentalGroup

universe u

noncomputable section

-- `ChainComplex.linearYonedaObj` is the canonical core owner for the cochain complex
-- `Hom_{ℤ[π₁(X, x)]}(C_*(X̃), A)`. This file keeps the source-facing based universal-cover
-- cochain complex as a thin abbrev over that owner.

variable {X : Type u} [TopologicalSpace X] {x : X}
variable (A : Rep ℤ (FundamentalGroup X x))
variable (coverChains : ChainComplex (Rep ℤ (FundamentalGroup X x)) ℕ)

/-- Problem 18.6.1. For a based space `(X, x)`, a `π₁(X, x)`-representation `A`, and a chosen
`π₁(X, x)`-equivariant chain complex `coverChains` modeling the universal cover, the cochains on
`X` with coefficients in `A` are modeled by the canonical cochain complex
`Hom_{ℤ[π₁(X, x)]}(coverChains, A)`. -/
abbrev universalCoverCoefficientCochainComplex
    (A : Rep ℤ (FundamentalGroup X x))
    (coverChains : ChainComplex (Rep ℤ (FundamentalGroup X x)) ℕ) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  coverChains.linearYonedaObj ℤ A

/-- Unfolding `universalCoverCoefficientCochainComplex A coverChains` recovers the canonical
`linearYonedaObj` model. -/
theorem universalCoverCoefficientCochainComplex_def :
    universalCoverCoefficientCochainComplex A coverChains =
      coverChains.linearYonedaObj ℤ A :=
  rfl

/-- Degree `n` of `universalCoverCoefficientCochainComplex A coverChains` is the `ℤ`-module of
`π₁(X, x)`-equivariant morphisms `coverChains.X n ⟶ A`. -/
theorem universalCoverCoefficientCochainComplex_X (n : ℕ) :
    (universalCoverCoefficientCochainComplex A coverChains).X n =
      ModuleCat.of ℤ (coverChains.X n ⟶ A) :=
  rfl

/-- The differential on `universalCoverCoefficientCochainComplex A coverChains` is induced by
precomposition with the chain differential on `coverChains`. -/
theorem universalCoverCoefficientCochainComplex_d (i j : ℕ) :
    (universalCoverCoefficientCochainComplex A coverChains).d i j =
      ModuleCat.ofHom (Linear.leftComp ℤ A (coverChains.d j i)) :=
  rfl
