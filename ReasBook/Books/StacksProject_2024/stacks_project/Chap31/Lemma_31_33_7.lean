import Mathlib
import StacksProject_2024.Chap31.Definition_31_33_1
import StacksProject_2024.Chap31.Definition_31_34_1

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall note: semantic MCP search did not surface a ready-made strict-transform exactness
-- API; after Definition 31.33.1 publicized the functorial companion
-- `strictTransformFunctor`, the short-complex construction can now reuse the owner directly.

section

variable {S S' X : Scheme.{u}}
variable (b : S' ⟶ S) (E : S'.IdealSheafData) (f : X ⟶ S)

/-- The short complex of strict transforms induced from a short complex on `X.Modules`. -/
private abbrev strictTransformShortComplex
    (S₀ : ShortComplex X.Modules) :
    ShortComplex (strictTransformAmbient b f).Modules :=
  ShortComplex.mk
    ((strictTransformFunctor b E f).map S₀.f)
    ((strictTransformFunctor b E f).map S₀.g)
    (by sorry)

/-- The pullback short complex of a sequence of `\mathcal O_X`-modules along a base change
`T ⟶ S`. -/
private abbrev baseChangeShortComplex
    {T : Scheme.{u}} (f : X ⟶ S) (S₀ : ShortComplex X.Modules) (t : T ⟶ S) :
    ShortComplex (Limits.pullback f t).Modules :=
  S₀.map (Scheme.Modules.pullback (Limits.pullback.fst f t))

/-- Lemma 31.33.7: in the situation of Definition `31.33.1`, if a short exact sequence of quasi-
coherent `\mathcal O_X`-modules remains short exact after every base change `T ⟶ S`, then its
strict transforms relative to the blowup `b : S' ⟶ S` again form a short exact sequence. -/
@[stacks 080W]
theorem strictTransformShortComplex_shortExact_of_baseChangeShortExact
    (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) (S₀ : ShortComplex X.Modules)
    [S₀.X₁.IsQuasicoherent] [S₀.X₂.IsQuasicoherent] [S₀.X₃.IsQuasicoherent]
    (hbase : ∀ {T : Scheme.{u}} (t : T ⟶ S), (baseChangeShortComplex f S₀ t).ShortExact) :
    (strictTransformShortComplex b (I.comap b) f S₀).ShortExact := sorry

end

end AlgebraicGeometry.Scheme.Modules
