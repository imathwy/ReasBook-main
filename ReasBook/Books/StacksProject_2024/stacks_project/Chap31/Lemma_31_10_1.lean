import Mathlib
import StacksProject_2024.Chap29.Lemma_29_15_4
import StacksProject_2024.Chap29.Lemma_29_32_10
import StacksProject_2024.Chap29.Lemma_29_32_12
import StacksProject_2024.Chap31.Lemma_31_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the ring-level Kähler differential base-change
-- theorem `KaehlerDifferential.isBaseChange` and the scheme morphism base-change owner
-- `LocallyOfFiniteType`; local Chapter 29/31 precedent fixes the scheme-level owners as
-- `Ω[f.toShHom]`, `pullback.snd f g`, and `Scheme.fittingIdealSheaf`.

/-- Helper: for a locally finite type scheme morphism, its sheaf of relative differentials is
finite type as an `\mathcal O_X`-module. -/
instance instIsFiniteTypeDifferentialsOfLocallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    (Ω[f.toShHom]).IsFiniteType := sorry

/-- Helper: for a scheme morphism, its sheaf of relative differentials is quasi-coherent. -/
instance instIsQuasicoherentDifferentials
    {X S : Scheme.{u}} (f : X ⟶ S) :
    (Ω[f.toShHom]).IsQuasicoherent := sorry

/-- Lemma 31.10.1: let `f : X ⟶ S` be locally of finite type and let `g : S' ⟶ S` be an
arbitrary base change. For every `i`, the closed subscheme of `X ×[S] S'` cut out by the
`i`th Fitting ideal of `Ω_{X×[S]S'/S'}` is the pullback of the closed subscheme of `X` cut out
by the `i`th Fitting ideal of `Ω_{X/S}`. In ideal-sheaf form this says
`(Fit_i Ω_{X/S}).comap (X ×[S] S' ⟶ X) = Fit_i Ω_{X×[S]S'/S'}`. -/
@[stacks 0C3I]
theorem fittingIdealSheaf_differentials_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (i : ℕ) :
    (Scheme.fittingIdealSheaf (Ω[f.toShHom]) i).comap (pullback.fst f g) =
      Scheme.fittingIdealSheaf (Ω[(pullback.snd f g).toShHom]) i := sorry

end AlgebraicGeometry
