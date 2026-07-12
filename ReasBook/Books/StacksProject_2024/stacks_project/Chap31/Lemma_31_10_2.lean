import StacksProject_2024.Chap29.Definition_29_32_1
import StacksProject_2024.Chap29.Lemma_29_35_10
import StacksProject_2024.Chap31.FittingIdealSheaf

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: semantic MCP search was unavailable in this run, so local Chapter 29/31
-- precedent fixes the scheme-side pointwise owner as `Scheme.Hom.UnramifiedAt` and the Fitting
-- closed locus as `(Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0).support`. The Stacks tag evidence
-- is consistent: item tag `0C3J` and source URL tag `0C3J`.

/-- For a locally finite type scheme morphism, `Ω[f.toShHom]` is finite type. -/
instance instIsFiniteTypeDifferentialsOfLocallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    (Ω[f.toShHom]).IsFiniteType := sorry

/-- For a scheme morphism, `Ω[f.toShHom]` is quasi-coherent. -/
instance instIsQuasicoherentDifferentials
    {X S : Scheme.{u}} (f : X ⟶ S) :
    (Ω[f.toShHom]).IsQuasicoherent := sorry

/-- Lemma 31.10.2: let `f : X ⟶ S` be locally of finite type. The closed subscheme of `X` cut
out by the zeroth Fitting ideal of `Ω_{X/S}` has underlying set exactly the points where `f` is
not unramified. -/
@[stacks 0C3J]
theorem fittingIdealSheaf_differentials_support_eq_nonUnramifiedAtLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0).support : Set X) =
      {x : X | ¬ f.UnramifiedAt x} := sorry

end AlgebraicGeometry
