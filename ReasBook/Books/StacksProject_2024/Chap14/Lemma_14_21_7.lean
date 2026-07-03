import Mathlib

open CategoryTheory Limits Opposite Simplicial

universe u

namespace SSet

/- 
Domain-style sampling for Lemma 14.21.7:
- primary domain: simplicial-set inclusions obtained by adjoining a single simplex, and the
  resulting canonical pushout squares in `SSet`;
- sampled owner-style declarations:
  `SSet.Subcomplex.N`,
  `SSet.Subcomplex.ofSimplex`,
  `CategoryTheory.Subfunctor.range_ι`,
  `SSet.boundary`,
  `SSet.skeletonOfMono`,
  `SSet.Subcomplex.BicartSq.isPushout`,
  `SSet.yonedaEquiv`;
- best owner abstraction:
  `source-facing`: a new nondegenerate simplex `x : U.N` whose boundary already lands in the
    source subcomplex `U`, together with the canonical equality saying that adjoining `x.simplex`
    generates all of `V`;
  `core/canonical`: the ambient owners `Subcomplex.N`, `Subcomplex.ofSimplex`, `SSet.boundary`,
    `Subcomplex.range`, and `Subcomplex.BicartSq.isPushout`;
  `bridge/view`: the induced boundary map `∂Δ[x.dim] ⟶ U` and the canonical `IsPushout` square;
- primitive data: only the source subcomplex `U`, the new simplex `x : U.N`, the canonical
  boundary-factorization predicate `x.boundary_range_le`, and the equality
  `U ⊔ Subcomplex.ofSimplex x.simplex = ⊤`;
- derived API: the boundary map `∂Δ[x.dim] ⟶ U` induced by `x.boundary_range_le` and the
  resulting pushout square.
-/

namespace Subcomplex
namespace N

variable {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)

/-- The boundary of the simplex classified by `x.simplex` lands in the source subcomplex `U`. -/
abbrev boundary_range_le : Prop :=
  Subcomplex.range (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex) ≤ U

end N
end Subcomplex

/-- Lemma 14.21.7: if a subcomplex `U ⊆ V` is obtained by adjoining the new nondegenerate simplex
`x : U.N`, if the boundary of `x.simplex` already lands in `U`, and if adjoining `x.simplex`
generates all of `V`, then the square `∂Δ[x.dim] ⟶ U`, `Δ[x.dim] ⟶ V` defined by `x.simplex` is
a pushout square. -/
-- Proof sketch: the boundary of the canonical map `Δ[x.dim] ⟶ V` classified by `x.simplex`
-- factors through `U` by `hboundary`. Then identify the image of `Δ[x.dim] ⟶ V` with
-- `Subcomplex.ofSimplex x.simplex`, use `hgen` to express that adjoining this subcomplex to `U`
-- gives all of `V`, identify its intersection with `U` with the boundary, and apply
-- `SSet.Subcomplex.BicartSq.isPushout` to the resulting bicartesian square of subcomplexes.
theorem isPushout_of_subcomplex_adjoin_simplex
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le)
    (hgen : U ⊔ Subcomplex.ofSimplex x.simplex = ⊤) :
    IsPushout ∂Δ[x.dim].ι
      (U.lift (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex) hboundary)
      (yonedaEquiv.symm x.simplex) U.ι := sorry

end SSet
