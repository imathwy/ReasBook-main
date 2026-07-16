import StacksProject_2024.stacks_project.Chap20.Lemma_20_37_7

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry.RingedSpaceCohomology

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/- Domain-style sampling for Lemma 20.37.9:
- primary domain: truncation-limit comparisons in `D(𝒪_X)` and vanishing of higher
  cohomology of negative cohomology sheaves on covers of opens by members of a chosen family;
- sampled owner declarations:
  `CategoryTheory.IsTruncationDerivedLimitComparison`,
  `Opens.IsBasis`,
  `LocallyUniformNegativeCohomologySheafVanishing`,
  `isIso_of_truncationDerivedLimitComparison_of_locallyUniformNegativeCohomologySheafVanishing`;
- best owner abstraction: the truncation-limit comparison is already owned by the Chapter 13
  declaration `IsTruncationDerivedLimitComparison`, while Chapter 20 already owns
  the cohomology-sheaf notation `𝓗[q](X, E)` and the canonical topological owner
  `Opens.IsBasis`; by `Opens.isBasis_iff_nbhd`, this is exactly the source covering condition
  that every open subset admits a covering by members of `𝓑`. The textbook route for Lemma
  `20.37.9` factors the source-facing vanishing hypothesis through the canonical Chapter 20
  predicate
  `LocallyUniformNegativeCohomologySheafVanishing`, so this file should expose exactly that
  packaging step and then invoke Lemma `20.37.7`.

Source/core/bridge triage:
- `source-facing`: the coverwise negative-cohomology-sheaf vanishing criterion of
  Lemma `20.37.9`, expressed via the equivalent canonical basis owner `Opens.IsBasis`;
- `core/canonical`: `IsTruncationDerivedLimitComparison`,
  `LocallyUniformNegativeCohomologySheafVanishing`, and `Opens.IsBasis`;
- `bridge/view`: the constant-bound packaging of the basiswise vanishing hypothesis into the
  local-uniform vanishing owner of Lemma `20.37.7`.
-/

/-- Helper for Lemma 20.37.9: a coverwise vanishing bound in all negative cohomological degrees
packages into the local-uniform shrinking hypothesis of Lemma `20.37.7`. -/
lemma Opens.IsBasis.locallyUniformNegativeCohomologySheafVanishing_of_uniform_basis_vanishing
    {𝓑 : Set (Opens X.carrier)}
    (h𝓑 : Opens.IsBasis 𝓑)
    (E : DerivedCategory X.Modules)
    (d : ℕ)
    (hvanish :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ p : ℕ, d < p →
          ∀ q : ℤ, q < 0 →
            IsZero ((𝓗[q](X, E)).H' p U)) :
    LocallyUniformNegativeCohomologySheafVanishing X E := by
  -- Use the same bound `d` at every point of `X`, exactly as in the textbook proof.
  intro x
  refine ⟨d, ?_⟩
  intro W hxW
  -- Shrink `W` to a chosen covering member through `x`, then apply the coverwise vanishing
  -- hypothesis.
  rcases Opens.isBasis_iff_nbhd.mp h𝓑 hxW with ⟨U, hU, hxU, hUW⟩
  refine ⟨U, hxU, hUW, ?_⟩
  intro q hq p hp
  simpa using hvanish hU p hp q hq

-- Proof sketch: first package the coverwise hypothesis into
-- `LocallyUniformNegativeCohomologySheafVanishing` using the same integer `d` at every point.
-- Then apply Lemma `20.37.7` directly to the given truncation-derived-limit comparison morphism.
/-- Lemma 20.37.9: let `(X, 𝒪_X)` be a ringed space and let `E ∈ D(𝒪_X)`.
Assume there exist an integer `d ≥ 0` and a set `𝓑` of opens of `X` whose members form a basis
of `X`, equivalently every open subset of `X` admits a covering by members of `𝓑`, and
`H^p(U, H^q(E)) = 0` for `U ∈ 𝓑`, `p > d`, and `q < 0`. Then any compatible comparison morphism
from `E` to the right-derived inverse limit of the truncation tower `τ≥(-n) E` from
Remark `13.34.5` is an isomorphism in `D(𝒪_X)`. -/
@[stacks 0D64]
theorem truncationComparison_isIso_of_coverwise_negative_cohomologySheaf_vanishing
    (E : DerivedCategory X.Modules)
    {K : DerivedCategory X.Modules}
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E K c)
    (𝓑 : Set (Opens X.carrier))
    (h𝓑 : Opens.IsBasis 𝓑)
    (d : ℕ)
    (hvanish :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ p : ℕ, d < p →
          ∀ q : ℤ, q < 0 →
            IsZero ((𝓗[q](X, E)).H' p U)) :
    IsIso c := by
  -- The comparison is now an immediate instance of Lemma `20.37.7`.
  exact
    isIso_of_truncationDerivedLimitComparison_of_locallyUniformNegativeCohomologySheafVanishing
      X E c hc <|
        Opens.IsBasis.locallyUniformNegativeCohomologySheafVanishing_of_uniform_basis_vanishing
          X h𝓑 E d hvanish

end

end AlgebraicGeometry.RingedSpace
