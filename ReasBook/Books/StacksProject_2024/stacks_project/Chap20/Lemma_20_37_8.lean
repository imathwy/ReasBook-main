import StacksProject_2024.Chap20.Lemma_20_37_6

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry.RingedSpaceCohomology

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

local notation "ModX" => RingedSpace.Modules X

section UniformBasisVanishing

/-
Domain-style sampling for Lemma 20.37.8:
- primary domain: truncation-derived-limit comparisons in `D(𝒪_X)` and basiswise
  eventual vanishing for cohomology sheaves on a ringed space;
- sampled owner declarations:
  `RingedSpace.cohomologySheaf`,
  `𝓗[q](X, E)`,
  `Opens.IsBasis`,
  `EventualCohomologySheafVanishingNear`,
  `IsTruncationDerivedLimitComparison`;
- best owner abstraction: the canonical Chapter 20 owner consumed downstream is
  `EventualCohomologySheafVanishingNear`, while the topological owner for the covering condition
  is the canonical basis predicate `Opens.IsBasis`; the cohomology-sheaf owner is
  `RingedSpace.cohomologySheaf`, whose Chapter 20 source-facing notation is `𝓗[q](X, E)`. The
  source-facing content of this file is the uniform basiswise vanishing hypothesis appearing in
  the statement itself, so the file should expose only the bridge from that raw hypothesis to the
  Chapter 20 eventual-vanishing owner instead of introducing a parallel wrapper predicate;
- primitive data: a derived object `E`, a bound `cohomologyBound : ℤ → ℤ`, a basis `𝓑` of opens,
  and vanishing on members of `𝓑` given directly by the basiswise hypothesis
  `∀ ⦃U⦄, U ∈ 𝓑 → ∀ m p, cohomologyBound m < p → ...`;
-- derived API here: the bridge from the basiswise source hypothesis, owned by the canonical basis
  predicate `Opens.IsBasis 𝓑`, to `EventualCohomologySheafVanishingNear`, followed by the
  canonical truncation-comparison theorem of Lemma `20.37.6`.

Source/core/bridge triage:
- `source-facing`: the uniform basiswise vanishing hypothesis together with `Opens.IsBasis 𝓑`;
- `core/canonical`: `Opens.IsBasis`, `RingedSpace.cohomologySheaf`,
  `EventualCohomologySheafVanishingNear`, and
  `IsTruncationDerivedLimitComparison`;
- `bridge/view`: the conversion theorem
  `Opens.IsBasis.eventualCohomologySheafVanishingNear_of_uniform_basis_vanishing`.
-/

-- Proof sketch: fix a point `x` and a neighborhood `W`. Since `𝓑` is a basis, choose
-- `U ∈ 𝓑` with `x ∈ U ⊆ W`. The same global function `cohomologyBound` serves as the local bound
-- `p(x,-)`, and the given vanishing hypothesis on members of `𝓑` is exactly the neighborhood
-- condition required in `EventualCohomologySheafVanishingNear`.
/-- A uniform vanishing bound on a topological basis implies the pointwise shrinking condition
`EventualCohomologySheafVanishingNear`. -/
theorem Opens.IsBasis.eventualCohomologySheafVanishingNear_of_uniform_basis_vanishing
    {E : DerivedCategory ModX}
    {cohomologyBound : ℤ → ℤ}
    {𝓑 : Set (Opens X.carrier)}
    (h𝓑 : Opens.IsBasis 𝓑)
    (hE :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ m : ℤ, ∀ p : ℕ, cohomologyBound m < (p : ℤ) →
          IsZero ((𝓗[(m - (p : ℤ))](X, E)).H' p U))
    :
    EventualCohomologySheafVanishingNear X E := by
  intro x
  refine ⟨cohomologyBound, ?_⟩
  intro W hxW
  rcases Opens.isBasis_iff_nbhd.mp h𝓑 hxW with ⟨U, hU, hxU, hUW⟩
  exact ⟨U, hxU, hUW, hE hU⟩

-- Proof sketch: first use
-- `Opens.IsBasis.eventualCohomologySheafVanishingNear_of_uniform_basis_vanishing` to convert the
-- basiswise vanishing assumption on a basis into the local hypothesis of Lemma `20.37.6`. Then
-- apply the local-to-global truncation comparison criterion for a compatible map to the derived
-- limit of the truncation tower.
/-- Lemma 20.37.8: let `(X, 𝒪_X)` be a ringed space and let `E ∈ D(𝒪_X)`. Assume there exist a
function `p(-) : ℤ → ℤ` and a basis `𝓑` of opens of `X` such that
`H^p(U, H^{m-p}(E)) = 0` for `p > p(m)` and `U ∈ 𝓑`. Then any compatible comparison morphism
from `E` to the right-derived inverse limit of the truncation tower `τ≥ -n E` from Remark
`13.34.5` is an isomorphism in `D(𝒪_X)`. -/
@[stacks 08U2]
theorem isIso_of_truncationDerivedLimitComparison_of_uniform_basis_vanishing
    {E : DerivedCategory ModX}
    {cohomologyBound : ℤ → ℤ}
    {𝓑 : Set (Opens X.carrier)}
    {L : DerivedCategory ModX} (c : E ⟶ L)
    (hc : IsTruncationDerivedLimitComparison E L c)
    (h𝓑 : Opens.IsBasis 𝓑)
    (hE :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ m : ℤ, ∀ p : ℕ, cohomologyBound m < (p : ℤ) →
          IsZero ((𝓗[(m - (p : ℤ))](X, E)).H' p U)) :
    IsIso c := by
  exact isIso_of_truncationDerivedLimitComparison_of_eventualCohomologySheafVanishingNear
    X E c hc
    (Opens.IsBasis.eventualCohomologySheafVanishingNear_of_uniform_basis_vanishing X h𝓑 hE)

end UniformBasisVanishing

end

end AlgebraicGeometry.RingedSpace
