import StacksProject_2024.Chap20.Lemma_20_37_4
import StacksProject_2024.Chap20.Lemma_20_37_10

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite (op)
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpaceCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [IsGrothendieckAbelian.{v} X.Modules]

local notation "DModX" => DerivedCategory X.Modules
local notation "HMod" => DerivedCategory.homologyFunctor X.Modules

/- Domain-style sampling for Lemma 20.37.11:
- primary domain: derived inverse limits of `𝒪_X`-modules and their cohomology sheaves
  on a ringed space;
- sampled owner declarations:
  `RingedSpace.cohomologySheaf`,
  `𝓗[q](X, K)`,
  `moduleUnderlyingSheaf`,
  `moduleSectionsAsAbelianFunctor`,
  `DerivedCategory.homologyFunctor`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `single_limit_isDerivedLimit_of_basis_acyclicity`;
- best owner abstraction in the minimal Chapter 20 closure: the chapter owner
  `RingedSpace.cohomologySheaf`, used through the source-facing notation `𝓗[q](X, K)`, together
  with the Chapter 20 open-sections owner `moduleSectionsAsAbelianFunctor X U`; the
  cohomology-sheaf tower and its sectionwise `R^1 lim` terms are derived API from
  those owners and should be written directly through those canonical functors, with the nearby
  owner theorem `single_limit_isDerivedLimit_of_basis_acyclicity` governing the inverse-limit
  behavior of the cohomology-sheaf tower rather than through raw presheaf-evaluation composites;
- primitive data: a ringed space `X`, a sequential inverse system `Ksys`, a chosen derived limit
  object `K`, and a degree `q`;
- derived API here: the direct composites
  `Ksys ⋙ DerivedCategory.homologyFunctor X.Modules q ⋙ moduleUnderlyingSheaf X`
  and
  `Ksys ⋙ DerivedCategory.homologyFunctor X.Modules q ⋙ moduleSectionsAsAbelianFunctor X U`,
  used directly rather than through one-off local wrapper declarations.

Source/core/bridge triage:
- `source-facing`: the basiswise acyclicity hypotheses and the resulting comparison theorem;
- `core/canonical`: `RingedSpace.cohomologySheaf`, `moduleUnderlyingSheaf`,
  `moduleSectionsAsAbelianFunctor`, `DerivedCategory.homologyFunctor`, and
  `SequentialInverseSystem.firstDerivedLimit`;
- `bridge/view`: the sectionwise towers over a fixed open `U`.
-/

-- Proof sketch: for each basis open `U ∈ ℬ`, the vanishing hypothesis kills the higher
-- cohomology of the sheaves `𝓗[q](X, K_n)`, so Lemma `20.37.10` identifies `H^q(U, K_n)` with
-- the degree-zero sections of `𝓗[q](X, K_n)`. Apply the Chapter 20 owner theorem
-- `single_limit_isDerivedLimit_of_basis_acyclicity` to the tower `n ↦ H^q(K_n)`: the hypothesis
-- `hR1lim` is exactly the vanishing of the canonical Milnor `R^1 lim` term for its
-- section tower. This identifies the degree-`q` cohomology sheaf of the chosen derived limit `K`
-- with the ordinary inverse limit sheaf of the cohomology-sheaf tower.
/-- Lemma 20.37.11: let `(X, 𝒪_X)` be a ringed space, let `(K_n)` be an inverse system in
`D(𝒪_X)`, and let `K = R lim_n K_n` be a chosen derived limit. Assume every open subset of `X`
admits a covering by members of `ℬ`, that for every `U ∈ ℬ`, every `n`, and every `p > 0` one
has `IsZero ((𝓗[q](X, K_n)).H' p U)`, and that for every `U ∈ ℬ` the inverse system
`n ↦ (𝓗[q](X, K_n)).H' 0 U` has vanishing `R^1 lim`. Then the cohomology sheaf `𝓗[q](X, K)` is
isomorphic to the inverse limit sheaf `limit (Ksys ⋙ HMod q ⋙ moduleUnderlyingSheaf X)`. -/
@[stacks 0BKU]
theorem derivedLimit_cohomologySheaf_isomorphic_limit_of_basiswise_acyclicity
    (Ksys : SequentialInverseSystem DModX)
    (K : DModX)
    (hK : IsDerivedLimit Ksys K)
    (ℬ : Set (Opens X.carrier))
    (hℬ : Opens.IsBasis ℬ)
    (q : ℤ)
    (hacyclic :
      ∀ U : Opens X.carrier, U ∈ ℬ →
        ∀ n : ℕ, ∀ p : ℕ, 0 < p →
          IsZero ((𝓗[q](X, Ksys.obj (op n))).H' p U))
    (hR1lim :
      ∀ U : Opens X.carrier, U ∈ ℬ →
        IsZero
          (SequentialInverseSystem.firstDerivedLimit
            (Ksys ⋙ HMod q ⋙ moduleSectionsAsAbelianFunctor X U)))
    :
    IsIsomorphic
      (𝓗[q](X, K))
      (limit (Ksys ⋙ HMod q ⋙ moduleUnderlyingSheaf X)) :=
  sorry

end

end AlgebraicGeometry.RingedSpace
