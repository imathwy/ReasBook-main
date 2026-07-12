import StacksProject_2024.Chap20.Sections_on_open
import StacksProject_2024.Chap20.Lemma_20_32_3
import StacksProject_2024.Chap20.Lemma_20_37_9

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

open scoped RingedSpaceCohomology
open scoped RingedSpaceOpenHypercohomology

section

variable (X : RingedSpace.{u})
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{v} X.Modules]

/- Domain-style sampling for Lemma 20.37.10:
- primary domain: hypercohomology of a derived `𝒪_X`-module on members of a covering
  family of opens and its
  comparison with sections of the cohomology sheaf;
- sampled owner declarations:
  `moduleOpenHypercohomology`,
  `RingedSpace.cohomologySheaf`,
  `𝓗[q](X, K)`,
  `Opens.IsBasis`,
  `CategoryTheory.Limits.IsZero`;
- best owner abstraction in the current minimal compile closure: the Chapter 20 fixed-open owner
  `moduleOpenHypercohomology X U K q`, used through the scoped notation `H^q(U, K)` from
  `Sections_on_open`, together with the Chapter 20 cohomology-sheaf owner
  `RingedSpace.cohomologySheaf X K q`, used through the scoped notation `𝓗[q](X, K)` from
  `Lemma_20_32_3`, and the canonical basis owner `Opens.IsBasis`;
- primitive data: the ringed space `X`, the derived object `K`, the family `ℬ` of opens, the
  chosen open `U ∈ ℬ`, the degree `q`, and the coverwise vanishing hypothesis on the cohomology
  sheaf;
- derived API: the comparison theorem below for members of the covering family.

Source/core/bridge triage:
- `source-facing`: the coverwise comparison `H^q(U, K) ≅ H^0(U, H^q(K))`;
- `core/canonical`: `moduleOpenHypercohomology`, `RingedSpace.cohomologySheaf`,
  `Opens.IsBasis`, and
  `IsZero`;
- `bridge/view`: the scoped source-facing notations `H^q(U, K)` and `𝓗[q](X, K)`. -/

-- Proof sketch: apply Lemma `20.37.9` with `d = 0` to identify `K` with the derived limit of its
-- truncation tower. For `U ∈ ℬ`, use the Milnor short exact sequence from `20.37.3.1` for that
-- tower. Example `20.29.3` computes the cohomology of each bounded-below truncation
-- `τ≥(-n) K` from its cohomology sheaves, and the hypothesis forces the resulting spectral
-- sequence to degenerate at `E₂`, giving `H^q(U, τ≥(-n) K) = H^0(U, H^q(τ≥(-n) K))`.
-- Once `n > -q`, these groups stabilize to `H^0(U, H^q(K))`, so the `R¹ lim` term
-- vanishes and the limit term is canonically `H^0(U, H^q(K))`.
/-- Lemma 20.37.10: let `(X, 𝒪_X)` be a ringed space, let `K ∈ D(𝒪_X)`, and
let `ℬ` be a set of opens of `X` whose members form a basis of `X`, equivalently every open
subset of `X` admits a covering by members of `ℬ`. If for every `U ∈ ℬ`, every `q : ℤ`, and
every `p > 0` one has `H^p(U, H^q(K)) = 0`, then for every `U ∈ ℬ` and every `q : ℤ` the
hypercohomology group `H^q(U, K)` is canonically isomorphic to the degree-zero cohomology
`H^0(U, H^q(K))` of the cohomology sheaf. -/
@[stacks 0BKT]
theorem moduleOpenHypercohomology_iso_zeroDegree_of_coverwise_cohomologySheafAcyclic
    (K : DerivedCategory X.Modules)
    (ℬ : Set (Opens X.carrier))
    (hℬ : Opens.IsBasis ℬ)
    (hacyclic :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ ℬ →
        ∀ q : ℤ, ∀ p : ℕ, 0 < p →
          IsZero ((𝓗[q](X, K)).H' p U))
    (U : Opens X.carrier) (hU : U ∈ ℬ) (q : ℤ) :
    IsIsomorphic
      (H^q(U, K))
      ((𝓗[q](X, K)).H' 0 U) := sorry

end

end AlgebraicGeometry.RingedSpace
