import StacksProject_2024.stacks_project.Chap20.Lemma_20_37_6

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

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 20.37.7:
- primary domain: truncation-derived-limit comparisons in `D(𝒪_X)` and local vanishing of
  cohomology sheaves on a ringed space;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `moduleUnderlyingSheaf`,
  `DerivedCategory.homologyFunctor`,
  `CategoryTheory.IsTruncationDerivedLimitComparison`,
  `EventualCohomologySheafVanishingNear`;
- best owner abstraction: the Chapter 13 truncation-tower owner
  `IsTruncationDerivedLimitComparison` together with the Chapter 20 cohomology-sheaf notation
  `𝓗[q](X, E)`; the present file should keep only the stronger source-facing
  local-uniform vanishing condition and bridge it to the canonical eventual-vanishing owner of
  Lemma `20.37.6`;
- primitive data: a derived object `E : DerivedCategory X.Modules` and the pointwise local bound
  `d_x`;
- derived API here: the bridge from uniform negative-degree vanishing to
  `EventualCohomologySheafVanishingNear`, followed by the canonical truncation-comparison theorem
  of Lemma `20.37.6`.

Source/core/bridge triage:
- `source-facing`: `LocallyUniformNegativeCohomologySheafVanishing`;
- `core/canonical`: `moduleUnderlyingSheaf`, `DerivedCategory.homologyFunctor`,
  `EventualCohomologySheafVanishingNear`, and
  `IsTruncationDerivedLimitComparison`;
- `bridge/view`: the conversion theorem
  `LocallyUniformNegativeCohomologySheafVanishing.eventualCohomologySheafVanishingNear`.
-/

/-- Helper for Lemma 20.37.7: a derived `𝒪_X`-module has locally uniform vanishing of higher cohomology for its
negative cohomology sheaves if, near each point `x`, there is one bound `d_x` that annihilates
`H^p(U, H^q(E))` for all `q < 0` on some neighborhood basis of `x`. -/
def LocallyUniformNegativeCohomologySheafVanishing
    (E : DerivedCategory ModX) : Prop :=
  ∀ x : X, ∃ d : ℕ,
    ∀ W : Opens X.carrier, x ∈ W →
      ∃ U : Opens X.carrier,
        x ∈ U ∧ U ≤ W ∧
          ∀ q : ℤ, q < 0 →
            ∀ p : ℕ, d < p →
              IsZero ((𝓗[q](X, E)).H' p U)

-- Proof sketch: this is immediate by unfolding
-- `LocallyUniformNegativeCohomologySheafVanishing`; the hypothesis already says that for each
-- point `x` and each neighborhood `W` of `x`, one may shrink to such a `U`.
/-- Helper for Lemma 20.37.7: the local uniform vanishing hypothesis can be applied after shrinking inside any prescribed
open neighborhood of a point. -/
theorem LocallyUniformNegativeCohomologySheafVanishing.exists_shrunk_open
    {E : DerivedCategory ModX}
    (hE : LocallyUniformNegativeCohomologySheafVanishing X E)
    (x : X) :
    ∃ d : ℕ,
      ∀ W : Opens X.carrier, x ∈ W →
        ∃ U : Opens X.carrier,
          x ∈ U ∧ U ≤ W ∧
            ∀ q : ℤ, q < 0 →
              ∀ p : ℕ, d < p →
                IsZero ((𝓗[q](X, E)).H' p U) := by
  -- Unfold the source-facing predicate once to recover the neighborhood-shrinking data at `x`.
  simpa [LocallyUniformNegativeCohomologySheafVanishing] using hE x

-- Proof sketch: for the total degree `m`, use the bound `p(x,m) = d_x + max(0,m)`. Then
-- `p(x,m) < p` implies both `d_x < p` and `m - p < 0`, so the defining negative-degree vanishing
-- hypothesis applies to the cohomology sheaf `H^{m-p}(E)`.
/-- Helper for Lemma 20.37.7: the local uniform vanishing hypothesis implies the eventual local
vanishing condition required in Lemma `20.37.6`. -/
theorem LocallyUniformNegativeCohomologySheafVanishing.eventualCohomologySheafVanishingNear
    {E : DerivedCategory ModX}
    (hE : LocallyUniformNegativeCohomologySheafVanishing X E) :
    EventualCohomologySheafVanishingNear X E := by
  -- Recover the pointwise bound `d_x` and the corresponding shrinking statement from the source
  -- hypothesis, then package it into the Chapter 20 eventual-vanishing owner.
  intro x
  rcases hE x with ⟨d, hd⟩
  refine ⟨fun m ↦ (d : ℤ) + max 0 m, ?_⟩
  intro W hxW
  rcases hd W hxW with ⟨U, hxU, hUW, hU⟩
  refine ⟨U, hxU, hUW, ?_⟩
  intro m p hp
  -- The chosen bound controls both the cohomological degree and the negativity of `m - p`.
  have hd0 : (0 : ℤ) ≤ d := by
    exact_mod_cast Nat.zero_le d
  have hd_le : (d : ℤ) ≤ (d : ℤ) + max 0 m := by
    simpa using add_le_add_left (le_max_left (0 : ℤ) m) (d : ℤ)
  have hdp : d < p := by
    have hdp' : (d : ℤ) < p := lt_of_le_of_lt hd_le hp
    exact_mod_cast hdp'
  have hm_le : m ≤ (d : ℤ) + max 0 m := by
    have hmax_le : max 0 m ≤ (d : ℤ) + max 0 m := by
      simpa [zero_add] using add_le_add_right hd0 (max 0 m)
    exact le_trans (le_max_right (0 : ℤ) m) hmax_le
  have hm_lt : m < p := lt_of_le_of_lt hm_le hp
  have hq : m - (p : ℤ) < 0 := by
    omega
  exact hU (m - (p : ℤ)) hq p hdp

-- Proof sketch: convert the source hypothesis to
-- `EventualCohomologySheafVanishingNear` via
-- `LocallyUniformNegativeCohomologySheafVanishing.eventualCohomologySheafVanishingNear`, then
-- apply Lemma `20.37.6`.
/-- Lemma 20.37.7: let `(X, 𝒪_X)` be a ringed space and let `E ∈ D(𝒪_X)`.
Assume that for every `x ∈ X` there exist an integer `d_x ≥ 0` and a fundamental system of open
neighborhoods of `x` such that `H^p(U, H^q(E)) = 0` for all members `U` of that system, all
`p > d_x`, and all `q < 0`. Then any compatible comparison map
from `E` to the right-derived inverse limit of the truncation tower `τ≥(-n) E`
from Remark `13.34.5` is an isomorphism in `D(𝒪_X)`. -/
@[stacks 0D63]
theorem isIso_of_truncationDerivedLimitComparison_of_locallyUniformNegativeCohomologySheafVanishing
    (E : DerivedCategory ModX)
    {L : DerivedCategory ModX} (c : E ⟶ L)
    (hc : IsTruncationDerivedLimitComparison E L c)
    (hE : LocallyUniformNegativeCohomologySheafVanishing X E) :
    IsIso c := by
  exact isIso_of_truncationDerivedLimitComparison_of_eventualCohomologySheafVanishingNear
    X E c hc hE.eventualCohomologySheafVanishingNear

end

end AlgebraicGeometry.RingedSpace
