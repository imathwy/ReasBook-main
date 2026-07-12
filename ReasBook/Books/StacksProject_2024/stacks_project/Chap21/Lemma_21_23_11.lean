import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap13.Lemma_13_35_7
import StacksProject_2024.Chap13.Lemma_13_42_3
import StacksProject_2024.Chap21.Lemma_21_23_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open RingedSite.Hom
open scoped RingedSiteCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/-
Domain-style sampling for Lemma 21.23.11:
- primary domain: derived sections over a fixed object of a ringed site and the comparison between
  `H^q(U, K)` and the sections `Γ(U, H^q(K))` of the cohomology sheaf;
- sampled owner declarations:
  `RingedSite.Hom.moduleSectionsAsAbelianFunctor`,
  `RingedSite.Hom.cohomologyOverObject`,
  `RingedSite.Hom.cohomologySheaf`;
- best owner abstraction: this theorem is `source-facing`, and Chapter 21 already owns the
  relevant notions by `H^q(U, K)` and `𝓗[q](X, K)`, while the module-sheaf specialization is the
  direct degree-zero use of `H^p(U, -)`, so the public statement
  should use those owners rather than a parallel derived-sections spelling or the raw sections
  bridge;
- primitive data: a ringed site `X`, an object `K : D(𝒪_X)`, a fixed object `U`, and an
  integer `q`;
- derived API: the source-facing objectwise cohomology owner
  `H^q(U, K)`, the cohomology sheaf `𝓗[q](X, K)`, and the
  degree-zero specialization `H^p(U, ℱ[0])`.

Source/core/bridge triage:
- `source-facing`: the fixed-object acyclicity criterion and its resulting comparison isomorphism;
- `core/canonical`: `RingedSite.Hom.moduleSectionsAsAbelianFunctor`,
  `RingedSite.Hom.moduleSectionsAsAbelianDerived`,
  `RingedSite.Hom.cohomologyOverObject`,
  `RingedSite.Hom.cohomologySheaf`;
- `bridge/view`: the degree-zero embedding `H^q(K) ↦ H^q(K)[0]`, confined to the upstream
  module-sheaf cohomology owner instead of appearing in the public theorem surface.
-/

section

variable (X : RingedSite.{u, v})

local notation "ModX" => ModuleCat X
local notation "DModX" => ModuleDerived X
local notation "HMod" => DerivedCategory.homologyFunctor ModX
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)

/-- Helper for Lemma 21.23.11: the source proof uses the shifted lower truncation stage
`τ_{\ge -(n + 1)} K` as the `n`-th term of the Milnor tower. -/
private noncomputable abbrev shifted_truncation_stage
    (K : DModX) (n : ℕ) : DModX :=
  (t.truncGE (-(((n + 1 : ℕ)) : ℤ))).obj K

-- The source proof needs one stage bound that simultaneously works for the `q` and `q - 1`
-- truncation towers, since eventual constancy is read in both adjacent degrees.
/-- Helper for Lemma 21.23.11: beyond a sufficiently large truncation stage, the truncation index
`-n` lies below `q - 1`, hence also below `q`. -/
private lemma truncation_stage_eventually_below_adjacent_degrees
    (q : ℤ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → -((n : ℕ) : ℤ) ≤ q - 1 := by
  refine ⟨Int.toNat (1 - q), ?_⟩
  intro n hn
  -- Convert the eventual stage inequality to an integer inequality and solve the bound linearly.
  have hbound : (((Int.toNat (1 - q)) : ℕ) : ℤ) ≤ n := by
    exact_mod_cast hn
  omega

/-- Helper for Lemma 21.23.11: below the queried degree, lower truncation does not change the
`q`-th cohomology sheaf, via the canonical truncation comparison from
`Lemma_13_42_3`. -/
private lemma cohomologySheaf_truncGE_isomorphic_of_le
    (K : DModX) (a q : ℤ) (haq : a ≤ q) :
    IsIsomorphic
      (𝓗[q](X, (t.truncGE a).obj K))
      (𝓗[q](X, K)) := by
  letI : IsIso ((HMod q).map ((t.truncGEπ a).app K)) :=
    isIso_homologyMap_truncGEπ_of_le K a q haq
  exact ⟨(asIso ((HMod q).map ((t.truncGEπ a).app K))).symm⟩

/-- Helper for Lemma 21.23.11: beyond a sufficiently large truncation stage, the cohomology
sheaves in degrees `q` and `q - 1` of `τ_{\ge -n} K` have stabilized to those of `K`. -/
private lemma adjacent_cohomologySheaf_truncGE_eventually_constant
    (K : DModX) (q : ℤ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsIsomorphic
        (𝓗[q](X, (t.truncGE (-((n : ℕ) : ℤ))).obj K))
        (𝓗[q](X, K)) ∧
      IsIsomorphic
        (𝓗[(q - 1)](X, (t.truncGE (-((n : ℕ) : ℤ))).obj K))
        (𝓗[(q - 1)](X, K)) := by
  rcases truncation_stage_eventually_below_adjacent_degrees q with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  intro n hn
  have hqMinusOne : -((n : ℕ) : ℤ) ≤ q - 1 := hn₀ n hn
  have hq : -((n : ℕ) : ℤ) ≤ q := by
    omega
  -- Apply the truncation comparison in the two adjacent cohomological degrees.
  refine ⟨?_, ?_⟩
  · exact cohomologySheaf_truncGE_isomorphic_of_le X K (-((n : ℕ) : ℤ)) q hq
  · exact cohomologySheaf_truncGE_isomorphic_of_le X K (-((n : ℕ) : ℤ)) (q - 1) hqMinusOne

/-- Helper for Lemma 21.23.11: the shifted lower truncation stages `τ_{\ge -(n + 1)} K` are
eventually below both adjacent degrees `q` and `q - 1`. -/
private lemma shifted_truncation_stage_eventually_below_adjacent_degrees
    (q : ℤ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → -(((n + 1 : ℕ)) : ℤ) ≤ q - 1 := by
  rcases truncation_stage_eventually_below_adjacent_degrees q with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  intro n hn
  have hstage : -(((n : ℕ)) : ℤ) ≤ q - 1 := hn₀ n hn
  omega

/-- Helper for Lemma 21.23.11: in the shifted tower used by the source proof, the cohomology
sheaves in degrees `q` and `q - 1` eventually stabilize to those of `K`. -/
private lemma adjacent_cohomologySheaf_shifted_truncGE_eventually_constant
    (K : DModX) (q : ℤ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsIsomorphic
        (𝓗[q](X, (t.truncGE (-(((n + 1 : ℕ)) : ℤ))).obj K))
        (𝓗[q](X, K)) ∧
      IsIsomorphic
        (𝓗[(q - 1)](X, (t.truncGE (-(((n + 1 : ℕ)) : ℤ))).obj K))
        (𝓗[(q - 1)](X, K)) := by
  rcases shifted_truncation_stage_eventually_below_adjacent_degrees q with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  intro n hn
  have hqMinusOne : -((((n + 1 : ℕ)) : ℤ)) ≤ q - 1 := hn₀ n hn
  have hq : -((((n + 1 : ℕ)) : ℤ)) ≤ q := by
    omega
  -- Apply the truncation comparison in the two adjacent cohomological degrees for the shifted
  -- stage `τ_{\ge -(n + 1)}`.
  refine ⟨?_, ?_⟩
  · exact cohomologySheaf_truncGE_isomorphic_of_le X K (-((((n + 1 : ℕ)) : ℤ))) q hq
  · exact
      cohomologySheaf_truncGE_isomorphic_of_le X K (-((((n + 1 : ℕ)) : ℤ))) (q - 1) hqMinusOne

-- Proof sketch: apply the spectral sequence of Lemma `13.21.3` to the sections functor
-- `Γ(U, -)` and to the bounded-below truncations `τ≥-n K`. The fixed-object
-- higher-cohomology vanishing hypothesis forces the spectral sequence to degenerate over `U`, so
-- for each truncation one gets
-- `H^q(U, τ≥-n K) ≅ Γ(U, 𝓗[q](X, τ≥-n K))`. For `n` large relative to `q`, the right-hand side
-- stabilizes to `Γ(U, 𝓗[q](X, K))`. Combine this stabilization with the Milnor short exact
-- sequence for `RΓ[X](U)` and the truncation-limit comparison from Lemma `21.23.10` to identify
-- `H^q(U, K)` with the sections `Γ(U, 𝓗[q](X, K))`.
/-- Lemma 21.23.11: let `(𝒞, 𝒪)` be a ringed site, let `K` be an object of `D(𝒪)`, and fix an
object `U` of `𝒞`. If for all `p > 0` and `q ∈ ℤ` the `q`-th cohomology sheaf `𝓗[q](X, K)` has
vanishing higher cohomology over `U`, then for every `q ∈ ℤ` the derived cohomology group
`H^q(U, K)` is naturally identified with the degree-zero cohomology
`H^0(U, (single0).obj (𝓗[q](X, K)))`, equivalently the sections `Γ(U, 𝓗[q](X, K))` of the
`q`-th cohomology sheaf. -/
@[stacks 0BKZ]
theorem ringedSite_cohomologyOverObject_iso_zeroDegree_of_cohomologySheafAcyclic
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
    (K : DModX)
    (U : X)
    (hacyclic :
      ∀ (p : ℤ), 0 < p → ∀ q : ℤ,
        IsZero (H^p(U, (single0).obj (𝓗[q](X, K)))))
    (q : ℤ) :
    IsIsomorphic
      (H^q(U, K))
      (H^0(U, (single0).obj (𝓗[q](X, K)))) := by
  -- Route correction: the source proof still has to run through the truncation tower
  -- `τ_{\ge -(n + 1)} K`, the Milnor short exact sequence over `U`, and eventual constancy in
  -- degrees `q` and `q - 1`.
  have hstableSheafShifted :
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        IsIsomorphic
          (𝓗[q](X, shifted_truncation_stage X K n))
          (𝓗[q](X, K)) ∧
        IsIsomorphic
          (𝓗[(q - 1)](X, shifted_truncation_stage X K n))
          (𝓗[(q - 1)](X, K)) :=
    adjacent_cohomologySheaf_shifted_truncGE_eventually_constant X K q
  let _ := hstableSheafShifted
  --
  -- The shifted source tower now has its verified stabilization frontier in adjacent degrees. The
  -- remaining blocker is therefore isolated to the source-faithful Milnor bridge: compare `K`
  -- with the derived limit of the shifted preimage tower, identify each bounded-below stage by
  -- Lemma `13.21.3`, and then use eventual constancy to kill the `R^1 lim` term.
  --
  -- TODO: construct the source-faithful chain
  -- `K ≅ R lim_n Q.obj ((Q.objPreimage K).truncGE (-(n + 1)))` over `RΓ(U, -)`, apply
  -- `ringedSiteDerivedSectionsOverObject_cohomology_shortExact`, identify each shifted truncation
  -- stage by the bounded-below spectral sequence of Lemma `13.21.3`, and finish by the verified
  -- shifted eventual constancy above.
  sorry

end
