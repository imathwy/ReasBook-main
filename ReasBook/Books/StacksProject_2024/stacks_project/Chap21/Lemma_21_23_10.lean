import StacksProject_2024.Chap21.Lemma_21_23_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom
open scoped RingedSiteCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/-
Domain-style sampling for Lemma 21.23.10:
- primary domain: truncation-derived-limit comparisons in `D(\mathcal O_X)` on a ringed site,
  under a uniform vanishing bound for the negative cohomology sheaves of a derived object;
- sampled owner declarations:
  `ModuleCat`,
  `ModuleDerived`,
  `cohomologyOverObject`,
  `BasiswiseEventualCohomologySheafVanishing`,
  `truncationComparison_isIso_of_uniform_basiswise_eventual_cohomologySheaf_vanishing`,
  `CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty`;
- best owner abstraction: this file is `source-facing` only for the negative-degree uniform
  specialization. The ambient module category, derived category, objectwise cohomology owner, and
  site cover owner are already canonical upstream, and the right abstraction for the proof is the
  uniform-eventual criterion from Lemma `21.23.9`;
- primitive data: a derived object `E`, a comparison map `c : E ⟶ K`, a basis subset `B`, and a
  uniform bound `d` for the negative cohomology sheaves on basis objects;
- derived API: the source-facing owner
  `UniformBasiswiseNegativeCohomologySheafVanishing` and its bridge
  `UniformBasiswiseNegativeCohomologySheafVanishing.toEventual`, used by the source-facing
  specialization of Lemma `21.23.9`.

Source/core/bridge triage:
- `source-facing`: the uniform negative-degree vanishing criterion below;
- `core/canonical`: `ModuleCat X`, `ModuleDerived X`, `H^p(U, K)`,
  `truncationComparison_isIso_of_uniform_basiswise_eventual_cohomologySheaf_vanishing`, and
  `X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B)`;
- `bridge/view`: the bound function `m ↦ d + max 0 m`, which converts the negative-degree
  vanishing hypothesis into the eventual-vanishing owner of Lemma `21.23.9`. -/

section

variable (X : RingedSite.{u, v})

local notation "ModX" => ModuleCat X
local notation "DModX" => ModuleDerived X
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)

/-- Uniform negative-degree vanishing on basis objects, with a single bound `d` shared across the
whole basis subset `B`. -/
def UniformBasiswiseNegativeCohomologySheafVanishing
    (E : DModX) (d : ℕ) (B : Set X) : Prop :=
  ∀ ⦃V : X⦄, V ∈ B → ∀ p q : ℤ, d < p → q < 0 →
    IsZero
      (H^p(V, (single0).obj (𝓗[q](X, E))))

-- Proof sketch: apply the Chapter 21 owner `Lemma 21.23.9` with the uniform eventual bound
-- `pBound(m) = d + max 0 m`. If `m < 0`, this reduces to the stated hypothesis with `q = m - p`;
-- if `m ≥ 0`, then `p > d + m` again forces `m - p < 0`, so the same negative-degree vanishing
-- applies.
/-- The uniform negative-degree vanishing hypothesis yields the uniform eventual-vanishing input
for Lemma `21.23.9` via the bound function `m ↦ d + max 0 m`. -/
theorem UniformBasiswiseNegativeCohomologySheafVanishing.toEventual
    {E : DModX} {d : ℕ} {B : Set X}
    (h : UniformBasiswiseNegativeCohomologySheafVanishing X E d B) :
    ∀ ⦃V : X⦄, V ∈ B → ∀ p m : ℤ, d + max 0 m < p →
      IsZero
        (H^p(V, (single0).obj (𝓗[(m - p)](X, E)))) := by
  intro V hV p m hp
  have h0d : (0 : ℤ) ≤ d := by
    exact_mod_cast Nat.zero_le d
  rcases lt_or_ge m 0 with hm | hm
  · have hd : (d : ℤ) < p := by
      simpa [max_eq_left_of_lt hm] using hp
    have hp0 : (0 : ℤ) < p := lt_of_le_of_lt h0d hd
    have hq : m - p < 0 := lt_trans (sub_lt_self m hp0) hm
    simpa using h hV p (m - p) hd hq
  · have hdm : (d : ℤ) + m < p := by
      simpa [max_eq_right hm] using hp
    have hd : (d : ℤ) < p := by
      exact lt_of_le_of_lt (le_add_of_nonneg_right hm) hdm
    have hmle : m ≤ (d : ℤ) + m := by
      simpa [add_comm] using le_add_of_nonneg_right h0d
    have hq : m - p < 0 := sub_lt_zero.mpr (lt_of_le_of_lt hmle hdm)
    simpa using h hV p (m - p) hd hq

variable [CategoryWithHomology (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

/-- Lemma 21.23.10: let `(𝒞, 𝒪)` be a ringed site, let `E ∈ D(𝒪)`,
and assume there exist an integer `d ≥ 0` and a subset `B` of objects of `𝒞` such that
every object admits a covering by members of `B` and
`H^p(V, H^q(E)) = 0` for `p > d`, `q < 0`, and `V ∈ B`. Then any compatible comparison map
from `E` to a chosen derived limit of the truncation tower `(τ≥ -n E)_n`, i.e. any
formalization of the canonical map `E ⟶ R lim_n τ≥ -n E` from
Remark `13.34.5`, is an isomorphism in `D(𝒪)`. -/
@[stacks 0D6P]
theorem truncationComparison_isIso_of_uniform_basiswise_negative_cohomologySheaf_vanishing
    (E K : DModX)
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E K c)
    (d : ℕ)
    (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish : UniformBasiswiseNegativeCohomologySheafVanishing X E d B) :
    IsIso c := by
  simpa using
    truncationComparison_isIso_of_uniform_basiswise_eventual_cohomologySheaf_vanishing
      X E K c hc (fun m ↦ d + max 0 m) B hcover
      (UniformBasiswiseNegativeCohomologySheafVanishing.toEventual X hvanish)

end
