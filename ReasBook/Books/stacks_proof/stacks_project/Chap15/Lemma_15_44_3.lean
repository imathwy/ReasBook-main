import stacks_proof.stacks_project.Chap10.Lemma_10_110_9
import stacks_proof.stacks_project.Chap10.Lemma_10_112_8
import stacks_proof.stacks_project.Chap10.Lemma_10_143_5
import stacks_proof.stacks_project.Chap15.Lemma_15_44_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.Etale A B]

/- Domain-style sampling for Lemma 15.44.3:
- primary domain: regular local rings under étale localization in local commutative algebra;
- sampled owner declarations of the same kind:
  `IsRegularLocalRing`,
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`,
  `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`,
  `localizationAtPrime_isNoetherianRing_iff_of_etale`;
- owner abstraction: the canonical local rings
  `Localization.AtPrime (q.asIdeal.under A)` and `Localization.AtPrime q.asIdeal`;
- primitive data: the étale algebra `A → B` and the prime `q : PrimeSpectrum B`;
- derived API: Noetherian ascent/descent for the localizations and regularity of the closed fiber
  of the induced local map.

Layer triage:
- `source-facing`: regularity equivalence for the local rings at `q ∩ A` and `q`;
- `core/canonical`: `IsRegularLocalRing` on those two owner localizations;
- `bridge/view`: identifying the closed fiber with a field via the canonical
  `Ideal.Fiber`/quotient comparison for the induced local map.

As in nearby chapter files phrased on localized owners, the prime should be carried by the
canonical point `q : PrimeSpectrum B` rather than by an ideal together with a separate
`[q.IsPrime]` instance. Its contraction `q.asIdeal.under A` is then built into the owner
localizations with no extra public data.
-/
section

variable (q : PrimeSpectrum B)

local notation "Aq" => Localization.AtPrime (q.asIdeal.under A)
local notation "Bq" => Localization.AtPrime q.asIdeal
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal Aq) Bq

/-- Lemma 15.44.3: if `A → B` is an étale ring map and `q` is a prime of `B`, then the local ring
`A_(q ∩ A)` is regular if and only if the local ring `B_q` is regular. -/
@[stacks 0AH0]
theorem localizationAtPrime_isRegularLocalRing_iff_of_etale :
    IsRegularLocalRing Aq ↔ IsRegularLocalRing Bq := by
  have hnoetherian : IsNoetherianRing Aq ↔ IsNoetherianRing Bq :=
    localizationAtPrime_isNoetherianRing_iff_of_etale q
  have hq_ne_top : q.asIdeal ≠ ⊤ :=
    Ideal.IsPrime.ne_top (inferInstance : q.asIdeal.IsPrime)
  have hEtaleAway : ∃ g : B, g ∉ q.asIdeal ∧ Algebra.Etale A (Localization.Away g) :=
    ⟨1, by simpa [Ideal.ne_top_iff_one] using hq_ne_top, inferInstance⟩
  have hclosedFiber : IsRegularLocalRing ClosedFiber := by
    have hmap : (maximalIdeal Aq).map (algebraMap Aq Bq) = maximalIdeal Bq := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (q.asIdeal.under A) Aq, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq A Aq Bq]
      simpa using map_eq_maximalIdeal_of_exists_etale_away q.asIdeal hEtaleAway
    let _ : Field (Bq ⧸ maximalIdeal Bq) := Ideal.Quotient.field (maximalIdeal Bq)
    let _ : IsRegularLocalRing (Bq ⧸ maximalIdeal Bq) := inferInstance
    let _ : IsRegularLocalRing (Bq ⧸ (maximalIdeal Aq).map (algebraMap Aq Bq)) :=
      IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq hmap).symm
    exact isRegularLocalRing_closedFiber_of_quotient
  constructor
  · intro hAq
    let _ : IsRegularLocalRing Aq := hAq
    let _ : IsNoetherianRing Bq := hnoetherian.mp inferInstance
    exact isRegularLocalRing_of_flat_localHom_of_regular_closedFiber hclosedFiber
  · intro hBq
    let _ : IsRegularLocalRing Bq := hBq
    let _ : IsNoetherianRing Aq := hnoetherian.mpr inferInstance
    exact isRegularLocalRing_of_flat_localHom_of_regularTarget Bq

end

end
