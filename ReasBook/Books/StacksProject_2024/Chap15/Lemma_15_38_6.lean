import Mathlib
import stacks_project.Chap10.Definition_10_137_10
import stacks_project.Chap15.Definition_15_37_3
import stacks_project.Chap15.Lemma_15_37_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingHom

universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling for Lemma 15.38.6:
- primary domain: smoothness at a prime versus adic formal smoothness of the induced local map in
  commutative algebra;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `Localization.localRingHom`,
  `Algebra.FormallySmooth.localization_base`,
  `RingHom.FormallySmooth.toTopologically`;
- best owner abstraction: the source-facing owner is `SmoothAtPrime A B q`, while the canonical
  local owner `IsSmoothAt A q.asIdeal` is the internal bridge, and the localized adic
  formal-smoothness condition is derived from the canonical localized algebra and then translated
  to the chapter owner `RingHom.formally_smooth_for_adic`;
- primitive data: a prime `q : PrimeSpectrum B` together with the finite-presentation hypothesis
  needed for the source-facing/local smoothness bridge;
- derived API: the equivalence between smoothness at `q` and adic formal smoothness of the
  canonical local map `A_(q ∩ A) → B_q`.

Source/core/bridge triage:
- `source-facing`: the equivalence between `SmoothAtPrime A B q` and adic formal smoothness of
  `A_(q ∩ A) → B_q`;
- `core/canonical`: `IsSmoothAt A q.asIdeal`;
- `bridge/view`: `(Localization.localRingHom ...).formally_smooth_for_adic` for the localized map
  `Localization.AtPrime (q.asIdeal.under A) → Localization.AtPrime q.asIdeal`. -/

private theorem localRingHom_formally_smooth_for_adic_of_isSmoothAt
    (q : PrimeSpectrum B) [IsSmoothAt A q.asIdeal] :
    formally_smooth_for_adic
      (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)
      (maximalIdeal (Localization.AtPrime q.asIdeal)) := by
  let f := Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl
  letI : Algebra (Localization.AtPrime (q.asIdeal.under A)) (Localization.AtPrime q.asIdeal) :=
    f.toAlgebra
  letI : TopologicalSpace (Localization.AtPrime (q.asIdeal.under A)) := ⊥
  letI : DiscreteTopology (Localization.AtPrime (q.asIdeal.under A)) := ⟨rfl⟩
  letI : TopologicalSpace (Localization.AtPrime q.asIdeal) :=
    Ideal.adicTopology (maximalIdeal (Localization.AtPrime q.asIdeal))
  letI : TopologicalRing.IsPreadicRing (Localization.AtPrime q.asIdeal) :=
    { toIsTopologicalRing := inferInstance
      exists_ideal_isAdic := ⟨maximalIdeal (Localization.AtPrime q.asIdeal), rfl⟩ }
  change f.FormallySmoothTopologically
  have hfsAlg :
      Algebra.FormallySmooth (Localization.AtPrime (q.asIdeal.under A))
        (Localization.AtPrime q.asIdeal) := by
    letI : Algebra.FormallySmooth A (Localization.AtPrime q.asIdeal) := ‹IsSmoothAt A q.asIdeal›
    simpa using
      (Algebra.FormallySmooth.localization_base (Ideal.primeCompl (q.asIdeal.under A)))
  have hfs : f.FormallySmooth := by
    simpa [f, RingHom.algebraMap_toAlgebra] using hfsAlg
  simpa [formally_smooth_for_adic, f] using
    (FormallySmooth.toTopologically hfs continuous_of_discreteTopology)

private theorem isSmoothAt_of_localRingHom_formally_smooth_for_adic
    [FinitePresentation A B] (q : PrimeSpectrum B)
    (hq :
      formally_smooth_for_adic
        (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)
        (maximalIdeal (Localization.AtPrime q.asIdeal))) :
    IsSmoothAt A q.asIdeal := by
  sorry

-- Proof sketch: rewrite `SmoothAtPrime A B q` through `smoothAtPrime_iff_isSmoothAt`, then use
-- the canonical localized-owner chain
-- `IsSmoothAt A q.asIdeal → Algebra.FormallySmooth A B_q
--   → Algebra.FormallySmooth A_(q ∩ A) B_q
--   → (A_(q ∩ A) → B_q).formally_smooth_for_adic (maximalIdeal B_q)`.
-- The converse uses the same localized map as source-facing adic data together with the
-- finite-presentation hypothesis carried by the theorem.
/-- Lemma 15.38.6 as a source-facing bridge: if `A → B` is finitely presented and `q` is a prime
of `B`, then `A → B` is smooth at `q` in the Stacks sense if and only if the induced local map
`A_(q ∩ A) → B_q` is formally smooth for the `maximalIdeal B_q`-adic topology. -/
theorem smoothAtPrime_iff_formally_smooth_for_adic_localized_map
    [FinitePresentation A B] (q : PrimeSpectrum B) :
    SmoothAtPrime A B q ↔
      formally_smooth_for_adic
        (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)
        (maximalIdeal (Localization.AtPrime q.asIdeal)) := by
  rw [smoothAtPrime_iff_isSmoothAt]
  constructor
  · intro hq
    letI : IsSmoothAt A q.asIdeal := hq
    exact localRingHom_formally_smooth_for_adic_of_isSmoothAt q
  · intro hq
    exact isSmoothAt_of_localRingHom_formally_smooth_for_adic q hq

end

end Algebra
