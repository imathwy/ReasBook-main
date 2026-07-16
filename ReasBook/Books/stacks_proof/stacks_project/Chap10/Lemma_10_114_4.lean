import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_105_1
import stacks_proof.stacks_project.Chap10.Lemma_10_105_5
import stacks_proof.stacks_project.Chap10.Lemma_10_105_9
import stacks_proof.stacks_project.Chap10.Lemma_10_112_4
import stacks_proof.stacks_project.Chap10.Lemma_10_112_7
import stacks_proof.stacks_project.Chap10.Lemma_10_114_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable [Algebra.FiniteType k S] [IsDomain S]

/-
Domain-style sampling:
- primary domain: dimension theory of irreducible affine schemes of finite type over a field,
  organized through catenary prime-chain owners and the height/localization API;
- sampled owner declarations of the same kind:
  `IsCatenaryRing.maximalPrimeChainsHaveSameLength`,
  `universallyCatenaryRing_of_cohenMacaulayRing`,
  `universallyCatenaryRing_of_essFiniteType`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`;
- best owner abstraction: the ambient owner is the catenary prime-spectrum API for `S`, while the
  local comparison is owned by the canonical height formula for `Localization.AtPrime`;
- primitive data: the finite type domain `S` over the field `k`, and a maximal ideal
  `m : MaximalSpectrum S`;
- derived API: the source-facing equality between `ringKrullDim S` and the Krull dimension of the
  maximal localization `Localization.AtPrime m.asIdeal`.

Source/core/bridge triage:
* `source-facing`: the equidimensionality statement that all maximal localizations of an affine
  domain of finite type over a field have the same dimension as the ambient ring;
* `core/canonical`: `IsCatenaryRing S` together with the owner equalities
  `IsLocalization.AtPrime.ringKrullDim_eq_height` and
  `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`;
* `bridge/view`: the finite-type-over-a-field route to catenarity and the maximal-chain
  comparison specialized from polynomial rings in Lemma `10.114.3`.
-/
-- Proof sketch: fields are universally catenary through the Cohen-Macaulay bridge, so every
-- finite type `k`-algebra is catenary by the essentially-finite-type owner theorem. For a domain,
-- `Spec S` is irreducible, and the maximal-chain comparison from Lemma `10.114.3` identifies the
-- common length of maximal chains from the generic point to any closed point. The owner
-- height/localization formulas then identify that common length with both `ringKrullDim S` and
-- `ringKrullDim (Localization.AtPrime m.asIdeal)`.
/-- Helper for Chap10 Lemma 10 114 4: finite algebra fibers have zero-dimensional local rings. -/
private lemma ringKrullDim_fiberLocalRingAt_eq_zero_of_moduleFinite
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
    [Module.Finite R T] (q : PrimeSpectrum T) :
    ringKrullDim (fiberLocalRingAt R T q) = 0 := by
  -- A finite algebra is quasi-finite, so the fiber ring is Artinian; localization preserves this.
  have hArt : IsArtinianRing (fiberLocalRingAt R T q) := by
    dsimp [fiberLocalRingAt]
    exact IsArtinianRing.localization_artinian
      ((fiberPrimeAt R T q).asIdeal.primeCompl)
      (Localization.AtPrime (fiberPrimeAt R T q).asIdeal)
  letI : IsArtinianRing (fiberLocalRingAt R T q) := hArt
  have hNoeth : IsNoetherianRing (fiberLocalRingAt R T q) := inferInstance
  letI : IsNoetherianRing (fiberLocalRingAt R T q) := hNoeth
  -- Convert the Artinian local fiber ring into the canonical zero-dimensional Krull statement.
  have hle : Ring.KrullDimLE 0 (fiberLocalRingAt R T q) :=
    (isArtinianRing_iff_krullDimLE_zero (R := fiberLocalRingAt R T q)).mp hArt
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hle

/-- Helper for Chap10 Lemma 10 114 4: under a finite going-down map, local dimensions agree with
the contracted prime. -/
private lemma ringKrullDim_localizationAtPrime_eq_under_of_moduleFinite_hasGoingDown
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
    [IsNoetherianRing R] [IsNoetherianRing T] [Module.Finite R T]
    [Algebra.HasGoingDown R T] (q : PrimeSpectrum T) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) := by
  -- Lemma 10.112.7 gives the fiber-dimension summand; finiteness kills that summand.
  calc
    ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
          ringKrullDim (fiberLocalRingAt R T q) :=
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
        q
    _ = ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) := by
      rw [ringKrullDim_fiberLocalRingAt_eq_zero_of_moduleFinite (R := R) (T := T) q]
      simp

/-- Helper for Chap10 Lemma 10 114 4: a polynomial ring over a field has the same dimension as
each of its maximal localizations. -/
private lemma ringKrullDim_mvPolynomial_eq_localizationAtMaximal
    {n : ℕ} (m : MaximalSpectrum (MvPolynomial (Fin n) k)) :
    ringKrullDim (MvPolynomial (Fin n) k) =
      ringKrullDim (Localization.AtPrime m.asIdeal) := by
  -- Both sides are the number of variables: globally by mathlib, locally by Lemma 10.114.1.
  calc
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
      simp
    _ = ringKrullDim (Localization.AtPrime m.asIdeal) :=
      (ringKrullDim_localizationAtMaximal_mvPolynomial (m := m)).symm

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 114 4: a finite injective polynomial normalization reduces the
target equality to the polynomial-ring equality. -/
private lemma ringKrullDim_eq_localizationAtMaximal_of_finite_injective_mvPolynomial
    {n : ℕ} (g : MvPolynomial (Fin n) k →ₐ[k] S)
    (hg_inj : Function.Injective g) (hg_fin : g.Finite) (m : MaximalSpectrum S) :
    ringKrullDim S = ringKrullDim (Localization.AtPrime m.asIdeal) := by
  let A := MvPolynomial (Fin n) k
  letI : Algebra A S := g.toAlgebra
  -- The normalization map makes `S` finite and integral over the polynomial subalgebra.
  have hFinite : Module.Finite A S := by
    simpa [A, AlgHom.Finite, RingHom.Finite] using hg_fin
  letI : Module.Finite A S := hFinite
  have hIntegral : Algebra.IsIntegral A S := inferInstance
  letI : Algebra.IsIntegral A S := hIntegral
  -- Injectivity is the faithful-scalar bridge needed both for dimension invariance and going down.
  have hFaithful : FaithfulSMul A S :=
    (faithfulSMul_iff_algebraMap_injective A S).mpr (by
      simpa [A, RingHom.algebraMap_toAlgebra] using hg_inj)
  letI : FaithfulSMul A S := hFaithful
  have hNoethS : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  letI : IsNoetherianRing S := hNoethS
  have hGoingDown : Algebra.HasGoingDown A S := inferInstance
  letI : Algebra.HasGoingDown A S := hGoingDown
  let p : Ideal A := m.asIdeal.under A
  have hpMax : p.IsMaximal := by
    dsimp [p]
    infer_instance
  let pMax : MaximalSpectrum A := ⟨p, hpMax⟩
  -- Compare global dimensions through integral invariance, then compare the two localizations.
  have hglobal : ringKrullDim S = ringKrullDim A := by
    exact
      (ringKrullDim_eq_of_injective_algebraMap_of_isIntegral (R := A) (S := S)
        (by simpa [A, RingHom.algebraMap_toAlgebra] using hg_inj)).symm
  have hpoly : ringKrullDim A = ringKrullDim (Localization.AtPrime p) := by
    simpa [A, pMax] using ringKrullDim_mvPolynomial_eq_localizationAtMaximal (k := k) pMax
  have hlocal :
      ringKrullDim (Localization.AtPrime m.asIdeal) =
        ringKrullDim (Localization.AtPrime p) := by
    simpa [A, p] using
      ringKrullDim_localizationAtPrime_eq_under_of_moduleFinite_hasGoingDown
        (R := A) (T := S) m.toPrimeSpectrum
  calc
    ringKrullDim S = ringKrullDim A := hglobal
    _ = ringKrullDim (Localization.AtPrime p) := hpoly
    _ = ringKrullDim (Localization.AtPrime m.asIdeal) := hlocal.symm

include k

/-- Chap10 Lemma 10 114 4: if `S` is a finite type `k`-algebra that is an integral domain, then every
maximal localization `Sₘ`, formalized as `Localization.AtPrime m.asIdeal`, has the same Krull
dimension as `S`. -/
@[stacks 00OS]
theorem ringKrullDim_eq_ringKrullDim_localizationAtMaximal_of_finiteType_domain_over_field
    (m : MaximalSpectrum S) :
    ringKrullDim S = ringKrullDim (Localization.AtPrime m.asIdeal) := by
  -- Noether normalization supplies the finite injective polynomial subalgebra used above.
  obtain ⟨n, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg k S
  exact ringKrullDim_eq_localizationAtMaximal_of_finite_injective_mvPolynomial g hg_inj hg_fin m

end
