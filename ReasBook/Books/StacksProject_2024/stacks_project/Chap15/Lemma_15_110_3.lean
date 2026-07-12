import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Noetherian.Basic
import StacksProject_2024.Chap05.Definition_5_10_5
import StacksProject_2024.Chap05.Definition_5_11_4
import StacksProject_2024.Chap05.Lemma_5_20_2
import StacksProject_2024.Chap10.Lemma_10_17_7
import StacksProject_2024.Chap10.Lemma_10_25_1
import StacksProject_2024.Chap10.Lemma_10_26_3
import StacksProject_2024.Chap10.Lemma_10_105_2
import StacksProject_2024.Chap10.Lemma_10_105_10
import StacksProject_2024.Chap10.Lemma_10_112_7
import StacksProject_2024.Chap10.Lemma_10_39_19
import StacksProject_2024.Chap10.Definition_10_162_9
import StacksProject_2024.Chap10.Lemma_10_164_1
import StacksProject_2024.Chap15.Lemma_15_10_5
import StacksProject_2024.Chap05.Lemma_5_20_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing B] [Module.Flat A B]
variable [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)]

/- Domain-style sampling for local dimension theory over `PrimeSpectrum`:
- topological owners from Chapter 5: `EquidimensionalSpace`
- topological catenary owner from Chapter 5 / Chapter 10: `CatenarySpace (PrimeSpectrum A)`,
  with ring-level alias `IsCatenaryRing A`
- fiber-ring owner used throughout Chapter 10: `Ideal.Fiber`
- spectrum/fiber bridge: `PrimeSpectrum.preimageHomeomorphFiber`
- faithfully-flat local-map owner: `Module.FaithfullyFlat.of_flat_of_isLocalHom`
- Noetherian descent owner: `isNoetherianRing_of_faithfullyFlat`

Layer triage:
- `source-facing`: the equidimensionality conclusions for the quotient spectra `Spec (B / pB)` and
  for `Spec A`
- `core/canonical`: `CatenarySpace (PrimeSpectrum A)`, `EquidimensionalSpace`, and `Ideal.Fiber`
- `bridge/view`: the comparison between the source quotient `B ⧸ p.asIdeal.map (algebraMap A B)`
  and the canonical fiber ring `p.asIdeal.Fiber B`, together with the ring-level alias
  `IsCatenaryRing A`

The source statement of part `(1)` is the quotient-spectrum claim `Spec (B / pB)`, so that
quotient must remain the main public theorem surface. The canonical fiber ring `p.asIdeal.Fiber B`
is still the right comparison owner for any auxiliary bridge, but it should not replace the
source-facing quotient statement. Likewise, the catenary conclusion of part `(2)` should live
first on the canonical owner `CatenarySpace (PrimeSpectrum A)`, with `IsCatenaryRing A` retained
only as the source-facing bridge spelling.
-/

omit [IsNoetherianRing B] [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: the flat local algebra map `A → B` is faithfully flat. -/
lemma algebraMap_faithfullyFlat : (algebraMap A B).FaithfullyFlat := by
  -- The local flatness hypotheses match the canonical faithful-flatness criterion.
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

include B in
omit [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: Noetherianity descends from `B` to `A` along the faithfully flat
local map `A → B`. -/
lemma source_isNoetherianRing : IsNoetherianRing A := by
  let _ : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  -- Apply the Chapter 10 faithfully-flat descent theorem to the structure map.
  exact isNoetherianRing_of_faithfullyFlat (algebraMap A B) <| by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: a prime of `B` minimal over `pB` contracts back to `p`. -/
lemma under_eq_of_mem_minimalPrimes_map
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : q.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes) :
    q.asIdeal.under A = p.asIdeal := by
  have hp_map_le_q : Ideal.map (algebraMap A B) p.asIdeal ≤ q.asIdeal := hq.1.2
  have hp_le_under : p.asIdeal ≤ q.asIdeal.under A :=
    Ideal.map_le_iff_le_comap.mp hp_map_le_q
  by_cases hunder : q.asIdeal.under A = p.asIdeal
  · exact hunder
  · letI : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
    letI : q.asIdeal.LiesOver (q.asIdeal.under A) := Ideal.over_under q.asIdeal
    have hp_lt_under : p.asIdeal < q.asIdeal.under A :=
      lt_of_le_of_ne hp_le_under (Ne.symm hunder)
    -- Going down lowers `q` to a prime over `p`, contradicting minimality over `pB`.
    obtain ⟨Q, hQ_lt, hQ_prime, hQ_liesOver⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt (R := A) (S := B) (Q := q.asIdeal) hp_lt_under
    have hp_map_le_Q : Ideal.map (algebraMap A B) p.asIdeal ≤ Q :=
      Ideal.map_le_iff_le_comap.mpr <| by
        simpa [Ideal.under_def] using hQ_liesOver.over.le
    have hq_le_Q : q.asIdeal ≤ Q :=
      hq.2 ⟨hQ_prime, hp_map_le_Q⟩ hQ_lt.le
    exact (hQ_lt.not_ge hq_le_Q).elim

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: if `q` is minimal over `pB`, then the canonical local fiber ring at
`q` is zero-dimensional. -/
lemma fiberLocalRingAt_krullDim_eq_zero_of_mem_minimalPrimes_map
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : q.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes) :
    ringKrullDim (fiberLocalRingAt A B q) = 0 := by
  -- Route correction: keep the minimality argument on the fiber over `p`, and only identify it
  -- with `fiberPrimeAt A B q` at the very end.
  let qOver : ↑(PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}) := ⟨q, by
    apply PrimeSpectrum.ext
    simpa [PrimeSpectrum.comap_asIdeal] using
      under_eq_of_mem_minimalPrimes_map (A := A) (B := B) p q hq⟩
  let e := PrimeSpectrum.preimageOrderIsoFiber A B p
  have hqOver_min : IsMin qOver := by
    intro r hr
    change q ≤ r.1
    have hr_comap : Ideal.comap (algebraMap A B) r.1.asIdeal = p.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal r.2
    have hp_map_le_r : Ideal.map (algebraMap A B) p.asIdeal ≤ r.1.asIdeal :=
      Ideal.map_le_iff_le_comap.mpr hr_comap.ge
    exact hq.2 ⟨r.1.2, hp_map_le_r⟩ hr
  -- Transport minimality to the owner fiber over `p`.
  have hfiber_min : IsMin (e qOver) := by
    intro s hs
    have hs' : e.symm s ≤ qOver := by
      simpa using e.symm.monotone hs
    simpa using e.monotone (hqOver_min hs')
  have hq_comap : PrimeSpectrum.comap (algebraMap A B) q = p := by
    apply PrimeSpectrum.ext
    simpa [PrimeSpectrum.comap_asIdeal] using
      under_eq_of_mem_minimalPrimes_map (A := A) (B := B) p q hq
  have hzero :
      ringKrullDim (Localization.AtPrime (e qOver).asIdeal) = 0 := by
    -- Minimal primes of the owner fiber give zero-dimensional localizations.
    letI : Ring.KrullDimLE 0 (Localization.AtPrime (e qOver).asIdeal) :=
      Ring.KrullDimLE.of_isLocalization
        (e qOver).asIdeal (PrimeSpectrum.isMin_iff.mp hfiber_min)
        (Localization.AtPrime (e qOver).asIdeal)
    exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  cases hq_comap
  simpa [fiberLocalRingAt, fiberPrimeAt, e, qOver] using hzero

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: for a prime `q` minimal over `pB`, the local dimension formula of
Lemma `10.112.7` loses its fiber term because the corresponding fiber local ring is
zero-dimensional. -/
lemma ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_of_mem_minimalPrimes_map
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : q.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime (q.asIdeal.under A)) := by
  letI : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  -- Rewrite the local dimension formula and then kill the fiber term at a minimal prime.
  calc
    ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime (q.asIdeal.under A)) +
          ringKrullDim (fiberLocalRingAt A B q) :=
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
        q
    _ = ringKrullDim (Localization.AtPrime (q.asIdeal.under A)) + 0 := by
      rw [fiberLocalRingAt_krullDim_eq_zero_of_mem_minimalPrimes_map (A := A) (B := B) p q hq]
    _ = ringKrullDim (Localization.AtPrime (q.asIdeal.under A)) := by
      simp

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: the unique closed point of `Spec R` for a local ring `R`. -/
abbrev localClosedPoint (R : Type u) [CommRing R] [IsLocalRing R] : PrimeSpectrum R :=
  ⟨IsLocalRing.maximalIdeal R, inferInstance⟩

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: quotienting by a prime sends that prime to the generic point of
the quotient spectrum. -/
lemma primeSpectrum_quotient_symm_self_eq_bot
    {R : Type u} [CommRing R] (q : PrimeSpectrum R) :
    q.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus.symm
      ⟨q, by
        change q.asIdeal ≤ q.asIdeal
        exact le_rfl⟩ =
      (⊥ : PrimeSpectrum (R ⧸ q.asIdeal)) := by
  let S := R ⧸ q.asIdeal
  let e : PrimeSpectrum S ≃o PrimeSpectrum.zeroLocus (q.asIdeal : Set R) :=
    q.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus
  have hq_zero : q ∈ PrimeSpectrum.zeroLocus (q.asIdeal : Set R) := by
    change q.asIdeal ≤ q.asIdeal
    exact le_rfl
  have hbot :
      PrimeSpectrum.comap (Ideal.Quotient.mk q.asIdeal) (⊥ : PrimeSpectrum S) = q := by
    -- Contracting the generic point of the quotient spectrum recovers the kernel prime `q`.
    apply PrimeSpectrum.ext
    change Ideal.comap (Ideal.Quotient.mk q.asIdeal) (⊥ : Ideal S) = q.asIdeal
    simpa [RingHom.ker_eq_comap_bot] using (Ideal.mk_ker (I := q.asIdeal))
  have he_bot : e (⊥ : PrimeSpectrum S) = ⟨q, hq_zero⟩ := by
    apply Subtype.ext
    change PrimeSpectrum.comap (Ideal.Quotient.mk q.asIdeal) (⊥ : PrimeSpectrum S) = q
    exact hbot
  calc
    e.symm ⟨q, hq_zero⟩ = e.symm (e (⊥ : PrimeSpectrum S)) := by
      rw [he_bot]
    _ = (⊥ : PrimeSpectrum S) := e.symm_apply_apply _

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: the zero locus of a prime ideal is the upper interval above the
corresponding point of the prime spectrum. -/
lemma primeSpectrum_zeroLocus_eq_Ici
    {R : Type u} [CommRing R] (q : PrimeSpectrum R) :
    PrimeSpectrum.zeroLocus (q.asIdeal : Set R) = Set.Ici q := by
  -- Unpack membership in the zero locus of a prime ideal as ideal containment.
  ext r
  change q.asIdeal ≤ r.asIdeal ↔ q ≤ r
  rfl

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: among irreducible closed subsets containing `q`, the closure of
`{q}` is the smallest one. -/
lemma toIrreducibleCloseds_le_of_mem
    {R : Type u} [CommRing R] (q : PrimeSpectrum R)
    (Z : IrreducibleCloseds (PrimeSpectrum R)) (hqZ : q ∈ (Z : Set (PrimeSpectrum R))) :
    toIrreducibleCloseds q ≤ Z := by
  -- The closure of `{q}` sits inside every closed subset containing `q`.
  change closure ({q} : Set (PrimeSpectrum R)) ⊆ (Z : Set (PrimeSpectrum R))
  exact closure_minimal (by simp [hqZ]) Z.isClosed'

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: localizing at `q` sends `q` to the closed point of the localized
spectrum. -/
lemma atPrime_symm_self_eq_localClosedPoint
    {R : Type u} [CommRing R] (q : PrimeSpectrum R) :
    let Rq := Localization.AtPrime q.asIdeal
    (IsLocalization.AtPrime.primeSpectrumOrderIso Rq q.asIdeal).symm
      ⟨q, by
        change q ≤ q
        exact le_rfl⟩ =
      localClosedPoint Rq := by
  let Rq := Localization.AtPrime q.asIdeal
  let e : PrimeSpectrum Rq ≃o Set.Iic q :=
    IsLocalization.AtPrime.primeSpectrumOrderIso Rq q.asIdeal
  have hq_iic : q ∈ Set.Iic q := by
    change q ≤ q
    exact le_rfl
  have hclosed :
      PrimeSpectrum.comap (algebraMap R Rq) (localClosedPoint Rq) = q := by
    -- The maximal ideal of the localized ring contracts back to the prime used to localize.
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R Rq) (IsLocalRing.maximalIdeal Rq) = q.asIdeal
    simpa [Rq, localClosedPoint] using
      (Localization.AtPrime.comap_maximalIdeal (R := R) (I := q.asIdeal))
  have he_closed : e (localClosedPoint Rq) = ⟨q, hq_iic⟩ := by
    apply Subtype.ext
    change PrimeSpectrum.comap (algebraMap R Rq) (localClosedPoint Rq) = q
    exact hclosed
  calc
    e.symm ⟨q, hq_iic⟩ = e.symm (e (localClosedPoint Rq)) := by
      rw [he_closed]
    _ = localClosedPoint Rq := e.symm_apply_apply _

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: if a minimal prime `η` specializes to `q`, then its localization in
`R_q` is again a minimal prime. -/
lemma localized_minimalPrime_mem_minimalPrimes_of_specializes
    {R : Type u} [CommRing R] (eta q : PrimeSpectrum R)
    (heta : eta.asIdeal ∈ minimalPrimes R)
    (hηq : eta ⤳ q) :
    Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) eta.asIdeal ∈
      minimalPrimes (Localization.AtPrime q.asIdeal) := by
  let Rq := Localization.AtPrime q.asIdeal
  have heta_le_q : eta.asIdeal ≤ q.asIdeal :=
    (PrimeSpectrum.le_iff_specializes eta q).2 hηq
  have hdisj : Disjoint (q.asIdeal.primeCompl : Set R) eta.asIdeal := by
    -- The specialization `η ≤ q` ensures that no element of `η` becomes invertible in `R_q`.
    refine Set.disjoint_left.mpr fun x hxS hxeta ↦ ?_
    exact hxS (heta_le_q hxeta)
  have hcomap :
      Ideal.comap (algebraMap R Rq)
        (Ideal.map (algebraMap R Rq) eta.asIdeal) = eta.asIdeal := by
    -- Localizing away from `q` preserves `η` because `η` is disjoint from `q`'s prime complement.
    simpa [Rq] using
      IsLocalization.comap_map_of_isPrime_disjoint
        q.asIdeal.primeCompl Rq eta.2 hdisj
  have hmap :
      Ideal.map (algebraMap R Rq) eta.asIdeal ∈
        (Ideal.map (algebraMap R Rq) (⊥ : Ideal R)).minimalPrimes := by
    -- Rewrite minimal primes after localization back to the source ring via the comap-map identity.
    rw [IsLocalization.minimalPrimes_map q.asIdeal.primeCompl Rq (⊥ : Ideal R)]
    change Ideal.comap (algebraMap R Rq)
        (Ideal.map (algebraMap R Rq) eta.asIdeal) ∈ minimalPrimes R
    simpa [hcomap]
  simpa [Rq] using hmap

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: quotienting a localization by an ideal rewrites its Krull dimension
as the Krull dimension of the corresponding zero locus in the localized prime spectrum. -/
lemma ringKrullDim_quotient_localizationAtPrime_eq_krullDim_zeroLocus
    {R : Type u} [CommRing R] (q : PrimeSpectrum R)
    (I : Ideal (Localization.AtPrime q.asIdeal)) :
    ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸ I) =
      Order.krullDim (PrimeSpectrum.zeroLocus (I : Set (Localization.AtPrime q.asIdeal))) := by
  -- This is the canonical quotient-to-zero-locus bridge, specialized to the localized ring.
  simpa using (ringKrullDim_quotient (R := Localization.AtPrime q.asIdeal) I)

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: the zero locus of an ideal has the same topological Krull
dimension as the quotient by that ideal. -/
lemma topologicalKrullDim_zeroLocus_eq_ringKrullDim_quotient
    {R : Type u} [CommRing R] (I : Ideal R) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set R)) = ringKrullDim (R ⧸ I) := by
  -- Move from the closed subset `V(I)` to the quotient spectrum via the canonical homeomorphism.
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := R ⧸ I)]
  simpa using
    IsHomeomorph.topologicalKrullDim_eq
      (s := PrimeSpectrum.zeroLocus (I : Set R))
      (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).isHomeomorph

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: every point of the spectrum of a local ring specializes to the
closed point. -/
lemma prime_le_localClosedPoint
    {R : Type u} [CommRing R] [IsLocalRing R] (q : PrimeSpectrum R) :
    q.asIdeal ≤ (localClosedPoint R).asIdeal := by
  -- Route correction: the upper-interval part of the local additivity proof should be organized
  -- around the canonical closed point of the local spectrum, not around an arbitrary component.
  -- Every proper ideal of a local ring lies in the maximal ideal, so every prime specializes there.
  exact IsLocalRing.le_maximalIdeal q.2.ne_top

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: every prime of a local ring specializes to the closed point. -/
lemma prime_specializes_localClosedPoint
    {R : Type u} [CommRing R] [IsLocalRing R] (q : PrimeSpectrum R) :
    q ⤳ localClosedPoint R := by
  -- Convert the order-theoretic closed-point comparison into the specialization relation.
  exact (PrimeSpectrum.le_iff_specializes q (localClosedPoint R)).1
    (prime_le_localClosedPoint (R := R) q)

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: every irreducible closed subset of the spectrum of a local ring
contains the closed point. -/
lemma localClosedPoint_mem_irreducibleCloseds
    {R : Type u} [CommRing R] [IsLocalRing R]
    (Z : IrreducibleCloseds (PrimeSpectrum R)) :
    localClosedPoint R ∈ (Z : Set (PrimeSpectrum R)) := by
  rcases Z.isIrreducible.nonempty with ⟨q, hqZ⟩
  have hq_closed : localClosedPoint R ∈ (toIrreducibleCloseds q : Set (PrimeSpectrum R)) := by
    -- The closed point lies in the closure of every point of the local spectrum.
    rw [PrimeSpectrum.closure_singleton, primeSpectrum_zeroLocus_eq_Ici]
    exact prime_le_localClosedPoint (R := R) q
  -- Once `q` lies in `Z`, the whole closure of `{q}` lies in `Z`.
  exact (toIrreducibleCloseds_le_of_mem q Z hqZ) hq_closed

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: the quotient by the closed point of a local spectrum has Krull
dimension `0`. -/
lemma ringKrullDim_quotient_localClosedPoint_eq_zero
    {R : Type u} [CommRing R] [IsLocalRing R] :
    ringKrullDim (R ⧸ (localClosedPoint R).asIdeal) = 0 := by
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  -- The quotient by the maximal ideal is the residue field, so its Krull dimension vanishes.
  simpa [localClosedPoint] using
    (ringKrullDim_eq_zero_of_isField (Field.toIsField (R ⧸ IsLocalRing.maximalIdeal R)))

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: in a Noetherian local catenary ring, prime quotients form the
canonical dimension function on the prime spectrum. -/
lemma primeQuotientKrullDimension_isDimensionFunction_local
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsCatenaryRing R] :
    IsDimensionFunction
      (fun q : PrimeSpectrum R ↦ (((ringKrullDim (R ⧸ q.asIdeal)).unbotD 0).toNat : ℤ)) := by
  -- This is exactly the local Noetherian catenarity criterion from Chapter 10.
  exact
    (isCatenaryRing_iff_primeQuotientKrullDimension_isDimensionFunction (A := R)).mp
      inferInstance

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: in a Noetherian local catenary ring, the upper interval from the
closed point to a prime has `toNat`-length equal to the Krull dimension of the corresponding prime
quotient. -/
lemma codimBetween_closedPoint_and_prime_toNat_eq_ringKrullDim_quotient_local
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsCatenaryRing R]
    (q : PrimeSpectrum R) :
    (ENat.toNat
      (codimBetween (toIrreducibleCloseds (localClosedPoint R)) (toIrreducibleCloseds q)
        (prime_specializes_localClosedPoint (R := R) q).toIrreducibleCloseds_le) : ℤ) =
      (((ringKrullDim (R ⧸ q.asIdeal)).unbotD 0).toNat : ℤ) := by
  -- Route correction: compute the upper interval via the local dimension function
  -- `r ↦ dim (R / r)` instead of transporting through `pointsEquivIrreducibleCloseds`.
  let δ : PrimeSpectrum R → ℤ :=
    fun r ↦ (((ringKrullDim (R ⧸ r.asIdeal)).unbotD 0).toNat : ℤ)
  have hδ : IsDimensionFunction δ :=
    primeQuotientKrullDimension_isDimensionFunction_local (R := R)
  have hqm : q ⤳ localClosedPoint R :=
    prime_specializes_localClosedPoint (R := R) q
  have hsub :
      δ q - δ (localClosedPoint R) =
        (ENat.toNat
          (codimBetween (toIrreducibleCloseds (localClosedPoint R)) (toIrreducibleCloseds q)
            hqm.toIrreducibleCloseds_le) : ℤ) :=
    hδ.sub_eq_codimBetween_pointClosure q (localClosedPoint R) hqm
  have hclosed : δ (localClosedPoint R) = 0 := by
    -- The local closed-point quotient is the residue field.
    simp [δ, ringKrullDim_quotient_localClosedPoint_eq_zero (R := R)]
  calc
    (ENat.toNat
      (codimBetween (toIrreducibleCloseds (localClosedPoint R)) (toIrreducibleCloseds q)
        hqm.toIrreducibleCloseds_le) : ℤ) =
        δ q - δ (localClosedPoint R) := by
          simpa using hsub.symm
    _ = δ q := by
      rw [hclosed, sub_zero]
    _ = (((ringKrullDim (R ⧸ q.asIdeal)).unbotD 0).toNat : ℤ) := rfl

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: in a Noetherian local catenary ring, the upper interval from the
closed point to a prime has codimension equal to the Krull dimension of the corresponding prime
quotient. -/
lemma codimBetween_closedPoint_and_prime_eq_ringKrullDim_quotient_local
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsCatenaryRing R]
    (q : PrimeSpectrum R) :
    ((codimBetween (toIrreducibleCloseds (localClosedPoint R)) (toIrreducibleCloseds q)
        (prime_specializes_localClosedPoint (R := R) q).toIrreducibleCloseds_le : ℕ∞) :
      WithBot ℕ∞) =
      ringKrullDim (R ⧸ q.asIdeal) := by
  let S := R ⧸ q.asIdeal
  let _ : IsLocalRing S := inferInstance
  let _ : FiniteRingKrullDim S := inferInstance
  let c : ℕ∞ :=
    codimBetween (toIrreducibleCloseds (localClosedPoint R)) (toIrreducibleCloseds q)
      (prime_specializes_localClosedPoint (R := R) q).toIrreducibleCloseds_le
  have hc_fin : c < ⊤ :=
    CatenarySpace.finite_codimBetween
      ((prime_specializes_localClosedPoint (R := R) q).toIrreducibleCloseds_le)
  have hnat :
      ENat.toNat c = (((ringKrullDim S).unbotD 0).toNat : ℕ) := by
    -- The earlier `toNat` formula is the stabilized upper-half computation.
    exact_mod_cast
      (codimBetween_closedPoint_and_prime_toNat_eq_ringKrullDim_quotient_local (R := R) q)
  have hc :
      (c : WithBot ℕ∞) = (((ENat.toNat c : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    -- The catenary hypothesis makes the codimension finite, so `ENat.toNat` can be inverted.
    exact congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hc_fin.ne).symm
  have hdim :
      ringKrullDim S =
        (((((ringKrullDim S).unbotD 0).toNat : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    have hbot : ringKrullDim S ≠ ⊥ := ringKrullDim_ne_bot
    have htop : ringKrullDim S ≠ ⊤ := ringKrullDim_ne_top
    -- Finite Krull dimension of the local quotient identifies the `WithBot` value with its
    -- `toNat` normalization.
    cases hs : ringKrullDim S with
    | bot =>
        exact (hbot hs).elim
    | coe d =>
        have hd_ne_top : d ≠ ⊤ := by
          intro hd_top
          exact htop <| by simpa [hs, hd_top]
        -- In the non-bottom branch, `unbotD` is definitionally the represented `ℕ∞` value.
        simpa using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hd_ne_top).symm
  -- Combine the finite codimension rewrite with the finite quotient-dimension normalization.
  calc
    (c : WithBot ℕ∞) = (((ENat.toNat c : ℕ) : ℕ∞) : WithBot ℕ∞) := hc
    _ = (((((ringKrullDim S).unbotD 0).toNat : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [hnat]
    _ = ringKrullDim S := hdim.symm

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsCatenaryRing B]
  [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: the Krull dimension of a prime quotient is the coheight of the
corresponding point of the prime spectrum. -/
lemma ringKrullDim_quotient_eq_coheight
    [IsNoetherianRing A] (p : PrimeSpectrum A) :
    ringKrullDim (A ⧸ p.asIdeal) = Order.coheight p := by
  -- Normalize the quotient term to the upper interval above `p`.
  rw [ringKrullDim_quotient]
  have hzero : PrimeSpectrum.zeroLocus (p.asIdeal : Set A) = Set.Ici p := by
    ext q
    change p.asIdeal ≤ q.asIdeal ↔ p ≤ q
    rfl
  -- The upper interval is the canonical owner for coheight.
  rw [hzero]
  exact (Order.coheight_eq_krullDim_Ici p).symm

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: on the spectrum of a local ring, a locally constant integer-valued
function is determined by its value at the closed point. -/
lemma isLocallyConstant_eq_value_at_localClosedPoint
    {R : Type u} [CommRing R] [IsLocalRing R] (f : PrimeSpectrum R → ℤ)
    (hf : IsLocallyConstant f) (p : PrimeSpectrum R) :
    f p = f (localClosedPoint R) := by
  -- Map the specialization `p ⤳ closed point` through the locally constant function.
  have hspec :
      f p ⤳ f (localClosedPoint R) :=
    (prime_specializes_localClosedPoint (R := R) p).map hf.continuous
  -- Integer-valued specializations are equal because `ℤ` has the discrete topology.
  exact Specializes.eq hspec

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] in
/-- Helper for Lemma 15.110.3: in an equidimensional spectrum, any two irreducible components of
`Spec R` arising from minimal primes of the same localization at `q` have the same dimension. -/
lemma topologicalKrullDim_localization_components_eq_of_equidimensional
    {R : Type u} [CommRing R] [EquidimensionalSpace (PrimeSpectrum R)]
    (q : PrimeSpectrum R) (m₁ m₂ : minimalPrimes (Localization.AtPrime q.asIdeal)) :
    topologicalKrullDim
        ((((OrderDual.ofDual (PrimeSpectrum.localizationAtPrimeIrreducibleComponents q m₁)).1 :
          irreducibleComponents (PrimeSpectrum R)) :
          Set (PrimeSpectrum R))) =
      topologicalKrullDim
        ((((OrderDual.ofDual (PrimeSpectrum.localizationAtPrimeIrreducibleComponents q m₂)).1 :
          irreducibleComponents (PrimeSpectrum R)) :
          Set (PrimeSpectrum R))) := by
  -- Compare the two components directly inside `Spec R` using the ambient equidimensionality.
  exact TopologicalSpace.topologicalKrullDim_eq_of_mem_irreducibleComponents
    (OrderDual.ofDual (PrimeSpectrum.localizationAtPrimeIrreducibleComponents q m₁)).1.2
    (OrderDual.ofDual (PrimeSpectrum.localizationAtPrimeIrreducibleComponents q m₂)).1.2

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: an order isomorphism on irreducible closed subsets preserves
relative codimension. -/
lemma codimBetween_eq_of_irreducibleCloseds_orderIso_local
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : IrreducibleCloseds X ≃o IrreducibleCloseds Y)
    {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween (e T) (e T') (e.monotone hTT') = codimBetween T T' hTT' := by
  -- Compare the interval owner `[T, T']` with its image under the order isomorphism.
  let eIcc : ↥(Set.Icc T T') ≃o ↥(Set.Icc (e T) (e T')) :=
    { toFun := fun z ↦ ⟨e z.1, by
        rcases z.2 with ⟨hz₁, hz₂⟩
        exact ⟨e.monotone hz₁, e.monotone hz₂⟩⟩
      invFun := fun z ↦ ⟨e.symm z.1, by
        rcases z.2 with ⟨hz₁, hz₂⟩
        exact ⟨by simpa using e.symm.monotone hz₁, by simpa using e.symm.monotone hz₂⟩⟩
      left_inv := by
        intro z
        ext x
        simp
      right_inv := by
        intro z
        ext x
        simp
      map_rel_iff' := by
        intro a b
        change e a.1 ≤ e b.1 ↔ a.1 ≤ b.1
        exact e.map_rel_iff }
  -- The interval bottom is the left endpoint, so `coheight` is unchanged by `eIcc`.
  let _ : Fact (T ≤ T') := ⟨hTT'⟩
  let _ : Fact (e T ≤ e T') := ⟨e.monotone hTT'⟩
  simpa [codimBetween, eIcc] using
    (Order.coheight_orderIso eIcc (⊥ : Set.Icc T T'))

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: the canonical localization bridge upgrades to an order isomorphism
on irreducible closed subsets. -/
noncomputable abbrev localizationAtPrimeIrreducibleClosedsOrderIso
    {R : Type u} [CommRing R] (q : PrimeSpectrum R) :
    IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime q.asIdeal)) ≃o
      { Z : IrreducibleCloseds (PrimeSpectrum R) //
        q ∈ (Z : Set (PrimeSpectrum R)) } :=
  ((PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization.AtPrime q.asIdeal)).symm.trans
    (PrimeSpectrum.localizationAtPrimeIrreducibleCloseds q)).dual

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: localizing a prime `η ≤ q` and transporting it back through
`PrimeSpectrum.localizationAtPrimeIrreducibleCloseds` recovers the closed subset `V(η)`. -/
lemma localizationAtPrimeIrreducibleCloseds_apply_eq_zeroLocus_of_specializes
    {R : Type u} [CommRing R] (eta q : PrimeSpectrum R)
    (hηq : eta ⤳ q) :
    let Rq := Localization.AtPrime q.asIdeal
    let etaq : PrimeSpectrum Rq :=
      (IsLocalization.AtPrime.primeSpectrumOrderIso Rq q.asIdeal).symm
        ⟨eta, (PrimeSpectrum.le_iff_specializes eta q).2 hηq⟩
    (((show IrreducibleCloseds (PrimeSpectrum R) from
        (PrimeSpectrum.localizationAtPrimeIrreducibleCloseds q etaq).1) :
        Set (PrimeSpectrum R))) =
      PrimeSpectrum.zeroLocus (eta.asIdeal : Set R) := by
  let Rq := Localization.AtPrime q.asIdeal
  let etaq : PrimeSpectrum Rq :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso Rq q.asIdeal).symm
      ⟨eta, (PrimeSpectrum.le_iff_specializes eta q).2 hηq⟩
  -- Unfold the localization bridge and identify the resulting irreducible closed set with the
  -- closure of `{eta}`.
  change closure ({eta} : Set (PrimeSpectrum R)) = PrimeSpectrum.zeroLocus (eta.asIdeal : Set R)
  simpa using PrimeSpectrum.closure_singleton eta

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: the localized closed point corresponds to the ambient closure
`closure {q}` under the localization irreducible-closed bridge. -/
lemma localizationAtPrimeIrreducibleCloseds_closedPoint_eq_toIrreducibleCloseds
    {R : Type u} [CommRing R] (q : PrimeSpectrum R) :
    let Rq := Localization.AtPrime q.asIdeal
    (localizationAtPrimeIrreducibleClosedsOrderIso q
      (toIrreducibleCloseds (localClosedPoint Rq))).1 = toIrreducibleCloseds q := by
  let Rq := Localization.AtPrime q.asIdeal
  apply IrreducibleCloseds.ext
  -- Specializing `η = q` in the zero-locus transport identifies the localized closed point with
  -- `closure {q}` in the ambient spectrum.
  simpa [Rq, localizationAtPrimeIrreducibleClosedsOrderIso,
    atPrime_symm_self_eq_localClosedPoint (R := R) q, PrimeSpectrum.closure_singleton] using
    localizationAtPrimeIrreducibleCloseds_apply_eq_zeroLocus_of_specializes
      (R := R) q q (Specializes.refl q)

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: the localization correspondence identifies the interval from the
localized closed point to `Z` with the ambient interval from `closure {q}` to the transported
irreducible closed subset. -/
noncomputable lemma localization_irreducibleCloseds_intervalOrderIso
    {R : Type u} [CommRing R] (q : PrimeSpectrum R)
    (Z : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime q.asIdeal))) :
    let Rq := Localization.AtPrime q.asIdeal
    let Zambient : IrreducibleCloseds (PrimeSpectrum R) :=
      (localizationAtPrimeIrreducibleClosedsOrderIso q Z).1
    Set.Icc (toIrreducibleCloseds (localClosedPoint Rq)) Z ≃o
      Set.Icc (toIrreducibleCloseds q) Zambient := by
  let Rq := Localization.AtPrime q.asIdeal
  let e := localizationAtPrimeIrreducibleClosedsOrderIso q
  let Zambient : IrreducibleCloseds (PrimeSpectrum R) := (e Z).1
  have hq_mem :
      q ∈ (toIrreducibleCloseds q : Set (PrimeSpectrum R)) := by
    -- The ambient closure `closure {q}` always contains its generic point `q`.
    rw [PrimeSpectrum.closure_singleton, primeSpectrum_zeroLocus_eq_Ici]
    exact le_rfl
  -- Package the localization correspondence as the interval order isomorphism actually used by
  -- `codimBetween`.
  refine
    { toEquiv :=
        { toFun := fun W ↦ ⟨(e W.1).1, ?_, ?_⟩
          invFun := fun W ↦
            let hWq : q ∈ ((W.1 : IrreducibleCloseds (PrimeSpectrum R)) : Set (PrimeSpectrum R)) :=
              W.2.1 hq_mem
            ⟨e.symm ⟨W.1, hWq⟩, ?_, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      map_rel_iff' := ?_ }
  · -- The lower endpoint `closure {q}` is the image of the localized closed point.
    calc
      toIrreducibleCloseds q = (e (toIrreducibleCloseds (localClosedPoint Rq))).1 := by
        simpa [Rq, e] using
          localizationAtPrimeIrreducibleCloseds_closedPoint_eq_toIrreducibleCloseds
            (R := R) q
      _ ≤ (e W.1).1 := by
        exact (e.monotone W.2.1)
  · -- The upper endpoint is preserved because `e` is monotone.
    simpa [Zambient] using (e.monotone W.2.2)
  · -- Recover the lower localized bound by pushing the ambient lower bound back through `e.symm`.
    have hlower :
        e (toIrreducibleCloseds (localClosedPoint Rq)) ≤
          ⟨W.1, let hWq : q ∈ ((W.1 : IrreducibleCloseds (PrimeSpectrum R)) :
              Set (PrimeSpectrum R)) := W.2.1 hq_mem; hWq⟩ := by
      change (e (toIrreducibleCloseds (localClosedPoint Rq))).1 ≤ W.1
      simpa [Rq, e] using W.2.1
    simpa using e.symm.monotone hlower
  · -- The ambient upper bound transports back to the localized interval.
    have hupper :
        ⟨W.1, let hWq : q ∈ ((W.1 : IrreducibleCloseds (PrimeSpectrum R)) :
            Set (PrimeSpectrum R)) := W.2.1 hq_mem; hWq⟩ ≤
          e Z := by
      change W.1 ≤ (e Z).1
      simpa [Zambient] using W.2.2
    simpa using e.symm.monotone hupper
  · intro W
    -- After applying `e` and `e.symm`, only the interval witness remains to check.
    apply Subtype.ext
    simp [e]
  · intro W
    -- The same normalization closes the ambient interval round-trip.
    apply Subtype.ext
    simp [e]
  · intro W₁ W₂
    -- The interval order is inherited from the ambient order on irreducible closed subsets.
    change (e W₁.1).1 ≤ (e W₂.1).1 ↔ W₁.1 ≤ W₂.1
    exact e.map_rel_iff

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: the localization order isomorphism identifies the interval from the
localized closed point to `Z` with the ambient interval from `closure {q}` to the transported
irreducible closed subset of `Spec R`. -/
lemma localization_codimBetween_interval_eq_codimBetween_localized
    {R : Type u} [CommRing R] (q : PrimeSpectrum R)
    (Z : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime q.asIdeal))) :
    let Rq := Localization.AtPrime q.asIdeal
    let Zambient : IrreducibleCloseds (PrimeSpectrum R) :=
      (localizationAtPrimeIrreducibleClosedsOrderIso q Z).1
    let hlocal : toIrreducibleCloseds (localClosedPoint Rq) ≤ Z :=
      toIrreducibleCloseds_le_of_mem (localClosedPoint Rq) Z
        (localClosedPoint_mem_irreducibleCloseds (R := Rq) Z)
    let hambient : toIrreducibleCloseds q ≤ Zambient :=
      toIrreducibleCloseds_le_of_mem q Zambient
        (localizationAtPrimeIrreducibleClosedsOrderIso q Z).2
    codimBetween (toIrreducibleCloseds q) Zambient hambient =
      codimBetween (toIrreducibleCloseds (localClosedPoint Rq)) Z hlocal := by
  let Rq := Localization.AtPrime q.asIdeal
  let Zambient : IrreducibleCloseds (PrimeSpectrum R) :=
    (localizationAtPrimeIrreducibleClosedsOrderIso q Z).1
  let hlocal : toIrreducibleCloseds (localClosedPoint Rq) ≤ Z :=
    toIrreducibleCloseds_le_of_mem (localClosedPoint Rq) Z
      (localClosedPoint_mem_irreducibleCloseds (R := Rq) Z)
  let hambient : toIrreducibleCloseds q ≤ Zambient :=
    toIrreducibleCloseds_le_of_mem q Zambient
      (localizationAtPrimeIrreducibleClosedsOrderIso q Z).2
  let eIcc :=
    localization_irreducibleCloseds_intervalOrderIso (R := R) q Z
  let _ : Fact (toIrreducibleCloseds (localClosedPoint Rq) ≤ Z) := ⟨hlocal⟩
  let _ : Fact (toIrreducibleCloseds q ≤ Zambient) := ⟨hambient⟩
  -- Transport the interval coheight through the explicit owner-level order isomorphism.
  simpa [codimBetween, Rq, Zambient, hlocal, hambient, eIcc] using
    (Order.coheight_orderIso eIcc
      (⊥ : Set.Icc (toIrreducibleCloseds (localClosedPoint Rq)) Z))

/-
The next lift only needs the minimal-prime order API; the local and catenary hypotheses are not
part of this step.
-/
omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [Module.Flat A B] [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: a specialization `p ⤳ p'` in `Spec A` lifts to a specialization
between primes of `B` minimal over the corresponding extended ideals. -/
lemma exists_prime_over_specialization_mem_minimalPrimes_map
    (p p' : PrimeSpectrum A) (hp : p ⤳ p') (q' : PrimeSpectrum B)
    (hq' : q'.asIdeal ∈ (Ideal.map (algebraMap A B) p'.asIdeal).minimalPrimes) :
    ∃ q : PrimeSpectrum B,
      q.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes ∧ q ⤳ q' := by
  have hpp' : p.asIdeal ≤ p'.asIdeal :=
    (PrimeSpectrum.le_iff_specializes p p').2 hp
  have hp_map_le_q' : Ideal.map (algebraMap A B) p.asIdeal ≤ q'.asIdeal :=
    le_trans (Ideal.map_mono hpp') hq'.1.2
  -- Choose a minimal prime over `pB` below the fixed prime `q'`.
  obtain ⟨q, hq, hqq'⟩ := Ideal.exists_minimalPrimes_le hp_map_le_q'
  refine ⟨⟨q, Ideal.minimalPrimes_isPrime hq⟩, hq, ?_⟩
  -- Convert the order comparison back into the specialization relation.
  exact (PrimeSpectrum.le_iff_specializes _ _).1 hqq'

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: a prime of `B` minimal over `pB` contracts to `p` already on prime
spectra, not just on ideals. -/
lemma primeSpectrum_comap_eq_of_mem_minimalPrimes_map
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : q.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes) :
    PrimeSpectrum.comap (algebraMap A B) q = p := by
  -- This is the spectrum-level packaging of the ideal contraction lemma proved above.
  apply PrimeSpectrum.ext
  simpa [PrimeSpectrum.comap_asIdeal] using
    under_eq_of_mem_minimalPrimes_map (A := A) (B := B) p q hq

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: if `p` is minimal in `A`, then every prime minimal over `pB` is
minimal in `B`. -/
lemma mem_minimalPrimes_of_mem_minimalPrimes_map_of_mem_minimalPrimes
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hp : p.asIdeal ∈ minimalPrimes A)
    (hq : q.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes) :
    q.asIdeal ∈ minimalPrimes B := by
  refine ⟨⟨q.2, bot_le⟩, ?_⟩
  intro J hJ hJ_le_q
  have hq_under : q.asIdeal.under A = p.asIdeal :=
    under_eq_of_mem_minimalPrimes_map (A := A) (B := B) p q hq
  have hJ_under_le_p : J.under A ≤ p.asIdeal := by
    -- Contract the intermediate prime below `q` back to `A`.
    exact (Ideal.comap_mono (f := algebraMap A B) hJ_le_q).trans hq_under.le
  have hp_le_hJ_under : p.asIdeal ≤ J.under A := by
    -- Minimality of `p` over `0` forces any contracted prime below `q` back up to `p`.
    exact hp.2 ⟨@Ideal.IsPrime.under A _ B _ _ J hJ.1, bot_le⟩ hJ_under_le_p
  have hp_map_le_J : Ideal.map (algebraMap A B) p.asIdeal ≤ J := by
    -- Once the contraction is exactly `p`, the extended ideal `pB` lies in the intermediate
    -- prime.
    exact Ideal.map_le_iff_le_comap.mpr hp_le_hJ_under
  -- Minimality of `q` over `pB` now forces `q ≤ J`, closing the `0`-minimality claim.
  exact hq.2 ⟨hJ.1, hp_map_le_J⟩ hJ_le_q

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [Module.Flat A B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: if a prime `z` specializes to a prime `q` minimal over `pB` and
still contracts to `p`, then `z` must already equal `q`. -/
lemma eq_of_specializes_to_minimalPrime_and_comap_eq
    (p : PrimeSpectrum A) (q z : PrimeSpectrum B)
    (hq : q.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes)
    (hzq : z ⤳ q)
    (hz : PrimeSpectrum.comap (algebraMap A B) z = p) :
    z = q := by
  have hz_le_q : z.asIdeal ≤ q.asIdeal :=
    (PrimeSpectrum.le_iff_specializes z q).2 hzq
  have hp_map_le_z : Ideal.map (algebraMap A B) p.asIdeal ≤ z.asIdeal := by
    -- The contraction identity `comap z = p` turns the extended ideal `pB` into a lower bound for
    -- `z`.
    apply Ideal.map_le_iff_le_comap.mpr
    simpa [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hz).ge
  have hq_le_z : q.asIdeal ≤ z.asIdeal :=
    hq.2 ⟨z.2, hp_map_le_z⟩ hz_le_q
  -- Minimality of `q` over `pB` collapses the remaining interval.
  apply PrimeSpectrum.ext
  exact le_antisymm hz_le_q hq_le_z

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: any intermediate prime between lifts of an immediate specialization
either still contracts to the source prime or has already reached the target minimal prime. -/
lemma intermediate_prime_contracts_or_hits_target_of_immediate_specialization
    (p p' : PrimeSpectrum A) (hp : IsImmediateSpecialization p p')
    (q q' z : PrimeSpectrum B)
    (hq : q.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes)
    (hq' : q'.asIdeal ∈ (Ideal.map (algebraMap A B) p'.asIdeal).minimalPrimes)
    (hqz : q ⤳ z) (hzq' : z ⤳ q') :
    PrimeSpectrum.comap (algebraMap A B) z = p ∨ z = q' := by
  let zA : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) z
  have hq_comap : PrimeSpectrum.comap (algebraMap A B) q = p :=
    primeSpectrum_comap_eq_of_mem_minimalPrimes_map (A := A) (B := B) p q hq
  have hq'_comap : PrimeSpectrum.comap (algebraMap A B) q' = p' :=
    primeSpectrum_comap_eq_of_mem_minimalPrimes_map (A := A) (B := B) p' q' hq'
  have hpzA : p ⤳ zA := by
    -- Contract the left specialization `q ⤳ z` back to `Spec A`.
    have hqz_comap :
        (PrimeSpectrum.comap (algebraMap A B) q).asIdeal ≤ zA.asIdeal := by
      simpa [zA, PrimeSpectrum.comap_asIdeal] using
        (Ideal.comap_mono ((PrimeSpectrum.le_iff_specializes q z).2 hqz))
    exact (PrimeSpectrum.le_iff_specializes p zA).1 <| by
      simpa [hq_comap] using hqz_comap
  have hzAp' : zA ⤳ p' := by
    -- Contract the right specialization `z ⤳ q'` back to `Spec A`.
    have hzq'_comap :
        zA.asIdeal ≤ (PrimeSpectrum.comap (algebraMap A B) q').asIdeal := by
      simpa [zA, PrimeSpectrum.comap_asIdeal] using
        (Ideal.comap_mono ((PrimeSpectrum.le_iff_specializes z q').2 hzq'))
    exact (PrimeSpectrum.le_iff_specializes zA p').1 <| by
      simpa [hq'_comap] using hzq'_comap
  rcases hp.eq_or_eq hpzA hzAp' with hzA_eq_p | hzA_eq_p'
  · exact Or.inl hzA_eq_p
  · -- Once the intermediate prime contracts to `p'`, minimality of `q'` over `p'B` forces
    -- equality with the target lift.
    exact Or.inr <|
      eq_of_specializes_to_minimalPrime_and_comap_eq
        (A := A) (B := B) p' q' z hq' hzq' hzA_eq_p'

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: in a Noetherian local catenary equidimensional ring, the local
dimension at `q` and the dimension of the prime quotient `B / q` add up to the ambient dimension
of `B`. -/
lemma ringKrullDim_localizationAtPrime_add_ringKrullDim_quotient_eq_ringKrullDim_local
    (q : PrimeSpectrum B) :
    ringKrullDim (Localization.AtPrime q.asIdeal) + ringKrullDim (B ⧸ q.asIdeal) =
      ringKrullDim B := by
  -- Route correction: the old lifted-fiber collapse branch was solving the wrong problem. The
  -- source proof only needs the ambient catenary chain `closed point ≤ q ≤ component`.
  -- TODO: choose a minimal prime of `B_q`, identify the corresponding irreducible component of
  -- `Spec B` through `q`, compute `codim(q, component)` by the localized quotient formula, compute
  -- `codim(closed point, q)` by `codimBetween_closedPoint_and_prime_eq_ringKrullDim_quotient_local`,
  -- and combine them with `CatenarySpace.codimBetween_additive`.
  sorry

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: the irreducible component attached to a minimal prime has the same
topological Krull dimension as the corresponding prime quotient. -/
lemma topologicalKrullDim_irreducibleComponent_eq_ringKrullDim_quotient_of_equiv_minimalPrime
    {R : Type u} [CommRing R] (Z : irreducibleComponents (PrimeSpectrum R))
    (m : minimalPrimes R)
    (hm : OrderDual.ofDual ((minimalPrimes.equivIrreducibleComponents R) m) = Z) :
    topologicalKrullDim (Z : Set (PrimeSpectrum R)) = ringKrullDim (R ⧸ m.1) := by
  -- Rewrite the chosen component through the canonical minimal-prime/component equivalence.
  subst hm
  -- The canonical component of `m` is the zero locus `V(m)`, so the quotient-spectrum
  -- homeomorphism computes its topological Krull dimension.
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := R ⧸ m.1)]
  simpa using
    IsHomeomorph.topologicalKrullDim_eq
      (s := PrimeSpectrum.zeroLocus (m.1 : Set R))
      (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus m.1).isHomeomorph

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: primes of `B` minimal over the same extended prime `pB` define
quotients of equal Krull dimension. -/
lemma ringKrullDim_quotient_eq_of_mem_minimalPrimes_map_direct
    (p : PrimeSpectrum A) (q₁ q₂ : PrimeSpectrum B)
    (hq₁ : q₁.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes)
    (hq₂ : q₂.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes) :
    ringKrullDim (B ⧸ q₁.asIdeal) = ringKrullDim (B ⧸ q₂.asIdeal) := by
  -- Route correction: compare the two quotient dimensions through the ambient local identity on
  -- `B`, not through the old descended function.
  -- TODO: rewrite both local terms to `ringKrullDim (Localization.AtPrime p.asIdeal)` using
  -- `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_of_mem_minimalPrimes_map`,
  -- then cancel the common source-local term in the two instances of
  -- `ringKrullDim_localizationAtPrime_add_ringKrullDim_quotient_eq_ringKrullDim_local`.
  sorry

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: quotienting `B / I` further by the image of a prime `q ⊃ I`
preserves the quotient Krull dimension of `B / q`. -/
lemma ringKrullDim_quotient_quotient_map_eq
    (I : Ideal B) (q : PrimeSpectrum B) (hIq : I ≤ q.asIdeal) :
    ringKrullDim ((B ⧸ I) ⧸ q.asIdeal.map (Ideal.Quotient.mk I)) =
      ringKrullDim (B ⧸ q.asIdeal) := by
  -- The third-isomorphism equivalence identifies the iterated quotient with the source quotient
  -- `B / q`, so Krull dimension is preserved across that ring equivalence.
  simpa using
    ringKrullDim_eq_of_ringEquiv
      (DoubleQuot.quotQuotEquivQuotOfLE (R := B) (I := I) (J := q.asIdeal) hIq)

-- Proof sketch: first derive `IsNoetherianRing A` by faithful-flat descent from the flat local
-- map `A → B` and `[IsNoetherianRing B]`. For a prime `p` of `A`, choose primes of `B` minimal
-- over `pB`. The direct equality above identifies the dimensions of the corresponding quotient
-- components, so every irreducible component of `Spec (B ⧸ p.asIdeal.map (algebraMap A B))` has
-- the same dimension.
/-- Lemma 15.110.3 (1): for a flat local map `A → B` of local rings, if `B` is Noetherian,
catenary, and `Spec B` is equidimensional, then for every prime ideal `p` of `A` the quotient
spectrum `Spec (B ⧸ p.asIdeal.map (algebraMap A B))`, equivalently `Spec (B / pB)`, is
equidimensional. -/
theorem primeSpectrum_quotient_equidimensional_of_flat_local_of_catenary_equidimensional
    (p : PrimeSpectrum A) :
    EquidimensionalSpace (PrimeSpectrum (B ⧸ p.asIdeal.map (algebraMap A B))) := by
  -- The source ring is Noetherian before passing to the quotient-dimension argument.
  let _ : IsNoetherianRing A := source_isNoetherianRing (A := A) (B := B)
  classical
  let I : Ideal B := Ideal.map (algebraMap A B) p.asIdeal
  -- Route correction: the upper local interval is now normalized by
  -- `codimBetween_closedPoint_and_prime_toNat_eq_ringKrullDim_quotient_local`, so the remaining
  -- source-faithful gap is the lower interval from `q` to a minimal prime and the final
  -- `ℕ∞`-valued additivity assembly. The new helper
  -- `ringKrullDim_quotient_localizationAtPrime_eq_krullDim_zeroLocus` isolates the quotient side
  -- of the local bridge, and
  -- `topologicalKrullDim_localization_components_eq_of_equidimensional` isolates the ambient
  -- equidimensional comparison between localization components through `q`.
  refine ⟨fun Z₁ Z₂ ↦ ?_⟩
  let e := (minimalPrimes.equivIrreducibleComponents (B ⧸ I)).symm
  let m₁ : minimalPrimes (B ⧸ I) := e (OrderDual.toDual Z₁)
  let m₂ : minimalPrimes (B ⧸ I) := e (OrderDual.toDual Z₂)
  have hm₁ :
      OrderDual.ofDual ((minimalPrimes.equivIrreducibleComponents (B ⧸ I)) m₁) = Z₁ := by
    -- Convert the chosen quotient component back to its minimal-prime representative.
    simpa [m₁, e]
  have hm₂ :
      OrderDual.ofDual ((minimalPrimes.equivIrreducibleComponents (B ⧸ I)) m₂) = Z₂ := by
    -- The same component/minimal-prime packaging applies to the second irreducible component.
    simpa [m₂, e]
  have hm₁_map : m₁.1 ∈ (Ideal.map (Ideal.Quotient.mk I) I).minimalPrimes := by
    -- In the quotient ring, a minimal prime is the image of a minimal prime of `I = pB`.
    simpa [I, Ideal.mk_ker] using m₁.2
  have hm₂_map : m₂.1 ∈ (Ideal.map (Ideal.Quotient.mk I) I).minimalPrimes := by
    -- The same minimal-prime transport holds for the second quotient component.
    simpa [I, Ideal.mk_ker] using m₂.2
  rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective I] at hm₁_map hm₂_map
  obtain ⟨J₁, hJ₁, hJ₁_map⟩ := hm₁_map
  obtain ⟨J₂, hJ₂, hJ₂_map⟩ := hm₂_map
  let q₁ : PrimeSpectrum B := ⟨J₁, Ideal.minimalPrimes_isPrime hJ₁⟩
  let q₂ : PrimeSpectrum B := ⟨J₂, Ideal.minimalPrimes_isPrime hJ₂⟩
  have hq₁ : q₁.asIdeal ∈ I.minimalPrimes := by
    -- The quotient minimal-prime transport lands back in `minimalPrimes I` after normalizing the
    -- kernel term of the quotient map.
    simpa [I, Ideal.mk_ker, sup_idem] using hJ₁
  have hq₂ : q₂.asIdeal ∈ I.minimalPrimes := by
    -- The same normalization identifies the second lifted prime as minimal over `pB`.
    simpa [I, Ideal.mk_ker, sup_idem] using hJ₂
  have hm₁_ideal : q₁.asIdeal.map (Ideal.Quotient.mk I) = m₁.1 := by
    -- The first lifted minimal prime maps back to the chosen quotient minimal prime.
    simpa [q₁] using hJ₁_map
  have hm₂_ideal : q₂.asIdeal.map (Ideal.Quotient.mk I) = m₂.1 := by
    -- The same quotient identification holds for the second lifted prime.
    simpa [q₂] using hJ₂_map
  have hquot :
      ringKrullDim (B ⧸ q₁.asIdeal) = ringKrullDim (B ⧸ q₂.asIdeal) :=
    ringKrullDim_quotient_eq_of_mem_minimalPrimes_map_direct
      (A := A) (B := B) p q₁ q₂ hq₁ hq₂
  have hZ₁ :
      topologicalKrullDim (Z₁ : Set (PrimeSpectrum (B ⧸ I))) =
        ringKrullDim (B ⧸ q₁.asIdeal) := by
    -- Rewrite the first component through its minimal prime in the quotient ring.
    calc
      topologicalKrullDim (Z₁ : Set (PrimeSpectrum (B ⧸ I))) =
          ringKrullDim ((B ⧸ I) ⧸ m₁.1) := by
            exact
              topologicalKrullDim_irreducibleComponent_eq_ringKrullDim_quotient_of_equiv_minimalPrime
                (R := B ⧸ I) Z₁ m₁ hm₁
      _ = ringKrullDim ((B ⧸ I) ⧸ q₁.asIdeal.map (Ideal.Quotient.mk I)) := by
            rw [hm₁_ideal]
      _ = ringKrullDim (B ⧸ q₁.asIdeal) := by
            exact ringKrullDim_quotient_quotient_map_eq (B := B) I q₁ hq₁.1.2
  have hZ₂ :
      topologicalKrullDim (Z₂ : Set (PrimeSpectrum (B ⧸ I))) =
        ringKrullDim (B ⧸ q₂.asIdeal) := by
    -- Repeat the same quotient-to-component comparison for the second component.
    calc
      topologicalKrullDim (Z₂ : Set (PrimeSpectrum (B ⧸ I))) =
          ringKrullDim ((B ⧸ I) ⧸ m₂.1) := by
            exact
              topologicalKrullDim_irreducibleComponent_eq_ringKrullDim_quotient_of_equiv_minimalPrime
                (R := B ⧸ I) Z₂ m₂ hm₂
      _ = ringKrullDim ((B ⧸ I) ⧸ q₂.asIdeal.map (Ideal.Quotient.mk I)) := by
            rw [hm₂_ideal]
      _ = ringKrullDim (B ⧸ q₂.asIdeal) := by
            exact ringKrullDim_quotient_quotient_map_eq (B := B) I q₂ hq₂.1.2
  calc
    topologicalKrullDim (Z₁ : Set (PrimeSpectrum (B ⧸ I))) = ringKrullDim (B ⧸ q₁.asIdeal) := hZ₁
    _ = ringKrullDim (B ⧸ q₂.asIdeal) := hquot
    _ = topologicalKrullDim (Z₂ : Set (PrimeSpectrum (B ⧸ I))) := hZ₂.symm

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [IsCatenaryRing B] in
/-- Helper for Lemma 15.110.3: in an equidimensional spectrum, quotienting by any two minimal
primes gives rings of the same Krull dimension. -/
lemma ringKrullDim_quotient_eq_of_mem_minimalPrimes_of_equidimensional
    {R : Type u} [CommRing R] [EquidimensionalSpace (PrimeSpectrum R)]
    (q₁ q₂ : PrimeSpectrum R)
    (hq₁ : q₁.asIdeal ∈ minimalPrimes R)
    (hq₂ : q₂.asIdeal ∈ minimalPrimes R) :
    ringKrullDim (R ⧸ q₁.asIdeal) = ringKrullDim (R ⧸ q₂.asIdeal) := by
  have hcomp₁ :
      PrimeSpectrum.zeroLocus (q₁.asIdeal : Set R) ∈
        irreducibleComponents (PrimeSpectrum R) := by
    -- A prime ideal in `minimalPrimes R` cuts out an irreducible component of `Spec R`.
    exact
      (PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents (R := R) (I := q₁.asIdeal)).2
        (by simpa [q₁.2.isRadical.radical] using hq₁)
  have hcomp₂ :
      PrimeSpectrum.zeroLocus (q₂.asIdeal : Set R) ∈
        irreducibleComponents (PrimeSpectrum R) := by
    -- The same component-identification applies to the second minimal prime.
    exact
      (PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents (R := R) (I := q₂.asIdeal)).2
        (by simpa [q₂.2.isRadical.radical] using hq₂)
  calc
    ringKrullDim (R ⧸ q₁.asIdeal) =
        topologicalKrullDim (PrimeSpectrum.zeroLocus (q₁.asIdeal : Set R)) := by
          -- Move from the quotient ring back to the corresponding component of `Spec R`.
          simpa using
            (topologicalKrullDim_zeroLocus_eq_ringKrullDim_quotient (R := R) q₁.asIdeal).symm
    _ = topologicalKrullDim (PrimeSpectrum.zeroLocus (q₂.asIdeal : Set R)) := by
          -- Equidimensionality identifies the dimensions of all irreducible components.
          exact TopologicalSpace.topologicalKrullDim_eq_of_mem_irreducibleComponents hcomp₁ hcomp₂
    _ = ringKrullDim (R ⧸ q₂.asIdeal) := by
          -- Return from the second component to its quotient ring.
          exact topologicalKrullDim_zeroLocus_eq_ringKrullDim_quotient (R := R) q₂.asIdeal

/-- Helper for Lemma 15.110.3: faithfully flat local maps admit primes of `B` minimal over every
extended prime `pB`. -/
lemma exists_minimalPrime_over_map (p : PrimeSpectrum A) :
    ∃ q : PrimeSpectrum B,
      q.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes := by
  let _ : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨q', hq'⟩ :=
    (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B)) p
  have hp_map_le_q' : Ideal.map (algebraMap A B) p.asIdeal ≤ q'.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr <| by
      simpa [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hq').ge
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hp_map_le_q'
  exact ⟨⟨q, Ideal.minimalPrimes_isPrime hq⟩, hq⟩

/-- Helper for Lemma 15.110.3: inside the equidimensional quotient `Spec (B / pB)`, all minimal
primes over `pB` define quotient rings of the same Krull dimension. -/
lemma ringKrullDim_quotient_eq_of_mem_minimalPrimes_map
    (p : PrimeSpectrum A) (q₁ q₂ : PrimeSpectrum B)
    (hq₁ : q₁.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes)
    (hq₂ : q₂.asIdeal ∈ (Ideal.map (algebraMap A B) p.asIdeal).minimalPrimes) :
    ringKrullDim (B ⧸ q₁.asIdeal) = ringKrullDim (B ⧸ q₂.asIdeal) := by
  let I : Ideal B := Ideal.map (algebraMap A B) p.asIdeal
  let π : B →+* B ⧸ I := Ideal.Quotient.mk I
  let _ : EquidimensionalSpace (PrimeSpectrum (B ⧸ I)) :=
    primeSpectrum_quotient_equidimensional_of_flat_local_of_catenary_equidimensional
      (A := A) (B := B) p
  let qbar₁ : PrimeSpectrum (B ⧸ I) :=
    ⟨q₁.asIdeal.map π, Ideal.isPrime_map_quotientMk_of_isPrime hq₁.1.2⟩
  let qbar₂ : PrimeSpectrum (B ⧸ I) :=
    ⟨q₂.asIdeal.map π, Ideal.isPrime_map_quotientMk_of_isPrime hq₂.1.2⟩
  have hqbar₁_map : qbar₁.asIdeal ∈ (Ideal.map π I).minimalPrimes := by
    -- Move the minimal prime of `pB` to the corresponding minimal prime of the quotient ideal.
    rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective I]
    refine ⟨q₁.asIdeal, ?_, by simp [qbar₁, π]⟩
    simpa [I, π, Ideal.mk_ker, sup_idem] using hq₁
  have hqbar₂_map : qbar₂.asIdeal ∈ (Ideal.map π I).minimalPrimes := by
    -- The same transport applies to the second minimal prime over `pB`.
    rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective I]
    refine ⟨q₂.asIdeal, ?_, by simp [qbar₂, π]⟩
    simpa [I, π, Ideal.mk_ker, sup_idem] using hq₂
  have hqbar₁ : qbar₁.asIdeal ∈ minimalPrimes (B ⧸ I) := by
    -- In the quotient ring the mapped ideal is zero, so these become honest minimal primes.
    simpa [I, π, Ideal.mk_ker] using hqbar₁_map
  have hqbar₂ : qbar₂.asIdeal ∈ minimalPrimes (B ⧸ I) := by
    -- This is the same zero-ideal specialization for the second prime.
    simpa [I, π, Ideal.mk_ker] using hqbar₂_map
  have hquot :
      ringKrullDim ((B ⧸ I) ⧸ qbar₁.asIdeal) =
        ringKrullDim ((B ⧸ I) ⧸ qbar₂.asIdeal) :=
    ringKrullDim_quotient_eq_of_mem_minimalPrimes_of_equidimensional
      (R := B ⧸ I) qbar₁ qbar₂ hqbar₁ hqbar₂
  -- Compare the two quotient minimal primes inside `Spec (B / pB)`, then rewrite each iterated
  -- quotient back to the original quotient `B / qᵢ`.
  calc
    ringKrullDim (B ⧸ q₁.asIdeal) =
        ringKrullDim ((B ⧸ I) ⧸ qbar₁.asIdeal) := by
          simpa [I, π, qbar₁] using
            (ringKrullDim_quotient_quotient_map_eq (B := B) I q₁ hq₁.1.2).symm
    _ = ringKrullDim ((B ⧸ I) ⧸ qbar₂.asIdeal) := hquot
    _ = ringKrullDim (B ⧸ q₂.asIdeal) := by
          simpa [I, π, qbar₂] using
            ringKrullDim_quotient_quotient_map_eq (B := B) I q₂ hq₂.1.2

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
  [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)] in
/-- Helper for Lemma 15.110.3: for a Noetherian source ring, equality of the integer-valued
prime-quotient dimensions forces equality of the underlying Krull dimensions. -/
lemma ringKrullDim_eq_of_primeQuotientValue_eq
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p₁ p₂ : PrimeSpectrum R)
    (h :
      (((ringKrullDim (R ⧸ p₁.asIdeal)).unbotD 0).toNat : ℤ) =
        (((ringKrullDim (R ⧸ p₂.asIdeal)).unbotD 0).toNat : ℤ)) :
    ringKrullDim (R ⧸ p₁.asIdeal) = ringKrullDim (R ⧸ p₂.asIdeal) := by
  let S₁ := R ⧸ p₁.asIdeal
  let S₂ := R ⧸ p₂.asIdeal
  let _ : FiniteRingKrullDim S₁ := inferInstance
  let _ : FiniteRingKrullDim S₂ := inferInstance
  have hnat :
      (((ringKrullDim S₁).unbotD 0).toNat : ℕ) =
        (((ringKrullDim S₂).unbotD 0).toNat : ℕ) := by
    -- The quoted integer-valued dimensions are just natural-number casts.
    exact_mod_cast h
  have hdim₁ :
      ringKrullDim S₁ =
        (((((ringKrullDim S₁).unbotD 0).toNat : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    have hbot : ringKrullDim S₁ ≠ ⊥ := ringKrullDim_ne_bot
    have htop : ringKrullDim S₁ ≠ ⊤ := ringKrullDim_ne_top
    -- Finite Krull dimension lets us recover the `WithBot` value from its `toNat` normalization.
    cases hs : ringKrullDim S₁ with
    | bot =>
        exact (hbot hs).elim
    | coe d =>
        have hd_ne_top : d ≠ ⊤ := by
          intro hd_top
          exact htop <| by simpa [hs, hd_top]
        simpa [S₁, hs] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hd_ne_top).symm
  have hdim₂ :
      ringKrullDim S₂ =
        (((((ringKrullDim S₂).unbotD 0).toNat : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    have hbot : ringKrullDim S₂ ≠ ⊥ := ringKrullDim_ne_bot
    have htop : ringKrullDim S₂ ≠ ⊤ := ringKrullDim_ne_top
    -- Apply the same finite-dimensional normalization to the second quotient ring.
    cases hs : ringKrullDim S₂ with
    | bot =>
        exact (hbot hs).elim
    | coe d =>
        have hd_ne_top : d ≠ ⊤ := by
          intro hd_top
          exact htop <| by simpa [hs, hd_top]
        simpa [S₂, hs] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hd_ne_top).symm
  -- Compare both Krull dimensions through their common `toNat` normal form.
  calc
    ringKrullDim S₁ =
        (((((ringKrullDim S₁).unbotD 0).toNat : ℕ) : ℕ∞) : WithBot ℕ∞) := hdim₁
    _ = (((((ringKrullDim S₂).unbotD 0).toNat : ℕ) : ℕ∞) : WithBot ℕ∞) := by
          rw [hnat]
    _ = ringKrullDim S₂ := hdim₂.symm

/-- Helper for Lemma 15.110.3: the source-side additive formula
`dim(A_p) + dim(A / p) = dim(A)` for the flat local map `A → B`. -/
lemma source_localizationAtPrime_add_ringKrullDim_quotient_eq_ringKrullDim
    (p : PrimeSpectrum A) :
    ringKrullDim (Localization.AtPrime p.asIdeal) + ringKrullDim (A ⧸ p.asIdeal) =
      ringKrullDim A := by
  -- Route correction: the source proof compares the local formulas for `A → B` and
  -- `(A / p) → (B / pB)` and then cancels their common closed fiber.
  -- TODO: choose `q` minimal over `pB`, rewrite `dim(B / pB)` to `dim(B / q)` via
  -- `ringKrullDim_quotient_eq_of_mem_minimalPrimes_map_direct`, apply Lemma `10.112.7` to
  -- `A → B` at `q` and to `(A / p) → (B / pB)` at the closed point, identify the two closed
  -- fibers via `DoubleQuot.quotQuotEquivQuotOfLE`, and cancel the common term.
  sorry

/-- Helper for Lemma 15.110.3: the source prime-quotient dimension on `Spec A` is a dimension
function. -/
lemma source_primeQuotient_dimension_isDimensionFunction :
    IsDimensionFunction
      (fun p : PrimeSpectrum A ↦ (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)) := by
  -- Route correction: the source proof should use the quotient-dimension function on `Spec A`
  -- itself, not the old descended function from `Spec B`.
  -- TODO: prove strict decrease from `ringKrullDim_quotient_eq_coheight` together with
  -- `Order.coheight_strictAnti`, and prove the unit drop along immediate specializations by
  -- applying `source_localizationAtPrime_add_ringKrullDim_quotient_eq_ringKrullDim` to the
  -- quotient ring `A ⧸ p.asIdeal`.
  sorry

/-- Helper for Lemma 15.110.3: minimal primes of `A` define source quotients of equal Krull
dimension. -/
lemma ringKrullDim_quotient_eq_of_mem_minimalPrimes_source
    (p₁ p₂ : PrimeSpectrum A)
    (hp₁ : p₁.asIdeal ∈ minimalPrimes A)
    (hp₂ : p₂.asIdeal ∈ minimalPrimes A) :
    ringKrullDim (A ⧸ p₁.asIdeal) = ringKrullDim (A ⧸ p₂.asIdeal) := by
  have hloc₁ : ringKrullDim (Localization.AtPrime p₁.asIdeal) = 0 := by
    -- Minimal primes localize to zero-dimensional local rings.
    letI : Ring.KrullDimLE 0 (Localization.AtPrime p₁.asIdeal) :=
      Ring.KrullDimLE.of_isLocalization p₁.asIdeal hp₁ (Localization.AtPrime p₁.asIdeal)
    exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  have hloc₂ : ringKrullDim (Localization.AtPrime p₂.asIdeal) = 0 := by
    -- The same zero-dimensionality holds for the second minimal prime.
    letI : Ring.KrullDimLE 0 (Localization.AtPrime p₂.asIdeal) :=
      Ring.KrullDimLE.of_isLocalization p₂.asIdeal hp₂ (Localization.AtPrime p₂.asIdeal)
    exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  have hsrc₁ :=
    source_localizationAtPrime_add_ringKrullDim_quotient_eq_ringKrullDim p₁
  have hsrc₂ :=
    source_localizationAtPrime_add_ringKrullDim_quotient_eq_ringKrullDim p₂
  have hquot₁ : ringKrullDim (A ⧸ p₁.asIdeal) = ringKrullDim A := by
    -- Killing the local term at a minimal prime leaves only the ambient source dimension.
    simpa [hloc₁] using hsrc₁
  have hquot₂ : ringKrullDim (A ⧸ p₂.asIdeal) = ringKrullDim A := by
    -- The same source formula collapse applies to the second minimal prime.
    simpa [hloc₂] using hsrc₂
  -- Kill the local terms at the minimal primes and compare the remaining quotient dimensions.
  calc
    ringKrullDim (A ⧸ p₁.asIdeal) = ringKrullDim A := hquot₁
    _ = ringKrullDim (A ⧸ p₂.asIdeal) := hquot₂.symm

-- Proof sketch: first derive `IsNoetherianRing A` by faithful-flat descent. Then the source
-- quotient-dimension function on `Spec A` is a dimension function, so the Chapter 5 owner theorem
-- yields catenarity of `Spec A`.
include B
/-- Core canonical owner for Lemma 15.110.3 (2): under the flat local hypotheses, the prime
spectrum `Spec A` is catenary. The ring-level conclusion `IsCatenaryRing A` is the thin alias
bridge to this owner theorem. -/
theorem catenarySpace_primeSpectrum_of_flat_local_of_catenary_equidimensional :
    CatenarySpace (PrimeSpectrum A) := by
  -- First descend Noetherianity so that the dimension-function criterion can be applied to `A`.
  let _ : IsNoetherianRing A := source_isNoetherianRing (A := A) (B := B)
  -- The source quotient-dimension function is the owner-level catenary witness on `Spec A`.
  exact
    (source_primeQuotient_dimension_isDimensionFunction (A := A)).catenarySpace

/-- Lemma 15.110.3 (2): for a flat local map `A → B` of local rings, if `B` is Noetherian,
catenary, and `Spec B` is equidimensional, then `A` is catenary. -/
theorem isCatenaryRing_of_flat_local_of_catenary_equidimensional :
    IsCatenaryRing A :=
  catenarySpace_primeSpectrum_of_flat_local_of_catenary_equidimensional (A := A) (B := B)

-- Proof sketch: once the source-side additive formula is available, minimal primes of `A` all
-- have quotients of dimension `dim A`. Transport those equal dimensions to irreducible components
-- through `minimalPrimes.equivIrreducibleComponents`.
/-- Lemma 15.110.3 (3): for a flat local map `A → B` of local rings, if `B` is Noetherian,
catenary, and `Spec B` is equidimensional, then `Spec A` is equidimensional. -/
theorem primeSpectrum_equidimensional_of_flat_local_of_catenary_equidimensional :
    EquidimensionalSpace (PrimeSpectrum A) := by
  -- Work in the source ring after Noetherian descent, and compare minimal irreducible components.
  let _ : IsNoetherianRing A := source_isNoetherianRing (A := A) (B := B)
  refine ⟨fun Z₁ Z₂ ↦ ?_⟩
  classical
  let e := (minimalPrimes.equivIrreducibleComponents A).symm
  let m₁ : minimalPrimes A := e (OrderDual.toDual Z₁)
  let m₂ : minimalPrimes A := e (OrderDual.toDual Z₂)
  have hm₁ :
      OrderDual.ofDual ((minimalPrimes.equivIrreducibleComponents A) m₁) = Z₁ := by
    -- Convert the first chosen component back to its minimal-prime representative.
    simpa [m₁, e]
  have hm₂ :
      OrderDual.ofDual ((minimalPrimes.equivIrreducibleComponents A) m₂) = Z₂ := by
    -- The same component/minimal-prime packaging applies to the second component.
    simpa [m₂, e]
  let p₁ : PrimeSpectrum A := ⟨m₁.1, Ideal.minimalPrimes_isPrime m₁.2⟩
  let p₂ : PrimeSpectrum A := ⟨m₂.1, Ideal.minimalPrimes_isPrime m₂.2⟩
  have hp₁ : p₁.asIdeal ∈ minimalPrimes A := by
    -- The first component is represented by a minimal prime of `A`.
    simpa [p₁, m₁]
  have hp₂ : p₂.asIdeal ∈ minimalPrimes A := by
    -- The second component is represented by a minimal prime of `A`.
    simpa [p₂, m₂]
  have hquot :
      ringKrullDim (A ⧸ p₁.asIdeal) = ringKrullDim (A ⧸ p₂.asIdeal) :=
    ringKrullDim_quotient_eq_of_mem_minimalPrimes_source (A := A) p₁ p₂ hp₁ hp₂
  calc
    topologicalKrullDim (Z₁ : Set (PrimeSpectrum A)) = ringKrullDim (A ⧸ p₁.asIdeal) := by
      exact
        topologicalKrullDim_irreducibleComponent_eq_ringKrullDim_quotient_of_equiv_minimalPrime
          (R := A) Z₁ m₁ hm₁
    _ = ringKrullDim (A ⧸ p₂.asIdeal) := hquot
    _ = topologicalKrullDim (Z₂ : Set (PrimeSpectrum A)) := by
      symm
      exact
        topologicalKrullDim_irreducibleComponent_eq_ringKrullDim_quotient_of_equiv_minimalPrime
          (R := A) Z₂ m₂ hm₂
omit B

end
