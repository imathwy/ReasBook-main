import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_130_1 (from Chap10) -/
universe u v

section

open scoped ENNReal

variable {k : Type u} [Field k]
variable {d : ℕ}
variable {S : Type v} [CommRing S] [Algebra k S]

/-
Domain-style sampling:
- primary domain: flatness loci for finite type algebras over a chosen quasi-finite polynomial
  presentation, compared with Cohen--Macaulayness and the local topological dimension stratum on
  `Spec`;
- sampled owner declarations:
  `Module.flatOverBaseLocus`,
  `AlgHom.QuasiFinite`,
  `Module.CohenMacaulay`,
  `PrimeSpectrum.dimensionStratum`;
- best owner abstraction: `Module.flatOverBaseLocus` for the flat-locus side, together with the
  explicit polynomial presentation map `π : MvPolynomial (Fin d) k →ₐ[k] S` as primitive
  source-facing data and the morphism-level owner `π.QuasiFinite`;
- primitive data: the finite type `k`-algebra structure on `S`, the chosen polynomial presentation
  `π`, and the quasi-finite hypothesis on `π`;
- derived API: the induced `MvPolynomial (Fin d) k`-algebra structure on `S`, the corresponding
  flat locus, and the comparison with the primewise Cohen--Macaulay condition together with the
  canonical dimension-`d` stratum owner.

Source/core/bridge triage:
- `source-facing`: the equality identifying the flat locus for the chosen presentation `π` with the
  Cohen--Macaulay and dimension-`d` locus;
- `core/canonical`: `Module.flatOverBaseLocus`, `AlgHom.QuasiFinite`, `Module.CohenMacaulay`, and
  `PrimeSpectrum.dimensionStratum`;
- `bridge/view`: the local algebra structure on `S` induced by `π`, used only to express the
  canonical flat-locus owner for this specific morphism.
-/
variable [Algebra.FiniteType k S]

-- Proof sketch: use the Chapter 10 owner `Module.flatOverBaseLocus` for the flatness locus of the
-- self-module `S`, with the `MvPolynomial (Fin d) k`-algebra structure induced by the chosen
-- polynomial presentation `π`. For a prime `q : Spec(S)`, let `p = q ∩ k[y₁, …, y_d]`.
-- Quasi-finiteness of `π` gives `dim S_q ≤ dim (k[y₁, …, y_d]_p)`. If `S_q` is flat over the
-- polynomial ring, apply the flat local criterion over the regular local ring
-- `(k[y₁, …, y_d])_p` to deduce that `S_q` is Cohen-Macaulay. Since `π` is quasi-finite, the
-- residue-field extension over `p` is finite, so the local dimension formula over the field `k`
-- identifies `q` with the dimension-`d` stratum of `Spec(S)`. Conversely, if `S_q` is
-- Cohen-Macaulay and `q` lies in that dimension-`d` stratum, the same local dimension comparison
-- forces `dim S_q = dim (k[y₁, …, y_d]_p)`, and the converse flatness criterion over the regular
-- local ring `(k[y₁, …, y_d])_p` gives flatness of `S_q` over `k[y₁, …, y_d]`.
/-- Lemma 10.130.1: for a finite type `k`-algebra `S` over a field `k` and a quasi-finite map
`π : k[y₁, …, y_d] → S`, the primes `q : Spec(S)` for which the local ring `S_q` is flat over
this chosen polynomial presentation are exactly the primes for which `S_q` is Cohen-Macaulay and
`q` lies in the dimension-`d` stratum of `Spec(S)`. -/
theorem flat_locus_eq_cohenMacaulay_inter_dimensionStratum_of_quasiFinite_polynomial
    (π : MvPolynomial (Fin d) k →ₐ[k] S) (hπ : π.QuasiFinite) :
    let _ : Algebra (MvPolynomial (Fin d) k) S := π.toAlgebra
    Module.flatOverBaseLocus (MvPolynomial (Fin d) k) S S =
      { q : PrimeSpectrum S |
          Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal) } ∩
        PrimeSpectrum.dimensionStratum S d := sorry

end

/-! ### Lemma_10_130_2 (from Chap10) -/
universe u v

namespace PrimeSpectrum

section

variable (R : Type u) [CommRing R]

/- 
Domain-style sampling:
- primary domain: local Cohen-Macaulayness on `Spec(R)` and the corresponding open locus;
- sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.LocallyCohenMacaulay`,
  `PrimeSpectrum.normalLocus`,
  `Module.flatOverBaseLocus`;
- best owner abstraction: the source-facing point-set owner should be a named locus on
  `PrimeSpectrum R`, with pointwise membership owned by the canonical local self-module predicate
  `Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)`;
- primitive data: the prime `p : PrimeSpectrum R` and its canonical local ring
  `Localization.AtPrime p.asIdeal`;
- derived API: the named locus on `Spec(R)`, its membership lemma, and openness/density theorems
  for finite type algebras over a field.

Source/core/bridge triage:
- `source-facing`: the Cohen-Macaulay locus in `Spec(R)`;
- `core/canonical`: `Localization.AtPrime` and `Module.CohenMacaulay` on the localized
  self-module;
- `bridge/view`: none beyond the membership lemma for the named locus.
-/

/-- The Cohen-Macaulay locus of `Spec(R)`, consisting of the primes whose local rings are
Cohen-Macaulay. -/
def cohenMacaulayLocus : Set (PrimeSpectrum R) :=
  { p | Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) }

/-- Membership in `PrimeSpectrum.cohenMacaulayLocus R` means that the corresponding local ring is
Cohen-Macaulay. -/
@[simp] theorem mem_cohenMacaulayLocus (p : PrimeSpectrum R) :
    p ∈ cohenMacaulayLocus R ↔
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) :=
  Iff.rfl

end

end PrimeSpectrum

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

-- Proof sketch: let `q : PrimeSpectrum S` be a point where `S_q` is Cohen-Macaulay. After
-- shrinking to a basic open neighborhood of `q`, choose a finite injective map from a polynomial
-- ring over `k` to `S` as in Lemmas `10.115.5` and `10.116.3`. Then Lemma `10.130.1` identifies
-- the Cohen--Macaulay locus near `q` with the flat locus of `S` over that polynomial ring, and
-- Theorem `10.129.4` shows that this flat locus is open.
/-- Lemma 10.130.2: for a finite type algebra `S` over a field `k`, the set of primes `q` such
that the local ring `S_q` is Cohen-Macaulay is an open subset of `Spec(S)`. -/
theorem isOpen_cohenMacaulayLocus_of_finiteType :
    IsOpen (PrimeSpectrum.cohenMacaulayLocus S) := sorry

end

/-! ### Lemma_10_130_3 (from Chap10) -/
universe u v

open PrimeSpectrum IsLocalRing Module.associatedPrimes
open scoped ENat

section

variable {S : Type v} [CommRing S]

/- Domain-style sampling:
- primary domain: the Cohen-Macaulay locus on `Spec(S)`, with the core local owner
  `Module.CohenMacaulay` on localized self-modules;
- sampled owner declarations of the same kind:
  `PrimeSpectrum.cohenMacaulayLocus`,
  `PrimeSpectrum.mem_cohenMacaulayLocus`,
  `Module.CohenMacaulay`,
  `Ring.KrullDimLE.of_isLocalization`;
- best owner abstraction: the source-facing owner remains the locus
  `PrimeSpectrum.cohenMacaulayLocus S`, while the reusable core input is the canonical
  `Module.CohenMacaulay` statement for `Localization.AtPrime q.1`;
- primitive data: a Noetherian ring, a minimal prime, and the canonical localization at that
  prime;
- derived API: Cohen-Macaulayness of that localization, then membership in the Cohen-Macaulay
  locus.

Source/core/bridge triage:
- `source-facing`: density of `PrimeSpectrum.cohenMacaulayLocus S`;
- `core/canonical`: `Module.CohenMacaulay R R` for a zero-dimensional Noetherian local ring, and
  its specialization to `Localization.AtPrime q.1` for `q : minimalPrimes S`;
- `bridge/view`: passage from a minimal prime to a point of `PrimeSpectrum S` lying in the locus.
-/

/-- A Noetherian local ring of Krull dimension at most zero is Cohen-Macaulay as a module over
itself. -/
theorem self_cohenMacaulay_of_krullDimLE_zero
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 0 R]
    [Nontrivial R] :
    Module.CohenMacaulay R R := by
  refine Module.CohenMacaulay.mk ?_
  have hann : Module.annihilator R R = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hassoc : maximalIdeal R ∈ associatedPrimes R R := by
    have hmin' : maximalIdeal R ∈ (⊥ : Ideal R).minimalPrimes :=
      Ideal.mem_minimalPrimes_of_krullDimLE_zero (maximalIdeal R)
    have hmin : maximalIdeal R ∈ (Module.annihilator R R).minimalPrimes := by
      simpa [hann] using hmin'
    exact minimalPrimes_annihilator_subset_associatedPrimes R R hmin
  have hdepth_le : moduleDepth R R ≤ 0 := by
    have hle : WithBot.some (moduleDepth R R : ℕ∞) ≤ ringKrullDim (R ⧸ maximalIdeal R) :=
      moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (maximalIdeal R) hassoc
    have hdim : ringKrullDim (R ⧸ maximalIdeal R) = 0 := by
      letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
      exact ringKrullDim_eq_zero_of_field (R ⧸ maximalIdeal R)
    rw [hdim] at hle
    simpa [WithBot.some_eq_coe] using hle
  have hdepth : moduleDepth R R = 0 := le_antisymm hdepth_le bot_le
  have hdim : ringKrullDim R = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  simp [Module.supportDim_self_eq_ringKrullDim, hdim, hdepth]

local instance (q : minimalPrimes S) : q.1.IsPrime :=
  Ideal.minimalPrimes_isPrime q.2

/-- If `q` is a minimal prime of a Noetherian ring `S`, then the localization `S_q` is
Cohen-Macaulay. -/
theorem cohenMacaulay_localizationAtPrime_self_of_minimalPrime
    [IsNoetherianRing S] (q : minimalPrimes S) :
    Module.CohenMacaulay (Localization.AtPrime q.1) (Localization.AtPrime q.1) := by
  letI : IsNoetherianRing (Localization.AtPrime q.1) :=
    IsLocalization.isNoetherianRing q.1.primeCompl (Localization.AtPrime q.1) inferInstance
  letI : Ring.KrullDimLE 0 (Localization.AtPrime q.1) :=
    Ring.KrullDimLE.of_isLocalization q.1 q.2 (Localization.AtPrime q.1)
  exact self_cohenMacaulay_of_krullDimLE_zero (Localization.AtPrime q.1)

/-- Every minimal prime of a Noetherian ring lies in its Cohen-Macaulay locus. -/
theorem mem_cohenMacaulayLocus_of_mem_minimalPrimes
    [IsNoetherianRing S]
    (q : PrimeSpectrum S) (hq : q.asIdeal ∈ minimalPrimes S) :
    q ∈ PrimeSpectrum.cohenMacaulayLocus S := by
  let qmin : minimalPrimes S := ⟨q.asIdeal, hq⟩
  simpa using cohenMacaulay_localizationAtPrime_self_of_minimalPrime qmin

-- Proof sketch: Lemma `10.130.2` gives that the Cohen--Macaulay locus is open. To prove density,
-- it is enough to show that every minimal prime of `S` lies in this locus. For a minimal prime
-- `q`, the local ring `Localization.AtPrime q.asIdeal` has Krull dimension zero, hence it is
-- Cohen--Macaulay.
/-- Lemma 10.130.3, owner-level form: for a Noetherian ring `S`, the set of primes `q` such that
the local ring `S_q` is Cohen-Macaulay is dense in `Spec(S)`. The finite type over a field
hypothesis from the source is used only to obtain `IsNoetherianRing S`, so the main public theorem
lives at the Noetherian-ring owner level. -/
theorem dense_cohenMacaulayLocus [IsNoetherianRing S] :
    Dense (PrimeSpectrum.cohenMacaulayLocus S) := by
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.dense_iff]
  intro U hU hUne
  rcases hU with ⟨f, rfl⟩
  rcases hUne with ⟨x, hx⟩
  obtain ⟨q, hq, hqx⟩ :=
    Ideal.exists_minimalPrimes_le (show (⊥ : Ideal S) ≤ x.asIdeal from bot_le)
  let q' : PrimeSpectrum S := ⟨q, Ideal.minimalPrimes_isPrime hq⟩
  have hq' : q'.asIdeal ∈ minimalPrimes S := by
    simpa [minimalPrimes] using hq
  refine ⟨q', ?_, mem_cohenMacaulayLocus_of_mem_minimalPrimes q' hq'⟩
  refine (PrimeSpectrum.mem_basicOpen f q').2 fun hfq ↦ ?_
  exact (PrimeSpectrum.mem_basicOpen f x).1 hx (hqx hfq)

/-- Lemma 10.130.3: for a finite type algebra `S` over a field `k`, the set of primes `q` such
that the local ring `S_q` is Cohen-Macaulay is dense in `Spec(S)`, so together with Lemma
`10.130.2` it is a dense open subset. -/
theorem dense_cohenMacaulayLocus_of_finiteType
    (k : Type u) [Field k] [Algebra k S] [Algebra.FiniteType k S] :
    Dense (PrimeSpectrum.cohenMacaulayLocus S) := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  exact dense_cohenMacaulayLocus

end

/-! ### Lemma_10_130_4 (from Chap10) -/
universe u v

namespace PrimeSpectrum

/- 
Domain-style sampling:
- primary domain: source-facing loci on `Spec(S)` cut out by properties of the fiber local ring
  and the relative fiber dimension;
- sampled owner declarations of the same kind:
  `fiberLocalRingAt`,
  `Module.CohenMacaulay`,
  `PrimeSpectrum.cohenMacaulayLocus`,
  `PrimeSpectrum.normalLocus`,
  `PrimeSpectrum.dimensionStratum`,
  `relativeDimensionAtLELocus`;
- best owner abstraction: the Cohen-Macaulay fiber condition should be owned by a named locus on
  `PrimeSpectrum S`, with pointwise membership owned by the canonical local self-module predicate
  `Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q)`; the
  relative-dimension-`d` refinement in Lemma `10.130.4` remains a theorem-level condition built
  from that owner and `relativeDimensionAt`;
- primitive data: the prime `q : PrimeSpectrum S` together with the core owners
  `fiberLocalRingAt R S q` and `relativeDimensionAt R S q`;
- derived API: the named Cohen-Macaulay fiber locus and the bridge identifying it with the
  Cohen-Macaulay locus of the fiber ring at `fiberPrimeAt R S q`.

Source/core/bridge triage:
- `source-facing`: `PrimeSpectrum.cohenMacaulayFiberLocus R S`;
- `core/canonical`: `fiberLocalRingAt R S q` and
  `Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q)`;
- `bridge/view`: the comparison with `PrimeSpectrum.cohenMacaulayLocus` on the fiber ring and the
  theorem-level intersection with the exact relative-dimension condition in Lemma `10.130.4`.
-/

/-- The locus in `Spec(S)` where the fiber local ring of `S/R` is Cohen-Macaulay. -/
def cohenMacaulayFiberLocus (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] :
    Set (PrimeSpectrum S) :=
  { q | Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) }

/-- Membership in `PrimeSpectrum.cohenMacaulayFiberLocus R S` means that the corresponding fiber
local ring is Cohen-Macaulay. -/
@[simp] theorem mem_cohenMacaulayFiberLocus (R : Type u) [CommRing R] (S : Type v) [CommRing S]
    [Algebra R S] (q : PrimeSpectrum S) :
    q ∈ cohenMacaulayFiberLocus R S ↔
      Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) :=
  Iff.rfl

/-- The source-facing fiber-local-ring formulation is equivalent to the fiber-ring
Cohen-Macaulay-locus formulation at the canonical fiber prime. -/
theorem mem_cohenMacaulayFiberLocus_iff_mem_cohenMacaulayLocus
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (q : PrimeSpectrum S) :
    q ∈ cohenMacaulayFiberLocus R S ↔
      fiberPrimeAt R S q ∈ PrimeSpectrum.cohenMacaulayLocus ((q.asIdeal.under R).Fiber S) := by
  rw [mem_cohenMacaulayFiberLocus]
  rw [PrimeSpectrum.mem_cohenMacaulayLocus ((q.asIdeal.under R).Fiber S) (fiberPrimeAt R S q)]
  rfl

end PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S] [Module.Flat R S]

-- Proof sketch: for a prime `q` in the locus, use Lemma `10.125.2` after shrinking around `q`
-- to obtain a quasi-finite map `R[t₁, …, t_d] → S_g` with `d = relativeDimensionAt R S q`.
-- Lemma `10.130.1` identifies the Cohen-Macaulay plus relative-dimension-`d` condition with
-- flatness over that polynomial ring, Lemma `10.128.8` upgrades the fiberwise flatness to
-- flatness of the local map, and Theorem `10.129.4` then shows the corresponding flatness locus
-- is open. Shrinking once more, every nearby prime satisfies the same fiberwise criterion.
/-- Lemma 10.130.4: if `R → S` is flat and of finite presentation, then for each `d : ℕ` the
subset of primes `q : Spec(S)` such that the local fiber ring at `q` is Cohen-Macaulay and the
relative dimension of `S/R` at `q` is `d` is open in `Spec(S)`. -/
theorem isOpen_cohenMacaulayFiber_and_relativeDimensionAt_eq_of_finitePresentation_flat
    (d : ℕ) :
    IsOpen
      ((PrimeSpectrum.cohenMacaulayFiberLocus R S) ∩
        { q : PrimeSpectrum S | relativeDimensionAt R S q = (d : WithBot ℕ∞) }) := sorry

end

/-! ### Lemma_10_130_5 (from Chap10) -/
universe u v

section

open PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S] [Module.Flat R S]

/- 
Domain-style sampling:
- primary domain: source-facing loci on `Spec(S)` cut out by the Cohen-Macaulay condition on the
  fiber local ring, together with the induced topology on each set-theoretic fiber of
  `PrimeSpectrum.comap (algebraMap R S)`;
- sampled owner declarations of the same kind:
  `PrimeSpectrum.cohenMacaulayFiberLocus`,
  `PrimeSpectrum.mem_cohenMacaulayFiberLocus_iff_mem_cohenMacaulayLocus`,
  `PrimeSpectrum.preimageHomeomorphFiber`,
  `dense_cohenMacaulayLocus_of_finiteType`;
- best owner abstraction: the source-facing owner remains the named locus
  `PrimeSpectrum.cohenMacaulayFiberLocus R S`; the set-theoretic fiber should use the canonical
  subtype `PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}` rather than a one-off local alias;
- primitive data: the finitely presented flat map `R → S`, the locus owner
  `PrimeSpectrum.cohenMacaulayFiberLocus R S`, and a base prime `p : PrimeSpectrum R`;
- derived API: the separate openness theorem and the fiberwise density theorem, both extracted from
  the source-facing conjunction.

Source/core/bridge triage:
- `source-facing`: openness of `PrimeSpectrum.cohenMacaulayFiberLocus R S` together with density on
  each fiber of `Spec(S) → Spec(R)`;
- `core/canonical`: `PrimeSpectrum.cohenMacaulayFiberLocus R S` and the canonical subtype fiber
  `PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}`;
- `bridge/view`: `PrimeSpectrum.preimageHomeomorphFiber R S p`, relating the set-theoretic fiber to
  `Spec (κ(p) ⊗[R] S)`.
-/

-- Proof sketch: apply Lemma `10.130.4` to see that the Cohen--Macaulay fiber locus is open in
-- `Spec(S)`. For a fixed `p : Spec(R)`, identify the fiber over `p` with `Spec(κ(p) ⊗[R] S)`; the
-- induced subset is exactly the Cohen--Macaulay locus of that finite type algebra over the field
-- `κ(p)`, so Lemma `10.130.3` gives density in the fiber.
/-- Lemma 10.130.5: if `R → S` is flat and of finite presentation, then the set of primes
`q : Spec(S)` for which the local fiber ring
`S_q ⊗[R] κ(q ∩ R)`, formalized as `fiberLocalRingAt R S q`, is Cohen-Macaulay is open in
`Spec(S)` and its induced subset on every fiber of `Spec(S) → Spec(R)` is dense. -/
theorem isOpen_and_fiberwiseDense_cohenMacaulayFiberLocus_of_finitePresentation_flat :
    IsOpen (cohenMacaulayFiberLocus R S) ∧
      ∀ p : PrimeSpectrum R,
        Dense
          (((↑) : comap (algebraMap R S) ⁻¹' {p} → PrimeSpectrum S) ⁻¹'
            cohenMacaulayFiberLocus R S) := sorry

/-- The Cohen-Macaulay fiber locus of a flat finitely presented map is open. -/
theorem isOpen_cohenMacaulayFiberLocus_of_finitePresentation_flat :
    IsOpen (cohenMacaulayFiberLocus R S) :=
  isOpen_and_fiberwiseDense_cohenMacaulayFiberLocus_of_finitePresentation_flat.1

end

section

open PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- On the fiber over `p : Spec(R)`, if the fiber ring `κ(p) ⊗[R] S` is finite type over
`κ(p)`, then the induced Cohen-Macaulay fiber locus is dense. -/
theorem dense_preimage_cohenMacaulayFiberLocus_of_fiberFiniteType
    (p : PrimeSpectrum R) [Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber S)] :
    Dense
      (((↑) : comap (algebraMap R S) ⁻¹' {p} → PrimeSpectrum S) ⁻¹'
        cohenMacaulayFiberLocus R S) := sorry

end

/-! ### Lemma_10_130_6 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/- 
Domain-style sampling:
- primary domain: Cohen-Macaulay local rings under tensor base change along a field extension;
- sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.LocallyCohenMacaulay`,
  `primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension`,
  `flat_locus_eq_cohenMacaulay_inter_dimensionStratum_of_quasiFinite_polynomial`;
- best owner abstraction: the local Cohen-Macaulay owner `Module.CohenMacaulay` on the localized
  self-modules downstairs and upstairs;
- primitive data: the finite type `k`-algebra `S` and the upstairs prime
  `qK : PrimeSpectrum S_K`; the downstairs prime is the canonical contraction
  `PrimeSpectrum.comap iSK qK`;
- derived API: the local dimension comparison from Lemma `10.116.6` and the flat-locus
  description from Lemma `10.130.1`, which support the proof but should not be repackaged as a
  second public owner here.

Source/core/bridge triage:
* `source-facing`: invariance of the Cohen-Macaulay condition for the local rings at the canonical
  contracted/lying-over pair of primes under the tensor base change `S ↦ K ⊗[k] S`;
* `core/canonical`: `Module.CohenMacaulay` on `Localization.AtPrime q.asIdeal` and
  `Localization.AtPrime qK.asIdeal`;
* `bridge/view`: the tensor-product map `iSK` and the induced contraction
  `PrimeSpectrum.comap iSK qK`.

The public statement should therefore stay directly on `Module.CohenMacaulay`; adding a separate
ring-level alias here would only duplicate the chapter owner abstraction.
-/

-- Proof sketch: after replacing `S` by a localization away from `q`, use Noether normalization to
-- choose a finite injective map `k[x₁, …, x_d] → S`. Base change this map to `K[x₁, …, x_d] →
-- K ⊗[k] S`, use Lemma `10.116.6` to identify the relevant relative dimensions, and apply Lemma
-- `10.130.1` to reduce both Cohen-Macaulay conditions to flatness of the two vertical maps in the
-- normalization square. Since the bottom horizontal map is flat, the two flatness conditions are
-- equivalent.
/-- Lemma 10.130.6: for a field extension `K / k`, a finite type `k`-algebra `S`, a prime
`qK : Spec(K ⊗[k] S)`, and its contraction `q := PrimeSpectrum.comap iSK qK`, the local ring
`S_q` is Cohen-Macaulay if and only if the local ring `(K ⊗[k] S)_{qK}` is Cohen-Macaulay. -/
theorem cohenMacaulay_localizationAtPrime_iff_of_tensorProduct_fieldExtension
    (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    Module.CohenMacaulay (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) ↔
      Module.CohenMacaulay (Localization.AtPrime qK.asIdeal)
        (Localization.AtPrime qK.asIdeal) := sorry

end

/-! ### Lemma_10_130_7 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R'] [Algebra.FiniteType R S]

/- 
Domain-style sampling:
- primary domain: base change on `PrimeSpectrum` for loci cut out by a fiber-local ring property;
- sampled owner declarations of the same kind:
  `PrimeSpectrum.cohenMacaulayFiberLocus`,
  `fiberLocalRingAt`,
  `Module.CohenMacaulay`,
  `relativeDimensionAt_le_preimage_eq_baseChange`,
  `smoothLocus_baseChange_preimage_eq`;
- best owner abstraction: the upstream named locus owner
  `PrimeSpectrum.cohenMacaulayFiberLocus R S`, whose membership is defined through the canonical
  fiber-local-ring owner `fiberLocalRingAt R S q` and the local self-module predicate
  `Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q)`;
- primitive data: the finite type map `R → S`, the arbitrary base change `R → R'`, and the
  induced map `Spec(R' ⊗[R] S) → Spec(S)`;
- derived API: the base-change equality for the inverse image of that locus owner.

Source/core/bridge triage:
* `source-facing`: the Cohen-Macaulay fiber locus of `Spec(S)`;
* `core/canonical`: `fiberLocalRingAt` and `Module.CohenMacaulay` on the fiber local self-module;
* `bridge/view`: inverse image along `PrimeSpectrum.comap includeRight.toRingHom`.
-/

-- Proof sketch: for `q' : Spec(R' ⊗[R] S)`, let `q` be its image in `Spec(S)`. The local fiber
-- ring of `S'/R'` at `q'` is the base change of the local fiber ring of `S/R` at `q` along the
-- residue-field extension `κ(q ∩ R) → κ(q' ∩ R')`. Apply Lemma `10.130.6` to that field extension
-- and then unwind the definitions of the two loci.
/-- Lemma 10.130.7: for a finite type ring map `R → S`, an arbitrary base change `R → R'`, and
`S' = R' ⊗[R] S`, the locus of primes of `S'` where the local fiber ring of `S'/R'` is
Cohen-Macaulay is exactly the inverse image of the corresponding locus of `S/R` under
`Spec(S') → Spec(S)`. -/
theorem cohenMacaulayFiberLocus_baseChange_preimage_eq :
    PrimeSpectrum.comap includeRight.toRingHom ⁻¹'
        PrimeSpectrum.cohenMacaulayFiberLocus R S =
      PrimeSpectrum.cohenMacaulayFiberLocus R' (R' ⊗[R] S) := sorry

end

/-! ### Lemma_10_130_8 (from Chap10) -/
universe u v

section

open PrimeSpectrum TopologicalSpace

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

variable [Algebra.FinitePresentation R S] [Module.Flat R S]

/- 
Domain-style sampling for Cohen-Macaulay fiber stratifications:
- primary domain: source-facing strata in `Spec(S)` cut out by the Cohen-Macaulay fiber locus and
  the exact relative fiber dimension, together with the quotient-factor decomposition attached to a
  finite clopen partition;
- sampled declarations of the same kind:
  `cohenMacaulayFiberLocus`,
  `isOpen_cohenMacaulayFiber_and_relativeDimensionAt_eq_of_finitePresentation_flat`,
  `relativeDimensionAt`,
  `exists_product_decomposition_by_dimensionStrata_of_finiteType_cohenMacaulay`;
- best owner abstraction: the source-facing owner is the actual stratum
  `(cohenMacaulayFiberLocus R S) ∩ { q : PrimeSpectrum S | relativeDimensionAt R S q = d }`;
  the product decomposition is only a `bridge/view` built from those strata;
- primitive data: the canonical locus owner `cohenMacaulayFiberLocus R S`, the pointwise
  invariant `relativeDimensionAt R S q`, and the flat finitely presented map `R → S`;
- derived API: openness of each stratum, finiteness of the nonempty strata, and the quotient
  factors whose spectra identify with those exact strata.

Source/core/bridge triage:
- `source-facing`: the exact Cohen-Macaulay fiber dimension-`d` stratum on `Spec(S)`;
- `core/canonical`: `cohenMacaulayFiberLocus`, `relativeDimensionAt`, `EquidimensionalSpace`, and
  `zeroLocus`;
- `bridge/view`: quotient ideals `I d` together with an `AlgEquiv` from `S` to the finite product
  of the corresponding quotient factors.
-/

-- Proof sketch: for each `d`, let `W d ⊆ Spec(S)` be the open locus from Lemma `10.130.4`
-- where the fiber local rings are Cohen-Macaulay and have relative dimension `d`. These opens are
-- pairwise disjoint and cover `Spec(S)`. Apply Lemma `10.24.3` repeatedly to the finite clopen
-- partition by the nonempty `W d` to obtain idempotents and hence a finite product decomposition
-- of `S` into quotient factors. Each factor is supported on one stratum, so its fibers remain
-- Cohen-Macaulay and equidimensional; when a fiber is nonempty, its Krull dimension is the
-- indexed dimension.
/-- Lemma 10.130.8: if `R → S` is flat and of finite presentation with Cohen-Macaulay fibers, then
`S` admits a finite product decomposition into quotient `R`-algebras indexed by the occurring
fiber dimensions. The `d`-th quotient factor cuts out exactly the nonempty stratum
`cohenMacaulayFiberLocus R S ∩
  { q : PrimeSpectrum S | relativeDimensionAt R S q = d }`,
and is again flat and finitely presented over `R` with Cohen-Macaulay fibers that are
equidimensional of Krull dimension `d` whenever the fiber is nonempty. -/
theorem exists_product_decomposition_by_pure_fiber_dimension_of_finitePresentation_flat
    (hCM : ∀ p : PrimeSpectrum R, CohenMacaulayRing (p.asIdeal.Fiber S)) :
    ∃ (D : Finset ℕ) (I : D → Ideal S) (e : S ≃ₐ[R] ((d : D) → S ⧸ I d)),
      (∀ d : D,
        cohenMacaulayFiberLocus R S ∩
            { q : PrimeSpectrum S | relativeDimensionAt R S q = ((d : ℕ) : WithBot ℕ∞) } =
          zeroLocus (I d : Set S)) ∧
        ∀ d : D,
          Set.Nonempty
              (cohenMacaulayFiberLocus R S ∩
                { q : PrimeSpectrum S | relativeDimensionAt R S q = ((d : ℕ) : WithBot ℕ∞) }) ∧
            Algebra.FinitePresentation R (S ⧸ I d) ∧
              Module.Flat R (S ⧸ I d) ∧
                ∀ p : PrimeSpectrum R,
                  CohenMacaulayRing (p.asIdeal.Fiber (S ⧸ I d)) ∧
                    EquidimensionalSpace (PrimeSpectrum (p.asIdeal.Fiber (S ⧸ I d))) ∧
                      Nonempty (PrimeSpectrum (p.asIdeal.Fiber (S ⧸ I d))) →
                        ringKrullDim (p.asIdeal.Fiber (S ⧸ I d)) = (d : ℕ) := sorry

end
