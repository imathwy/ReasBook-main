import Mathlib
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Away.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_109_1 (from Chap15) -/
open IsLocalRing
open RingPairCat

universe u

noncomputable section

section

variable {A Ah Ash Ahatsh : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/- Domain-style sampling:
- primary domain: local commutative algebra of henselizations, strict henselizations, and
  maximal-ideal completions of Noetherian local rings;
- sampled owner declarations:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `RingPairCat.henselizationToAdicCompletion`,
  `henselizationMapRingHom`,
  `existsUnique_algHom_between_strictHenselizations_of_residueFieldMap`,
  `strictHenselizationComparison`,
  `minimalPrimes`,
  `RingHom.FaithfullyFlat.injective`;
- best owner abstraction: the completion comparison should come from the pair-henselization owner
  map `RingPairCat.henselizationToAdicCompletion`, specialized to `(A, maximalIdeal A)` and
  composed with the Chapter 10 comparison `henselizationMapRingHom` from an arbitrary chosen
  henselization `Ah` into that owner. For strict henselizations, the source-facing statement is
  the branch-number inequality itself; any compatible residue-field map belongs only to the
  auxiliary bridge that derives the comparison `Ash → Ahatsh` from
  `existsUnique_algHom_between_strictHenselizations_of_residueFieldMap`, as in Chapter 10's
  `strictHenselizationComparison`, rather than to the main theorem surface;
- primitive data: the local Noetherian ring `A`, a chosen henselization `Ah`, and for part `(3)`
  the chosen strict henselizations of `A` and `ACompletion`;
- derived API: the owner-derived henselization-completion comparison and the induced contraction
  map on minimal primes, together with the owner-derived strict-henselization completion
  comparison and its locality / flatness properties.

Source/core/bridge triage:
- `source-facing`: the three branch-count comparisons in Lemma 15.109.1;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`, `minimalPrimes`,
  `RingHom.FaithfullyFlat`, the pair-henselization completion owner, and
  `existsUnique_algHom_between_strictHenselizations_of_residueFieldMap`;
- `bridge/view`: the owner-derived comparison `Ah → ACompletion` and the residue-field
  compatibility data used only to derive the strict-henselization completion comparison.
-/
local notation "A_pair" => pairOfIdeal (maximalIdeal A)
local notation "A_h" => henselizationRing A_pair

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

private noncomputable abbrev selfHenselizationMapRingHom
    (R : Type u) [CommRing R] [IsLocalRing R]
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    (R_h : Type u) [CommRing R_h] [Algebra R R_h] [IsHenselizationOf R R_h] :
    Rh →+* R_h :=
  @henselizationMapRingHom R Rh R_h _ _ _ _ _ _ R _ _ _ _ _ _

/-- The canonical comparison map from a chosen henselization `Ah` of a Noetherian local ring `A`
to the maximal-ideal completion `AdicCompletion (maximalIdeal A) A`. -/
noncomputable abbrev henselizationCompletionComparison
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh] :
    Rh →+* AdicCompletion (maximalIdeal R) R :=
  let R_pair := pairOfIdeal (maximalIdeal R)
  let R_h := henselizationRing R_pair
  R_pair.henselizationToAdicCompletion.comp (selfHenselizationMapRingHom R Rh R_h)

-- Proof sketch: combine injectivity of `Ah → Ahat` with the minimal-prime existence result for
-- injective maps and the going-down property for flat maps to show every minimal prime of `Ah` is
-- the contraction of some minimal prime of `Ahat`.
/-- Lemma 15.109.1 (1): for a Noetherian local ring `A`, the canonical compatible map from a
chosen henselization `Ah` to the maximal-ideal completion `AdicCompletion (maximalIdeal A) A`
induces a surjection from the minimal primes of the completion onto the minimal primes of `Ah`. -/
theorem henselizationCompletion_surjOn_minimalPrimes :
    Set.SurjOn
      (Ideal.comap (henselizationCompletionComparison A Ah))
      (minimalPrimes ACompletion)
      (minimalPrimes Ah) := sorry

-- Proof sketch: apply the previous surjectivity statement to the contraction map on minimal
-- primes and compare cardinalities of the minimal-prime sets.
/-- Lemma 15.109.1 (2): the number of branches of `A`, computed from a chosen henselization `Ah`,
is at most the number of minimal primes of the completion
`AdicCompletion (maximalIdeal A) A`. Since the completion is henselian, this is the number of
branches of the completion. -/
theorem branchNumber_le_completion_minimalPrimes :
    branchNumber A Ah ≤ (minimalPrimes ACompletion).encard := sorry

variable [CommRing Ahatsh] [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
variable [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]

-- Proof sketch: compare `Ash` with a strict henselization `Ahatsh` of the completion through the
-- flat injective owner comparison `Ash → Ahatsh`, obtained internally from the canonical
-- strict-henselization comparison bridge; the auxiliary composed `A`-algebra structure on
-- `Ahatsh` and the tower through `ACompletion` are derived internally from
-- `A → ACompletion → Ahatsh`. Repeat the minimal-prime argument from part `(1)`, and then
-- translate the resulting surjectivity into the inequality of geometric branch numbers.
/-- Lemma 15.109.1 (3): for a chosen strict henselization `Ash` of `A` and a chosen strict
henselization `Ahatsh` of the completion `ACompletion = AdicCompletion (maximalIdeal A) A`, the
canonical comparison between these strict henselizations induces the branch-count inequality from
`A` to its completion. -/
theorem geometricBranchNumber_le_completion :
    geometricBranchNumber A Ash ≤ geometricBranchNumber ACompletion Ahatsh := sorry

end

/-! ### Lemma_15_109_2 (from Chap15) -/
open IsLocalRing

universe u

noncomputable section

section

variable {A Ah : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/-
Domain-style sampling:
- primary domain: Noetherian local commutative algebra of henselizations, maximal-ideal
  completions, and minimal primes;
- sampled owner declarations:
  `branchNumber`,
  `minimalPrimes`,
  `henselizationCompletionComparison`,
  `henselizationCompletion_surjOn_minimalPrimes`;
- best owner abstraction: the source-facing equality criterion should use the canonical owner
  subtype `minimalPrimes Ah` for the minimal primes of the chosen henselization, while the
  comparison map to the completion remains the owner-derived
  `henselizationCompletionComparison A Ah`;
- primitive data: the Noetherian local ring `A`, its chosen henselization `Ah`, and the canonical
  comparison map `Ah → ACompletion`;
- derived API: the branch count `branchNumber A Ah`, the minimal-prime count
  `(minimalPrimes ACompletion).encard`, and the primality of the radicals of extended minimal
  primes.

Source/core/bridge triage:
- `source-facing`: the equivalence below;
- `core/canonical`: `minimalPrimes`, `branchNumber`, `AdicCompletion`, `Ideal.map`,
  `Ideal.radical`;
- `bridge/view`: `henselizationCompletionComparison A Ah`.
-/
-- Proof sketch: by Lemma `15.109.1`, the minimal primes of `ACompletion` surject onto the minimal
-- primes of `Ah`, so equality of branch counts is equivalent to every fiber over a minimal prime
-- of `Ah` consisting of a single minimal prime of `ACompletion`. Since both rings are Noetherian
-- by Lemma `15.45.3` and Algebra, Lemma `10.31.6`, this uniqueness is equivalent to the radical
-- of the extended ideal `qACompletion` being prime for each minimal prime `q` of `Ah`.
/-- Lemma 15.109.2: for a Noetherian local ring `A` with chosen henselization `Ah`, the number of
branches of `A` equals the number of minimal primes of the completion
`ACompletion = AdicCompletion (maximalIdeal A) A` if and only if for every minimal prime `q` of
`Ah`, the radical `√(qACompletion)` is prime. -/
theorem branchNumber_eq_completion_minimalPrimes_iff_radical_map_minimalPrime_isPrime
    :
    branchNumber A Ah = (minimalPrimes ACompletion).encard ↔
      ∀ q : minimalPrimes Ah,
        (Ideal.radical (Ideal.map (henselizationCompletionComparison A Ah) q)).IsPrime :=
      sorry

end

/-! ### Lemma_15_109_3 (from Chap15) -/
universe u v

section

variable {A : Type u} {C : Type v}
variable [CommRing A] [CommRing C] [Algebra A C]

local notation:max "A[" f "]" => Localization.Away f
local notation:max "C[" f "]" => Localization.Away (algebraMap A C f)

noncomputable local instance localizedAwayAlgebra (f : A) : Algebra A[f] C[f] :=
  (Localization.awayMapₐ (Algebra.ofId A C) f).toAlgebra

/-
Domain-style sampling for Lemma 15.109.3:
- primary domain: commutative algebra of local product decompositions detected on principal opens
  by idempotent localizations;
- sampled owner declarations:
  `exists_idempotent_localizationAway_of_surjective_of_flat_of_finitePresentation`,
  `Localization.awayMapₐ`,
  `RingHom.prod_bijective_of_isIdempotentElem`,
  `quotient_isLocalization_Away_one_sub_of_idempotent_generator`;
- best owner abstraction: the public local comparison morphisms should stay at the canonical
  `Localization.awayMapₐ` surface; the local hypothesis is already the localized owner-level datum
  produced upstream by
  `exists_idempotent_localizationAway_of_surjective_of_flat_of_finitePresentation`, while the
  idempotent quotient/product decomposition and the finite-cover gluing argument are derived API
  rather than parallel owner declarations. The owner property on the comparison maps is still
  `Function.Bijective`; the local complementary splitting is supplied by
  `RingHom.prod_bijective_of_isIdempotentElem`, and the quotient-localization bridge by
  `quotient_isLocalization_Away_one_sub_of_idempotent_generator`;
- primitive vs. derived:
  primitive data are the finitely generated ideal `I` and, for each `f ∈ I`, an idempotent in
  `A_f` whose associated away localization identifies `C_f`;
  derived API is the complementary quotient ideal `J`, with local bijectivity of the canonical
  away maps into `C × A ⧸ J`.

Source/core/bridge triage:
- `source-facing`: the existence theorem below;
- `core/canonical`: `Localization.awayMapₐ` for the localized comparison maps and
  `RingHom.prod_bijective_of_isIdempotentElem` together with
  `quotient_isLocalization_Away_one_sub_of_idempotent_generator` for the idempotent splitting and
  quotient-localization bridge, with target property `Function.Bijective`;
- `bridge/view`: quotient/product decompositions produced from the local idempotents. -/

-- Proof sketch: choose generators of `I`, write each localized algebra `C_f` as a localization of
-- `A_f` away from an idempotent, construct the complementary quotient ideal `J` from the
-- corresponding idempotent data, and then use the finite gluing criterion for local isomorphisms
-- on the cover by the chosen generators to extend the local product decomposition to every
-- `f ∈ I`.
/-- Lemma 15.109.3: if `I` is finitely generated and for each `f ∈ I` the localized map
`A_f → C_f` is localization away from an idempotent of `A_f`, then there exists a quotient ideal
`J ⊂ A` such that for every `f ∈ I` the localized map `A_f → (C × A ⧸ J)_f` is bijective. This
is the canonical quotient-algebra form of the source’s surjective complementary factor. -/
theorem exists_quotient_factor_of_localizationAway_idempotent_on_fg_ideal
    (I : Ideal A)
    (hI : I.FG)
    (hAway :
      ∀ ⦃f : A⦄, f ∈ I → ∃ e : A[f],
        IsIdempotentElem e ∧ IsLocalization.Away e C[f]) :
    ∃ J : Ideal A, ∀ ⦃f : A⦄, f ∈ I →
      Function.Bijective (Localization.awayMapₐ (Algebra.ofId A (C × A ⧸ J)) f) := sorry

end

/-! ### Lemma_15_109_4 (from Chap15) -/
universe u v w x

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsNoetherianRing A]
variable [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
variable [CommRing C] [Algebra A C]

variable (I : Ideal A)

local notation "Bhat" => AdicCompletion (Ideal.map (algebraMap A B) I) B

/- Domain-style sampling for Lemma 15.109.4:
- primary domain: algebraization of quotients of adic completions of finite type algebras under
  conormal control by the cotangent module of the kernel;
- sampled owner declarations:
  `AdicCompletion`,
  `Algebra.FiniteType`,
  `Ideal.Cotangent`,
  `exists_quotient_factor_of_localizationAway_idempotent_on_fg_ideal`;
- best owner abstraction: the source-facing theorem should stay on the canonical owners
  `AdicCompletion (Ideal.map (algebraMap A B) I) B`, `Algebra.FiniteType A _`, and
  `(RingHom.ker φ).Cotangent`; the local quotient-factor statement from Lemma `15.109.3` is only a
  bridge step in the proof, not a second public owner here;
- primitive data: the finite type `A`-algebra `B`, the completion surjection `φ : Bhat →ₐ[A] C`,
  and the annihilation condition on the kernel cotangent module;
- derived API: existence of a finite type `A`-algebra whose `I`-adic completion is `A`-algebra
  isomorphic to `C`.

Source/core/bridge triage:
- `source-facing`: the algebraization existence theorem below;
- `core/canonical`: `AdicCompletion`, `Algebra.FiniteType`, and `Ideal.Cotangent`;
- `bridge/view`: Lemma `15.109.3` and the idempotent-splitting argument used in the proof sketch. -/

-- Proof sketch: apply Lemma `15.109.3` to complement the local idempotent factor defined by the
-- surjection `Bhat → C`, glue the resulting finite algebra over `B`, then use henselian lifting of
-- idempotents after an étale neighborhood to split the finite algebra into two factors whose
-- `I`-adic completions are `C` and its complement.
/-- Lemma 15.109.4: let `A` be a Noetherian ring, `I` an ideal of `A`, and `B` a finite type
`A`-algebra. If `φ : Bhat →ₐ[A] C` is a surjective `A`-algebra map from the `I`-adic completion
`Bhat` of `B`, and if a power `I ^ c` annihilates the conormal module
`(RingHom.ker φ).Cotangent = J / J^2` of its kernel, then `C` is `A`-algebra isomorphic to the
`I`-adic completion of some finite type `A`-algebra. -/
theorem exists_finiteType_algebra_with_completion_algEquiv_of_kernelCotangent_annihilated
    (φ : Bhat →ₐ[A] C) (hφ : Function.Surjective φ) (c : ℕ)
    (hker :
      Ideal.map (algebraMap A Bhat) (I ^ c) ≤
        Module.annihilator Bhat (RingHom.ker φ).Cotangent) :
    ∃ (D : Type x) (_ : CommRing D) (_ : Algebra A D) (_ : Algebra.FiniteType A D),
      Nonempty (AdicCompletion (Ideal.map (algebraMap A D) I) D ≃ₐ[A] C) := sorry

end

/-! ### Lemma_15_109_5 (from Chap15) -/
open IsLocalRing

universe u

section

variable {A Ah : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/-
Domain-style sampling:
- primary domain: minimal-prime comparison between a Noetherian local ring's henselization and
  maximal-ideal completion;
- sampled owner declarations:
  `minimalPrimes`,
  `henselizationCompletionComparison`,
  `branchNumber_eq_completion_minimalPrimes_iff_radical_map_minimalPrime_isPrime`,
  `ringKrullDim_eq_ringKrullDim_maximalIdeal_adicCompletion`;
- best owner abstraction: the source-facing theorem is a `bridge/view` statement over the
  canonical comparison map `henselizationCompletionComparison A Ah`, while the minimal-prime data
  should use the owner subtype `minimalPrimes _` rather than a raw ideal together with a separate
  membership hypothesis;
- primitive data: a minimal prime `q : minimalPrimes ACompletion` whose quotient has Krull
  dimension `1`;
- derived API: existence of a minimal prime `qh : minimalPrimes Ah` whose extension to
  `ACompletion` has radical `q`.

Source/core/bridge triage:
- `source-facing`: the existence theorem below for a one-dimensional completed branch;
- `core/canonical`: `minimalPrimes`, `AdicCompletion`, `Ideal.map`, `Ideal.radical`, and the
  completion comparison owner `henselizationCompletionComparison`;
- `bridge/view`: passage from the chosen henselization to the completion along that canonical map.
-/

-- Proof sketch: reduce first to the henselian case using the standard identification of the
-- completions of `A` and `Ah`. Then apply Lemma `15.109.4` to the quotient of `ACompletion` by the
-- kernel of the localization map at `q`, use the one-dimensional minimal-prime hypothesis to
-- algebraize that quotient, and finally descend along the henselian local map to obtain a minimal
-- prime `qh` of `Ah` whose extension to the completion has radical `q`.
/-- Lemma 15.109.5: let `(A, 𝔪)` be a Noetherian local ring with chosen henselization `Ah`, let
`ACompletion = AdicCompletion (maximalIdeal A) A`, and let `q` be a minimal prime of
`ACompletion` such that `dim (ACompletion / q) = 1`. Then there exists a minimal prime `qh` of
`Ah` such that `q = √(qh ACompletion)`, where `qh ACompletion` is taken along the canonical
comparison map `Ah → ACompletion`. -/
theorem exists_minimalPrime_henselization_of_completion_minimalPrime_dim_one
    (q : minimalPrimes ACompletion) (hdim : ringKrullDim (ACompletion ⧸ q.1) = 1) :
    ∃ qh : minimalPrimes Ah,
      (q : Ideal ACompletion) =
        Ideal.radical (Ideal.map (henselizationCompletionComparison A Ah) qh) := sorry

end

/-! ### Lemma_15_109_6 (from Chap15) -/
open PrimeSpectrum IsLocalRing

universe u

section

variable {A Ah : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
private abbrev PuncturedSpectrum (R : Type u) [CommRing R] [IsLocalRing R] :=
  { p : PrimeSpectrum R // p.asIdeal ≠ maximalIdeal R }

/-
Domain-style sampling:
- primary domain: topological connectedness of punctured prime spectra for Noetherian local rings,
  compared across henselization and maximal-ideal completion;
- sampled owner declarations:
  `PrimeSpectrum`,
  `PreconnectedSpace`,
  `henselizationCompletionComparison`,
  `exists_minimalPrime_henselization_of_completion_minimalPrime_dim_one`;
- best owner abstraction: the punctured spectrum should remain a direct subtype view on the
  canonical owner `PrimeSpectrum R`, while disconnectedness is expressed by the canonical
  topological predicate `¬ PreconnectedSpace _` rather than by a parallel wrapper notion;
- primitive data: the local Noetherian ring `A`, its chosen henselization `Ah`, and the punctured
  spectrum subtype on each local ring;
- derived API: the disconnectedness comparison between the punctured spectra of `Ah` and
  `ACompletion`.

Source/core/bridge triage:
- `source-facing`: the punctured-spectrum disconnectedness equivalence below;
- `core/canonical`: `PrimeSpectrum`, `PreconnectedSpace`, `AdicCompletion`, and `maximalIdeal`;
- `bridge/view`: the canonical henselization-to-completion comparison together with the
  algebraization descent from Lemmas `15.109.4` and `15.109.5`.
-/

-- Proof sketch: identify the completion of the henselization with the completion `ACompletion`,
-- so it suffices to compare the punctured spectra of a henselian local ring and its completion.
-- Faithful flatness of the completion map gives one implication by surjectivity on punctured
-- spectra, and the converse descends a disconnection of the punctured spectrum of `ACompletion`
-- to a disconnection of the punctured spectrum of `Ah` using the algebraization steps from
-- Lemmas `15.109.4` and `15.109.5`.
/-- Lemma 15.109.6: for a Noetherian local ring `A` and a chosen henselization `Ah` of `A`, the
punctured spectrum of the maximal-ideal completion `ACompletion = AdicCompletion (maximalIdeal A) A`
is disconnected if and only if the punctured spectrum of `Ah` is disconnected. Here
“disconnected” is formalized as failure of preconnectedness of the corresponding punctured
spectrum. -/
theorem puncturedSpectrum_completion_disconnected_iff_henselization_disconnected :
    ¬ PreconnectedSpace (PuncturedSpectrum ACompletion) ↔
      ¬ PreconnectedSpace (PuncturedSpectrum Ah) := sorry

end

/-! ### Lemma_15_109_7 (from Chap15) -/
open IsLocalRing

universe u

section

variable {A Ah Ash Ahatsh : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
variable [CommRing Ahatsh] [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
variable [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/- Domain-style sampling:
- primary domain: one-dimensional Noetherian local rings, their henselizations, strict
  henselizations, and maximal-ideal completions;
- sampled owner declarations:
  `branchNumber`,
  `geometricBranchNumber`,
  `branchNumber_eq_completion_minimalPrimes_iff_radical_map_minimalPrime_isPrime`,
  `exists_minimalPrime_henselization_of_completion_minimalPrime_dim_one`,
  `geometricBranchNumber_le_completion`,
  `ringKrullDim_strictHenselization_eq`;
- best owner abstraction: the source-facing owners remain `branchNumber` and
  `geometricBranchNumber`, while the completion comparison and strict-henselization comparison are
  derived from the canonical Chapter 15 bridges already introduced in `15.109.1`, `15.109.2`,
  `15.109.5`, and `15.45.7`;
- primitive data: the one-dimensional Noetherian local ring `A`, a chosen henselization `Ah`, a
  chosen strict henselization `Ash`, and a chosen strict henselization `Ahatsh` of `ACompletion`;
- derived API: the minimal-prime count `(minimalPrimes ACompletion).encard`, the canonical
  completion comparison inequalities, and the one-dimensional quotient criterion on minimal
  primes of `ACompletion`.

Source/core/bridge triage:
- `source-facing`: the two branch-count equalities below;
- `core/canonical`: `branchNumber`, `geometricBranchNumber`, `minimalPrimes`, `ACompletion`,
  and the Krull-dimension owners;
- `bridge/view`: the completion comparison criteria from `15.109.1`, `15.109.2`, and `15.109.5`,
  together with `ringKrullDim_strictHenselization_eq`.
-/

-- Proof sketch: combine Lemmas `15.109.1`, `15.109.2`, and `15.109.5`. The dimension hypothesis on
-- `A` transfers to `ACompletion` by Lemma `15.43.1`, so every minimal prime of `ACompletion`
-- satisfies the one-dimensional quotient hypothesis needed to produce a minimal prime of `Ah`.
/-- For a one-dimensional Noetherian local ring, the number of branches equals the number of
minimal primes of the maximal-ideal completion. -/
theorem branchNumber_eq_completion_minimalPrimes_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) :
    branchNumber A Ah = (minimalPrimes ACompletion).encard := sorry

-- Proof sketch: apply the ordinary branch-count statement to the strict henselization `Ash`,
-- use Lemma `15.45.7` to keep the Krull dimension equal to `1` after strict henselization, and
-- compare `Ash` with `Ahatsh` through the canonical strict-henselization completion bridge from
-- Lemma `15.109.1`. The compatible residue-field map used to build that bridge is internal and
-- should not appear in the public API here.
/-- Lemma 15.109.7: if `(A, 𝔪)` is a one-dimensional Noetherian local ring, then the number of
geometric branches of `A` equals the number of geometric branches of its maximal-ideal
completion. -/
theorem geometricBranchNumber_eq_completion_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) :
    geometricBranchNumber A Ash =
      geometricBranchNumber ACompletion Ahatsh := sorry

end

/-! ### Lemma_15_109_8 (from Chap15) -/
open IsLocalRing

universe u

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/- Domain-style sampling:
- primary domain: Noetherian local commutative algebra of formal fibers, Nagata rings,
  henselizations, and strict henselizations;
- sampled owner declarations:
  `LocalFormalFibersHaveProperty`,
  `NagataRing`,
  `branchNumber`,
  `geometricBranchNumber`,
  `branchNumber_le_completion_minimalPrimes`,
  `geometricBranchNumber_le_completion`;
- best owner abstraction: the source-facing hypothesis should stay in the Chapter 15 owner
  `LocalFormalFibersHaveProperty`, specialized to the canonical bridge
  `Algebra.IsGeometricallyNormalProperty`. The branch counts should be expressed through the
  existing owners `branchNumber` and `geometricBranchNumber`, while the completion side uses the
  canonical object `ACompletion`;
- primitive data: the Noetherian local ring `A`, a chosen henselization or strict henselization,
  and the chosen strict henselization of `ACompletion`;
- derived API: the Nagata conclusion for `A`, the minimal-prime count of `ACompletion`, and the
  equality of branch counts.

Source/core/bridge triage:
- `source-facing`: the three clauses of Lemma `15.109.8`;
- `core/canonical`: `LocalFormalFibersHaveProperty`, `NagataRing`, `branchNumber`,
  `geometricBranchNumber`, `minimalPrimes`, and `ACompletion`;
- `bridge/view`: the completion comparison theorems from Lemma `15.109.1` and the compatible
  residue-field comparison used internally to build the strict-henselization comparison in part
  `(3)`.
-/

-- Proof sketch: geometrically normal rings are geometrically reduced, so Lemma `15.52.4` upgrades
-- the hypothesis on the formal fibers of `A` to the Nagata property.
/-- Lemma 15.109.8 (1): if the formal fibers of the Noetherian local ring `A` are geometrically
normal, then `A` is a Nagata ring. This applies in particular when `A` is excellent or
quasi-excellent. -/
theorem nagataRing_of_geometricallyNormal_formalFibers
    (hgeom :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    NagataRing A := sorry

variable {Ah : Type u}
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

-- Proof sketch: first use part `(1)` to see that `A` is Nagata. Then compare the minimal primes
-- of a chosen henselization `Ah` with those of the completion `ACompletion`: Lemma `15.109.1`
-- gives one inequality, and the Stacks argument reduces the reverse inequality to the domain case,
-- passes to the normalization, and uses normality of the completed local factors.
/-- Lemma 15.109.8 (2): if the formal fibers of the Noetherian local ring `A` are geometrically
normal, then the number of branches of `A`, computed from a chosen henselization `Ah`, equals the
number of minimal primes of its completion `ACompletion`. -/
theorem branchNumber_eq_completion_minimalPrimes_of_geometricallyNormal_formalFibers
    (hgeom :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    branchNumber A Ah = (minimalPrimes ACompletion).encard := sorry

variable {Ash Ahatsh : Type u}
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
variable [CommRing Ahatsh] [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
variable [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]

-- Proof sketch: apply the branch-count equality to the strict henselization `Ash`, using that
-- strict henselizations preserve geometrically normal formal fibers and the canonical
-- strict-henselization completion comparison from Lemma `15.109.1`; the compatible
-- residue-field comparison needed to build that bridge is internal to the proof.
/-- Lemma 15.109.8 (3): if the formal fibers of the Noetherian local ring `A` are geometrically
normal, then the number of geometric branches of `A` equals the number of geometric branches of
its completion `ACompletion`. -/
theorem geometricBranchNumber_eq_completion_of_geometricallyNormal_formalFibers
    (hgeom :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    geometricBranchNumber A Ash = geometricBranchNumber ACompletion Ahatsh := sorry

end
