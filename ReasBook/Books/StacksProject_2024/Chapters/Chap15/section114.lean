import Mathlib
import Mathlib.Algebra.CharP.MixedCharZero
import Mathlib.RingTheory.Localization.AtPrime.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_114_1_Krasner_s_lemma (from Chap15) -/
open IsLocalRing Polynomial

universe u

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsCompleteLocalRing A] [Ring.KrullDimLE 1 A]

/- Domain-style sampling:
- primary domain: Henselian local algebra of complete local domains, with source-facing control of
  roots under small coefficient perturbations;
- sampled owner-level declarations of the same kind:
  `Ring.KrullDimLE`,
  `Ring.krullDimLE_one_iff_of_noZeroDivisors`,
  `Ideal.mem_map_C_iff`,
  `HenselianLocalRing.is_henselian`,
  `HenselianRing.is_henselian`,
  `IsAdicComplete.henselianRing`,
  `localRing_henselian_of_isCompleteLocalRing`;
- best owner abstraction: the canonical local lifting owner is `HenselianLocalRing`, obtained here
  from completeness via `localRing_henselian_of_isCompleteLocalRing`; polynomial perturbations with
  coefficients in `𝔪 ^ n` are canonically expressed by membership in `(𝔪 ^ n).map C`,
  congruence modulo powers of the maximal ideal is canonically expressed by `SModEq`, and the
  dimension hypothesis is most canonically carried by the owner instance `[Ring.KrullDimLE 1 A]`;
- primitive data: the complete local domain `A`, the source-facing one-dimensional hypothesis
  encoded canonically by `[Ring.KrullDimLE 1 A]`, the polynomial `P`, the chosen root `α`, the
  nonvanishing derivative value `P.derivative.eval α`, and the target precision `c`;
- derived API: eventual stability of the root under perturbations lying in the polynomial ideal
  `(𝔪 ^ n).map C`.

Layer triage:
- `source-facing`: `exists_root_of_small_polynomial_perturbation`;
- `core/canonical`: `HenselianLocalRing`, `HenselianRing`, `Ideal.map`, and `SModEq`;
- `bridge/view`: `localRing_henselian_of_isCompleteLocalRing`, which upgrades complete-local data
  to the henselian owner used in the background proof strategy.
-/
local notation "𝔪" => maximalIdeal A

-- Proof sketch: use the canonical henselian owner supplied by completeness together with the
-- canonical dimension-at-most-one owner `[Ring.KrullDimLE 1 A]` to compare the nonzero derivative
-- value `P.derivative.eval α` with a sufficiently high power of `𝔪`. For `Q ∈ (𝔪 ^ n).map C`,
-- the values `(P + Q).eval α` and `(P + Q).derivative.eval α` are small perturbations of the
-- corresponding values for `P`; the henselian lifting step then produces a root congruent to `α`
-- modulo `𝔪 ^ c`. The zero-dimensional edge case allowed by `[Ring.KrullDimLE 1 A]` is harmless
-- for this conclusion, so the exact equality `ringKrullDim A = 1` is omitted from the main API.
/-- Lemma 15.114.1 (Krasner's lemma): in a complete local domain of Krull dimension at most `1`,
a simple root `α` of a polynomial `P` persists under sufficiently small perturbations of the
coefficients, with the new root congruent to `α` modulo any prescribed power of the maximal
ideal. This keeps the source mathematics while replacing the redundant exact equality
`ringKrullDim A = 1` by the canonical owner hypothesis `[Ring.KrullDimLE 1 A]`. -/
theorem exists_root_of_small_polynomial_perturbation
    (P : A[X]) {α : A} (hα : P.IsRoot α) (hderiv : P.derivative.eval α ≠ 0) (c : ℕ) :
    ∃ n : ℕ, ∀ Q : A[X], Q ∈ (𝔪 ^ n).map C →
      ∃ β : A, (P + Q).IsRoot β ∧ β ≡ α [SMOD 𝔪 ^ c] := sorry

end

/-! ### Lemma_15_114_2 (from Chap15) -/
open IsLocalRing
open scoped TensorProduct

universe u

section

variable {A Khat M : Type u}

variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field Khat] [Algebra (AdicCompletion (maximalIdeal A) A) Khat]
variable [IsFractionRing (AdicCompletion (maximalIdeal A) A) Khat]
variable [Algebra A Khat] [IsScalarTower A (AdicCompletion (maximalIdeal A) A) Khat]
variable [Algebra (FractionRing A) Khat] [IsScalarTower A (FractionRing A) Khat]
variable [Field M] [Algebra Khat M] [FiniteDimensional Khat M] [Algebra.IsSeparable Khat M]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/- Domain-style sampling:
- primary domain: finite separable extensions of fraction fields of discrete valuation rings and
  their descent along completion;
- sampled owner-level declarations:
  `Field.exists_primitive_element`,
  `Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt`,
  `IsKrasner.krasner`,
  `IsTamelyRamifiedWithRespectTo`;
- best owner abstraction: the base field owner is the canonical fraction field `FractionRing A`,
  and the completion comparison is the standard base-change object `Khat ⊗[FractionRing A] L`
  viewed through a `Khat`-algebra equivalence, with `FractionRing A → Khat` constrained by the
  canonical tower `A → ACompletion → Khat`;
- primitive data: the discrete valuation ring `A`, the chosen fraction field `Khat` of its
  maximal-ideal completion together with its compatible `A`- and `FractionRing A`-algebra
  structures, and the finite separable extension `M / Khat`;
- derived API: existence of a finite separable extension of `FractionRing A` whose base change to
  `Khat` recovers `M`.

Layer triage:
- `source-facing`: `exists_finite_separable_extension_with_completion_baseChange`;
- `core/canonical`: `FractionRing A`, `TensorProduct`, `AlgEquiv`, and the sampled mathlib
  primitive-element / approximation / Krasner owners;
- `bridge/view`: the `Khat`-algebra equivalence between the descended base change and `M`.
-/

local notation "K" => FractionRing A

-- Proof sketch: choose a primitive element `θ` for `M/Khat`, approximate its minimal polynomial
-- over the completed discrete valuation ring by a monic polynomial over `A`, apply Krasner's lemma
-- to get a nearby root in `M`, and identify the resulting simple `K`-extension `L` after tensoring
-- with `Khat`, using the completion tower to interpret the tensor product over `K`.
/-- Lemma 15.114.2: if `A` is a discrete valuation ring with fraction field `K`, `Khat` is the
fraction field of the maximal-ideal adic completion of `A` equipped with the compatible tower
`A → A^∧ → Khat` and induced map `K = FractionRing A → Khat`, and `M / Khat` is finite separable,
then there exists a finite separable extension `L / K` whose base change to `Khat` is isomorphic
to `M`. -/
theorem exists_finite_separable_extension_with_completion_baseChange :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L), Nonempty ((Khat ⊗[K] L) ≃ₐ[Khat] M) := sorry

end

/-! ### Definition_15_114_3 (from Chap15) -/
open IsLocalRing
open IsExtensionOfDiscreteValuationRings
open Ideal
open Ideal.Quotient

universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ}

/- Domain-style sampling for Definition 15.114.3:
- primary domain: mixed characteristic for discrete valuation rings and the associated absolute
  ramification index of the DVR extension `ℤ_(p) ⊂ A`;
- sampled owner declarations:
  `MixedCharZero`,
  `MixedCharZero.reduce_to_maximal_ideal`,
  `IsExtensionOfDiscreteValuationRings.ramificationIndex`,
  `Localization.localRingHom`,
  `IsLocalization.algEquiv`;
- best owner abstraction: the canonical owner for mixed characteristic is `MixedCharZero A p`,
  while the source-facing numerical invariant should be the ramification index of the canonical DVR
  extension `Localization.AtPrime (Ideal.span {(p : ℤ)}) ⊂ A`;
- primitive data: the canonical owner `MixedCharZero A p`;
- derived API: the DVR characterization theorem, the bridge identifying `(p) ⊂ ℤ` with the
  inverse image of `maximalIdeal A`, and the resulting absolute ramification index.

Source/core/bridge triage:
- `source-facing`: the DVR characterization theorem for mixed characteristic `(0, p)`;
- `core/canonical`: `MixedCharZero A p` and
  `IsExtensionOfDiscreteValuationRings.ramificationIndex`;
- `bridge/view`: the equivalence with `CharZero (FractionRing A) ∧ CharP (ResidueField A) p`, and
  the induced map `Localization.AtPrime (Ideal.span {(p : ℤ)}) → A`.

This file should therefore recall `MixedCharZero` directly, keep only the DVR characterization as
the source-facing companion, and define the absolute ramification index through the chapter DVR
extension owner rather than a parallel ideal-level specialization. -/

/- Definition 15.114.3: mixed characteristic `(0, p)` is the canonical owner
`MixedCharZero A p`. -/
#check MixedCharZero

variable {A}

/-- Definition 15.114.3, source-form companion: for a discrete valuation ring, mixed
characteristic `(0, p)` is equivalent to characteristic zero on the fraction field together with
characteristic `p` on the residue field. -/
theorem mixedCharZero_iff_fractionRing_charZero_and_residueField_charP
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (p : ℕ) [Fact p.Prime] :
    MixedCharZero A p ↔ CharZero (FractionRing A) ∧ CharP (ResidueField A) p := by
  constructor
  · intro h
    let _ : CharZero A := h.toCharZero
    constructor
    · infer_instance
    · have hmax :
          (∃ I : Ideal A, I ≠ ⊤ ∧ CharP (A ⧸ I) p) ↔
            ∃ I : Ideal A, I.IsMaximal ∧ CharP (A ⧸ I) p :=
        @MixedCharZero.reduce_to_maximal_ideal A _ p Fact.out
      rcases hmax.mp h.charP_quotient with ⟨I, hImax, hIchar⟩
      have hI : I = maximalIdeal A := IsLocalRing.eq_maximalIdeal hImax
      subst hI
      simpa [IsLocalRing.ResidueField] using hIchar
  · rintro ⟨hFrac, hResidue⟩
    let _ : CharZero (FractionRing A) := hFrac
    let _ : CharZero A := RingHom.charZero (algebraMap A (FractionRing A))
    refine ⟨?_⟩
    refine ⟨maximalIdeal A, (maximalIdeal.isMaximal A).ne_top, ?_⟩
    simpa [IsLocalRing.ResidueField] using hResidue

section AbsoluteRamificationIndex

variable (p) [Fact p.Prime] [MixedCharZero A p]

local notation "pℤ" => Ideal.span ({(p : ℤ)} : Set ℤ)

private instance intPrimeIdeal_isPrime : Ideal.IsPrime pℤ := by
  have hp : Nat.Prime p := Fact.out
  exact
    (Ideal.span_singleton_prime (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)).2
      (Int.prime_iff_natAbs_prime.2 (by simpa using hp))

private theorem span_intPrime_eq_comap_maximalIdeal :
    pℤ = Ideal.comap (Int.castRingHom A) (maximalIdeal A) := by
  let _ : CharP (ResidueField A) p :=
    (mixedCharZero_iff_fractionRing_charZero_and_residueField_charP A p).mp inferInstance |>.2
  ext z
  constructor
  · intro hz
    rw [Ideal.mem_comap]
    have hp_mem : ((p : ℤ) : A) ∈ maximalIdeal A := by
      exact eq_zero_iff_mem.mp <| by
        change ((p : ℤ) : ResidueField A) = 0
        simpa using (CharP.cast_eq_zero (ResidueField A) p)
    rcases Ideal.mem_span_singleton.mp hz with ⟨k, rfl⟩
    simpa [Int.cast_mul, mul_comm] using
      Ideal.mul_mem_left (maximalIdeal A) (((k : ℤ) : A)) hp_mem
  · intro hz
    rw [Ideal.mem_span_singleton]
    exact (CharP.intCast_eq_zero_iff (ResidueField A) p z).mp <| by
      exact eq_zero_iff_mem.mpr hz

private instance self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

private noncomputable def intPrimeLocalizationToA :
    Localization.AtPrime pℤ →+* A :=
  (Localization.algEquiv (maximalIdeal A).primeCompl A).toRingHom.comp
    (Localization.localRingHom pℤ (maximalIdeal A) (Int.castRingHom A)
      (show pℤ = Ideal.comap (Int.castRingHom A) (maximalIdeal A) from
        span_intPrime_eq_comap_maximalIdeal p))

private instance intPrimeLocalization_isDVR :
    IsDiscreteValuationRing (Localization.AtPrime pℤ) := by
  have hp : Nat.Prime p := Fact.out
  simpa using
    (IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
      (span_singleton_eq_bot.not.mpr (show (p : ℤ) ≠ 0 by
        exact_mod_cast hp.ne_zero))
      (Localization.AtPrime pℤ))

private noncomputable instance intPrimeLocalizationAlgebra :
    Algebra (Localization.AtPrime pℤ) A :=
  RingHom.toAlgebra (intPrimeLocalizationToA p)

private noncomputable instance intPrimeLocalization_isExtension :
    IsExtensionOfDiscreteValuationRings (Localization.AtPrime pℤ) A where
  toIsLocalHom := by
    let e := Localization.algEquiv (maximalIdeal A).primeCompl A
    let er := e.toRingHom
    let f :=
      Localization.localRingHom pℤ (maximalIdeal A) (Int.castRingHom A)
        (show pℤ = Ideal.comap (Int.castRingHom A) (maximalIdeal A) from
          span_intPrime_eq_comap_maximalIdeal p)
    have he : IsLocalHom er := by
      refine IsLocalHom.mk fun x hx_unit ↦ ?_
      have : IsUnit (e.symm (er x)) := by
        simpa using hx_unit.map e.symm
      simpa [er] using this
    have hf : IsLocalHom f := inferInstance
    simpa [e, er, f, intPrimeLocalizationToA] using
      (RingHom.isLocalHom_comp er f : IsLocalHom (er.comp f))
  algebraMap_injective := by
    change Function.Injective (intPrimeLocalizationToA p)
    let _ : CharZero A := (inferInstance : MixedCharZero A p).toCharZero
    refine
      (Localization.algEquiv (maximalIdeal A).primeCompl A).injective.comp ?_
    simpa [Localization.localRingHom] using
      (IsLocalization.map_injective_of_injective'
        (Ideal.primeCompl pℤ)
        A
        (Localization.AtPrime (maximalIdeal A))
        (Localization.le_comap_primeCompl_iff.mpr
          (ge_of_eq (show pℤ = Ideal.comap (Int.castRingHom A) (maximalIdeal A) from
            span_intPrime_eq_comap_maximalIdeal p)))
        (show (0 : A) ∉ Ideal.primeCompl (maximalIdeal A) by simp [Ideal.primeCompl])
        Int.cast_injective)

/-- Definition 15.114.3, numerical companion: when `A` has mixed characteristic `(0, p)`, its
absolute ramification index is the ramification index of the canonical DVR extension
`ℤ_(p) ⊂ A`. -/
noncomputable def absoluteRamificationIndex : ℕ :=
  ramificationIndex (Localization.AtPrime pℤ) A

end AbsoluteRamificationIndex

end
