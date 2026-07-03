import Mathlib.Algebra.CharP.MixedCharZero
import Mathlib.RingTheory.Localization.AtPrime.Basic
import stacks_project.Chap15.Definition_15_112_1
-- Declarations for this item will be appended below by the statement pipeline.

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
