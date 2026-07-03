import Mathlib
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_160_1 (from Chap10) -/
universe u

open IsLocalRing

section

variable (R : Type u) [CommRing R]

-- Domain-style sampling:
-- * primary domain: local rings and adic completion.
-- * layer: `source-facing`; this item introduces the chapter owner for complete local rings.
-- * sampled owner declarations:
--   `IsAdicComplete`,
--   `AdicCompletion.of_bijective_iff`,
--   `AdicCompletion.ofAlgEquiv`,
--   `isLocalRing_of_isAdicComplete_maximal`.
-- * owner abstraction: `IsAdicComplete (maximalIdeal R) R`.
-- * primitive data: locality and maximal-ideal adic completeness.
-- * derived API: completion-map bijectivity and the induced completion equivalence.

/-- Definition 10.160.1: a complete local ring is a local ring that is complete for the adic
topology defined by its maximal ideal. -/
class IsCompleteLocalRing : Prop extends IsLocalRing R, IsAdicComplete (maximalIdeal R) R

variable {R}

/-- Any local ring that is adically complete with respect to its maximal ideal is a complete local
ring. -/
instance [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] : IsCompleteLocalRing R := {}

end

/-! ### Lemma_10_160_2 (from Chap10) -/
universe u

open IsLocalRing AdicCompletion
open scoped TensorProduct

/-
Domain-style sampling:
* primary domain: complete local rings, finite algebras over them, and the canonical product
  decomposition indexed by primes over the maximal ideal;
* sampled owner declarations in the chapter/domain:
  `IsCompleteLocalRing`,
  `IsLocalRing.quotient`,
  `Algebra.QuasiFinite.finite_primesOver`,
  `exists_pi_algEquiv_henselianLocalRing_of_finite`,
  `completion_tensorProductOverBase_ringEquiv_pi_localRingCompletion`,
  `Ideal.primesOver`;
* best owner abstraction:
  - for part `(1)`, the chapter owner `IsCompleteLocalRing`;
  - for part `(2)`, the canonical `maximalIdeal R`-fiber `((maximalIdeal R).primesOver S)` and the
    associated completed-local factors, rather than an ad hoc existential package of unnamed rings;
* primitive data:
  - part `(1)`: a complete local ring `R` and a proper quotient ideal `I`;
  - part `(2)`: a finite `R`-algebra `S` over a Noetherian complete local base;
* derived API:
  - quotient stability of the owner `IsCompleteLocalRing`;
  - the product decomposition of `S` as the canonical product of the completed localizations at
    primes over `maximalIdeal R`, with finiteness of that owner index set supplied by the
    canonical theorem `Algebra.QuasiFinite.finite_primesOver`.

Layer classification:
* `quotient_isCompleteLocalRing` is `source-facing`;
* `finiteProductOfNoetherianCompleteLocalRings_of_finite` is `bridge/view`: it records the source
  finite-product conclusion through the chapter's canonical `primesOver`-indexed completion owner.
-/

section

variable {R : Type u} [CommRing R] [IsCompleteLocalRing R]

-- Proof sketch: the quotient of a local ring by a proper ideal is local, and maximal-ideal adic
-- completeness descends along quotient maps.
/-- Lemma 10.160.2 (1): if `I` is a proper ideal of a complete local ring `R`, then the quotient
`R ⧸ I` is again a complete local ring. -/
theorem quotient_isCompleteLocalRing (I : Ideal R) (hI : I ≠ ⊤) :
    IsCompleteLocalRing (R ⧸ I) := sorry

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
variable {S : Type u} [CommRing S] [Algebra R S] [Module.Finite R S]

attribute [local instance high] Algebra.TensorProduct.leftAlgebra IsScalarTower.right

local notation "Rₚ" => Localization.AtPrime (maximalIdeal R)
local notation "Sₚ" => Localization (Algebra.algebraMapSubmonoid S (Ideal.primeCompl (maximalIdeal R)))
local notation "pSₚ" => Ideal.map (algebraMap Rₚ Sₚ) (maximalIdeal Rₚ)
local notation "Rₚ^" => AdicCompletion (maximalIdeal Rₚ) Rₚ
local notation "Sₚ^" => AdicCompletion pSₚ Sₚ
private abbrev CompletionFactors : Type u :=
  ∀ q : (maximalIdeal R).primesOver S,
    AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1)
private abbrev closedPoint : PrimeSpectrum R :=
  ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩

omit [IsNoetherianRing R] in
private theorem localizedBase_isAdicComplete :
    IsAdicComplete (maximalIdeal Rₚ) Rₚ := by
  rw [← IsAdicComplete.congr_ringEquiv
    (maximalIdeal Rₚ)
    ((IsLocalization.algEquiv (maximalIdeal R).primeCompl Rₚ R).toRingEquiv)]
  simpa [IsLocalRing.map_ringEquiv_maximalIdeal] using
    (inferInstance : IsAdicComplete (maximalIdeal R) R)

-- Proof sketch: specialize Lemma `10.97.8` to the closed point `p = maximalIdeal R`. The local
-- ring `R_(maximalIdeal R)` identifies canonically with `R`, and since `R` is complete local, so
-- does its maximal-ideal completion. After these owner-level identifications, the tensor term
-- `R^∧ ⊗[R] S` reduces via `TensorProduct.lid` to `S`. The finiteness of the index owner
-- `((maximalIdeal R).primesOver S)` is already the canonical theorem
-- `Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) (maximalIdeal R)`.
/-- Lemma 10.160.2 (2): for a finite algebra over a Noetherian complete local ring, the target
ring is canonically the product of the completed localizations at the primes lying over the
maximal ideal of the base, indexed by the owner set `((maximalIdeal R).primesOver S)`. -/
noncomputable def finiteProductOfNoetherianCompleteLocalRings_of_finite :
    S ≃+* ∀ q : (maximalIdeal R).primesOver S,
      AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) := by
  change S ≃+* CompletionFactors
  letI : IsAdicComplete (maximalIdeal Rₚ) Rₚ := localizedBase_isAdicComplete
  letI : IsScalarTower R Rₚ^ Rₚ^ := IsScalarTower.right
  let eBase : R ≃ₐ[R] Rₚ^ :=
    (IsLocalization.algEquiv (maximalIdeal R).primeCompl Rₚ R).symm.trans <|
      (AdicCompletion.ofAlgEquiv (maximalIdeal Rₚ)).restrictScalars R
  let eTensor : S ≃ₐ[R] Rₚ^ ⊗[R] S :=
    (Algebra.TensorProduct.lid R S).symm.trans
      (Algebra.TensorProduct.congr eBase (show S ≃ₐ[R] S from AlgEquiv.refl))
  let ePi : Rₚ^ ⊗[R] S ≃+* CompletionFactors :=
    completion_tensorProductOverBase_ringEquiv_pi_localRingCompletion S closedPoint
  exact eTensor.toRingEquiv.trans <|
    ePi

end

/-! ### Lemma_10_160_3 (from Chap10) -/
universe u

open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R]

-- Domain-style sampling:
-- * primary domain: complete local rings and maximal-ideal adic completion.
-- * layer: `bridge/view`; the source statement is the Noetherianity consequence of the chapter
--   owner `IsCompleteLocalRing`, obtained by comparing `R` with its canonical completion.
-- * sampled declarations:
--   `IsCompleteLocalRing`,
--   `AdicCompletion.ofAlgEquiv`,
--   `adicCompletion_isNoetherian_and_isAdicComplete`,
--   `isNoetherianRing_of_ringEquiv`.
-- * owner abstraction: `IsCompleteLocalRing R`; the raw hypothesis
--   `IsAdicComplete (maximalIdeal R) R` is derived from this owner and should not remain the main
--   public interface here.
-- * primitive data: the ring `R`, the complete-local owner structure, and the finite-generation
--   hypothesis on `maximalIdeal R`.
-- * derived API: Noetherianity of the maximal-ideal adic completion and the canonical completion
--   equivalence back to `R`.

-- Proof sketch: apply Lemma `10.97.5` to the ideal `maximalIdeal R`. The quotient
-- `R ⧸ maximalIdeal R` is the residue field of the local ring `R`, hence Noetherian. Since `R`
-- is complete for the `maximalIdeal R`-adic topology by hypothesis, the canonical map
-- `R → AdicCompletion (maximalIdeal R) R` is bijective, so the Noetherianity of the completion
-- transfers back to `R`.
/-- Lemma 10.160.3: a complete local ring whose maximal ideal is finitely generated is
Noetherian. -/
theorem isNoetherianRing_of_isCompleteLocalRing_of_maximalIdeal_fg
    (hfg : (maximalIdeal R).FG) : IsNoetherianRing R := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  let _ : IsNoetherianRing (R ⧸ maximalIdeal R) := by infer_instance
  let _ : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) :=
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal R) hfg).1
  exact isNoetherianRing_of_ringEquiv (AdicCompletion (maximalIdeal R) R)
    (AdicCompletion.ofAlgEquiv (maximalIdeal R)).symm.toRingEquiv

end

/-! ### Definition_10_160_4 (from Chap10) -/
universe u

open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R]

/-
Source/core/bridge triage:
* source-facing: `IsCoefficientRing R Λ`, the textbook notion of a coefficient ring inside a
  complete local ring;
* core/canonical: `IsCompleteLocalRing Λ`, the chapter owner for maximal-ideal adic completeness
  of the subring `Λ`;
* bridge/view: the local inclusion `Λ.subtype : Λ →+* R` together with the induced residue-field
  map.

Primitive data here are exactly the extra source clauses beyond the complete-local owner on `Λ`:
the local inclusion into `R`, the bijectivity on residue fields, and the identification of the
maximal ideal with the ideal generated by the residue characteristic. The separate
`IsAdicComplete (maximalIdeal Λ) Λ` field was duplicate derived API and should be recovered from
`IsCompleteLocalRing Λ` instead of stored as primitive public data.
-/
/-- Definition 10.160.4: a subring `Λ ⊆ R` of a complete local ring is a coefficient ring when
`Λ` is itself local and complete for its maximal-ideal adic topology, its maximal ideal is the
intersection with the maximal ideal of `R`, the induced map on residue fields is bijective, and
this maximal ideal is generated by the residue characteristic `p` of `R`. -/
class IsCoefficientRing (Λ : Subring R) : Prop
    extends IsCompleteLocalRing Λ, IsLocalHom (Λ.subtype : Λ →+* R)
    where
  residueField_bijective :
    Function.Bijective (ResidueField.map (Λ.subtype : Λ →+* R))
  maximalIdeal_eq_span_residueChar :
    maximalIdeal Λ = Ideal.span ({(ringChar (ResidueField R) : Λ)} : Set Λ)

variable {R}

-- Proof sketch: a coefficient ring identifies its maximal ideal with the principal ideal generated
-- by the residue characteristic, so principality is immediate from the standard singleton-span
-- instance.
/-- The maximal ideal of a coefficient ring is principal, generated by the residue characteristic
of the ambient residue field. -/
instance (Λ : Subring R) [h : IsCoefficientRing R Λ] : (maximalIdeal Λ).IsPrincipal := by
  classical
  rw [h.maximalIdeal_eq_span_residueChar]
  infer_instance

end

/-! ### Definition_10_160_5 (from Chap10) -/
universe u

open Ideal IsLocalRing Ideal.Quotient

section

variable (R : Type u) [CommRing R]

-- Domain-style sampling:
-- * primary domain: mixed-characteristic complete local rings and discrete valuation rings.
-- * layer: `source-facing`; this item defines the chapter notion of a Cohen ring.
-- * sampled owner declarations:
--   `IsCompleteLocalRing`,
--   `IsDiscreteValuationRing`,
--   `IsCoefficientRing.maximalIdeal_eq_span_residueChar`,
--   `IsLocalRing.maximalIdeal`,
--   `PadicInt.maximalIdeal_eq_span_p`.
-- * owner abstraction: `IsCompleteLocalRing R` is the canonical owner for maximal-ideal adic
--   completeness in this chapter, so completeness should not remain a separate primitive field.
-- * primitive data: the DVR structure and the statement that the maximal ideal is generated by
--   the canonical residue characteristic.
-- * derived API: the textbook existential prime-generator formulation and the constructor from
--   that formulation back to the source-facing owner.

/-- Definition 10.160.5: a Cohen ring is a complete discrete valuation ring whose maximal ideal is
generated by the image of a prime natural number. -/
class IsCohenRing : Prop extends IsDomain R, IsDiscreteValuationRing R, IsCompleteLocalRing R
    where
  maximalIdeal_eq_span_residueChar :
    maximalIdeal R = Ideal.span {(ringChar (ResidueField R) : R)}

variable {R}

private theorem ringChar_residueField_eq_of_maximalIdeal_eq_span_natPrime [IsDomain R]
    [IsDiscreteValuationRing R] {p : ℕ} (hp : Nat.Prime p)
    (hmax : maximalIdeal R = Ideal.span {(p : R)}) :
    ringChar (ResidueField R) = p := by
  apply CharP.ringChar_of_prime_eq_zero hp
  change Ideal.Quotient.mk (maximalIdeal R) p = 0
  exact eq_zero_iff_mem.mpr <| by
    rw [hmax]
    exact Ideal.subset_span (by simp)

namespace IsCohenRing

/-- The residue characteristic element of a Cohen ring lies in its maximal ideal. -/
theorem residueChar_mem_maximalIdeal [IsCohenRing R] :
    (ringChar (ResidueField R) : R) ∈ maximalIdeal R := by
  rw [IsCohenRing.maximalIdeal_eq_span_residueChar]
  exact Ideal.subset_span (by simp)

/-- The residue characteristic element of a Cohen ring is not a unit. -/
theorem residueChar_not_isUnit [IsCohenRing R] :
    ¬ IsUnit (ringChar (ResidueField R) : R) := by
  simpa [IsLocalRing.mem_maximalIdeal] using residueChar_mem_maximalIdeal

/-- The residue characteristic of a Cohen ring is nonzero, hence prime. -/
theorem residueChar_ne_zero [IsCohenRing R] : ringChar (ResidueField R) ≠ 0 := by
  intro hzero
  apply IsDiscreteValuationRing.not_a_field R
  rw [IsCohenRing.maximalIdeal_eq_span_residueChar, hzero]
  simp

/-- The residue characteristic of a Cohen ring is prime. -/
theorem residueChar_prime [IsCohenRing R] : Nat.Prime (ringChar (ResidueField R)) := by
  apply CharP.char_prime_of_ne_zero (ResidueField R)
  exact residueChar_ne_zero

instance instFactResidueCharPrime [IsCohenRing R] :
    Fact (Nat.Prime (ringChar (ResidueField R))) :=
  ⟨residueChar_prime⟩

/-- Companion reformulation of the defining prime-generator condition in textbook existential
form. -/
theorem maximalIdeal_eq_span_natPrime [IsCohenRing R] :
    ∃ p : ℕ, Nat.Prime p ∧ maximalIdeal R = Ideal.span {(p : R)} :=
  ⟨ringChar (ResidueField R), residueChar_prime, IsCohenRing.maximalIdeal_eq_span_residueChar⟩

/-- The quotient of a Cohen ring by the ideal generated by its residue characteristic is its
residue field. -/
noncomputable def quotientSpanResidueCharRingEquiv [IsCohenRing R] :
    (R ⧸ Ideal.span {(ringChar (ResidueField R) : R)}) ≃+* ResidueField R :=
  Ideal.quotEquivOfEq IsCohenRing.maximalIdeal_eq_span_residueChar.symm

/-- A complete discrete valuation ring whose maximal ideal is generated by a prime natural number
is a Cohen ring. -/
theorem of_maximalIdeal_eq_span_natPrime [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] {p : ℕ} (hp : Nat.Prime p)
    (hmax : maximalIdeal R = Ideal.span {(p : R)}) :
    IsCohenRing R :=
  { maximalIdeal_eq_span_residueChar := by
      rw [ringChar_residueField_eq_of_maximalIdeal_eq_span_natPrime hp hmax]
      exact hmax }

end IsCohenRing

end

/-! ### Lemma_10_160_6 (from Chap10) -/
universe u

open Ideal IsLocalRing

section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p]

/- Domain-style sampling:
* primary domain: mixed-characteristic local commutative algebra of Cohen rings and residue
  fields;
* source-facing layer: existence of a Cohen ring whose quotient by `(p)` is identified with `k`;
* sampled owner declarations:
  - `IsCohenRing`,
  - `IsCohenRing.maximalIdeal_eq_span_residueChar`,
  - `IsCohenRing.quotientSpanResidueCharRingEquiv`,
  - `IsLocalRing.ResidueField`;
* owner abstraction: `IsCohenRing Λ` is the canonical owner; the quotient by `(p)` is the
  source-facing bridge, while the maximal-ideal equality and residue-field identification are
  derived from the owner;
* primitive data: a Cohen ring `Λ` together with a quotient-ring equivalence
  `(Λ ⧸ Ideal.span {(p : Λ)}) ≃+* k`;
* derived API: the residue-field equivalence `ResidueField Λ ≃+* k` and the equality
  `maximalIdeal Λ = Ideal.span {(p : Λ)}`.
-/

-- Proof sketch: start from the canonical Cohen ring `ℤ_[p]` for `𝔽_p`, then apply the residue
-- field extension construction from Lemma `10.159.1` to obtain a flat local `ℤ_[p]`-algebra with
-- residue field `k`. Completing that algebra preserves the quotient by powers of `p`, yields a
-- complete Noetherian local ring with maximal ideal generated by `p`, and the one-dimensional
-- regular-local criterion identifies the completion as a discrete valuation ring, hence a Cohen
-- ring. The public conclusion is stated on the quotient `Λ ⧸ (p)`, leaving the maximal-ideal
-- generator equality as derived API from the Cohen-ring owner.
/-- Lemma 10.160.6: for a prime number `p` and a field `k` of characteristic `p`, there exists a
Cohen ring `Λ` such that `Λ ⧸ Ideal.span {(p : Λ)}` is isomorphic to `k`. -/
theorem exists_cohenRing_with_quotient_by_prime_ringEquiv :
    ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ),
      Nonempty ((Λ ⧸ Ideal.span {(p : Λ)}) ≃+* k) := sorry

end

/-! ### Lemma_10_160_7 (from Chap10) -/
universe u

open Ideal IsLocalRing

section

variable {Λ : Type u} [CommRing Λ] [IsCohenRing Λ]

local notation "p" => ringChar (ResidueField Λ)

/- Domain-style sampling:
* primary domain: formally smooth algebras arising from quotient rings of mixed-characteristic
  complete discrete valuation rings;
* source/core/bridge triage:
  - source-facing: the formal smoothness of the canonical `ZMod (p ^ n)`-algebra
    `Λ ⧸ (p ^ n)`;
  - core/canonical: `Algebra.FormallySmooth`, `IsCohenRing.maximalIdeal_eq_span_residueChar`,
    `CharP.quotient`, and `ZMod.algebra`;
  - bridge/view: the ring-hom reformulation via `RingHom.formallySmooth_algebraMap`, and the
    textbook prime generator `p = ringChar (ResidueField Λ)`;
* sampled owner declarations:
  `Algebra.FormallySmooth`,
  `IsCohenRing`,
  `CharP.quotient`,
  `ZMod.algebra`,
  `IsCohenRing.of_maximalIdeal_eq_span_natPrime`,
  `IsCohenRing.maximalIdeal_eq_span_residueChar`,
  `RingHom.formallySmooth_algebraMap`;
* best owner abstraction: `Algebra.FormallySmooth R S` is the conclusion owner abstraction, while
  `IsCohenRing Λ` is the primitive source-ring owner; the chosen prime generator and
  ring-hom formulation are derived API, not primitive public surface;
* primitive data: the Cohen-ring owner and the quotient ring
  `Λ ⧸ Ideal.span {((p ^ n) : Λ)}`;
* derived API: the quotient characteristic theorem, the local `ZMod`-algebra elaboration, and the
  algebra-map bridge to `RingHom.FormallySmooth`.
-/

/-- The quotient of a Cohen ring by the ideal generated by the `n`-th power of its residue
characteristic has characteristic that same prime power. -/
theorem quotient_charP_residueCharPow (n : ℕ+) :
    CharP (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) (p ^ (n : ℕ)) := by
  sorry

local instance quotientResidueCharPowCharP (n : ℕ+) :
    CharP (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) (p ^ (n : ℕ)) :=
  quotient_charP_residueCharPow n

noncomputable local instance quotientResidueCharPowAlgebra (n : ℕ+) :
    Algebra (ZMod (p ^ (n : ℕ))) (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) :=
  ZMod.algebra _ _

-- Proof sketch: for `n = 1`, the quotient is the residue field of `Λ`, so the characteristic-`p`
-- field criterion gives formal smoothness over `ZMod p`. For the inductive step, pass from
-- `Λ ⧸ (p ^ n)` to `Λ ⧸ (p ^ (n + 1))` using the square-zero extension criterion for formal
-- smoothness applied to the ideal generated by `p ^ n`.
/-- Lemma 10.160.7: if `Λ` is a Cohen ring and `p = ringChar (ResidueField Λ)`, then the
canonical `ZMod (p ^ n)`-algebra `Λ ⧸ (p ^ n)` is formally smooth for every positive
integer `n`. -/
theorem cohenRing_zmodPow_quotient_formallySmooth (n : ℕ+) :
    Algebra.FormallySmooth (ZMod (p ^ (n : ℕ)))
      (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) := by
  sorry

/-- Companion bridge: the canonical algebra map `ZMod (p ^ n) → Λ ⧸ (p ^ n)` is formally smooth
in the ring-hom sense. -/
theorem cohenRing_zmodPow_quotient_algebraMap_formallySmooth (n : ℕ+) :
    RingHom.FormallySmooth
      (algebraMap (ZMod (p ^ (n : ℕ))) (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)})) := by
  exact RingHom.formallySmooth_algebraMap.mpr (cohenRing_zmodPow_quotient_formallySmooth n)

end

/-! ### Theorem_10_160_8_Cohen_structure_theorem (from Chap10) -/
universe u

open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R]

/- Domain-style sampling:
* primary domain: Cohen structure and finite-variable formal power series presentations of complete
  local rings.
* source/core/bridge triage:
  - `source-facing`: the textbook quotient presentation of `R` by a finite-variable power series
    ring over either a field or a Cohen ring;
  - `core/canonical`: `MvPowerSeries σ A` with `[Finite σ]`, together with the chapter owners
    `IsCoefficientRing` and `IsCohenRing`;
  - `bridge/view`: the quotient presentation obtained from a surjective power-series map via
    `RingHom.quotientKerEquivOfSurjective`.
* sampled owner declarations:
  `IsCoefficientRing`,
  `IsCohenRing`,
  `isNoetherianRing_mvPowerSeries_of_finite`,
  `RingHom.quotientKerEquivOfSurjective`.
* best owner abstraction: the finite-index power series ring `MvPowerSeries σ A` is the canonical
  owner for “formal power series in finitely many variables”; the quotient model is derived API
  from a surjective map out of that owner.
* primitive data: a finite index type `σ`, a coefficient field or Cohen ring, and a surjective
  ring homomorphism `MvPowerSeries σ _ →+* R`.
* derived API: the ideal-kernel quotient presentation.
-/

-- Proof sketch: choose a coefficient ring `Λ₀ ⊆ R`. If the residue field has characteristic zero,
-- `Λ₀` is a field and the chosen generators of `maximalIdeal R` define a surjective map
-- `MvPowerSeries σ Λ₀ →+* R` for a finite index type `σ`; passing to the kernel identifies `R`
-- with the corresponding
-- quotient. In positive residue characteristic, pick a Cohen ring mapping into `R` via the
-- coefficient-ring construction and argue in the same way.
/-- Primitive Cohen-structure presentation: under the coefficient-ring and finite-generation
hypotheses, `R` admits a surjective map from a finite-index formal power series ring over either a
field or a Cohen ring. The quotient-by-kernel presentation is derived from this owner theorem via
`RingHom.quotientKerEquivOfSurjective`. -/
theorem exists_surjective_mvPowerSeries_of_exists_coefficientRing_of_maximalIdeal_fg
    (hcoeff : ∃ Λ₀ : Subring R, IsCoefficientRing R Λ₀) (hfg : (maximalIdeal R).FG) :
    ∃ (σ : Type u) (_ : Finite σ),
      (∃ (k : Type u) (_ : Field k) (φ : MvPowerSeries σ k →+* R), Function.Surjective φ) ∨
        ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ)
          (φ : MvPowerSeries σ Λ →+* R), Function.Surjective φ := sorry

-- Proof sketch: apply the primitive surjective-presentation theorem above and identify the target
-- with the quotient by the kernel of the chosen surjective map using
-- `RingHom.quotientKerEquivOfSurjective`.
/-- Theorem 10.160.8 (Cohen structure theorem): if a complete local ring `R` has a coefficient
ring and its maximal ideal is finitely generated, then `R` is isomorphic to a quotient of a
finite-variable formal power series ring over either a field or a Cohen ring. -/
theorem exists_mvPowerSeries_quotient_of_exists_coefficientRing_of_maximalIdeal_fg
    (hcoeff : ∃ Λ₀ : Subring R, IsCoefficientRing R Λ₀) (hfg : (maximalIdeal R).FG) :
    ∃ (σ : Type u) (_ : Finite σ),
      (∃ (k : Type u) (_ : Field k) (I : Ideal (MvPowerSeries σ k)),
        Nonempty ((MvPowerSeries σ k ⧸ I) ≃+* R)) ∨
        ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ)
          (I : Ideal (MvPowerSeries σ Λ)),
          Nonempty ((MvPowerSeries σ Λ ⧸ I) ≃+* R) := by
  rcases exists_surjective_mvPowerSeries_of_exists_coefficientRing_of_maximalIdeal_fg R hcoeff hfg with
    ⟨σ, hσ, hσR⟩
  refine ⟨σ, hσ, ?_⟩
  rcases hσR with hfield | hcohen
  · rcases hfield with ⟨k, _, φ, hφ⟩
    left
    refine ⟨k, inferInstance, RingHom.ker φ, ?_⟩
    exact ⟨RingHom.quotientKerEquivOfSurjective hφ⟩
  · rcases hcohen with ⟨Λ, _, _, φ, hφ⟩
    right
    refine ⟨Λ, inferInstance, inferInstance, RingHom.ker φ, ?_⟩
    exact ⟨RingHom.quotientKerEquivOfSurjective hφ⟩

end

/-! ### Remark_10_160_9 (from Chap10) -/
universe u

section

/- Domain-style sampling:
- primary domain: Cohen structure and universal catenarity for Noetherian complete local rings.
- sampled owner declarations:
  `IsCompleteLocalRing`,
  `IsRegularLocalRing`,
  `exists_mvPowerSeries_quotient_of_exists_coefficientRing_of_maximalIdeal_fg`,
  `universallyCatenaryRing_of_cohenMacaulayRing`.
- best owner abstraction: the ambient owners are `IsCompleteLocalRing R`,
  `IsRegularLocalRing R`, and `UniversallyCatenaryRing R`; the regular-local quotient statement is
  a `bridge/view` corollary of the Cohen-structure owner theorem, not a second source owner.
- primitive data: the complete-local and Noetherian owner hypotheses on `R`.
- derived API: finite-variable power-series support instances, the regular-local quotient
  presentation, and universal catenarity.

Source/core/bridge triage:
* `source-facing`: the remark-level corollary that a Noetherian complete local ring is a quotient
  of a regular local ring, and hence universally catenary;
* `core/canonical`: `IsCompleteLocalRing`, `IsRegularLocalRing`, and `UniversallyCatenaryRing`;
* `bridge/view`: the quotient presentation extracted from
  `exists_mvPowerSeries_quotient_of_exists_coefficientRing_of_maximalIdeal_fg`.
-/

/-- Formal power series in finitely many variables over a complete local ring form a complete local
ring. -/
instance mvPowerSeries_fin_isCompleteLocalRing (R : Type u) [CommRing R]
    [IsCompleteLocalRing R] (d : ℕ) :
    IsCompleteLocalRing (MvPowerSeries (Fin d) R) := sorry

/-- Formal power series in finitely many variables over a regular local ring form a regular local
ring. -/
instance mvPowerSeries_fin_isRegularLocalRing (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (d : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin d) R) := sorry

-- Proof sketch: view the maximal ideal as generated by the coordinate variables and compute the
-- Krull dimension inductively, removing one power-series variable at a time.
/-- The Krull dimension of the `d`-variable formal power series ring over a field is `d`. -/
theorem ringKrullDim_mvPowerSeries_fin_field (k : Type u) [Field k] (d : ℕ) :
    ringKrullDim (MvPowerSeries (Fin d) k) = d := sorry

-- Proof sketch: apply the Cohen structure theorem. In equal characteristic, the source is a
-- formal power series ring over the residue field; in mixed characteristic, it is a formal power
-- series ring over a Cohen ring. Both source rings are regular local, and the structure theorem
-- identifies `R` with a quotient by a closed ideal.
/-- Remark 10.160.9: the Cohen structure theorem presents every Noetherian complete local ring as a
quotient of a regular local ring. -/
theorem exists_regularLocalRing_quotient_of_isCompleteLocalRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsCompleteLocalRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S) (I : Ideal S),
      Nonempty ((S ⧸ I) ≃+* R) :=
  sorry

-- Proof sketch: choose a regular local ring `S` and an ideal `I` with `S ⧸ I ≃+* R` from the
-- quotient presentation above. Lemma `10.105.9` makes the regular local ring `S` universally
-- catenary, and universal catenarity descends to the quotient `S ⧸ I`, hence to `R`.
/-- A Noetherian complete local ring is universally catenary. -/
theorem universallyCatenaryRing_of_isCompleteLocalRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsCompleteLocalRing R] :
    UniversallyCatenaryRing R := sorry

end

/-! ### Lemma_10_160_10 (from Chap10) -/
universe u v

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsCompleteLocalRing R] [IsRegularLocalRing R]

/- Domain-style sampling:
* primary domain: Cohen-structure presentations of complete regular local rings.
* source/core/bridge triage:
  - `source-facing`: the intrinsic equal-characteristic power-series presentation of `R`;
  - `core/canonical`: the finite-index owner `MvPowerSeries σ A` with `[Finite σ]`;
  - `bridge/view`: the chosen coefficient-field presentation via `Algebra k R` and the canonical
    residue-field map `ResidueField.map (algebraMap k R)`.
* sampled owner declarations:
  `IsRegularLocalRing`,
  `exists_mvPowerSeries_quotient_of_exists_coefficientRing_of_maximalIdeal_fg`,
  `isNoetherianRing_mvPowerSeries_of_finite`,
  `ResidueField.map`.
* best owner abstraction: the chapter already treats “formal power series in finitely many
  variables” through `MvPowerSeries σ _` with `[Finite σ]`, so the target statements should not
  keep the lower-level `Fin d` encoding as their main public surface.
* primitive data: the regular-complete-local owner on `R`, and in the bridge theorem a field
  `k` with a residue-field isomorphism.
* derived API: any `Fin d` presentation obtained from the finite-index owner via
  `Fintype.equivFin`.
-/

-- Proof sketch: in equal characteristic, the Cohen structure theorem provides a coefficient field
-- mapping isomorphically to `ResidueField R`. Applying the power-series presentation to a regular
-- system of parameters then identifies `R` with a finite-variable formal power series ring over
-- that field, hence over `ResidueField R`.
/-- Lemma 10.160.10 (1): if a complete regular local ring has the same characteristic as its
residue field, then it is isomorphic to a finite-variable formal power series ring over its
residue field. -/
theorem exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic
    (heqchar : ringChar R = ringChar (ResidueField R)) :
    ∃ (σ : Type) (_ : Finite σ), Nonempty (MvPowerSeries σ (ResidueField R) ≃+* R) := sorry

-- Proof sketch: choose elements of `maximalIdeal R` whose classes form a basis of the cotangent
-- space over `k`, and send the variables of a finite-index power series ring `MvPowerSeries σ k`
-- to these elements. Since both rings are complete for the maximal-ideal topology, the induced
-- continuous `k`-algebra map is surjective; regularity forces injectivity by the dimension count.
/-- Lemma 10.160.10 (2): if `k → R` induces an isomorphism onto the residue field of a complete
regular local ring, then `R` is `k`-algebra isomorphic to a finite-variable formal power series
ring over `k`. -/
theorem exists_algEquiv_mvPowerSeries_of_residueField_bijective
    (k : Type v) [Field k] [Algebra k R]
    (hres : Function.Bijective (ResidueField.map (algebraMap k R))) :
    ∃ (σ : Type) (_ : Finite σ), Nonempty (MvPowerSeries σ k ≃ₐ[k] R) := sorry

end

/-! ### Lemma_10_160_11 (from Chap10) -/
universe u

open IsLocalRing

section

-- Domain-style sampling:
-- * primary domain: Cohen structure for Noetherian complete local domains.
-- * source/core/bridge triage:
--   - source-facing: existence of a finite regular complete local subring `R₀ ⊆ R` whose
--     inclusion is local, induces an isomorphism on residue fields, and whose abstract
--     regular-complete-local structure admits the source-level power-series/Cohen-ring
--     presentation;
--   - core/canonical: `IsCompleteLocalRing`, `IsRegularLocalRing`, `IsLocalHom`,
--     `ResidueField.map`, and `Module.Finite`;
--   - bridge/view: the power-series/Cohen-ring model of an arbitrary regular complete local ring.
-- * sampled owner declarations:
--   `IsCompleteLocalRing`,
--   `IsRegularLocalRing`,
--   `IsCohenRing`,
--   `exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic`.
-- * owner abstraction: there is no upstream owner for the full source-facing package “finite
--   regular complete local subring with residue-field isomorphism”, so the theorem should expose
--   exactly those canonical primitive clauses instead of collapsing to the stricter owner
--   `IsCoefficientRing`.
-- * primitive data: the complete-local and regular-local owners on `R₀`, the local inclusion
--   `R₀ ↪ R`, the induced residue-field bijectivity, and the module-finite inclusion into `R`.
-- * derived API: the source-facing power-series/Cohen-ring alternative on `R₀`.

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/-- Helper for Lemma 10.160.11: a finite-index power-series presentation can be reindexed along
`Fintype.equivFin` to a `Fin d`-indexed presentation. -/
lemma exists_fin_powerSeries_model_of_finite_index_model
    {A S : Type u} [CommRing A] [CommRing S]
    (h : ∃ (σ : Type) (_ : Finite σ), Nonempty (MvPowerSeries σ A ≃+* S)) :
    ∃ d : ℕ, Nonempty (MvPowerSeries (Fin d) A ≃+* S) := by
  classical
  rcases h with ⟨σ, hσ, ⟨e⟩⟩
  let _ : Fintype σ := Fintype.ofFinite σ
  -- Reindex the finite variable set by the canonical equivalence with `Fin (card σ)`.
  refine ⟨Fintype.card σ, ?_⟩
  refine ⟨?_⟩
  exact (MvPowerSeries.renameEquiv A (Fintype.equivFin σ).symm).toRingEquiv.trans e

-- Proof sketch: the mixed-characteristic source proof should choose a Cohen ring lifting the
-- residue field and then apply the regular local structure theorem over that coefficient ring.
/-- Helper for Lemma 10.160.11: the mixed-characteristic branch of the regular complete local
power-series presentation should produce a `Fin d`-indexed model over a Cohen ring. -/
theorem exists_powerSeries_model_of_regular_completeLocalRing_mixedChar
    (R₀ : Type u) [CommRing R₀] [IsCompleteLocalRing R₀] [IsRegularLocalRing R₀]
    (hmixed : ringChar R₀ ≠ ringChar (ResidueField R₀)) :
    ∃ d : ℕ, ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ),
      Nonempty (MvPowerSeries (Fin d) Λ ≃+* R₀) :=
  -- TODO: prove the mixed-characteristic branch source-faithfully by exhibiting a Cohen ring
  -- lifting `ResidueField R₀` and then applying the regular complete local structure theorem over
  -- that coefficient ring.
  sorry

-- Proof sketch: use Lemma `10.160.10` in equal characteristic, and isolate the mixed
-- characteristic branch behind the dedicated Cohen-ring helper above.
/-- Helper for Lemma 10.160.11: a regular complete local ring is a finite-variable formal power
series ring over either its residue field or a Cohen ring. -/
theorem exists_powerSeries_model_of_regular_completeLocalRing
    (R₀ : Type u) [CommRing R₀] [IsCompleteLocalRing R₀] [IsRegularLocalRing R₀] :
    ∃ d : ℕ,
      Nonempty (MvPowerSeries (Fin d) (ResidueField R₀) ≃+* R₀) ∨
        ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ),
          Nonempty (MvPowerSeries (Fin d) Λ ≃+* R₀) := by
  by_cases heqchar : ringChar R₀ = ringChar (ResidueField R₀)
  · -- In equal characteristic, Lemma `10.160.10` already gives the model over the residue field.
    rcases
        exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic
          (R := R₀) heqchar with
      ⟨σ, hσ, hmodel⟩
    rcases
        exists_fin_powerSeries_model_of_finite_index_model
          (A := ResidueField R₀) (S := R₀) ⟨σ, hσ, hmodel⟩ with
      ⟨d, hmodelFin⟩
    exact ⟨d, Or.inl hmodelFin⟩
  · -- The mixed-characteristic branch is delegated to the dedicated Cohen-ring presentation
    -- helper so the public theorem stays a clean case split.
    rcases
        exists_powerSeries_model_of_regular_completeLocalRing_mixedChar
          (R₀ := R₀) heqchar with
      ⟨d, Λ, hΛ, hCohen, hmodel⟩
    exact ⟨d, Or.inr ⟨Λ, hΛ, hCohen, hmodel⟩⟩

-- Proof sketch: the source-faithful construction chooses a coefficient field or Cohen ring inside
-- `R`, adjoins a system of parameters, and uses the Stacks finiteness and injectivity lemmas to
-- identify the source with a finite regular complete local subring of `R`.
/-- Helper for Lemma 10.160.11: construct the finite regular complete local subring package before
adding the power-series-model clause. -/
theorem exists_finite_regular_completeLocalSubring_without_model :
    ∃ (R₀ : Subring R) (_ : IsCompleteLocalRing R₀) (_ : IsRegularLocalRing R₀)
      (_ : IsLocalHom (R₀.subtype : R₀ →+* R))
      (_ : Function.Bijective (ResidueField.map (R₀.subtype : R₀ →+* R))),
      Module.Finite R₀ R :=
  -- TODO: follow the textbook coefficient-ring plus parameter-ideal construction. The current
  -- dependency closure does not yet expose the earlier coefficient-ring existence theorem needed
  -- to start this argument source-faithfully.
  sorry

-- Proof sketch: in equal characteristic, take the image of the canonical power-series map from a
-- coefficient field and a system of parameters; in mixed characteristic, start from a Cohen ring
-- and adjoin formal power-series variables over it. In either case the resulting source ring is a
-- regular complete local subring `R₀ ⊆ R`, the inclusion is local and residue-field bijective,
-- and the Stacks argument shows that `R` is finite over `R₀`.
/-- Lemma 10.160.11: a Noetherian complete local domain contains a finite regular complete local
subring whose inclusion induces an isomorphism on residue fields, and that subring is a
finite-variable formal power series ring over either its residue field or a Cohen ring. -/
theorem exists_finite_regular_completeLocalSubring :
    ∃ (R₀ : Subring R) (_ : IsCompleteLocalRing R₀) (_ : IsRegularLocalRing R₀)
      (_ : IsLocalHom (R₀.subtype : R₀ →+* R))
      (_ : Function.Bijective (ResidueField.map (R₀.subtype : R₀ →+* R)))
      (_ : Module.Finite R₀ R),
      ∃ d : ℕ,
        Nonempty (MvPowerSeries (Fin d) (ResidueField R₀) ≃+* R₀) ∨
        ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ),
            Nonempty (MvPowerSeries (Fin d) Λ ≃+* R₀) := by
  rcases exists_finite_regular_completeLocalSubring_without_model (R := R) with
    ⟨R₀, hcomplete, hregular, hlocal, hresidue, hfinite⟩
  letI : IsCompleteLocalRing R₀ := hcomplete
  letI : IsRegularLocalRing R₀ := hregular
  -- Once the source-faithful subring witness is constructed, the presentation theorem for
  -- regular complete local rings supplies the final power-series/Cohen-ring alternative.
  rcases exists_powerSeries_model_of_regular_completeLocalRing (R₀ := R₀) with ⟨d, hmodel⟩
  exact ⟨R₀, hcomplete, hregular, hlocal, hresidue, hfinite, d, hmodel⟩

end
