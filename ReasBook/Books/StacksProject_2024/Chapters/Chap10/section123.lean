import Mathlib
import Mathlib.RingTheory.Algebraic.StronglyTranscendental
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_123_1 (from Chap10) -/
universe u v

open Polynomial
open scoped BigOperators

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

/-- Lemma 10.123.1: if `φ : R →+* S` and `t : S` satisfy a polynomial relation
`φ(a₀) + φ(a₁) t + ⋯ + φ(aₙ) tⁿ = 0`, then `φ(aₙ) * t` is integral over `R` with respect to
`φ`. -/
-- Proof sketch: package the displayed relation as `p.eval₂ φ t = 0` for the polynomial
-- `p = ∑ i, C (aᵢ) X^i`, observe that `p` has leading coefficient `aₙ`, and then apply the
-- canonical owner theorem `RingHom.isIntegralElem_leadingCoeff_mul`.
theorem isIntegralElem_mul_lastCoeff_of_sum_eq_zero (φ : R →+* S) {t : S} {n : ℕ}
    (a : Fin (n + 1) → R) (h : ∑ i : Fin (n + 1), φ (a i) * t ^ (i : ℕ) = 0) :
    φ.IsIntegralElem (φ (a ⟨n, Nat.lt_succ_self n⟩) * t) := by
  let p : R[X] := ∑ i : Fin (n + 1), C (a i) * X ^ (i : ℕ)
  let i0 : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have hp_eval : p.eval₂ φ t = ∑ i : Fin (n + 1), φ (a i) * t ^ (i : ℕ) := by
    simp [p, Polynomial.eval₂_finset_sum]
  have hp : p.eval₂ φ t = 0 := hp_eval.trans h
  by_cases han : a i0 = 0
  · simpa [i0, han] using φ.isIntegralElem_zero
  · have hcoeff : p.coeff n = a i0 := by
      calc
        p.coeff n = ∑ i : Fin (n + 1), (C (a i) * X ^ (i : ℕ) : R[X]).coeff n := by simp [p]
        _ = (C (a i0) * X ^ n : R[X]).coeff n := by
            refine Fintype.sum_eq_single i0 ?_
            intro i hi
            rw [coeff_C_mul, coeff_X_pow]
            by_cases hni : n = (i : ℕ)
            · exact (hi (Fin.ext hni.symm)).elim
            · simp [hni]
        _ = a i0 := by simp [i0, coeff_C_mul, coeff_X_pow]
    have hdeg_le : p.natDegree ≤ n := by
      simpa [p] using
        (natDegree_sum_le_of_forall_le _ _ fun i _ ↦
            (natDegree_C_mul_X_pow_le (a i) (i : ℕ)).trans (Nat.le_of_lt_succ i.2))
    have hdeg : p.natDegree = n :=
      natDegree_eq_of_le_of_coeff_ne_zero hdeg_le (by simpa [hcoeff] using han)
    have hlead : p.leadingCoeff = a i0 := by
      rw [Polynomial.leadingCoeff, hdeg, hcoeff]
    simpa [i0, hlead] using φ.isIntegralElem_leadingCoeff_mul p t hp

end RingHom

end

/-! ### Lemma_10_123_2 (from Chap10) -/
section

universe u v

open Polynomial

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

/-- Lemma 10.123.2: if `φ : R[X] →+* S` and `t : S` is integral over `R[X]`, and if there is a
monic polynomial `p : R[X]` such that `t * φ p` lies in the image of `φ`, then there exists
`q : R[X]` such that `t - φ q` is integral over `R` with respect to the composite map
`R → R[X] → S`. -/
-- Proof sketch: equip `S` with the `R`-algebra structure induced by `φ.comp C`, convert `φ` into
-- the corresponding `R`-algebra morphism from `R[X]`, apply the canonical mathlib theorem
-- `exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range`, and then translate the conclusion
-- back to `RingHom.IsIntegralElem` for the composite map `φ.comp C`.
theorem exists_isIntegralElem_sub_of_isIntegralElem_of_mul_mem_range
    {φ : R[X] →+* S} {t : S} {p : R[X]}
    (ht : φ.IsIntegralElem t) (hpm : p.Monic) (hp : t * φ p ∈ Set.range φ) :
    ∃ q : R[X], (φ.comp C).IsIntegralElem (t - φ q) := by
  letI : Algebra R S := (φ.comp C).toAlgebra
  let φ' : R[X] →ₐ[R] S :=
    { toRingHom := φ
      commutes' := by
        intro r
        simp [RingHom.algebraMap_toAlgebra] }
  have hp' : φ' p * t ∈ φ'.range := by
    rcases hp with ⟨q, hq⟩
    exact ⟨q, by simpa [φ', mul_comm] using hq⟩
  obtain ⟨q, hq⟩ :=
    exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range φ' t p ht hpm hp'
  refine ⟨q, ?_⟩
  simpa [IsIntegral, RingHom.IsIntegralElem, RingHom.algebraMap_toAlgebra, φ'] using hq

end RingHom

end

/-! ### Lemma_10_123_3 (from Chap10) -/
/- Lemma 10.123.3: for an `R`-algebra `S`, if `φ : R[X] →ₐ[R] S`, `t : S` is integral over
`R[X]`, and `φ p * t` lies in the image of `φ`, then after multiplying `t` by a power of
`p.leadingCoeff`, one can subtract `φ q` for some `q : R[X]` and obtain an element integral over
`R`. This is exactly the canonical mathlib theorem
`exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range`. -/
recall exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range

/-! ### Lemma_10_123_5 (from Chap10) -/
section

universe u v

open Polynomial

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

/-- Lemma 10.123.5: in the finite polynomial-map situation with integrally closed constant image, if
`u * φ p` lies in the conductor ideal `conductor R (φ X)` of `φ : R[X] →+* S`, then after
multiplying `u` by a power of the image of the leading coefficient of `p`, the result still lies in
that same conductor ideal. -/
theorem exists_pow_leadingCoeff_mul_mem_conductor
    {φ : Polynomial R →+* S} (hfinite : φ.Finite)
    (hintegrallyClosed : IsIntegrallyClosedIn ((φ.comp C).range) S)
    {u : S} {p : Polynomial R}
    (hu :
      letI : Algebra R S := (φ.comp C).toAlgebra
      u * φ p ∈ conductor R (φ X)) :
    letI : Algebra R S := (φ.comp C).toAlgebra
    ∃ m : ℕ, u * φ (C p.leadingCoeff) ^ m ∈ conductor R (φ X) := by
  letI : Algebra R S := (φ.comp C).toAlgebra
  let φ' : Polynomial R →ₐ[R] S := aeval (φ X)
  have hφ' : φ'.toRingHom = φ := by
    apply Polynomial.ringHom_ext'
    · ext r
      simp [φ', RingHom.algebraMap_toAlgebra]
    · simp [φ']
  have hφp : φ' p = φ p := by
    simpa using DFunLike.congr_fun hφ' p
  have hφX : φ' X = φ X := by
    simpa using DFunLike.congr_fun hφ' X
  have hRS : integralClosure R S = ⊥ := by
    letI : Algebra R ((φ.comp C).range) := RingHom.toAlgebra (φ.comp C).rangeRestrict
    letI : IsScalarTower R ((φ.comp C).range) S := .of_algebraMap_eq fun _ ↦ rfl
    letI : Algebra.IsIntegral R ((φ.comp C).range) := {
      isIntegral := fun x ↦ by
        rcases x with ⟨x, ⟨r, rfl⟩⟩
        simpa [RingHom.algebraMap_toAlgebra] using
          (show _root_.IsIntegral R (algebraMap R ((φ.comp C).range) r) from
            isIntegral_algebraMap)
    }
    apply le_antisymm
    · intro x hx
      rw [Algebra.mem_bot]
      have hx' : _root_.IsIntegral ((φ.comp C).range) x :=
        (show _root_.IsIntegral R x from hx).tower_top
      have hx'' : x ∈ (φ.comp C).range := (Subring.isIntegrallyClosedIn_iff.mp
        hintegrallyClosed) hx'
      simpa [RingHom.algebraMap_toAlgebra] using hx''
    · exact bot_le
  obtain ⟨m, hm⟩ := exists_leadingCoeff_pow_smul_mem_conductor
    φ' u p hRS
    (by
      show φ'.toRingHom.Finite
      rw [hφ']
      exact hfinite)
    (by simpa [hφp, hφX, mul_comm] using hu)
  refine ⟨m, ?_⟩
  simpa [φ', hφ', Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using hm

end RingHom

end

/-! ### Lemma_10_123_6 (from Chap10) -/
/- Lemma 10.123.6 lies in the commutative-algebra/Zariski-main-theorem domain governing conductor
ideals of polynomial algebras. Sampled owner declarations in this domain are
`exists_leadingCoeff_pow_smul_mem_conductor`,
`exists_leadingCoeff_pow_smul_mem_radical_conductor`, and
`isStronglyTranscendental_mk_radical_conductor` from
`Mathlib.RingTheory.ZariskisMainTheorem`.

Layer triage: this item is `core/canonical`, not `bridge/view`. The source statement is already the
canonical coefficientwise radical-conductor theorem for a finite polynomial map with integrally
closed constant image, so no local wrapper or paraphrase theorem should be introduced here.

Primitive data are the polynomial algebra map `φ`, the multiplier `t`, the polynomial `p`, and the
integrally-closed/finite hypotheses; the coefficientwise radical-conductor conclusion is derived
API. -/
recall exists_leadingCoeff_pow_smul_mem_radical_conductor

/-! ### Definition_10_123_7 (from Chap10) -/
/- Definition 10.123.7: the source-facing notion is the canonical mathlib owner predicate
`IsStronglyTranscendental R x`. The theorem below is only a bridge/view to the coefficientwise
wording from the source text. -/
recall IsStronglyTranscendental

open Polynomial

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {x : S}

/-- Bridge/view: strong transcendence is equivalent to saying that any annihilated polynomial
relation forces the multiplier to annihilate every coefficient. -/
theorem isStronglyTranscendental_iff_forall_mul_coeff_eq_zero :
    IsStronglyTranscendental R x ↔
      ∀ u : S, ∀ p : R[X], u * p.aeval x = 0 → ∀ n : ℕ, u * algebraMap R S (p.coeff n) = 0 := by
  constructor
  · intro hx u p hp n
    have hcoeff := congrArg (fun q : S[X] ↦ q.coeff n) <|
      hx u p (by simpa [mul_comm] using hp)
    simpa [coeff_mul_C, coeff_map, mul_comm] using hcoeff
  · intro hx u p hp
    ext n
    simpa [coeff_mul_C, coeff_map, mul_comm] using
      hx u p (by simpa [mul_comm] using hp) n

end

/-! ### Lemma_10_123_8 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsReduced S]

-- Proof sketch: first apply
-- `isStronglyTranscendental_mk_of_mem_minimalPrimes` to pass from `S` to `S ⧸ q` while keeping the
-- base ring `R`. Then descend the base ring along the surjection `R → R ⧸ q.under R` using
-- `IsStronglyTranscendental.of_surjective_left`.
/-- Lemma 10.123.8: if `q` is a minimal prime of `S`, then the image of a strongly transcendental
element `x` in `S ⧸ q` is strongly transcendental over the quotient subring `R ⧸ q.under R`. -/
theorem isStronglyTranscendental_quotient_over_under_of_mem_minimalPrimes
    {x : S} (hx : IsStronglyTranscendental R x) (q : Ideal S) (hq : q ∈ minimalPrimes S) :
    IsStronglyTranscendental (R ⧸ q.under R) (Ideal.Quotient.mk q x) :=
  (isStronglyTranscendental_mk_of_mem_minimalPrimes hx q hq).of_surjective_left
    Ideal.Quotient.mk_surjective

end

/-! ### Lemma_10_123_9 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsReduced S]

/- Domain-style sampling for Lemma 10.123.9:
- primary domain: strong transcendence versus quasi-finiteness for a polynomially generated
  algebra;
- sampled owner declarations:
  `IsStronglyTranscendental`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`;
- best owner abstraction: the mathlib theorem
  `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`;
- primitive data: the element `x : S`, its strong transcendence over `R`, the finite polynomial map
  `Polynomial.aeval x`, and the prime `q : Ideal S`;
- derived API: the source-facing contrapositive below.

Source/core/bridge triage:
- `source-facing`: the textbook negation of quasi-finiteness under a strong-transcendence
  hypothesis;
- `core/canonical`: `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`;
- `bridge/view`: this theorem, which packages the canonical owner theorem in the source's
  contrapositive form. -/

-- Proof sketch: argue by contradiction. If `R → S` were quasi-finite at a prime `q`, then the
-- canonical mathlib theorem `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt` applied to the
-- finite polynomial map `Polynomial.aeval x : R[X] →ₐ[R] S` would show that `x` is not strongly
-- transcendental over `R`.
/-- Lemma 10.123.9: the source states this for an inclusion of domains, but the canonical owner
theorem only needs `S` reduced. If `x : S` is strongly transcendental over `R` and `S` is finite
over the polynomial subring `R[x]`, then `R → S` is not quasi-finite at any prime of `S`. -/
theorem not_quasiFiniteAt_of_isStronglyTranscendental_of_aeval_finite
    {x : S} (hx : IsStronglyTranscendental R x)
    (hfinite : (Polynomial.aeval x : Polynomial R →ₐ[R] S).Finite)
    (q : Ideal S) [q.IsPrime] :
    ¬ Algebra.QuasiFiniteAt R q := by
  intro hq
  letI : Algebra.QuasiFiniteAt R q := hq
  exact (Algebra.not_isStronglyTranscendental_of_quasiFiniteAt hfinite q) hx

end

/-! ### Lemma_10_123_10 (from Chap10) -/
/- Domain-style sampling for Lemma 10.123.10:
- primary domain: strong transcendence and quasi-finiteness in commutative algebra;
- sampled owner declarations:
  `IsStronglyTranscendental`,
  `Algebra.QuasiFiniteAt`,
  `not_quasiFiniteAt_of_isStronglyTranscendental_of_aeval_finite`;
- best owner abstraction: the chapter theorem
  `not_quasiFiniteAt_of_isStronglyTranscendental_of_aeval_finite` from Lemma `10.123.9`;
- primitive data: `x : S`, its strong transcendence over `R`, finiteness of `Polynomial.aeval x`,
  and the prime `q`;
- derived API: the reduced-ring wording from the source, whose extra reducedness and
  `FaithfulSMul` assumptions are redundant for the canonical conclusion.

Source/core/bridge triage:
- `source-facing`: the Stacks negation of quasi-finiteness for a ring finite over `R[x]`;
- `core/canonical`: `IsStronglyTranscendental`, `Algebra.QuasiFiniteAt`, and the owner theorem
  from Lemma `10.123.9`;
- `bridge/view`: this file is recall-only, since the canonical chapter theorem already has the
  mathematically correct public statement. -/

/- Lemma 10.123.10: the reduced-ring formulation is already covered by the canonical chapter
theorem `not_quasiFiniteAt_of_isStronglyTranscendental_of_aeval_finite`. The extra assumptions
`IsReduced R`, `IsReduced S`, and `FaithfulSMul R S` are redundant for the public API, so this
numbered item is refined to a direct recall of the owner theorem rather than a parallel wrapper. -/
recall not_quasiFiniteAt_of_isStronglyTranscendental_of_aeval_finite

/-! ### Lemma_10_123_11 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.123.11: if `S` is a quotient of `R[X]`, `q` is a prime ideal of `S`, and `R → S` is
quasi-finite at `q`, then there exists an element of the integral closure of `R` in `S` outside
`q` such that localizing the integral closure and `S` away from that element gives the same ring. -/
-- Proof sketch: a surjective `R`-algebra map `R[X] → S` makes `S` finite type over `R`. Apply the
-- algebraic Zariski main theorem at `q` to conclude `Algebra.ZariskisMainProperty R q`, which is
-- exactly the existence of such an element in `integralClosure R S` with bijective away map.
theorem zariskisMainProperty_of_surjective_polynomial
    (φ : Polynomial R →ₐ[R] S) (hφ : Function.Surjective φ) (q : Ideal S) [q.IsPrime]
    [Algebra.QuasiFiniteAt R q] : Algebra.ZariskisMainProperty R q := by
  letI : Algebra.FiniteType R S := Algebra.FiniteType.of_surjective φ hφ
  exact Algebra.ZariskisMainProperty.of_finiteType q

end

/-! ### Theorem_10_123_12_Zariski_s_Main_Theorem (from Chap10) -/
universe u v

/-
Domain-style sampling:
- primary domain: quasi-finite finite-type ring maps and the algebraic Zariski main theorem;
- sampled owner API:
  `Algebra.ZariskisMainProperty`,
  `Algebra.ZariskisMainProperty.of_finiteType`,
  `Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective`,
  `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`;
- source-facing: the Stacks statement that for a finite type `R`-algebra `S` and a prime `q`,
  quasi-finiteness at `q` gives an element of `integralClosure R S` away from `q` with bijective
  away map;
- core/canonical owner: `Algebra.ZariskisMainProperty`;
- bridge/view: passing from `q : PrimeSpectrum S` to the owner input `q.asIdeal`.

Primitive data are only the finite-type algebra structure, the prime, and the canonical owner
`Algebra.QuasiFiniteAt`. The integral-closure witness and away-map bijectivity are already the
definition of `Algebra.ZariskisMainProperty`, so this file should recall the owner theorem directly
instead of keeping a parallel unpacked theorem.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Theorem 10.123.12 (Zariski's Main Theorem): for a finite type `R`-algebra `S` and a prime
`q ⊂ S`, if `R → S` is quasi-finite at `q`, then there exists an element of the integral closure
`S' = integralClosure R S` outside `q` such that the canonical away map `S'[1/g] → S[1/g]` is
bijection, equivalently `S'_g ≅ S_g`. This is exactly the canonical owner theorem
`Algebra.ZariskisMainProperty.of_finiteType`. -/
recall Algebra.ZariskisMainProperty.of_finiteType

end

/-! ### Lemma_10_123_13 (from Chap10) -/
open AlgebraicGeometry
open RingHom
open Topology

universe u

/- Domain-style sampling:
- primary domain: quasi-finite finite-type morphisms in affine algebraic geometry;
- sampled owner declarations:
  `Algebra.QuasiFiniteAt`,
  `Scheme.Hom.QuasiFiniteAt`,
  `Scheme.arrowStalkMapSpecIso`,
  `Scheme.Hom.isOpen_quasiFiniteAt`;
- source-facing layer: the textbook affine statement that the quasi-finite locus in `Spec(S)` is
  open for a finite type algebra `R → S`;
- core/canonical owner: `Scheme.Hom.isOpen_quasiFiniteAt` for scheme morphisms, together with the
  affine-point owner `Scheme.Hom.QuasiFiniteAt`;
- bridge/view: the comparison below identifying `Scheme.Hom.QuasiFiniteAt` on
  `Spec.map (algebraMap R S)` with the ring-theoretic owner `Algebra.QuasiFiniteAt R q.asIdeal`.

Primitive data are only the finite-type algebra structure and the owner predicate
`Algebra.QuasiFiniteAt`. The openness statement itself belongs to the scheme-level owner
`Scheme.Hom.isOpen_quasiFiniteAt`, so this file should stay a thin affine bridge rather than
introducing any parallel local quasi-finite-locus wrapper.
-/

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

omit [Algebra.FiniteType R S] in
/-- Affine bridge: for `Spec(S) → Spec(R)`, the scheme-theoretic pointwise quasi-finite predicate
agrees with the ring-theoretic owner `Algebra.QuasiFiniteAt` at the corresponding prime of `S`. -/
lemma specMap_quasiFiniteAt_iff (q : PrimeSpectrum S) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).QuasiFiniteAt q ↔
      Algebra.QuasiFiniteAt R q.asIdeal := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  change (CommRingCat.Hom.hom ((Spec.map φ).stalkMap q)).QuasiFinite ↔ _
  rw [QuasiFinite.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ q)]
  have hloc :
      (algebraMap R (Localization.AtPrime (Ideal.comap (algebraMap R S) q.asIdeal))).QuasiFinite := by
    rw [RingHom.quasiFinite_algebraMap]
    exact .of_isLocalization (Ideal.comap (algebraMap R S) q.asIdeal).primeCompl
  trans ((Localization.localRingHom (Ideal.comap (algebraMap R S) q.asIdeal) q.asIdeal
      (algebraMap R S) rfl).comp
      (algebraMap R (Localization.AtPrime (Ideal.comap (algebraMap R S) q.asIdeal)))).QuasiFinite
  · exact (RingHom.QuasiFinite.comp_iff hloc).symm
  · have hcomp :
        (Localization.localRingHom (Ideal.comap (algebraMap R S) q.asIdeal) q.asIdeal
          (algebraMap R S) rfl).comp
          (algebraMap R (Localization.AtPrime (Ideal.comap (algebraMap R S) q.asIdeal))) =
          algebraMap R (Localization.AtPrime q.asIdeal) := by
        ext x
        simp [Localization.localRingHom_to_map]
        simpa using
          (IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal) x).symm
    simp [hcomp, RingHom.quasiFinite_algebraMap]

/-- Lemma 10.123.13: for a finite type ring map `R → S`, the subset of `Spec(S)` consisting of the
points where `R → S` is quasi-finite is open. -/
-- Proof sketch: start with a prime `q` where `R → S` is quasi-finite. Apply Zariski's main
-- theorem to obtain an element of the integral closure away from `q` such that after localizing,
-- `S` agrees with an integral algebra over `R`. Replace that integral algebra by a finite
-- `R`-subalgebra after shrinking to a basic open neighborhood, use that finite algebras are
-- quasi-finite, and conclude that the whole basic open neighborhood lies in the quasi-finite locus.
theorem isOpen_setOf_quasiFiniteAt :
    IsOpen { q : PrimeSpectrum S | Algebra.QuasiFiniteAt R q.asIdeal } := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  have hft : LocallyOfFiniteType (Spec.map φ) := by
    refine HasRingHomProperty.Spec_iff.mpr ?_
    change (algebraMap R S).FiniteType
    rw [RingHom.finiteType_algebraMap]
    infer_instance
  letI : LocallyOfFiniteType (Spec.map φ) := hft
  have hopen : IsOpen { q : PrimeSpectrum S | (Spec.map φ).QuasiFiniteAt q } :=
    (Spec.map φ).isOpen_quasiFiniteAt
  convert hopen using 1
  ext q
  change Algebra.QuasiFiniteAt R q.asIdeal ↔ (Spec.map φ).QuasiFiniteAt q
  simpa [φ] using (specMap_quasiFiniteAt_iff q).symm

end

/-! ### Lemma_10_123_14 (from Chap10) -/
universe u v

open Topology

/-
Domain-style sampling:
- primary domain: quasi-finite finite-type algebras, integral closures, and the algebraic
  Zariski Main Theorem;
- sampled owner declarations:
  `Algebra.ZariskisMainProperty`,
  `Algebra.ZariskisMainProperty.of_finiteType`,
  `Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective`,
  `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`;
- best owner abstraction: the primewise local comparison data are owned upstream by
  `Algebra.ZariskisMainProperty`; the present lemma is the `source-facing` globalized integral
  closure statement built from those local owners together with the induced map on prime spectra;
- primitive data: an intermediate subalgebra `S'' : Subalgebra R S`, the inclusion
  `S'' ≤ integralClosure R S`, finiteness `Module.Finite R S''`, the open-embedding statement on
  `PrimeSpectrum`, and the away-map bijectivity clause for basic opens in the image;
- derived API to avoid as primitive wrappers: one-off conjunction packages for “finite subalgebra
  of the integral closure” and for the combined Zariski-main comparison property.

Source/core/bridge triage:
- `source-facing`: the global open-embedding and finite intermediate-subalgebra formulation of
  Lemma `10.123.14`;
- `core/canonical`: `Algebra.ZariskisMainProperty` for the local comparison ingredient;
- `bridge/view`: passing from the primewise owner theorem to the global spectrum/open-cover
  formulation used here.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S] [Algebra.QuasiFinite R S]

/-- Lemma 10.123.14 (1): if `S' = integralClosure R S` and `R → S` is finite type and
quasi-finite, then the induced map `Spec(S) → Spec(S')` is a homeomorphism onto an open subset,
i.e. an open embedding. -/
-- Proof sketch: apply Zariski's Main Theorem pointwise to each prime of `S` to obtain basic open
-- neighborhoods on which `Spec(S) → Spec(S')` is identified with the spectrum map of a bijective
-- localization-away map. Quasi-compactness of `Spec(S)` then lets one glue these local
-- identifications into a global open embedding.
theorem primeSpectrum_comap_integralClosure_isOpenEmbedding :
    IsOpenEmbedding (PrimeSpectrum.comap (integralClosure R S).val.toRingHom) := sorry

/-- Lemma 10.123.14 (2): if `g ∈ S' = integralClosure R S` and the basic open `D(g)` of
`Spec(S')` is contained in the image of `Spec(S) → Spec(S')`, then the canonical localization map
`S'_g → S_g` is bijective, equivalently `S'_g ≅ S_g`. -/
-- Proof sketch: cover the image of `Spec(S) → Spec(S')` by finitely many principal opens coming
-- from the pointwise Zariski-main theorem. Over each overlap with `D(g)` the away map is
-- bijective; apply the standard local-on-a-principal-cover criterion to descend bijectivity to the
-- away map at `g`.
theorem awayMap_bijective_of_basicOpen_subset_range_integralClosure
    (g : integralClosure R S)
    (hg :
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (integralClosure R S))) ⊆
        Set.range (PrimeSpectrum.comap (integralClosure R S).val.toRingHom))) :
    Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom g) := sorry

/-- Lemma 10.123.14 (3): there exists a finite `R`-subalgebra `S''` of the integral closure
`S' = integralClosure R S` such that the induced map `Spec(S) → Spec(S'')` is an open embedding,
and whenever a basic open `D(g)` of `Spec(S'')` is contained in its image, the canonical
localization map `S''_g → S_g` is bijective. -/
-- Proof sketch: choose finitely many elements of the integral closure whose principal opens cover
-- `Spec(S)` and on which the away maps to `S` are bijective. Generate an `R`-subalgebra of the
-- integral closure by these elements together with finitely many auxiliary generators for the
-- corresponding localized rings; this subalgebra is module-finite over `R` and inherits the two
-- local properties from the chosen finite cover.
theorem exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties :
    ∃ S'' : Subalgebra R S,
      S'' ≤ integralClosure R S ∧
      Module.Finite R S'' ∧
      IsOpenEmbedding (PrimeSpectrum.comap S''.val.toRingHom) ∧
      ∀ g : S'',
        ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S'')) ⊆
          Set.range (PrimeSpectrum.comap S''.val.toRingHom)) →
          Function.Bijective (Localization.awayMap S''.val.toRingHom g) := sorry

end
