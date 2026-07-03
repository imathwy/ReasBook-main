import Mathlib
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_38_1 (from Chap10) -/
section

universe u v

open Polynomial

variable {R : Type u} {S : Type v} [CommRing R] [Ring S]

namespace RingHom

/-- Definition 10.38.1: an element `g : S` is integral over an ideal `I` with respect to a ring
homomorphism `φ : R →+* S` if `g` satisfies a monic polynomial relation over `R` whose
`X^j`-coefficient lies in `I ^ (d - j)`, where `d` is the degree of the polynomial.

This is the source-facing coefficient formulation; ordinary integrality remains owned by
`RingHom.IsIntegralElem`, and Lemma 10.38.2 later identifies this notion with integrality over the
Rees algebra. -/
def IsIntegralOverIdeal (φ : R →+* S) (I : Ideal R) (g : S) : Prop :=
  ∃ P : R[X], P.Monic ∧ eval₂ φ g P = 0 ∧ ∀ j : ℕ, P.coeff j ∈ I ^ (P.natDegree - j)

end RingHom

end

/-! ### Lemma_10_38_2 (from Chap10) -/
open Polynomial

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

namespace RingHom

private lemma term_eval_eq (s : S) (a : R) (d i : ℕ) (hi : i ≤ d) :
    eval₂ (algebraMap S[X] S[X]) (C s * X)
      (C (C ((algebraMap R S) a) * X ^ (d - i) : S[X]) * X ^ i) =
    C ((algebraMap R S) a * s ^ i) * X ^ d := by
  simp only [eval₂_mul, eval₂_C, eval₂_X_pow]
  calc
    (C ((algebraMap R S) a) * X ^ (d - i) : S[X]) * (C s * X) ^ i
        = (C ((algebraMap R S) a) * X ^ (d - i) : S[X]) * (C (s ^ i) * X ^ i) := by
            rw [mul_pow, ← C_pow]
    _ = C ((algebraMap R S) a * s ^ i) * X ^ ((d - i) + i) := by
          rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial]
          simp [monomial_mul_monomial, add_comm, mul_comm]
    _ = C ((algebraMap R S) a * s ^ i) * X ^ d := by rw [Nat.sub_add_cancel hi]

-- Proof sketch: for the forward direction, translate a defining polynomial relation for
-- `(algebraMap R S).IsIntegralOverIdeal I s` into a monic polynomial relation for `C s * X` over
-- the canonical Rees algebra `reesAlgebra I`. For the reverse direction, rewrite back to the
-- textbook generator presentation and apply
-- `Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral`.
attribute [local instance] Polynomial.algebra in
/-- Lemma 10.38.2: an element `s : S` is integral over the ideal `I` in the sense that it satisfies
a monic polynomial relation with coefficients in the powers `I ^ (d - i)` if and only if the
polynomial element `C s * X : S[X]` is integral over the canonical Rees algebra
`reesAlgebra I ⊆ R[X]`. -/
lemma isIntegralOverIdeal_iff_isIntegral_C_mul_X (I : Ideal R) (s : S) :
    (algebraMap R S).IsIntegralOverIdeal I s ↔
      _root_.IsIntegral (reesAlgebra I) (C s * X : S[X]) := by
  constructor
  · rintro ⟨p, hpM, hp0, hpI⟩
    let A : Subalgebra R R[X] := reesAlgebra I
    let f : ℕ → A[X] := fun i ↦
      C ⟨C (p.coeff i) * X ^ (p.natDegree - i), by
          simpa [A, C_mul_X_pow_eq_monomial] using (reesAlgebra.monomial_mem).2 (hpI i)⟩ * X ^ i
    let q : A[X] := ∑ i ∈ Finset.range (p.natDegree + 1), f i
    change (algebraMap A S[X]).IsIntegralElem (C s * X : S[X])
    refine ⟨q, ?_, ?_⟩
    · refine monic_of_natDegree_le_of_coeff_eq_one p.natDegree ?_ ?_
      · simpa [q, f] using
          (natDegree_sum_le_of_forall_le (Finset.range (p.natDegree + 1)) f fun i hi ↦
            (natDegree_C_mul_X_pow_le _ _).trans (by simpa [Nat.lt_succ_iff] using hi))
      · ext
        simp [q, f, hpM]
    · have hqsum : eval₂ (algebraMap A S[X]) (C s * X) q
          = ∑ i ∈ Finset.range (p.natDegree + 1), eval₂ (algebraMap A S[X]) (C s * X) (f i) := by
          simpa [q] using
            (Polynomial.eval₂_finset_sum (algebraMap A S[X]) (Finset.range (p.natDegree + 1))
              f (C s * X))
      calc
        eval₂ (algebraMap A S[X]) (C s * X) q
            = ∑ i ∈ Finset.range (p.natDegree + 1),
                C ((algebraMap R S) (p.coeff i) * s ^ i) * X ^ p.natDegree := by
                  rw [hqsum]
                  refine Finset.sum_congr rfl fun i hi ↦ ?_
                  have hi' : i ≤ p.natDegree := by simpa [Nat.lt_succ_iff] using hi
                  simpa [f] using term_eval_eq s (p.coeff i) p.natDegree i hi'
        _ = C ((aeval s) p) * X ^ p.natDegree := by
              rw [← Finset.sum_mul]
              congr 1
              simp [aeval_def, eval₂_eq_sum_range, map_sum]
        _ = 0 := by
              have hp0' : aeval s p = 0 := by simpa [aeval_def] using hp0
              rw [hp0']
              simp
  · intro hs
    have hrees :
        Algebra.adjoin R { C r * X | r ∈ I } = reesAlgebra I := by
      simpa [Set.ext_iff, C_mul_X_eq_monomial] using adjoin_monomial_eq_reesAlgebra I
    rw [← hrees] at hs
    exact exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral hs

end RingHom

end

/-! ### Lemma_10_38_3 (from Chap10) -/
section

universe u v

open Polynomial

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

section Algebra

variable [Algebra R S]

attribute [local instance] Polynomial.algebra

local instance (I : Ideal R) : IsScalarTower R (reesAlgebra I) S[X] :=
  IsScalarTower.subalgebra' R R[X] S[X] (reesAlgebra I)

private theorem isIntegralOverIdeal_zero_algebraMap (I : Ideal R) :
    (algebraMap R S).IsIntegralOverIdeal I 0 := by
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I (0 : S)]
  simpa using (isIntegral_zero : _root_.IsIntegral (reesAlgebra I) (0 : S[X]))

private theorem isIntegralOverIdeal_add_algebraMap {I : Ideal R} {x y : S}
    (hx : (algebraMap R S).IsIntegralOverIdeal I x)
    (hy : (algebraMap R S).IsIntegralOverIdeal I y) :
    (algebraMap R S).IsIntegralOverIdeal I (x + y) := by
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I x] at hx
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I y] at hy
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I (x + y)]
  simpa [C_add, add_mul] using hx.add hy

private theorem isIntegralOverIdeal_smul_algebraMap (I : Ideal R) {r : R} {s : S}
    (hs : (algebraMap R S).IsIntegralOverIdeal I s) :
    (algebraMap R S).IsIntegralOverIdeal I (r • s) := by
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I s] at hs
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I (r • s)]
  simpa [Algebra.smul_def, C_mul, mul_assoc] using hs.smul r

/-- Lemma 10.38.3 (1): the elements of `S` that are integral over the ideal `I` form the
canonical `R`-submodule of `S`. -/
def integralOverIdealSubmodule (I : Ideal R) : Submodule R S where
  carrier := { s | (algebraMap R S).IsIntegralOverIdeal I s }
  zero_mem' := isIntegralOverIdeal_zero_algebraMap I
  add_mem' := by
    intro x y hx hy
    exact isIntegralOverIdeal_add_algebraMap hx hy
  smul_mem' := by
    intro r s hs
    exact isIntegralOverIdeal_smul_algebraMap I hs

/-- Membership in the canonical submodule from Lemma 10.38.3 (1) is exactly integrality over
the ideal `I`. -/
theorem mem_integralOverIdealSubmodule_iff (I : Ideal R) (s : S) :
    s ∈ integralOverIdealSubmodule I ↔ (algebraMap R S).IsIntegralOverIdeal I s :=
  Iff.rfl

/-- Elements integral over an ideal are closed under scalar multiplication by the base ring. -/
theorem IsIntegralOverIdeal.smul {I : Ideal R} {r : R} {s : S}
    (hs : (algebraMap R S).IsIntegralOverIdeal I s) :
    (algebraMap R S).IsIntegralOverIdeal I (r • s) := by
  change s ∈ integralOverIdealSubmodule I at hs
  change r • s ∈ integralOverIdealSubmodule I
  exact (integralOverIdealSubmodule I).smul_mem r hs

end Algebra

/-- Zero is integral over any ideal. -/
theorem isIntegralOverIdeal_zero (φ : R →+* S) (I : Ideal R) :
    φ.IsIntegralOverIdeal I 0 := by
  letI := φ.toAlgebra
  change (0 : S) ∈ integralOverIdealSubmodule I
  exact (integralOverIdealSubmodule I).zero_mem

/-- Elements integral over an ideal are closed under addition. -/
theorem IsIntegralOverIdeal.add {φ : R →+* S} {I : Ideal R} {x y : S}
    (hx : φ.IsIntegralOverIdeal I x) (hy : φ.IsIntegralOverIdeal I y) :
    φ.IsIntegralOverIdeal I (x + y) := by
  letI := φ.toAlgebra
  change x ∈ integralOverIdealSubmodule I at hx
  change y ∈ integralOverIdealSubmodule I at hy
  change x + y ∈ integralOverIdealSubmodule I
  exact (integralOverIdealSubmodule I).add_mem hx hy

/-- Lemma 10.38.3 (2): if `s` is integral over `R` and `s'` is integral over the ideal `I`, then
`s * s'` is integral over `I`. -/
theorem IsIntegralElem.mul_isIntegralOverIdeal {φ : R →+* S} {I : Ideal R} {s s' : S}
    (hs : φ.IsIntegralElem s) (hs' : φ.IsIntegralOverIdeal I s') :
    φ.IsIntegralOverIdeal I (s * s') := by
  letI := φ.toAlgebra
  letI : Algebra R[X] S[X] := Polynomial.algebra R S
  letI : IsScalarTower R (reesAlgebra I) S[X] :=
    IsScalarTower.subalgebra' R R[X] S[X] (reesAlgebra I)
  change (algebraMap R S).IsIntegralOverIdeal I (s * s')
  change (algebraMap R S).IsIntegralOverIdeal I s' at hs'
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I s'] at hs'
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I (s * s')]
  have hsC : _root_.IsIntegral (reesAlgebra I) (C s : S[X]) := by
    exact (show _root_.IsIntegral R (C s : S[X]) from by
      simpa using hs.map (CAlgHom : S →ₐ[R] S[X]).toRingHom).tower_top
  simpa [C_mul, mul_assoc] using hsC.mul hs'

end RingHom

end

/-! ### Lemma_10_38_4 (from Chap10) -/
section

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

/-
Domain triage:
* source-facing: `φ.IsIntegralOverIdeal I x`, the chapter's ideal-relative integrality predicate.
* core/canonical owner: `Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map`.
* bridge/view: this lemma repackages the owner theorem for an arbitrary integral ring hom `φ`.
-/
recall Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map

/-- Lemma 10.38.4: every element of the extended ideal `I.map φ = IS` is integral over `I`
whenever `φ : R →+* S` is integral. -/
theorem isIntegralOverIdeal_of_mem_map {φ : R →+* S} (hφ : φ.IsIntegral) {I : Ideal R} {x : S}
    (hx : x ∈ I.map φ) :
    φ.IsIntegralOverIdeal I x := by
  letI := φ.toAlgebra
  letI : Algebra.IsIntegral R S := ⟨hφ⟩
  simpa [IsIntegralOverIdeal, Polynomial.aeval_def] using
    Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map hx

end RingHom

end

/-! ### Lemma_10_38_5 (from Chap10) -/
universe u

open Polynomial
open MvPolynomial (aeval mapEquivMonic)
open scoped BigOperators

section

private theorem coeff_mapEquivMonic_aeval {A : Type u} [CommRing A] (n : ℕ) (c : Fin n → A)
    (i : Fin n) :
    (((mapEquivMonic A A n) (aeval c) : MonicDegreeEq A n) :
      Polynomial A).coeff (i : ℕ) = c i := by
  simp [mapEquivMonic, coeff_freeMonic]

/-- Lemma 10.38.5 (1): if the monic polynomial `x^n + a_{n-1}x^{n-1} + ⋯ + a₀` divides the monic
polynomial `x^m + b_{m-1}x^{m-1} + ⋯ + b₀` over a commutative ring `K`, then every coefficient
`a i` is integral over any subring `R₀ ⊆ K` containing all coefficients `b j`. -/
theorem coeff_integral_of_dvd_monicPolynomialOfCoeffs
    {K : Type u} [CommRing K] {n m : ℕ} (a : Fin n → K) (b : Fin m → K)
    (hdiv : X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ) ∣
      X ^ m + ∑ j : Fin m, C (b j) * X ^ (j : ℕ)) {R₀ : Subring K}
    (hb : ∀ j : Fin m, b j ∈ R₀) :
    ∀ i : Fin n, IsIntegral R₀ (a i) := by
  let p : MonicDegreeEq R₀ m := (mapEquivMonic R₀ R₀ m) (aeval fun j ↦ ⟨b j, hb j⟩)
  let q : MonicDegreeEq K n := (mapEquivMonic K K n) (aeval a)
  have hdiv' : (q : K[X]) ∣ (p : R₀[X]).map (algebraMap R₀ K) := by
    simpa [p, q, mapEquivMonic, freeMonic, Polynomial.map_sum] using hdiv
  intro i
  have hcoeff : (q : K[X]).coeff (i : ℕ) = a i := by
    simpa [q] using coeff_mapEquivMonic_aeval n a i
  simpa [hcoeff] using
    isIntegral_coeff_of_dvd (p : R₀[X]) (q : K[X]) p.monic q.monic hdiv' (i : ℕ)

/-- Lemma 10.38.5 (2): if the same divisibility holds and `R ⊆ K` contains all coefficients `a i`
and `b j`, then each `a i` lies in the radical of the ideal generated by the `b j` inside `R`. -/
theorem coeff_mem_radical_span_of_dvd_monicPolynomialOfCoeffs
    {K : Type u} [CommRing K] {n m : ℕ} (a : Fin n → K) (b : Fin m → K)
    (hdiv : X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ) ∣
      X ^ m + ∑ j : Fin m, C (b j) * X ^ (j : ℕ)) {R : Subring K}
    (ha : ∀ i : Fin n, a i ∈ R) (hb : ∀ j : Fin m, b j ∈ R) :
    ∀ i : Fin n, (⟨a i, ha i⟩ : R) ∈
      (Ideal.span (Set.range fun j : Fin m ↦ (⟨b j, hb j⟩ : R))).radical := by
  obtain hR | hR := subsingleton_or_nontrivial R
  · letI : Subsingleton R := hR
    intro i
    let I : Ideal R := Ideal.span (Set.range fun j : Fin m ↦ (⟨b j, hb j⟩ : R))
    have hzero : (⟨a i, ha i⟩ : R) = 0 := Subsingleton.elim _ _
    simp [hzero]
  · letI : Nontrivial R := hR
    let p : MonicDegreeEq R m := (mapEquivMonic R R m) (aeval fun j ↦ ⟨b j, hb j⟩)
    let q : MonicDegreeEq R n := (mapEquivMonic R R n) (aeval fun i ↦ ⟨a i, ha i⟩)
    have hdiv' : (q : R[X]) ∣ (p : R[X]) := by
      refine (map_dvd_map (algebraMap R K) (fun x y h ↦ Subtype.ext h) q.monic).1 ?_
      simpa [p, q, mapEquivMonic, freeMonic, Polynomial.map_sum] using hdiv
    intro i
    have hi : (i : ℕ) ≠ (q : R[X]).natDegree := by
      simpa [q] using i.is_lt.ne
    have hcoeff : (q : R[X]).coeff (i : ℕ) = (⟨a i, ha i⟩ : R) := by
      simpa [q] using coeff_mapEquivMonic_aeval n (fun i ↦ (⟨a i, ha i⟩ : R)) i
    have hcoeffs :
        {x | ∃ j < m, (p : R[X]).coeff j = x} =
          Set.range fun j : Fin m ↦ (⟨b j, hb j⟩ : R) := by
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        refine ⟨⟨j, hj⟩, ?_⟩
        simpa using
          (coeff_mapEquivMonic_aeval m (fun j ↦ (⟨b j, hb j⟩ : R)) ⟨j, hj⟩).symm
      · rintro ⟨j, rfl⟩
        exact ⟨j, j.is_lt, coeff_mapEquivMonic_aeval m (fun j ↦ (⟨b j, hb j⟩ : R)) j⟩
    simpa [hcoeff, hcoeffs] using
      coeff_mem_radical_span_coeff_of_dvd (p : R[X]) (q : R[X]) p.monic q.monic hdiv'
        (i : ℕ) hi

end

/-! ### Lemma_10_38_6 (from Chap10) -/
universe u

open Polynomial

noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S] [IsIntegrallyClosed R]

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-
Domain triage:
* source-facing: the coefficientwise statement that the minimal polynomial over `FractionRing R`
  of an element integral over the normal domain `R` has coefficients in the image of `R`;
* core/canonical owner: `minpoly.isIntegrallyClosed_eq_field_fractions`, specialized to the
  fraction-field extension `FractionRing R ⊆ FractionRing S`;
* bridge/view: `coeff_map` turns the canonical polynomial identity into the textbook
  coefficientwise conclusion.
-/
recall minpoly.isIntegrallyClosed_eq_field_fractions

/-- Lemma 10.38.6: every coefficient of the minimal polynomial over `FractionRing R` of an element
integral over the normal domain `R` lies in the image of `R`. -/
theorem coeff_minpoly_mem_range_of_isIntegral (g : S) (hg : IsIntegral R g) (n : ℕ) :
    (minpoly K (algebraMap S L g)).coeff n ∈ Set.range (algebraMap R K) := by
  refine ⟨(minpoly R g).coeff n, ?_⟩
  rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hg, coeff_map]

/-! ### Proposition_10_38_7 (from Chap10) -/
universe u v

section

open Ideal

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsDomain S] [Algebra R S] [FaithfulSMul R S]
variable [Algebra.IsIntegral R S] [IsIntegrallyClosed R]

/- Domain triage:
* primary domain: going down for integral extensions of domains and prime ideals lying over one
  another;
* sampled owner declarations:
  `Algebra.HasGoingDown`,
  the integrally-closed-domain instance in
  `Mathlib.RingTheory.IntegralClosure.GoingDown`,
  `Ideal.exists_ideal_le_liesOver_of_le`,
  and the chapter-level recall style in `Lemma_10_39_19`;
* layer: `core/canonical` for the owner instance, with the textbook prime-lifting conclusion as
  derived `bridge/view` API.

Primitive-vs-derived split:
* primitive data: none in this file; Proposition 10.38.7 is a canonical recall item once the
  ambient hypotheses are in place;
* derived API: the source-facing existence statement for primes below a chosen `Q'`.
-/
/- Proposition 10.38.7 (Stacks tag `00H8`): let `R ⊆ S` be an inclusion of domains with `R`
normal and `S` integral over `R`. Then for primes `p ≤ p'` of `R` and any prime `Q'` of `S`
lying over `p'`, there exists a prime `Q ≤ Q'` of `S` lying over `p`; equivalently, the algebra
map `R → S` has going down. In mathlib this is the canonical instance
`Algebra.HasGoingDown R S`; the inclusion hypothesis `R ⊆ S` is encoded by `FaithfulSMul R S`,
and normality of the domain `R` is `IsIntegrallyClosed R`. This owner instance is unnamed, so the
direct canonical recall shape is instance synthesis of `Algebra.HasGoingDown R S`. The domain
structure on `R` is inferred from the faithful inclusion into the domain `S`. -/
#check (inferInstance : Algebra.HasGoingDown R S)

/- Companion recall: after instantiating the owner class above, the source-shaped prime-ideal
conclusion is the canonical theorem `Ideal.exists_ideal_le_liesOver_of_le`. -/
recall exists_ideal_le_liesOver_of_le
    [Algebra.HasGoingDown R S] {p p' : Ideal R} [p.IsPrime] [p'.IsPrime] (Q' : Ideal S)
    [Q'.IsPrime] [Q'.LiesOver p'] (hpp' : p ≤ p') : ∃ Q ≤ Q', Q.IsPrime ∧ Q.LiesOver p

end
