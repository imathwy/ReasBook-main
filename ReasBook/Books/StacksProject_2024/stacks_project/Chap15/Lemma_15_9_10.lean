import Mathlib
import StacksProject_2024.Chap15.Lemma_15_9_6
import StacksProject_2024.Chap15.Lemma_15_9_8
import StacksProject_2024.Chap15.Lemma_15_9_9

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open Topology PrimeSpectrum
open scoped TensorProduct
open Algebra.TensorProduct
open Ideal.Quotient (eq_zero_iff_mem)

universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.IsIntegral A B]

/- Domain-style sampling:
- primary domain: quotient comparison maps for extended ideals under tensor base change;
- sampled owner declarations: `Ideal.le_comap_map`, `Ideal.map_map`, `Ideal.quotientMapₐ`,
  `Algebra.TensorProduct.includeLeft`;
- best owner abstraction: the quotient algebra map induced by tensor base change is the canonical
  owner `Ideal.quotientMapₐ`; the extended-ideal containment is only proof data for that owner;
- primitive data: the ideal `I` and the algebra map `includeLeft : B →ₐ[A] B ⊗[A] A'`;
- derived API: the induced quotient map on `B / I B`.

Layer triage:
- `source-facing`: the idempotent-lifting existence theorem below;
- `core/canonical`: `Ideal.quotientMapₐ`;
- `bridge/view`: the extended-ideal containment used to instantiate that quotient map. -/

omit [Algebra.IsIntegral A B] in
private theorem extendedIdeal_le_comap_extendedIdeal
    (I : Ideal A) {C : Type*} [CommRing C] [Algebra A C] (f : B →ₐ[A] C) :
    I.map (algebraMap A B) ≤
      (Ideal.map (algebraMap A C) I).comap f := by
  simpa [Ideal.map_map] using
    (show Ideal.map (algebraMap A B) I ≤
        Ideal.comap (f : B →+* C)
          (Ideal.map (f : B →+* C) (Ideal.map (algebraMap A B) I)) from
      Ideal.le_comap_map)

/-- Helper for Lemma 15.9.10: the powers `X ^ d` and `(X - 1) ^ d` are coprime. -/
lemma x_pow_X_sub_one_pow_isCoprime
    {R : Type*} [CommRing R] (d : ℕ) :
    IsCoprime (X ^ d : R[X]) ((X - 1) ^ d) := by
  -- A Bézout identity for `X` and `X - 1` propagates to their powers.
  have hbase : IsCoprime (X : R[X]) (X - 1) := by
    refine ⟨1, -1, ?_⟩
    ring
  exact hbase.pow

/-- Helper for Lemma 15.9.10: mapping `(X - 1)^d` across a ring equivalence gives the native
polynomial over the target ring. -/
private lemma map_X_sub_one_pow_eq_X_sub_one_pow_via_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (d : ℕ) :
    (((X - 1) ^ d : R[X]).map e.toRingHom) = ((X - 1) ^ d : S[X]) := by
  -- The coefficient map fixes `X`, sends `1` to `1`, and commutes with powers.
  simp

/-- Helper for Lemma 15.9.10: every positive power of an idempotent is the idempotent itself. -/
private lemma pow_eq_self_of_pos_of_isIdempotentElem
    {R : Type*} [CommRing R] {e : R}
    (he : IsIdempotentElem e) {n : ℕ} (hn : 0 < n) :
    e ^ n = e := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  clear hn
  -- Peel off one factor and collapse the remaining power by induction.
  induction m with
  | zero =>
      simp
  | succ m ihm =>
      calc
        e ^ Nat.succ (Nat.succ m) = e ^ Nat.succ m * e := by rw [pow_succ]
        _ = e * e := by rw [ihm]
        _ = e := he.eq

/-- Helper for Lemma 15.9.10: evaluating `X ^ d` at an idempotent returns that idempotent when
`d > 0`. -/
private lemma aeval_X_pow_eq_of_isIdempotentElem
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {e : S} {d : ℕ}
    (he : IsIdempotentElem e) (hd : 0 < d) :
    aeval e (X ^ d : R[X]) = e := by
  -- Evaluate to `e ^ d`, then collapse the positive idempotent power.
  simpa [Polynomial.aeval_def] using pow_eq_self_of_pos_of_isIdempotentElem he hd

/-- Helper for Lemma 15.9.10: evaluating `(X - 1) ^ d` at any element lands in the ideal generated
by its complement when `d > 0`. -/
private lemma aeval_X_sub_one_pow_mem_span_one_sub
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {e : S} {d : ℕ}
    (hd : 0 < d) :
    aeval e ((X - 1) ^ d : R[X]) ∈ Ideal.span ({1 - e} : Set S) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  -- One copy of `e - 1` already generates the complementary principal ideal.
  have hmem : (e - 1) ^ n * (e - 1) ∈ Ideal.span ({1 - e} : Set S) := by
    rw [Ideal.mem_span_singleton]
    refine ⟨-((e - 1) ^ n), ?_⟩
    ring
  simpa [Polynomial.aeval_def, pow_succ] using hmem

/-- Helper for Lemma 15.9.10: quotienting after evaluation agrees with evaluating after quotienting
the coefficients, provided the coefficient square commutes. -/
private lemma quotient_aeval_eq_aeval_map_tensor_lift
    {A1 B1 : Type*} [CommRing A1] [CommRing B1] [Algebra A1 B1]
    (I1 : Ideal A1) (IB1 : Ideal B1)
    [Algebra (A1 ⧸ I1) (B1 ⧸ IB1)]
    (hcomm :
      (algebraMap (A1 ⧸ I1) (B1 ⧸ IB1)).comp (Ideal.Quotient.mk I1) =
        (Ideal.Quotient.mk IB1).comp (algebraMap A1 B1))
    (p : A1[X]) (b1 : B1) :
    Ideal.Quotient.mk IB1 (aeval b1 p) =
      aeval (Ideal.Quotient.mk IB1 b1) (p.map (Ideal.Quotient.mk I1)) := by
  -- This is exactly the canonical `map_aeval_eq_aeval_map` transport across the quotient square.
  simpa [Polynomial.aeval_def] using p.map_aeval_eq_aeval_map hcomm b1

/-- Helper for Lemma 15.9.10: after passing from `B1 / I B1` to a prime quotient `B1 / Q`, the
evaluation of a polynomial over `A1` can still be computed by evaluating the reduced polynomial at
the image of the chosen element. -/
private lemma quotient_factor_aeval_eq_aeval_for_prime_quotient
    {A1 B1 : Type*} [CommRing A1] [CommRing B1] [Algebra A1 B1]
    (I1 : Ideal A1) {Q : PrimeSpectrum B1}
    [Algebra (A1 ⧸ I1) (B1 ⧸ Q.asIdeal)]
    (hcomm :
      (algebraMap (A1 ⧸ I1) (B1 ⧸ Q.asIdeal)).comp (Ideal.Quotient.mk I1) =
        (Ideal.Quotient.mk Q.asIdeal).comp (algebraMap A1 B1))
    (p : A1[X]) (b1 : B1) :
    Ideal.Quotient.mk Q.asIdeal (aeval b1 p) =
      aeval (Ideal.Quotient.mk Q.asIdeal b1) (p.map (Ideal.Quotient.mk I1)) := by
  -- This is the same quotient-evaluation transport as above, specialized to the prime quotient
  -- that appears in the geometric support contradiction.
  simpa using
    quotient_aeval_eq_aeval_map_tensor_lift
      (A1 := A1) (B1 := B1) I1 Q.asIdeal hcomm p b1

/-- Helper for Lemma 15.9.10: the canonical quotient factor map sends the class of a representative
to its class in the larger quotient. -/
private lemma prime_quotient_factor_apply_mk
    {R : Type*} [CommRing R] (S T : Ideal R) (hST : S ≤ T) (z : R) :
    Ideal.Quotient.factor (R := R) (S := S) (T := T) hST (Ideal.Quotient.mk S z) =
      Ideal.Quotient.mk T z := by
  rfl

/-- Helper for Lemma 15.9.10: if `Q` lies over `p ∈ V(I)`, then the extended ideal `I S` is
contained in `Q`. -/
private lemma map_le_asIdeal_of_mem_zeroLocus_of_comap_eq
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) {Q : PrimeSpectrum S} {p : PrimeSpectrum R}
    (hp : p ∈ PrimeSpectrum.zeroLocus (I : Set R))
    (hQp : PrimeSpectrum.comap (algebraMap R S) Q = p) :
    Ideal.map (algebraMap R S) I ≤ Q.asIdeal := by
  -- Membership in `V(I)` gives `I ≤ p`; then `Ideal.map_le_iff_le_comap` finishes after
  -- identifying the contraction of `Q` with `p`.
  have hp_le : I ≤ p.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus p (I : Set R)).1 hp
  have hcomap : p.asIdeal = Ideal.comap (algebraMap R S) Q.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hQp).symm
  exact Ideal.map_le_iff_le_comap.mpr <| by
    simpa [hcomap] using hp_le

/-- Helper for Lemma 15.9.10: in a domain-like target, evaluating `(X - 1) ^ d` at zero is
nonzero for positive `d`. -/
private lemma aeval_X_sub_one_pow_ne_zero_at_zero
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Nontrivial S] [NoZeroDivisors S] {d : ℕ}
    (_hd : 0 < d) :
    aeval (0 : S) ((X - 1) ^ d : R[X]) ≠ 0 := by
  -- Evaluating at zero keeps only the constant coefficient, which here is `(-1)^d`.
  intro hzero
  have hcoeff_zero : (algebraMap R S) (((X - 1 : R[X]) ^ d).coeff 0) = 0 := by
    simpa [Polynomial.aeval_def] using hzero
  have hcoeffR : (((X - 1 : R[X]) ^ d).coeff 0) = (-1 : R) ^ d := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [sub_eq_add_neg]
  have hcoeff_eval : (algebraMap R S) (((X - 1 : R[X]) ^ d).coeff 0) = (- (1 : S)) ^ d := by
    calc
      (algebraMap R S) (((X - 1 : R[X]) ^ d).coeff 0) = algebraMap R S ((-1 : R) ^ d) := by
        rw [hcoeffR]
      _ = (- (1 : S)) ^ d := by simp
  have hne : (- (1 : S)) ^ d ≠ 0 := by
    exact pow_ne_zero d (neg_ne_zero.mpr one_ne_zero)
  exact hne (hcoeff_eval.symm.trans hcoeff_zero)

/-- Helper for Lemma 15.9.10: a prime in the zero locus of the ideal generated by `x` and `y`
contains both generators. -/
private lemma pair_mem_asIdeal_of_mem_zeroLocus_span
    {R : Type*} [CommRing R] {x y : R} {Q : PrimeSpectrum R}
    (hQ : Q ∈ PrimeSpectrum.zeroLocus (Ideal.span ({x, y} : Set R) : Set R)) :
    x ∈ Q.asIdeal ∧ y ∈ Q.asIdeal := by
  -- The zero-locus condition is exactly the ideal containment `span {x, y} ≤ Q`.
  have hspan :
      Ideal.span ({x, y} : Set R) ≤ Q.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus Q (Ideal.span ({x, y} : Set R) : Set R)).1 hQ
  constructor
  · -- The left generator belongs to the spanning ideal by construction.
    exact hspan (Ideal.subset_span (by simp))
  · -- The right generator belongs to the same spanning ideal as well.
    exact hspan (Ideal.subset_span (by simp))

/-- Helper for Lemma 15.9.10: the transported factor evaluations cannot vanish simultaneously in a
prime quotient lying over `V(I1)`. -/
private theorem prime_quotient_contradiction_of_transported_factor_evaluations
    {A0 A1 B1 : Type*} [CommRing A0] [CommRing A1] [CommRing B1] [Algebra A1 B1]
    (I1 : Ideal A1) (IB1 : Ideal B1) [Algebra (A1 ⧸ I1) (B1 ⧸ IB1)]
    (hIB1_map : Ideal.map (algebraMap A1 B1) I1 = IB1)
    {Q : PrimeSpectrum B1} (d : ℕ) (hd : 0 < d) (eIso : A0 ≃+* (A1 ⧸ I1))
    (h1 : A1[X]) (b1 x y : B1) (ebar1 : B1 ⧸ IB1)
    (hb1 : ebar1 = Ideal.Quotient.mk IB1 b1)
    (hx_eval : Ideal.Quotient.mk IB1 x = ebar1)
    (hy_def : y = aeval b1 h1)
    (hhred :
      (((X - 1) ^ d : A0[X]).map eIso.toRingHom) = h1.map (Ideal.Quotient.mk I1))
    (hQxy : Q ∈ PrimeSpectrum.zeroLocus (Ideal.span ({x, y} : Set B1) : Set B1))
    (hQI : PrimeSpectrum.comap (algebraMap A1 B1) Q ∈ PrimeSpectrum.zeroLocus (I1 : Set A1)) :
    False := by
  -- Passing to the prime quotient forces both evaluated factors to vanish.
  rcases pair_mem_asIdeal_of_mem_zeroLocus_span (x := x) (y := y) hQxy with ⟨hxQ, hyQ⟩
  have hI1Q :
      Ideal.map (algebraMap A1 B1) I1 ≤ Q.asIdeal :=
    map_le_asIdeal_of_mem_zeroLocus_of_comap_eq
      (I := I1) (Q := Q)
      (p := PrimeSpectrum.comap (algebraMap A1 B1) Q) hQI rfl
  have hI1Q' :
      I1 ≤ Ideal.comap (algebraMap A1 B1) Q.asIdeal :=
    Ideal.map_le_iff_le_comap.mp hI1Q
  let _ : Algebra (A1 ⧸ I1) (B1 ⧸ Q.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap hI1Q'
  have hIB1Q : IB1 ≤ Q.asIdeal := by
    rw [← hIB1_map]
    exact hI1Q
  let qQ : B1 ⧸ IB1 →+* B1 ⧸ Q.asIdeal :=
    Ideal.Quotient.factor (R := B1) (S := IB1) (T := Q.asIdeal) hIB1Q
  have hqQ_ebar_zero : qQ ebar1 = 0 := by
    -- The first factor becomes zero in the prime quotient.
    calc
      qQ ebar1 = qQ (Ideal.Quotient.mk IB1 x) := by rw [← hx_eval]
      _ = Ideal.Quotient.mk Q.asIdeal x := by
            rw [prime_quotient_factor_apply_mk IB1 Q.asIdeal hIB1Q x]
      _ = 0 := eq_zero_iff_mem.mpr hxQ
  have hb1Q_zero : Ideal.Quotient.mk Q.asIdeal b1 = 0 := by
    -- The chosen lift `b1` maps to the same residue class as `ebar1`, hence also to zero.
    calc
      Ideal.Quotient.mk Q.asIdeal b1 = qQ (Ideal.Quotient.mk IB1 b1) := by
        rw [prime_quotient_factor_apply_mk IB1 Q.asIdeal hIB1Q b1]
      _ = qQ ebar1 := by rw [← hb1]
      _ = 0 := hqQ_ebar_zero
  have hquotient_prime_comm :
      (algebraMap (A1 ⧸ I1) (B1 ⧸ Q.asIdeal)).comp (Ideal.Quotient.mk I1) =
        (Ideal.Quotient.mk Q.asIdeal).comp (algebraMap A1 B1) := by
    -- The coefficient square to the prime quotient commutes on representatives.
    ext a
    rfl
  have hyQ_eval :
      Ideal.Quotient.mk Q.asIdeal y =
        aeval (Ideal.Quotient.mk Q.asIdeal b1)
          ((((X - 1) ^ d : A0[X]).map eIso.toRingHom)) := by
    -- Reuse the same quotient-evaluation transport in the prime quotient.
    calc
      Ideal.Quotient.mk Q.asIdeal y = Ideal.Quotient.mk Q.asIdeal (aeval b1 h1) := by
        rw [hy_def]
      _ =
          aeval (Ideal.Quotient.mk Q.asIdeal b1) (h1.map (Ideal.Quotient.mk I1)) := by
            simpa using
              quotient_factor_aeval_eq_aeval_for_prime_quotient
                (I1 := I1) hquotient_prime_comm h1 b1
      _ =
          aeval (Ideal.Quotient.mk Q.asIdeal b1)
            ((((X - 1) ^ d : A0[X]).map eIso.toRingHom)) := by
              rw [← hhred]
  have hmap :
      (((X - 1) ^ d : A0[X]).map eIso.toRingHom) = ((X - 1) ^ d : (A1 ⧸ I1)[X]) := by
    -- Normalize the transported polynomial back to the native `(X - 1)^d`.
    simpa using map_X_sub_one_pow_eq_X_sub_one_pow_via_ringEquiv eIso d
  have hzero_eval :
      aeval (0 : B1 ⧸ Q.asIdeal) ((X - 1) ^ d : (A1 ⧸ I1)[X]) = 0 := by
    -- Substituting the zero class of `b1` reduces to the forbidden evaluation at zero.
    calc
      aeval (0 : B1 ⧸ Q.asIdeal) ((X - 1) ^ d : (A1 ⧸ I1)[X]) =
          aeval (Ideal.Quotient.mk Q.asIdeal b1) ((((X - 1) ^ d : A0[X]).map eIso.toRingHom)) := by
            rw [hb1Q_zero, ← hmap]
      _ = Ideal.Quotient.mk Q.asIdeal y := by rw [← hyQ_eval]
      _ = 0 := eq_zero_iff_mem.mpr hyQ
  exact
    aeval_X_sub_one_pow_ne_zero_at_zero
      (R := A1 ⧸ I1) (S := B1 ⧸ Q.asIdeal) (d := d) hd hzero_eval

/-- Helper for Lemma 15.9.10: a pointwise prime-avoidance contradiction upgrades to the exact
disjoint-closure hypothesis needed by Lemma 15.9.8. -/
private theorem image_zeroLocus_disjoint_of_prime_avoidance
    {A1 B1 : Type*} [CommRing A1] [CommRing B1] [Algebra A1 B1]
    [Algebra.IsIntegral A1 B1]
    (I1 : Ideal A1) (J : Ideal B1)
    (havoid :
      ∀ Q : PrimeSpectrum B1,
        Q ∈ PrimeSpectrum.zeroLocus (J : Set B1) →
        PrimeSpectrum.comap (algebraMap A1 B1) Q ∈ PrimeSpectrum.zeroLocus (I1 : Set A1) →
        False) :
    Disjoint
      (closure (PrimeSpectrum.comap (algebraMap A1 B1) '' PrimeSpectrum.zeroLocus (J : Set B1)))
      (PrimeSpectrum.zeroLocus (I1 : Set A1)) := by
  have hInt : RingHom.IsIntegral (algebraMap A1 B1) :=
    algebraMap_isIntegral_iff.mpr inferInstance
  have hClosedImage :
      IsClosed
        (PrimeSpectrum.comap (algebraMap A1 B1) ''
          PrimeSpectrum.zeroLocus (J : Set B1)) := by
    -- Integral maps induce closed maps on spectra, so the closure is already the actual image.
    exact
      (PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap A1 B1) hInt)
        _ (isClosed_zeroLocus (J : Set B1))
  -- Once the closure is removed, disjointness is exactly the pointwise prime-avoidance statement.
  rw [hClosedImage.closure_eq]
  exact Set.disjoint_left.2 fun p hpImage hpI ↦ by
    rcases hpImage with ⟨Q, hQJ, rfl⟩
    exact havoid Q hQJ hpI

/-- Helper for Lemma 15.9.10: the common support of a pair misses `V(I1)` once every prime in
that support lying over `V(I1)` leads to a contradiction. -/
private theorem image_zeroLocus_span_pair_disjoint_of_prime_contradiction
    {A1 B1 : Type*} [CommRing A1] [CommRing B1] [Algebra A1 B1]
    [Algebra.IsIntegral A1 B1]
    (I1 : Ideal A1) (x y : B1)
    (havoid :
      ∀ Q : PrimeSpectrum B1,
        Q ∈ PrimeSpectrum.zeroLocus (Ideal.span ({x, y} : Set B1) : Set B1) →
        PrimeSpectrum.comap (algebraMap A1 B1) Q ∈ PrimeSpectrum.zeroLocus (I1 : Set A1) →
        False) :
    Disjoint
      (closure
        (PrimeSpectrum.comap (algebraMap A1 B1) ''
          PrimeSpectrum.zeroLocus (Ideal.span ({x, y} : Set B1) : Set B1)))
      (PrimeSpectrum.zeroLocus (I1 : Set A1)) := by
  -- This is the pair-generated ideal specialization used in the main theorem.
  simpa using
    image_zeroLocus_disjoint_of_prime_avoidance
      (A1 := A1) (B1 := B1) I1 (Ideal.span ({x, y} : Set B1)) havoid

/-- Helper for Lemma 15.9.10: once the common support of `x` and `y` is known to miss `V(I1)`,
Lemma 15.9.8 produces the localization element that is `1` modulo `I1` and maps into the ideal
generated by `x` and `y`. -/
private theorem exists_eq_one_mod_ideal_and_image_mem_span_pair_of_prime_contradiction
    {A1 B1 : Type*} [CommRing A1] [CommRing B1] [Algebra A1 B1]
    [Algebra.IsIntegral A1 B1]
    (I1 : Ideal A1) (x y : B1)
    (havoid :
      ∀ Q : PrimeSpectrum B1,
        Q ∈ PrimeSpectrum.zeroLocus (Ideal.span ({x, y} : Set B1) : Set B1) →
        PrimeSpectrum.comap (algebraMap A1 B1) Q ∈ PrimeSpectrum.zeroLocus (I1 : Set A1) →
        False) :
    ∃ s : A1, Ideal.Quotient.mk I1 s = 1 ∧
      algebraMap A1 B1 s ∈ Ideal.span ({x, y} : Set B1) := by
  -- Convert the pointwise prime contradiction into the closed-set disjointness hypothesis required
  -- by Lemma 15.9.8, then read off the desired localization element.
  have hdisj :
      Disjoint
        (closure
          (PrimeSpectrum.comap (algebraMap A1 B1) ''
            PrimeSpectrum.zeroLocus (Ideal.span ({x, y} : Set B1) : Set B1)))
        (PrimeSpectrum.zeroLocus (I1 : Set A1)) :=
    image_zeroLocus_span_pair_disjoint_of_prime_contradiction
      (A1 := A1) (B1 := B1) I1 x y havoid
  simpa using
    exists_eq_one_mod_ideal_and_image_mem_of_disjoint_closure_image_zeroLocus
      (algebraMap A1 B1) I1 (Ideal.span ({x, y} : Set B1)) hdisj

/-- Helper for Lemma 15.9.10: integrality of `A → B` survives tensoring on the right with any
`A`-algebra. -/
private theorem tensor_base_change_isIntegral_right
    {A1 : Type u} [CommRing A1] [Algebra A A1] :
    let _ : Algebra A1 (B ⊗[A] A1) := TensorProduct.rightAlgebra
    Algebra.IsIntegral A1 (B ⊗[A] A1) := by
  let _ : Algebra A1 (B ⊗[A] A1) := TensorProduct.rightAlgebra
  let e : A1 ⊗[A] B ≃ₐ[A1] B ⊗[A] A1 :=
    { __ := Algebra.TensorProduct.comm A A1 B
      commutes' := by
        intro a1
        rfl }
  let _ : Algebra.IsIntegral A1 (A1 ⊗[A] B) := inferInstance
  -- First use the canonical integral instance on `A1 ⊗[A] B`, then transport it across the
  -- tensor-commutation equivalence to the right-base-change model `B ⊗[A] A1`.
  exact (AlgEquiv.isIntegral_iff (R := A1) e).mp inferInstance

/-- Helper for Lemma 15.9.10: an orthogonal pair generating the unit ideal produces an
idempotent whose two complementary pieces lie in the corresponding principal ideals. -/
lemma orthogonal_pair_generates_idempotent
    {R : Type*} [CommRing R] (x y : R) (hxy : x * y = 0)
    (hspan : Ideal.span ({x, y} : Set R) = ⊤) :
    ∃ e : R, IsIdempotentElem e ∧
      e ∈ Ideal.span ({x} : Set R) ∧
      1 - e ∈ Ideal.span ({y} : Set R) := by
  -- Choose a Bézout relation `a * x + b * y = 1` and set `e := a * x`.
  have hone : (1 : R) ∈ Ideal.span ({x, y} : Set R) := by
    simpa [hspan] using (Ideal.mem_top : (1 : R) ∈ (⊤ : Ideal R))
  rcases Ideal.mem_span_pair.mp hone with ⟨a, b, hab⟩
  refine ⟨a * x, ?_, ?_, ?_⟩
  · -- The orthogonality `x * y = 0` kills the mixed term in the Bézout identity.
    have heq : a * x = (a * x) ^ 2 := by
      calc
        a * x = (a * x) * 1 := by simp
        _ = (a * x) * (a * x + b * y) := by rw [hab]
        _ = (a * x) * (a * x) + (a * x) * (b * y) := by ring
        _ = (a * x) * (a * x) + 0 := by
              rw [show (a * x) * (b * y) = (a * b) * (x * y) by ring]
              simp [hxy]
        _ = (a * x) ^ 2 := by ring
    simpa [IsIdempotentElem, pow_two] using heq.symm
  · -- The constructed idempotent is visibly a multiple of `x`.
    rw [Ideal.mem_span_singleton]
    exact ⟨a, by ring⟩
  · -- The complementary piece is the `y`-part of the Bézout relation.
    have hcomp : 1 - a * x = b * y := by
      calc
        1 - a * x = (a * x + b * y) - a * x := by rw [hab]
        _ = b * y := by ring
    rw [Ideal.mem_span_singleton, hcomp]
    exact ⟨b, by ring⟩

/-- Helper for Lemma 15.9.10: if an element is supported on an idempotent and its complement is
supported on the complementary idempotent, then the element equals that idempotent. -/
lemma eq_of_mem_span_idempotent_and_compl
    {R : Type*} [CommRing R] {e r : R} (he : IsIdempotentElem e)
    (hr : r ∈ Ideal.span ({e} : Set R))
    (hcomp : 1 - r ∈ Ideal.span ({1 - e} : Set R)) :
    r = e := by
  -- Multiplying the complement relation by `e` kills it, while membership in `(e)` gives `e * r = r`.
  rcases Ideal.mem_span_singleton.mp hr with ⟨a, ha⟩
  rcases Ideal.mem_span_singleton.mp hcomp with ⟨b, hb⟩
  have hmul_left : e * r = r := by
    rw [ha, show e * (e * a) = (e * e) * a by ring, he.eq]
  have hmul_right : e * (1 - r) = 0 := by
    rw [hb]
    rw [show e * ((1 - e) * b) = (e * (1 - e)) * b by ring]
    rw [show e * (1 - e) = 0 by
      calc
        e * (1 - e) = e - e * e := by ring
        _ = e - e := by rw [he.eq]
        _ = 0 := by simp]
    simp
  have hre : e = r := by
    calc
      e = e * 1 := by simp
      _ = e * (r + (1 - r)) := by ring
      _ = e * r + e * (1 - r) := by ring
      _ = r := by rw [hmul_left, hmul_right]; simp
  exact hre.symm

/-- Helper for Lemma 15.9.10: a ring hom carries principal-ideal membership to the corresponding
principal ideal generated by the image. -/
private lemma map_mem_span_singleton
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {u z : R}
    (hz : z ∈ Ideal.span ({u} : Set R)) :
    φ z ∈ Ideal.span ({φ u} : Set S) := by
  -- Expand the principal-ideal witness in the source and map it termwise into the target.
  rcases Ideal.mem_span_singleton.mp hz with ⟨a, ha⟩
  rw [Ideal.mem_span_singleton]
  refine ⟨φ a, ?_⟩
  calc
    φ z = φ (u * a) := by rw [ha]
    _ = φ u * φ a := by simp

/-- Helper for Lemma 15.9.10: once the support and complementary-support relations are transported
into a quotient, the localized idempotent class is uniquely determined. -/
private lemma localized_idempotent_class_eq
    {R1 R2 S : Type*} [CommRing R1] [CommRing R2] [CommRing S]
    (ψ : S →+* R2) (q12 : R1 →+* R2) {ebar1 ybar : R1} {e2 x2 y2 : S}
    (hq12idem : IsIdempotentElem (q12 ebar1))
    (hx2 : ψ x2 = q12 ebar1)
    (hy2 : ψ y2 = q12 ybar)
    (he2mem : e2 ∈ Ideal.span ({x2} : Set S))
    (hcomp2mem : 1 - e2 ∈ Ideal.span ({y2} : Set S))
    (hybar_mem : ybar ∈ Ideal.span ({1 - ebar1} : Set R1)) :
    ψ e2 = q12 ebar1 := by
  -- Transport the support relation for `e2` through `ψ` and rewrite the generator using `hx2`.
  have he2_quotient_mem :
      ψ e2 ∈ Ideal.span ({q12 ebar1} : Set R2) := by
    have hmapped :
        ψ e2 ∈ Ideal.span ({ψ x2} : Set R2) := by
      simpa using map_mem_span_singleton (φ := ψ) he2mem
    simpa [hx2] using hmapped
  -- Transport the complementary support relation for `y2` and then enlarge the generated ideal.
  have hy2_quotient_mem_compl :
      ψ y2 ∈ Ideal.span ({1 - q12 ebar1} : Set R2) := by
    have hmapped :
        q12 ybar ∈ Ideal.span ({q12 (1 - ebar1)} : Set R2) := by
      simpa using map_mem_span_singleton (φ := q12) hybar_mem
    simpa [hy2, map_sub] using hmapped
  have hspan_y2_le :
      Ideal.span ({ψ y2} : Set R2) ≤ Ideal.span ({1 - q12 ebar1} : Set R2) := by
    -- A principal ideal is contained in any ideal that already contains its generator.
    refine Ideal.span_le.2 ?_
    intro z hz
    have hz' : z = ψ y2 := by simpa using hz
    rw [hz']
    exact hy2_quotient_mem_compl
  have hcomp2_quotient_mem :
      1 - ψ e2 ∈ Ideal.span ({1 - q12 ebar1} : Set R2) := by
    have hmapped :
        1 - ψ e2 ∈ Ideal.span ({ψ y2} : Set R2) := by
      simpa [map_sub, hy2] using map_mem_span_singleton (φ := ψ) hcomp2mem
    exact hspan_y2_le hmapped
  exact
    eq_of_mem_span_idempotent_and_compl
      hq12idem he2_quotient_mem hcomp2_quotient_mem

/-- Helper for Lemma 15.9.10: the tensor-product base-change map acts as the canonical left
inclusion on generators coming from `B`. -/
private lemma productMap_includeLeft_apply
    {A A1 A2 B : Type*} [CommRing A] [CommRing A1] [CommRing A2] [CommRing B]
    [Algebra A B] [Algebra A A1] [Algebra A A2] [Algebra A2 (B ⊗[A] A2)]
    (g : A1 →ₐ[A] B ⊗[A] A2) (b : B) :
    (Algebra.TensorProduct.productMap
      (includeLeft : B →ₐ[A] B ⊗[A] A2)
      g)
        ((includeLeft : B →ₐ[A] B ⊗[A] A1) b) =
      (includeLeft : B →ₐ[A] B ⊗[A] A2) b := by
  -- Expand `includeLeft b` to `b ⊗ 1`, then evaluate the product map on that tensor.
  rw [Algebra.TensorProduct.includeLeft_apply]
  rw [Algebra.TensorProduct.productMap_apply_tmul]
  simp

/-- Helper for Lemma 15.9.10: two quotient maps agree on a class once they agree on a chosen
representative of that class. -/
private lemma quotient_maps_agree_on_representative
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {I : Ideal R} {J : Ideal S} {K : Ideal T}
    (qB1 : R ⧸ I →+* S ⧸ J) (q12 : S ⧸ J →+* T ⧸ K) (qB2 : R ⧸ I →+* T ⧸ K)
    {ebar : R ⧸ I} {b : R} {b1 : S}
    (hb : ebar = Ideal.Quotient.mk I b)
    (hb1 : qB1 ebar = Ideal.Quotient.mk J b1)
    (hcomp : q12 (Ideal.Quotient.mk J b1) = qB2 (Ideal.Quotient.mk I b)) :
    q12 (qB1 ebar) = qB2 ebar := by
  -- Rewrite both quotient classes to the common representative and then use `hcomp`.
  calc
    q12 (qB1 ebar) = q12 (Ideal.Quotient.mk J b1) := by rw [hb1]
    _ = qB2 (Ideal.Quotient.mk I b) := hcomp
    _ = qB2 ebar := by rw [hb]

/-- Helper for Lemma 15.9.10: once the image of `s` lies in the ideal generated by `x` and `y`,
any target algebra in which `s` becomes a unit makes the images of `x` and `y` generate `⊤`. -/
private lemma span_pair_eq_top_of_generator_witness_and_isUnit_image
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {s : R} {x y : S}
    (hs_unit : IsUnit (algebraMap R T s))
    (hmem : algebraMap R S s ∈ Ideal.span ({x, y} : Set S)) :
    Ideal.span ({algebraMap S T x, algebraMap S T y} : Set T) = ⊤ := by
  let J : Ideal T := Ideal.span ({algebraMap S T x, algebraMap S T y} : Set T)
  have hs_mem : algebraMap R T s ∈ J := by
    rcases Ideal.mem_span_pair.mp hmem with ⟨a, b, hab⟩
    -- Map the witness relation across the target algebra to land in the localized span.
    refine Ideal.mem_span_pair.mpr ⟨algebraMap S T a, algebraMap S T b, ?_⟩
    calc
      algebraMap S T a * algebraMap S T x + algebraMap S T b * algebraMap S T y =
          algebraMap S T (a * x + b * y) := by
        simp [map_add, map_mul]
      _ = algebraMap S T (algebraMap R S s) := by
        simpa using congrArg (algebraMap S T) hab
      _ = algebraMap R T s := by
        simpa using (DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S T) s).symm
  -- Any ideal containing a unit is already the whole ring.
  exact J.eq_top_of_isUnit_mem hs_mem hs_unit

/-- Helper for Lemma 15.9.10: the canonical map from `Localization.Away s` to `A ⧸ I` exists
because `s` becomes a unit modulo `I`. -/
private theorem isUnit_mk_of_eq_one_mod_ideal
    (I : Ideal A) {s : A} (hs : Ideal.Quotient.mk I s = 1) :
    IsUnit ((Ideal.Quotient.mk I) s) := by
  simpa [hs] using (isUnit_one : IsUnit (1 : A ⧸ I))

/-- Helper for Lemma 15.9.10: the localization lift agrees with the quotient map on coefficients. -/
private theorem awayLiftToQuotient_of_eq_one_mod_ideal_commutes
    (I : Ideal A) {s : A} (hs : Ideal.Quotient.mk I s = 1) (a : A) :
    IsLocalization.Away.lift s (isUnit_mk_of_eq_one_mod_ideal (A := A) I hs)
        (algebraMap A (Localization.Away s) a) =
      Ideal.Quotient.mk I a := by
  simpa using
    IsLocalization.Away.lift_eq s (isUnit_mk_of_eq_one_mod_ideal (A := A) I hs) a

/-- Helper for Lemma 15.9.10: the canonical map from `Localization.Away s` to `A ⧸ I` exists
because `s` becomes a unit modulo `I`. -/
private noncomputable def awayLiftToQuotient_of_eq_one_mod_ideal
    (I : Ideal A) {s : A} (hs : Ideal.Quotient.mk I s = 1) :
    Localization.Away s →ₐ[A] A ⧸ I :=
  { toRingHom := IsLocalization.Away.lift s (isUnit_mk_of_eq_one_mod_ideal (A := A) I hs)
    commutes' := awayLiftToQuotient_of_eq_one_mod_ideal_commutes (A := A) I hs }

/-- Helper for Lemma 15.9.10: the quotient lift from `Localization.Away s` to `A ⧸ I` is
surjective. -/
private theorem awayLiftToQuotient_surjective_of_eq_one_mod_ideal
    (I : Ideal A) {s : A} (hs : Ideal.Quotient.mk I s = 1) :
    Function.Surjective (awayLiftToQuotient_of_eq_one_mod_ideal (A := A) I hs) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨algebraMap A (Localization.Away s) a, ?_⟩
  change awayLiftToQuotient_of_eq_one_mod_ideal (A := A) I hs
      (algebraMap A (Localization.Away s) a) = Ideal.Quotient.mk I a
  simp [awayLiftToQuotient_of_eq_one_mod_ideal]

/-- Helper for Lemma 15.9.10: the extended ideal maps into the kernel of the localization lift. -/
private theorem awayQuotIdeal_le_ker_awayLiftToQuotient_of_eq_one_mod_ideal
    (I : Ideal A) {s : A} (hs : Ideal.Quotient.mk I s = 1) :
    Ideal.map (algebraMap A (Localization.Away s)) I ≤
      RingHom.ker (awayLiftToQuotient_of_eq_one_mod_ideal (A := A) I hs) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change awayLiftToQuotient_of_eq_one_mod_ideal (A := A) I hs
      (algebraMap A (Localization.Away s) a) = 0
  rw [show awayLiftToQuotient_of_eq_one_mod_ideal (A := A) I hs
      (algebraMap A (Localization.Away s) a) = Ideal.Quotient.mk I a by
      simp [awayLiftToQuotient_of_eq_one_mod_ideal]]
  exact eq_zero_iff_mem.mpr ha

/-- Helper for Lemma 15.9.10: the localization lift kills exactly the extended ideal. -/
private theorem ker_awayLiftToQuotient_eq_awayQuotIdeal_of_eq_one_mod_ideal
    (I : Ideal A) {s : A} (hs : Ideal.Quotient.mk I s = 1) :
    RingHom.ker (awayLiftToQuotient_of_eq_one_mod_ideal (A := A) I hs) =
      Ideal.map (algebraMap A (Localization.Away s)) I := by
  rw [Ideal.ext_iff]
  intro z
  constructor
  · intro hz
    have hz0 : awayLiftToQuotient_of_eq_one_mod_ideal (A := A) I hs z = 0 := by
      exact RingHom.mem_ker.mp hz
    obtain ⟨n, a, hzsurj⟩ := IsLocalization.Away.surj s z
    have hza0 : Ideal.Quotient.mk I a = 0 := by
      have hmap :
          awayLiftToQuotient_of_eq_one_mod_ideal (A := A) I hs z *
              Ideal.Quotient.mk I s ^ n =
            Ideal.Quotient.mk I a := by
        simpa [awayLiftToQuotient_of_eq_one_mod_ideal, map_mul, map_pow] using
          congrArg (awayLiftToQuotient_of_eq_one_mod_ideal (A := A) I hs) hzsurj
      simpa [hz0, hs] using hmap.symm
    have haI : a ∈ I := eq_zero_iff_mem.mp hza0
    have hzmul :
        z * algebraMap A (Localization.Away s) s ^ n ∈
          Ideal.map (algebraMap A (Localization.Away s)) I := by
      simpa [hzsurj] using
        Ideal.mem_map_of_mem (algebraMap A (Localization.Away s)) haI
    have hsPowUnit : IsUnit (algebraMap A (Localization.Away s) s ^ n) :=
      IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit s)
    rcases hsPowUnit with ⟨w, hw⟩
    have hw_inv : algebraMap A (Localization.Away s) s ^ n * ↑w⁻¹ = 1 := by
      simpa [hw] using w.mul_inv
    have hz_eq :
        z = (z * algebraMap A (Localization.Away s) s ^ n) * ↑w⁻¹ := by
      calc
        z = z * 1 := by simp
        _ = z * (algebraMap A (Localization.Away s) s ^ n * ↑w⁻¹) := by rw [hw_inv]
        _ = (z * algebraMap A (Localization.Away s) s ^ n) * ↑w⁻¹ := by rw [mul_assoc]
    rw [hz_eq]
    exact (Ideal.map (algebraMap A (Localization.Away s)) I).mul_mem_right _ hzmul
  · intro hz
    exact awayQuotIdeal_le_ker_awayLiftToQuotient_of_eq_one_mod_ideal (A := A) I hs hz

/-- Helper for Lemma 15.9.10: if `s` is `1` modulo `I`, then the quotient by the extended ideal of
`Localization.Away s` is canonically equivalent to `A ⧸ I`. -/
private theorem exists_quotientAlgEquiv_localizationAway_of_eq_one_mod_ideal
    (I : Ideal A) {s : A} (hs : Ideal.Quotient.mk I s = 1) :
    ∃ _eIso : (A ⧸ I) ≃ₐ[A ⧸ I]
      ((Localization.Away s) ⧸ Ideal.map (algebraMap A (Localization.Away s)) I), True := by
  let e :
      ((Localization.Away s) ⧸ Ideal.map (algebraMap A (Localization.Away s)) I) ≃ₐ[A] A ⧸ I :=
    (Ideal.quotientEquivAlgOfEq A
        (ker_awayLiftToQuotient_eq_awayQuotIdeal_of_eq_one_mod_ideal (A := A) I hs).symm).trans <|
      Ideal.quotientKerAlgEquivOfSurjective
        (awayLiftToQuotient_surjective_of_eq_one_mod_ideal (A := A) I hs)
  have he :
      Function.LeftInverse e
        (algebraMap (A ⧸ I)
          ((Localization.Away s) ⧸ Ideal.map (algebraMap A (Localization.Away s)) I)) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change e (Ideal.Quotient.mk _ (algebraMap A (Localization.Away s) a)) =
        Ideal.Quotient.mk I a
    simp [e, awayLiftToQuotient_of_eq_one_mod_ideal]
  have hbij :
      Function.Bijective
        (Algebra.ofId (A ⧸ I)
          ((Localization.Away s) ⧸ Ideal.map (algebraMap A (Localization.Away s)) I)) := by
    refine ⟨he.injective, ?_⟩
    intro y
    refine ⟨e y, ?_⟩
    apply e.injective
    simpa using he (e y)
  exact ⟨AlgEquiv.ofBijective
      (Algebra.ofId (A ⧸ I)
        ((Localization.Away s) ⧸ Ideal.map (algebraMap A (Localization.Away s)) I))
      hbij, trivial⟩

noncomputable def quotientAlgEquiv_localizationAway_of_eq_one_mod_ideal
    (I : Ideal A) {s : A} (hs : Ideal.Quotient.mk I s = 1) :
    (A ⧸ I) ≃ₐ[A ⧸ I]
      ((Localization.Away s) ⧸ Ideal.map (algebraMap A (Localization.Away s)) I) :=
  Classical.choose
    (exists_quotientAlgEquiv_localizationAway_of_eq_one_mod_ideal (A := A) I hs)

-- Proof sketch: choose the polynomial witness for `ebar` from Lemma `15.9.9`, then apply the
-- étale factorization lift of Lemma `15.9.6` to split it modulo `I` into the factors `X^d` and
-- `(X - 1)^d` after an étale base change inducing `A / I ≃ A' / I A'`. Evaluating the lifted
-- factors at a chosen lift of `ebar` in the tensor product gives orthogonal elements. A lying-over
-- argument shows that their common support misses `V(I A')`, so one more localization on the base
-- makes them generate the unit ideal. A Bézout relation then produces the desired idempotent.
/-- Lemma 15.9.10: if `A → B` is integral and `ebar` is an idempotent of `B / I B`, then after an
étale base change `A → A'` inducing an isomorphism `A / I ≃ A' / I A'`, there is an idempotent in
`B ⊗[A] A'` whose image in the quotient by the extended ideal `I` is the base-change of `ebar`. -/
theorem exists_etale_baseChange_idempotent_lift_of_isIdempotentElem_mod_map
    (I : Ideal A) (ebar : B ⧸ I.map (algebraMap A B)) (hebar : IsIdempotentElem ebar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (e' : B ⊗[A] A'),
      IsIdempotentElem e' ∧
        (Ideal.quotientMapₐ (Ideal.map (algebraMap A (B ⊗[A] A')) I)
          (includeLeft : B →ₐ[A] B ⊗[A] A')
          (extendedIdeal_le_comap_extendedIdeal I
            (includeLeft : B →ₐ[A] B ⊗[A] A'))) ebar =
          Ideal.Quotient.mk (Ideal.map (algebraMap A (B ⊗[A] A')) I) e' := by
  -- TODO: the source-faithful proof route has been stabilized into the helper lemmas above:
  -- `localized_idempotent_class_eq`, `productMap_includeLeft_apply`, and
  -- `quotient_maps_agree_on_representative`. The remaining blocker is a deterministic elaboration
  -- timeout in the long localized tensor-product tail of this theorem.
  sorry

end

end Algebra
