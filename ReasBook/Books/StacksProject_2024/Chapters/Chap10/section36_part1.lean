import Mathlib
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_36_1 (from Chap10) -/
/-
Source/core/bridge triage:
* source-facing: integrality of an element and of a ring map in the textbook sense;
* core/canonical: the mathlib owner predicates `RingHom.IsIntegralElem` and
  `RingHom.IsIntegral`;
* bridge/view: the algebra-specialized predicate `IsIntegral`, obtained by applying
  `RingHom.IsIntegralElem` to `algebraMap`.

Primitive data here are only the ring map `φ : R →+* S` and the element `s : S`. The defining
polynomial witness is already part of the owner predicate, so keeping any local wrapper or
restatement would only duplicate existing public API.
-/

/- Definition 10.36.1 (1): for a ring map `φ : R →+* S`, an element `s : S` is integral over `R`
with respect to `φ` exactly in the canonical owner predicate `φ.IsIntegralElem s`, defined by the
existence of a monic polynomial `P : R[X]` with `eval₂ φ s P = 0`. -/
recall RingHom.IsIntegralElem

/- Definition 10.36.1 (2): a ring map `φ : R →+* S` is integral exactly in the canonical owner
predicate `φ.IsIntegral`, i.e. every `s : S` satisfies `φ.IsIntegralElem s`. -/
recall RingHom.IsIntegral

/-! ### Lemma_10_36_2 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Helper for Lemma 10.36.2: the hypothesis `yM ⊆ M` says that `M` is invariant under the
left-multiplication endomorphism by `y`. -/
lemma stable_under_mul_mem_invtSubmodule {y : S} {M : Submodule R S}
    (hy : ∀ m ∈ M, y * m ∈ M) :
    M ∈ (Algebra.lsmul R R S y).invtSubmodule := by
  -- Rewrite the stability hypothesis into the standard invariant-submodule API.
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  intro m hm
  simpa [Algebra.smul_def] using hy m hm

/-- Helper for Lemma 10.36.2: iterating left multiplication by `y` and then applying to `1`
produces the powers of `y`. -/
lemma lsmul_pow_apply_one (y : S) :
    ∀ n : ℕ, ((Algebra.lsmul R R S y : Module.End R S) ^ n) (1 : S) = y ^ n := by
  intro n
  induction n with
  | zero =>
      -- The zeroth iterate is the identity endomorphism.
      simp
  | succ n ih =>
      -- One more iterate multiplies the previous value by `y`.
      calc
        ((Algebra.lsmul R R S y : Module.End R S) ^ (n + 1)) (1 : S)
            = (Algebra.lsmul R R S y) (((Algebra.lsmul R R S y : Module.End R S) ^ n) (1 : S)) := by
                rw [pow_succ', Module.End.mul_apply]
        _ = y * y ^ n := by
              simpa [Algebra.smul_def] using congrArg (fun z : S ↦ y * z) ih
        _ = y ^ (n + 1) := by
              rw [pow_succ']

/-- Helper for Lemma 10.36.2: evaluating the annihilating polynomial of the restricted
left-multiplication endomorphism at the distinguished element `1 ∈ M` recovers `P(y)` in `S`. -/
lemma aeval_restrict_lsmul_apply_one {y : S} {M : Submodule R S}
    (h1 : (1 : S) ∈ M) (hy : ∀ m ∈ M, y * m ∈ M) (P : Polynomial R) :
    ↑((Polynomial.aeval
        ((Algebra.lsmul R R S y).restrict
          ((Algebra.lsmul R R S y).mem_invtSubmodule_iff_forall_mem_of_mem.mp
            (stable_under_mul_mem_invtSubmodule (R := R) (S := S) hy))) P)
      (⟨1, h1⟩ : M)) =
      Polynomial.aeval y P := by
  let f : Module.End R S := Algebra.lsmul R R S y
  have hstable_invt : M ∈ f.invtSubmodule :=
    stable_under_mul_mem_invtSubmodule (R := R) (S := S) hy
  have hstable : ∀ m ∈ M, f m ∈ M :=
    f.mem_invtSubmodule_iff_forall_mem_of_mem.mp hstable_invt
  let φ : Module.End R M := f.restrict hstable
  let oneM : M := ⟨1, h1⟩
  have hpow_restrict : ∀ n : ℕ, ↑(((f.restrict hstable) ^ n) oneM) = y ^ n := by
    intro n
    -- Replace the restricted iterate by the ambient iterate before evaluating at `1`.
    have hpow_eq :
        (f.restrict hstable) ^ n =
          (f ^ n).restrict (Module.End.pow_apply_mem_of_forall_mem (f' := f) n hstable) := by
      simpa using (Module.End.pow_restrict (f' := f) n hstable)
    calc
      ↑(((f.restrict hstable) ^ n) oneM)
          = ↑(((f ^ n).restrict (Module.End.pow_apply_mem_of_forall_mem (f' := f) n hstable))
              oneM) := by
                rw [hpow_eq]
      _ = (f ^ n) (1 : S) := by
            simp [oneM, LinearMap.restrict_apply]
      _ = y ^ n := by
            simpa [f] using lsmul_pow_apply_one (R := R) (S := S) y n
  -- Compare polynomial evaluation term-by-term on additive generators.
  refine Polynomial.induction_on' P ?_ ?_
  · intro P Q hP hQ
    -- The claim is additive in the polynomial.
    calc
      ↑((Polynomial.aeval φ (P + Q)) oneM)
          = ↑((Polynomial.aeval φ P) oneM) + ↑((Polynomial.aeval φ Q) oneM) := by
              simp [Polynomial.aeval_add]
      _ = Polynomial.aeval y P + Polynomial.aeval y Q := by
            rw [hP, hQ]
      _ = Polynomial.aeval y (P + Q) := by
            rw [Polynomial.aeval_add]
  · intro n a
    -- On a monomial, the restricted action on `1` is exactly scalar times `y ^ n`.
    calc
      ↑((Polynomial.aeval φ (Polynomial.monomial n a)) oneM)
          = ↑(((algebraMap R (Module.End R M) a * φ ^ n) oneM)) := by
              rw [Polynomial.aeval_monomial]
      _ = (algebraMap R S) a * y ^ n := by
            simp [Module.End.mul_apply, φ, hpow_restrict n, Algebra.smul_def]
      _ = Polynomial.aeval y (Polynomial.monomial n a) := by
            rw [Polynomial.aeval_monomial]

/-- Owner-form criterion for Lemma 10.36.2: if a finitely generated `R`-submodule `M` of `S`
contains `1` and is stable under multiplication by `y`, then `y` is integral over `R`. -/
theorem isIntegral_of_stable_fg_submodule {y : S} {M : Submodule R S}
    (hfg : M.FG) (h1 : (1 : S) ∈ M) (hy : ∀ m ∈ M, y * m ∈ M) :
    IsIntegral R y := by
  haveI : Module.Finite R M := Module.Finite.of_fg hfg
  have hstable_invt : M ∈ (Algebra.lsmul R R S y).invtSubmodule :=
    stable_under_mul_mem_invtSubmodule (R := R) (S := S) hy
  have hstable : ∀ m ∈ M, (Algebra.lsmul R R S y) m ∈ M :=
    (Algebra.lsmul R R S y).mem_invtSubmodule_iff_forall_mem_of_mem.mp hstable_invt
  let φ : Module.End R M := (Algebra.lsmul R R S y).restrict hstable
  let oneM : M := ⟨1, h1⟩
  -- Apply finite-module Cayley-Hamilton to the restricted left-multiplication map.
  obtain ⟨P, hmonic, hP⟩ := LinearMap.exists_monic_and_aeval_eq_zero R φ
  have hP_apply : (Polynomial.aeval φ P) oneM = 0 := by
    -- Evaluate the annihilating endomorphism at the element represented by `1`.
    simpa [hP] using congrArg (fun f : Module.End R M ↦ f oneM) hP
  have hP_apply_coe : ↑((Polynomial.aeval φ P) oneM) = (0 : S) := by
    simpa using congrArg Subtype.val hP_apply
  have hP_y : Polynomial.aeval y P = 0 := by
    -- The restricted polynomial identity at `1` is exactly the polynomial identity for `y`.
    calc
      Polynomial.aeval y P = ↑((Polynomial.aeval φ P) oneM) := by
        symm
        exact aeval_restrict_lsmul_apply_one (R := R) (S := S) (M := M) h1 hy P
      _ = 0 := hP_apply_coe
  exact ⟨P, hmonic, by simpa [Polynomial.aeval_def] using hP_y⟩

/-- Lemma 10.36.2: if there exists a finitely generated `R`-submodule `M` of `S` containing `1`
and stable under multiplication by `y`, then `y` is integral over `R`. This is the thin
source-facing corollary of `isIntegral_of_stable_fg_submodule`. -/
theorem isIntegral_of_exists_fg_submodule_of_one_mem_of_mul_mem {y : S}
    (hM : ∃ M : Submodule R S, M.FG ∧ (1 : S) ∈ M ∧ ∀ m ∈ M, y * m ∈ M) :
    IsIntegral R y := by
  rcases hM with ⟨M, hfg, h1, hy⟩
  -- Unpack the witness submodule and invoke the owner-form criterion.
  exact isIntegral_of_stable_fg_submodule hfg h1 hy

end

/-! ### Lemma_10_36_3 (from Chap10) -/
/- Lemma 10.36.3: a finite ring map is integral. This is exactly the canonical mathlib theorem
`RingHom.Finite.to_isIntegral`. -/
recall RingHom.Finite.to_isIntegral

/-! ### Lemma_10_36_4 (from Chap10) -/
universe u v

open Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.36.4: a finite set of elements of an `R`-algebra `S` is integral over `R`
elementwise if and only if it is contained in an `R`-subalgebra of `S` that is finite over
`R`. -/
theorem forall_isIntegral_iff_exists_subalgebra_finite_containing {s : Set S} (hs : s.Finite) :
    (∀ x ∈ s, IsIntegral R x) ↔
      ∃ S' : Subalgebra R S, Module.Finite R S' ∧ s ⊆ S' := by
  constructor
  · intro hs_integral
    exact ⟨adjoin R s, finite_adjoin_of_finite_of_isIntegral hs hs_integral, subset_adjoin⟩
  · rintro ⟨S', hS', hsS'⟩ x hx
    letI := hS'
    have hInt : Algebra.IsIntegral R S' := inferInstance
    exact S'.isIntegral_iff.mp hInt x (hsS' hx)

end

/-! ### Lemma_10_36_5 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra `S` has a finite generating set consisting of elements integral over `R`. -/
def HasFiniteIntegralGeneratingSet
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∃ s : Finset S, (∀ x ∈ (s : Set S), IsIntegral R x) ∧ Algebra.adjoin R (s : Set S) = ⊤

/-- A finite `R`-algebra is exactly one generated by finitely many elements that are each
integral over `R`. -/
private theorem finite_iff_exists_integral_generators :
    Module.Finite R S ↔
      HasFiniteIntegralGeneratingSet R S := by
  constructor
  · intro h
    letI : Module.Finite R S := h
    obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R S).out
    exact ⟨s, fun x _ ↦ IsIntegral.of_finite R x, hs⟩
  · rintro ⟨s, hsInt, hs⟩
    have htop : Module.Finite R (⊤ : Subalgebra R S) := by
      have hfinite : Module.Finite R (Algebra.adjoin R (s : Set S)) :=
        Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet hsInt
      rw [hs] at hfinite
      exact hfinite
    letI : Module.Finite R (⊤ : Subalgebra R S) := htop
    exact Module.Finite.equiv Subalgebra.topEquiv.toLinearEquiv

/-- Lemma 10.36.5: for an `R`-algebra `S`, the following are equivalent: `S` is finite over `R`;
`S` is integral and of finite type over `R`; and `S` is generated as an `R`-algebra by finitely
many elements that are each integral over `R`. -/
theorem finite_tfae_isIntegral_finiteType_exists_integral_generators :
    List.TFAE
      [ Module.Finite R S
      , Algebra.IsIntegral R S ∧ Algebra.FiniteType R S
      , HasFiniteIntegralGeneratingSet R S
      ] := by
  tfae_have 1 ↔ 2 := Algebra.finite_iff_isIntegral_and_finiteType
  tfae_have 1 ↔ 3 := finite_iff_exists_integral_generators
  tfae_finish

end

/-! ### Lemma_10_36_6 (from Chap10) -/
/- Lemma 10.36.6: if `R → S` and `S → T` are integral ring homomorphisms, then the composite
ring homomorphism `R → T` is integral. This is exactly the canonical mathlib theorem
`RingHom.IsIntegral.trans`. -/
recall RingHom.IsIntegral.trans

/-! ### Lemma_10_36_7 (from Chap10) -/
/- Lemma 10.36.7: for a ring homomorphism `R → S`, the elements of `S` that are integral over
`R` form an `R`-subalgebra of `S`. In mathlib this canonical subalgebra is `integralClosure R S`.
-/
recall integralClosure

/- Companion recall: membership in `integralClosure R S` is exactly integrality over `R`. This is
the single-step bridge from the source set-theoretic phrasing to the canonical subalgebra API. -/
recall mem_integralClosure_iff

/-! ### Lemma_10_36_8 (from Chap10) -/
universe u v w

open Polynomial

/- Domain triage:
* source-facing: integrality of an element in a finite product algebra.
* core/canonical owner: `IsIntegral`.
* bridge/view: `Polynomial.piEquiv`, the evaluation maps `Pi.evalRingHom`, and the binary owner
  theorem `IsIntegral.pair_iff`.
Primitive data remains exactly the witness polynomial from `IsIntegral`; the componentwise
criterion is derived API. -/

namespace IsIntegral

/-- Lemma 10.36.8: an element of a finite product ring is integral over the product ring if and
only if each component is integral over the corresponding factor. -/
-- Proof sketch: use `Polynomial.piEquiv` to pass between a polynomial over the product ring and
-- its tuple of component polynomials. For the reverse implication, pad the component annihilating
-- polynomials to a common degree before reassembling them into a single monic polynomial over the
-- product ring.
theorem pi_iff {ι : Type u} [Finite ι] {R : ι → Type v} {S : ι → Type w}
    [∀ i, CommRing (R i)] [∀ i, Ring (S i)] [∀ i, Algebra (R i) (S i)] {s : Π i, S i} :
    IsIntegral (Π i, R i) s ↔ ∀ i, IsIntegral (R i) (s i) := by
  classical
  let _ := Fintype.ofFinite ι
  let e := piEquiv R
  have h_eval (r : Polynomial (Π i, R i)) (i : ι) :
      Pi.evalRingHom S i (aeval s r) = aeval (s i) (e r i) := by
    simpa [e, piEquiv] using
      r.map_aeval_eq_aeval_map
        (show (algebraMap (R i) (S i)).comp (Pi.evalRingHom R i) =
            (Pi.evalRingHom S i).comp (algebraMap (Π i, R i) (Π i, S i)) by
          ext x
          rfl)
        s
  constructor
  · rintro ⟨p, hpM, hp0⟩ i
    refine ⟨e p i, hpM.map (Pi.evalRingHom R i), ?_⟩
    have h : Pi.evalRingHom S i (aeval s p) = 0 := congrArg (Pi.evalRingHom S i) hp0
    rw [h_eval p i] at h
    exact h
  · intro hs
    choose p hpM hp0 using hs
    let N : ℕ := Finset.univ.sup fun i : ι ↦ (p i).natDegree
    let qfun : Π i, Polynomial (R i) := fun i ↦ p i * X ^ (N - (p i).natDegree)
    let q : Polynomial (Π i, R i) := e.symm qfun
    have hle (i : ι) : (p i).natDegree ≤ N := by
      let f : ι → ℕ := fun j ↦ (p j).natDegree
      change f i ≤ (Finset.univ : Finset ι).sup f
      exact Finset.le_sup (show i ∈ (Finset.univ : Finset ι) by simp)
    have hq (i : ι) : e q i = qfun i := by
      simp [q, qfun]
    refine ⟨q, ?_, ?_⟩
    · refine monic_of_natDegree_le_of_coeff_eq_one N ?_ ?_
      · rw [natDegree_le_iff_coeff_eq_zero]
        intro n hn
        ext i
        have hle_i : (p i).natDegree ≤ N := hle i
        have hk : N - (p i).natDegree ≤ n := by
          omega
        have hqcoeff : (qfun i).coeff n = 0 := by
          dsimp [qfun]
          rw [coeff_mul_X_pow', if_pos hk]
          · apply Polynomial.coeff_eq_zero_of_natDegree_lt
            omega
        have : q.coeff n i = (qfun i).coeff n := by
          simpa [e, piEquiv] using
            congrArg (fun f : Polynomial (R i) ↦ f.coeff n) (hq i)
        exact this.trans hqcoeff
      · ext i
        have hqcoeff : (qfun i).coeff N = 1 := by
          dsimp [qfun]
          have hcoeff_mul :
              (p i * X ^ (N - (p i).natDegree)).coeff N = (p i).coeff (p i).natDegree := by
            simpa [Nat.add_sub_of_le (hle i)] using
              coeff_mul_X_pow (p i) (N - (p i).natDegree) (p i).natDegree
          exact hcoeff_mul.trans (hpM i).coeff_natDegree
        have : q.coeff N i = (qfun i).coeff N := by
          simpa [e, piEquiv] using
            congrArg (fun f : Polynomial (R i) ↦ f.coeff N) (hq i)
        exact this.trans hqcoeff
    · ext i
      have hzero : aeval (s i) (qfun i) = 0 := by
        dsimp [qfun]
        simp [Polynomial.aeval_def, hp0 i]
      calc
        (aeval s q) i = Pi.evalRingHom S i (aeval s q) := rfl
        _ = aeval (s i) (e q i) := h_eval q i
        _ = aeval (s i) (qfun i) := by simp [hq i]
        _ = 0 := hzero

end IsIntegral

/-! ### Definition_10_36_9 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Definition 10.36.9 (Tag 00GP): for a ring map `R → S`, the canonical `R`-subalgebra
`integralClosure R S` is the integral closure `S'` of `R` in `S`. -/
recall integralClosure

/- The same definition uses the canonical owner predicate `IsIntegrallyClosedIn R S` for the map
`R → S` being integrally closed. -/
recall IsIntegrallyClosedIn {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] :
    Prop

end

section

variable {S : Type u} [CommRing S]

namespace Subring

variable (R : Subring S)

/-- Companion bridge for Definition 10.36.9: a subring `R` of `S` is integrally closed in `S`
exactly when it agrees with the canonical integral-closure subring. -/
theorem isIntegrallyClosedIn_iff_eq_integralClosure :
    IsIntegrallyClosedIn R S ↔ R = (integralClosure R S).toSubring := by
  have hbot : (⊥ : Subalgebra R S).toSubring = R := by
    ext x
    rw [Subalgebra.mem_toSubring, Algebra.mem_bot, Set.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  constructor
  · intro h
    have hc : integralClosure R S = ⊥ :=
      (IsIntegrallyClosedIn.integralClosure_eq_bot_iff S
        (FaithfulSMul.algebraMap_injective R S)).mpr h
    calc
      R = (⊥ : Subalgebra R S).toSubring := hbot.symm
      _ = (integralClosure R S).toSubring := by simp [hc]
  · intro h
    have hc : integralClosure R S = ⊥ := by
      apply Subalgebra.toSubring_injective
      calc
        (integralClosure R S).toSubring = R := h.symm
        _ = (⊥ : Subalgebra R S).toSubring := hbot.symm
    exact (IsIntegrallyClosedIn.integralClosure_eq_bot_iff S
      (FaithfulSMul.algebraMap_injective R S)).mp hc

end Subring

end

/-! ### Lemma_10_36_10 (from Chap10) -/
section

universe u v w

open IsIntegral

variable {ι : Type u} [Finite ι]
variable {R : ι → Type v} {S : ι → Type w}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]

/-- Lemma 10.36.10 (1): an element of the product ring lies in the integral closure of
`∏ i, R i` in `∏ i, S i` exactly when each component lies in the integral closure of `R i`
in `S i`. -/
-- Proof sketch: Rewrite membership in each integral closure using `mem_integralClosure_iff`,
-- then apply `IsIntegral.pi_iff` from Lemma 10.36.8 to pass between integrality over the
-- product ring and componentwise integrality.
theorem mem_integralClosure_pi_iff {s : Π i, S i} :
    s ∈ integralClosure (Π i, R i) (Π i, S i) ↔ ∀ i, s i ∈ integralClosure (R i) (S i) := by
  simp [mem_integralClosure_iff, IsIntegral.pi_iff]

omit [Finite ι] in
private theorem algebraMap_pi_injective_iff :
    Function.Injective (algebraMap (Π i, R i) (Π i, S i)) ↔
      ∀ i, Function.Injective (algebraMap (R i) (S i)) := by
  classical
  constructor
  · intro h i x y hxy
    have hxy' :
        algebraMap (Π j, R j) (Π j, S j) (Pi.single i x) =
          algebraMap (Π j, R j) (Π j, S j) (Pi.single i y) := by
      funext j
      by_cases hji : j = i
      · subst hji
        change algebraMap (R j) (S j) ((Pi.single j x) j) =
            algebraMap (R j) (S j) ((Pi.single j y) j)
        simpa using hxy
      · change algebraMap (R j) (S j) ((Pi.single i x) j) =
            algebraMap (R j) (S j) ((Pi.single i y) j)
        simp [Pi.single_eq_of_ne hji]
    simpa using congrFun (h hxy') i
  · intro h x y hxy
    ext i
    exact h i (by simpa using congrFun hxy i)

/-- Lemma 10.36.10 (2): the product map `∏ i, R i → ∏ i, S i` is integrally closed if and only
if each component map `R i → S i` is integrally closed. -/
-- Proof sketch: unfold `IsIntegrallyClosedIn` via `isIntegrallyClosedIn_iff`. Injectivity of the
-- product algebra map is equivalent to componentwise injectivity by testing on `Pi.single`, and
-- the existence condition is transported componentwise using `IsIntegral.pi_iff`.
theorem isIntegrallyClosedIn_pi_iff :
    IsIntegrallyClosedIn (Π i, R i) (Π i, S i) ↔ ∀ i, IsIntegrallyClosedIn (R i) (S i) := by
  classical
  rw [isIntegrallyClosedIn_iff, algebraMap_pi_injective_iff]
  constructor
  · intro h i
    rw [isIntegrallyClosedIn_iff]
    constructor
    · exact h.1 i
    · intro x hx
      have hs : IsIntegral (Π i, R i) (Pi.single i x) := by
        rw [IsIntegral.pi_iff]
        intro j
        by_cases hji : j = i
        · subst hji
          simpa using hx
        · simpa [Pi.single_eq_of_ne hji] using (isIntegral_zero : IsIntegral (R j) (0 : S j))
      obtain ⟨y, hy⟩ := h.2 hs
      exact ⟨y i, by simpa using congrFun hy i⟩
  · intro h
    constructor
    · intro i
      exact (isIntegrallyClosedIn_iff.mp (h i)).1
    · intro x hx
      choose y hy using fun i ↦ by
        letI : IsIntegrallyClosedIn (R i) (S i) := h i
        change ∃ y : R i, algebraMap (R i) (S i) y = x i
        exact IsIntegrallyClosedIn.algebraMap_eq_of_integral ((IsIntegral.pi_iff.mp hx) i)
      exact ⟨y, by funext i; exact hy i⟩

end

/-! ### Lemma_10_36_11 (from Chap10) -/
/- Lemma 10.36.11: integral closure commutes with localization. For a ring map `A → B` and a
multiplicative subset `S ⊆ A`, localizing the integral closure `integralClosure A B` at `S`
produces the integral closure of `Aₛ` in `Bₛ`. This is exactly the canonical mathlib theorem
`IsLocalization.integralClosure`. -/
recall IsLocalization.integralClosure

/-! ### Lemma_10_36_12 (from Chap10) -/
section

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.36.12: an element `x : S` is integral over `R` if and only if, for every prime ideal
`p` of `R`, the image of `x` in the localization of `S` at `p` is integral over
`Localization.AtPrime p.asIdeal`. -/
-- Proof sketch: localization preserves integrality for the forward implication. For the converse,
-- consider the ideal `I = { r ∈ R | r • x is integral over R }`. The primewise hypothesis shows
-- that after localizing at each maximal ideal, the image of `I` is the unit ideal: clear one
-- denominator using `exists_multiple_integral_of_isLocalization`, then clear the remaining
-- localization denominator using `exists_isIntegral_smul_of_isIntegral_map`. The local-global
-- ideal criterion `Ideal.eq_of_localization_maximal` gives `I = ⊤`, so `1 ∈ I` and hence `x` is
-- integral over `R`. This is Stacks Project, tag `034K`.
theorem isIntegral_iff_forall_isIntegral_atPrime {x : S} :
    IsIntegral R x ↔
      ∀ p : PrimeSpectrum R,
        IsIntegral (Localization.AtPrime p.asIdeal)
          (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) x) :=
  by
    constructor
    · intro hx p
      exact (hx.map (IsScalarTower.toAlgHom R S _)).tower_top
    · intro hx
      let I : Ideal R := {
        carrier := { r | IsIntegral R (r • x) }
        zero_mem' := by simpa using (isIntegral_zero : IsIntegral R (0 : S))
        add_mem' := by
          intro a b ha hb
          simpa [add_smul] using ha.add hb
        smul_mem' := by
          intro a b hb
          simpa [Algebra.smul_def, smul_smul, mul_assoc, mul_left_comm, mul_comm] using
            ((show IsIntegral R (algebraMap R S a) from isIntegral_algebraMap).mul hb) }
      have hlocalized :
          ∀ (P : Ideal R) (_ : P.IsMaximal), Ideal.map (algebraMap R (Localization.AtPrime P)) I = ⊤ :=
        by
        intro P hP
        let Sₚ := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
        have hxₚ : IsIntegral (Localization.AtPrime P) (algebraMap S Sₚ x) := by
          simpa [Sₚ] using hx (PrimeSpectrum.mk P hP.isPrime)
        obtain ⟨r, hr⟩ :=
          hxₚ.exists_multiple_integral_of_isLocalization P.primeCompl (algebraMap S Sₚ x)
        have hr' : IsIntegral R (algebraMap S Sₚ (r.1 • x)) := by
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R S Sₚ]
          simpa [Submonoid.smul_def, Algebra.smul_def] using hr
        obtain ⟨s, hs, hsr⟩ :=
          IsLocalization.exists_isIntegral_smul_of_isIntegral_map P.primeCompl hr'
        have hmemI : s * r.1 ∈ I := by
          simpa [I, smul_smul, mul_assoc, mul_left_comm, mul_comm] using hsr
        exact (Ideal.map (algebraMap R (Localization.AtPrime P)) I).eq_top_of_isUnit_mem
          (Ideal.mem_map_of_mem _ hmemI)
          (IsLocalization.map_units (Localization.AtPrime P) ⟨s * r.1, P.primeCompl.mul_mem hs r.2⟩)
      have htop : I = ⊤ := by
        refine Ideal.eq_of_localization_maximal fun m hm ↦ ?_
        simpa [Ideal.map_top] using hlocalized m hm
      have hone : (1 : R) ∈ I := by
        simp [htop]
      simpa [I, one_smul] using hone

end

/-! ### Lemma_10_36_13 (from Chap10) -/
/- Lemma 10.36.13 (1): integrality of a ring map is stable under base change. In the chapter's
canonical owner language from Definition `10.36.1`, this is exactly the mathlib declaration
`RingHom.isIntegral_isStableUnderBaseChange`. -/
recall RingHom.isIntegral_isStableUnderBaseChange

/- Lemma 10.36.13 (2): finiteness of a ring map is stable under base change. In the chapter's
canonical owner language from Definition `10.7.1`, this is exactly the mathlib declaration
`RingHom.finite_isStableUnderBaseChange`. -/
recall RingHom.finite_isStableUnderBaseChange

/-! ### Lemma_10_36_14 (from Chap10) -/
/- Lemma 10.36.14 (1): let `R → S` be a ring map and let `f₁, …, fₙ ∈ R` generate the unit
ideal. If each localized map `R_{fᵢ} → S_{fᵢ}` is integral, then `R → S` is integral. This is
exactly the canonical mathlib theorem `RingHom.isIntegral_ofLocalizationSpan`. -/
recall RingHom.isIntegral_ofLocalizationSpan :
  RingHom.OfLocalizationSpan RingHom.IsIntegral

/- Lemma 10.36.14 (2): let `R → S` be a ring map and let `f₁, …, fₙ ∈ R` generate the unit
ideal. If each localized map `R_{fᵢ} → S_{fᵢ}` is finite, then `R → S` is finite. This is exactly
the canonical mathlib theorem `RingHom.finite_ofLocalizationSpan`. -/
recall RingHom.finite_ofLocalizationSpan :
  RingHom.OfLocalizationSpan RingHom.Finite

/-! ### Lemma_10_36_15 (from Chap10) -/
/- Lemma 10.36.15 (1): let `A → B → C` be ring maps. If `A → C` is integral, then so is `B → C`.
This is exactly the canonical mathlib theorem `RingHom.IsIntegral.tower_top`. -/
recall RingHom.IsIntegral.tower_top

/- Lemma 10.36.15 (2): let `A → B → C` be ring maps. If `A → C` is finite, then so is `B → C`.
This is exactly the canonical mathlib theorem `RingHom.Finite.of_comp_finite`. -/
recall RingHom.Finite.of_comp_finite

/-! ### Lemma_10_36_16 (from Chap10) -/
section

universe u v w x y

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]
variable {B' : Type w} [CommRing B'] [Algebra A B'] [Algebra B' B] [IsScalarTower A B' B]
variable {C : Type x} [CommRing C] [Algebra B' C]
variable {C' : Type y} [CommRing C'] [Algebra B' C'] [Algebra C' C] [IsScalarTower B' C' C]
variable [Algebra A C'] [IsScalarTower A B' C'] [Algebra A C] [IsScalarTower A C' C]

namespace IsIntegralClosure

/-- Lemma 10.36.16: if `B'` is the integral closure of `A` in `B` and `C'` is the integral
closure of `B'` in `C`, then `C'` is the integral closure of `A` in `C`. This is the
source-faithful closure-of-closure transitivity statement, proved by combining the canonical owner
API for integral closures with transitivity of integral algebras. -/
theorem trans [IsIntegralClosure B' A B] [IsIntegralClosure C' B' C] :
    IsIntegralClosure C' A C := by
  letI : IsIntegrallyClosedIn C' C := IsIntegrallyClosedIn.of_isIntegralClosure B'
  letI : Algebra.IsIntegral A B' := IsIntegralClosure.isIntegral_algebra A B
  letI : Algebra.IsIntegral B' C' := IsIntegralClosure.isIntegral_algebra B' C
  letI : Algebra.IsIntegral A C' := Algebra.IsIntegral.trans B'
  exact IsIntegralClosure.of_isIntegrallyClosedIn

end IsIntegralClosure

end

/-! ### Lemma_10_36_17 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [FaithfulSMul R S] [Algebra.IsIntegral R S]

/- Lemma 10.36.17 (Stacks tag `00GQ`): if `R → S` is an integral ring extension with `R ⊂ S`,
then the induced map `Spec(S) → Spec(R)` is surjective. In mathlib this is exactly
`Algebra.IsIntegral.comap_surjective`; the inclusion hypothesis is encoded by `FaithfulSMul R S`,
which gives injectivity of `algebraMap R S`. -/
recall Algebra.IsIntegral.comap_surjective

end

/-! ### Lemma_10_36_18 (from Chap10) -/
universe u v

section

variable {R : Type u} {K : Type v} [CommRing R] [Field K] [Algebra R K]

/- Domain triage:
* primary domain: integral and algebraic commutative algebra over a field-valued algebra;
* core/canonical owners: `isField_of_isIntegral_of_isField`,
  `Algebra.IsIntegral.isAlgebraic`, `Algebra.IsIntegral.of_finite`, and
  `Algebra.IsAlgebraic.of_finite`;
* layer split: the two part `(1)` statements and the algebraicity statement in part `(2)` are
  direct owner recalls, while `isField_of_finite_subring_of_field` is the source-facing bridge
  from module-finiteness to the owner field criterion;
* primitive data vs. derived API: the primitive hypotheses are the `R`-algebra structure on the
  field `K`, injectivity of `algebraMap R K`, and, in part `(2)`, finite generation as an
  `R`-module. Integrality and algebraicity are derived from the owner instances, so no local
  wrapper structure is needed.
-/

/- Lemma 10.36.18 (1) (Stacks tag `00GR`): if `K` is integral over `R` and the structure map
`R → K` is injective, then `R` is a field. This is exactly the canonical mathlib theorem
`isField_of_isIntegral_of_isField`. -/
recall isField_of_isIntegral_of_isField

/- Lemma 10.36.18 (1) (Stacks tag `00GR`): if `K` is integral over `R` and `K` is a field, then
`K / R` is algebraic. This is the canonical owner instance
`Algebra.IsIntegral.isAlgebraic`; the subring language from the source is redundant here because
any algebra map `R → K` into a field already forces `R` to be nontrivial. -/
recall Algebra.IsIntegral.isAlgebraic

/-- Lemma 10.36.18 (2) (Stacks tag `00GR`): if `R` is identified with a subring of the field `K`
and `K` is finite over `R`, then `R` is a field. -/
theorem isField_of_finite_subring_of_field
    (hinj : Function.Injective (algebraMap R K)) [Module.Finite R K] :
    IsField R := by
  exact isField_of_isIntegral_of_isField hinj (Field.toIsField K)

/- Lemma 10.36.18 (2) (Stacks tag `00GR`): if `K` is finite over `R` and `K` is a field, then
`K / R` is algebraic. This is the field-codomain specialization of the canonical owner instance
`Algebra.IsAlgebraic.of_finite`. -/
recall Algebra.IsAlgebraic.of_finite

end

/-! ### Lemma_10_36_19 (from Chap10) -/
universe u v

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

/- Domain triage:
* primary domain: integral and finite-dimensional commutative `k`-algebras over a field;
* core/canonical owners: `fieldOfFiniteDimensional`, `isField_of_isIntegral_of_isField'`, and
  `Ideal.Quotient.maximal_of_isField`;
* layer split: parts (1) and (2) are direct owner recalls, while part (3) is the source-facing
  bridge from prime ideals to the owner quotient-field criterion.
-/

/- A domain that is finite-dimensional as a `k`-algebra over a field `k` is a field. This is
exactly the owner declaration `fieldOfFiniteDimensional`, which supplies the field structure
itself. -/
recall fieldOfFiniteDimensional

/- A domain that is integral as a `k`-algebra over a field `k` is a field. This is exactly the
canonical theorem `isField_of_isIntegral_of_isField'`, specialized to the field `k`. -/
recall isField_of_isIntegral_of_isField'

-- Proof sketch: for a prime ideal `P`, the quotient `S ⧸ P` is a domain and remains integral over
-- `k`; apply part (2) to conclude that `S ⧸ P` is a field, which is equivalent to `P` being
-- maximal.
/-- Lemma 10.36.19: if a `k`-algebra `S` is integral over the field `k`, then every prime ideal of
`S` is maximal. -/
theorem ideal_isMaximal_of_isPrime_of_integral_over_field
    [Algebra.IsIntegral k S] (P : Ideal S) (hP : P.IsPrime) : P.IsMaximal := by
  letI : P.IsPrime := hP
  exact Ideal.Quotient.maximal_of_isField P <|
    isField_of_isIntegral_of_isField' (Field.toIsField k)

end

/-! ### Lemma_10_36_20 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsIntegral R S]

open PrimeSpectrum Ideal

/- Domain triage:
* primary domain: integral extensions and the induced map on prime spectra;
* core/canonical owner: `Ideal.comap_lt_comap_of_integral_mem_sdiff` from the going-up API;
* layer split: the ideal-level strict-comap theorem is the owner result, while the theorem below is
  the source-facing bridge reformulating it as incomparability in `PrimeSpectrum`;
* primitive data vs. derived API: the primitive hypotheses are the integral `R`-algebra structure
  on `S`, distinct primes `q ≠ q'`, and equality of their images under `PrimeSpectrum.comap`. The
  specialization-order incomparability is derived from the owner theorem and should not be stored
  as separate local data.
-/

/-- Lemma 10.36.20: distinct points of `Spec(S)` with the same image in `Spec(R)` are
incomparable in the specialization order, equivalently their prime ideals are incomparable by
inclusion. -/
theorem primes_over_same_prime_are_incomparable (q q' : PrimeSpectrum S) (hqq' : q ≠ q')
    (himage : comap (algebraMap R S) q = comap (algebraMap R S) q') :
    ¬ q ≤ q' ∧ ¬ q' ≤ q := by
  have hnot_le :
      ∀ ⦃a b : PrimeSpectrum S⦄,
        a ≠ b →
        comap (algebraMap R S) a = comap (algebraMap R S) b →
        ¬ a ≤ b := by
    intro a b hab hab_comap hab_le
    have hab' : a.asIdeal < b.asIdeal := by
      refine lt_of_le_of_ne hab_le ?_
      intro h
      exact hab (PrimeSpectrum.ext h)
    obtain ⟨hab_le', x, hxb, hxa⟩ := SetLike.lt_iff_le_and_exists.mp hab'
    have hcomap :
        Ideal.comap (algebraMap R S) a.asIdeal = Ideal.comap (algebraMap R S) b.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hab_comap
    exact (comap_lt_comap_of_integral_mem_sdiff hab_le' ⟨hxb, hxa⟩
      (Algebra.IsIntegral.isIntegral x)).ne hcomap
  exact ⟨hnot_le hqq' himage, hnot_le hqq'.symm himage.symm⟩

end

/-! ### Lemma_10_36_21 (from Chap10) -/
universe u v

section

open PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain triage:
* primary domain: finite ring maps and the induced map on prime spectra;
* source-facing layer: a finite ring map `f : R →+* S` has finite fibers on `Spec`;
* core/canonical owner: `Algebra.QuasiFinite R S`, with finite-fiber theorem
  `Algebra.QuasiFinite.finite_comap_preimage_singleton`;
* bridge/view: `RingHom.QuasiFinite.of_finite` turns the finite map into the owner hypothesis.

Primitive data vs. derived API:
* primitive input: a ring hom `f : R →+* S` together with `f.Finite`;
* derived conclusion: for each `p : Spec R`, the fiber `(PrimeSpectrum.comap f)⁻¹({p})` is finite.
-/

/-- Lemma 10.36.21: a finite ring map has finite fibers on prime spectra. -/
theorem finite_comap_preimage_singleton_of_finite (f : R →+* S) (hf : f.Finite)
    (p : PrimeSpectrum R) : (PrimeSpectrum.comap f ⁻¹' {p}).Finite := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.QuasiFinite R S := RingHom.QuasiFinite.of_finite hf
  simpa using Algebra.QuasiFinite.finite_comap_preimage_singleton p

end

/-! ### Lemma_10_36_22 (from Chap10) -/
universe u v

section

open Ideal PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsIntegral R S]

private theorem exists_ideal_ge_of_comap_eq_of_le_of_specializingMap
    {p p' : Ideal R} [p'.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hQ : Ideal.comap (algebraMap R S) Q = p) (hpq : p ≤ p') :
    ∃ Q' : Ideal S, Q ≤ Q' ∧ Q'.IsPrime ∧ Ideal.comap (algebraMap R S) Q' = p' := by
  let hgu : SpecializingMap (PrimeSpectrum.comap (algebraMap R S)) :=
    (isClosedMap_comap_of_isIntegral (algebraMap R S)
      (algebraMap_isIntegral_iff.mpr inferInstance)).specializingMap
  by_cases h : p = p'
  · subst h
    exact ⟨Q, le_rfl, inferInstance, hQ⟩
  · have hspec :
        PrimeSpectrum.comap (algebraMap R S) ⟨Q, inferInstance⟩ ⤳
          (⟨p', inferInstance⟩ : PrimeSpectrum R) := by
      rw [← PrimeSpectrum.le_iff_specializes]
      change Ideal.comap (algebraMap R S) Q ≤ p'
      simpa [hQ] using hpq
    obtain ⟨Q', hQQ', hQ'p⟩ := hgu hspec
    exact ⟨Q'.asIdeal, by simpa using (PrimeSpectrum.le_iff_specializes _ _).mpr hQQ', Q'.2,
      by simpa using congrArg PrimeSpectrum.asIdeal hQ'p⟩

private theorem exists_ideal_gt_of_comap_eq_of_lt_of_specializingMap
    {p p' : Ideal R} [p'.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hQ : Ideal.comap (algebraMap R S) Q = p) (hpq : p < p') :
    ∃ Q' : Ideal S, Q < Q' ∧ Q'.IsPrime ∧ Ideal.comap (algebraMap R S) Q' = p' := by
  obtain ⟨Q', hQQ', hQ'prime, hQ'p'⟩ :=
    exists_ideal_ge_of_comap_eq_of_le_of_specializingMap Q hQ hpq.le
  refine ⟨Q', lt_of_le_of_ne hQQ' ?_, hQ'prime, hQ'p'⟩
  intro hQQ'eq
  exact hpq.ne <| hQ.symm.trans <| hQQ'eq ▸ hQ'p'

/- Lemma 10.36.22: in an integral extension, a prime of `S` lying over `p` extends to a prime of
`S` lying over any larger prime `p'` of `R`. This is the integral specialization of the owner
abstraction from Definition 10.41.1 (1), using the canonical closed-map theorem
`PrimeSpectrum.isClosedMap_comap_of_isIntegral`. -/
#check exists_ideal_ge_of_comap_eq_of_le_of_specializingMap

/- If `p < p'`, the same specialization of the owner theorem
from Definition 10.41.1 (1) yields a strictly larger prime over `p'`. -/
#check exists_ideal_gt_of_comap_eq_of_lt_of_specializingMap

end

/-! ### Lemma_10_36_23 (from Chap10) -/
universe u v w

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite R S] [Algebra.FinitePresentation R S]

namespace Module.FinitePresentation

/-
Source/core/bridge triage:
* source-facing: finite and finitely presented change of scalars for finitely presented modules.
* core/canonical: `Module.FinitePresentation` with the owner lemmas
  `of_restrictScalars_finiteType`, `of_finite_of_finitePresentation`, and `trans`.
* bridge/view: this theorem is the source-facing equivalence obtained by composing those owner
  lemmas in the two directions.
-/
-- Proof sketch: for the forward direction, combine finite presentation of `S` as an
-- `R`-algebra with finiteness of `S` over `R` to descend a finitely presented `R`-module structure
-- on `M` to a finitely presented `S`-module structure. For the reverse direction, use transitivity
-- of finite presentation along the finitely presented `R`-algebra `S`.
/-- Lemma 10.36.23: if `R → S` is finite and finitely presented, then an `S`-module `M` is
finitely presented over `R` if and only if it is finitely presented over `S`. -/
theorem iff_of_finite_finitePresentation :
    Module.FinitePresentation R M ↔ Module.FinitePresentation S M := by
  constructor
  · intro hM
    -- The forward direction is the finite-type restriction-of-scalars bridge from Lemma 10.6.4.
    let _ : Module.FinitePresentation R M := hM
    exact Module.FinitePresentation.of_restrictScalars_finiteType (R := R)
  · intro hM
    -- For the reverse direction, first make `S` finitely presented as an `R`-module.
    let _ : Module.FinitePresentation S M := hM
    let _ : Module.FinitePresentation R S :=
      Module.FinitePresentation.of_finite_of_finitePresentation R S
    -- Transitivity along `R → S → M` then recovers finite presentation over `R`.
    exact Module.FinitePresentation.trans (R := R) (M := M) S

end Module.FinitePresentation
