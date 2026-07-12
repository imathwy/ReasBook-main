import Mathlib
import StacksProject_2024.Chap15.Definition_15_112_7
import StacksProject_2024.Chap15.Lemma_15_112_4
import StacksProject_2024.Chap15.Lemma_15_115_2
import StacksProject_2024.Chap15.Lemma_15_116_3

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing Polynomial
open IsExtensionOfDiscreteValuationRings

universe u v

noncomputable section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p]

local notation "K" => FractionRing A

/- Domain-style sampling:
* primary domain: ramification theory for finite separable extensions of the fraction field of a
  discrete valuation ring, expressed on the intrinsic DVR structure of the integral closure;
* sampled owner declarations:
  `IsTotallyRamifiedWithRespectTo`,
  `ramificationIndex`,
  `integralClosure`,
  `integralClosure_isDiscreteValuationRing_of_totallyRamified`;
* best owner abstraction: once the theorem has produced an explicit witness
  `[IsTotallyRamifiedWithRespectTo A L]`, the owner ring is `B = integralClosure A L` itself, with
  canonical DVR API `ramificationIndex A B`; the explicit generator and congruence equations for a
  chosen uniformizer are source-facing extra data over that owner;
* primitive data: the DVR `A`, the chosen uniformizer `π`, the integers `n` and `q`, and the
  finite separable extension `L / FractionRing A`;
* derived API: total ramification of `L / FractionRing A`, the DVR structure on
  `B = integralClosure A L`, its ramification index over `A`, and the explicit congruence
  equations for a generator of `maximalIdeal B`.

Layer triage:
* `source-facing`: the existence theorem for a totally ramified separable extension with a
  prescribed uniformizer congruence;
* `core/canonical`: `IsTotallyRamifiedWithRespectTo`, `integralClosure A L`, and
  `ramificationIndex A (integralClosure A L)`;
* `bridge/view`: the explicit branch ideal is unnecessary here because total ramification makes
  `maximalIdeal (integralClosure A L)` the intrinsic owner of the source-facing generator data.
-/

/-- Helper for Lemma 15.116.7: a ring equivalence between local rings carries the maximal ideal to
the maximal ideal by transport of nonunits. -/
private lemma ringEquiv_map_maximalIdeal
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) :
    Ideal.map e.toRingHom (maximalIdeal R) = maximalIdeal S := by
  -- Compare membership after rewriting both maximal ideals as the set of nonunits.
  ext x
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    simpa using hx

/-- Helper for Lemma 15.116.7: the trivial fraction-field extension already provides the required
degree-one totally ramified witness. -/
private theorem exists_trivial_extension_data_of_degree_one
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 1 < n) :
    ∃ (L : Type (max u v)) (_ : Field L) (_ : Algebra A L) (_ : Algebra K L)
      (_ : IsScalarTower A K L) (_ : FiniteDimensional K L) (_ : Algebra.IsSeparable K L)
      (_ : IsTotallyRamifiedWithRespectTo A L),
      let B := integralClosure A L
      Module.finrank K L = 1 ∧
        ∃ πB b b' : B,
          ramificationIndex A B = 1 ∧
            maximalIdeal B = Ideal.span ({πB} : Set B) ∧
            πB ^ 1 = algebraMap A B π + algebraMap A B (π ^ n) * b ∧
            πB ^ 1 = algebraMap A B π + πB ^ n * b' := by
  let L := K
  let B := integralClosure A L
  letI : IsTotallyRamifiedWithRespectTo A L := inferInstance
  letI : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).mpr (IsFractionRing.injective A L)
  letI : IsDiscreteValuationRing B :=
    integralClosure_isDiscreteValuationRing_of_totallyRamified (A := A) (K1 := L)
  letI : IsExtensionOfDiscreteValuationRings A B := inferInstance
  letI : (maximalIdeal B).LiesOver (maximalIdeal A) := (Ideal.liesOver_iff _ _).2 rfl
  obtain ⟨τ, _, hτ⟩ := exists_uniformizer_generator B
  let hU : IsUnramifiedWithRespectTo A L := inferInstance
  have hram : ramificationIndex A B = 1 := by
    -- The trivial extension is unramified, so its ramification index is `1`.
    simpa [IsExtensionOfDiscreteValuationRings.ramificationIndex] using
      hU.ramificationIdx_eq_one (maximalIdeal B)
  have hassoc : Associated (algebraMap A B π) τ := by
    -- Read the degree-one ramification index into the uniformizer comparison lemma.
    simpa [hram] using
      (uniformizer_image_associated_uniformizer_pow_ramificationIndex
        (A := A) (B := B) π τ hπ hτ)
  have hmax : maximalIdeal B = Ideal.span ({algebraMap A B π} : Set B) := by
    -- The image of the chosen base uniformizer is itself a target uniformizer.
    calc
      maximalIdeal B = Ideal.span ({τ} : Set B) := hτ
      _ = Ideal.span ({algebraMap A B π} : Set B) := by
        exact (Ideal.span_singleton_eq_span_singleton).mpr hassoc.symm
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  -- Package the trivial extension witness with vanishing correction terms.
  refine ⟨by simp, algebraMap A B π, 0, 0, hram, hmax, ?_, ?_⟩
  · simp
  · simp [hn.ne']

/-- Helper for Lemma 15.116.7: in characteristic zero, the radical extension `X^q - π` is
separable over the fraction field. -/
private theorem uniformizerRootExtension_isSeparable_of_charZero
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {q : ℕ} (hq : ∃ m : ℕ, q = p ^ m) [CharZero K] :
    Algebra.IsSeparable K (uniformizerRootExtension π q) := by
  let hπirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  rcases hq with ⟨m, rfl⟩
  have hp_pos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hq_pos : 0 < p ^ m := pow_pos hp_pos m
  letI : NeZero (p ^ m) := ⟨Nat.ne_of_gt hq_pos⟩
  letI : Fact (Irreducible π) := ⟨hπirr⟩
  let L := uniformizerRootExtension π (p ^ m)
  let z : L := uniformizerRoot π (p ^ m)
  let f : K[X] := uniformizerRootFractionPolynomial π (p ^ m)
  have hz_integral : IsIntegral K z := by
    -- The distinguished quotient root is integral because it satisfies the defining monic
    -- polynomial `X ^ q - π`.
    simpa [L, z, f, uniformizerRootExtension, uniformizerRoot] using
      (AdjoinRoot.isIntegral_root (f := f))
  have hf_irr : Irreducible f := by
    -- The source Eisenstein argument from Lemma `15.115.2` gives irreducibility over `K`.
    simpa [f] using
      (uniformizerRootFractionPolynomial_irreducible
        (A := A) (π := π) (n := p ^ m) hπirr (NeZero.ne (p ^ m)))
  have hf_sep : f.Separable := hf_irr.separable
  have hz_aeval : aeval z f = 0 := by
    -- The quotient root kills its defining polynomial by construction.
    simpa [z, f, uniformizerRoot] using (AdjoinRoot.eval₂_root f)
  have hmonic : f.Monic := by
    -- The polynomial `X ^ q - π` is monic, so irreducibility identifies the minimal polynomial.
    simpa [f, uniformizerRootPolynomial] using
      (Polynomial.monic_X_pow_sub_C (algebraMap A K π) (NeZero.ne (p ^ m)))
  have hmin : minpoly K z = f := by
    -- Route correction: pin down the minimal polynomial first, then transport separability from
    -- the source polynomial to the whole simple field.
    exact (minpoly.eq_of_irreducible_of_monic hf_irr hz_aeval hmonic).symm
  have hz_sep : IsSeparable K z := by
    -- The distinguished root is separable because its minimal polynomial divides a separable
    -- polynomial.
    exact Polynomial.Separable.of_dvd hf_sep (minpoly.dvd K z hz_aeval)
  have hsep_adjoin : Algebra.IsSeparable K K⟮z⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).2 hz_sep
  let e : L ≃ₐ[K] K⟮z⟯ := by
    -- The ambient quotient field is exactly the simple extension generated by the distinguished
    -- root.
    simpa [L, z, uniformizerRootExtension, hmin] using
      (IntermediateField.adjoinRootEquivAdjoin K hz_integral :
        AdjoinRoot (minpoly K z) ≃ₐ[K] K⟮z⟯)
  let _ : Algebra.IsSeparable K K⟮z⟯ := hsep_adjoin
  exact AlgEquiv.Algebra.isSeparable e.symm

/-- Helper for Lemma 15.116.7: in the radical extension ring `A[X] / (X^q - π)`, the
distinguished quotient root already generates the maximal ideal. -/
private theorem uniformizer_root_generates_maximalIdeal
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {q : ℕ} (hq : ∃ m : ℕ, q = p ^ m) :
    maximalIdeal (uniformizerRootExtensionRing π q) =
      Ideal.span ({AdjoinRoot.root (uniformizerRootPolynomial π q)} :
        Set (uniformizerRootExtensionRing π q)) := by
  let hπirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  rcases hq with ⟨m, rfl⟩
  have hp_pos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hq_pos : 0 < p ^ m := pow_pos hp_pos m
  letI : NeZero (p ^ m) := ⟨Nat.ne_of_gt hq_pos⟩
  letI : Fact (Irreducible π) := ⟨hπirr⟩
  let R1 := uniformizerRootExtensionRing π (p ^ m)
  let y : R1 := AdjoinRoot.root (uniformizerRootPolynomial π (p ^ m))
  obtain ⟨τ, -, hτ⟩ := exists_uniformizer_generator R1
  have hram : ramificationIndex A R1 = p ^ m := by
    -- The canonical radical-extension ramification computation fixes the target exponent.
    simpa [R1] using
      (ramificationIndex_uniformizerRootExtensionRing
        (A := A) (π := π) (n := p ^ m) (hπ := hπirr) (hn := hq_pos))
  have hτpow : Associated (algebraMap A R1 π) (τ ^ (p ^ m)) := by
    -- Any chosen uniformizer of `R1` differs from the image of `π` by the displayed
    -- ramification-index power.
    simpa [hram] using
      (uniformizer_image_associated_uniformizer_pow_ramificationIndex
        (A := A) (B := R1) π τ hπ hτ)
  have hy_pow : y ^ (p ^ m) = algebraMap A R1 π := by
    -- The quotient root satisfies the defining equation already over `A`.
    simpa [y, uniformizerRootPolynomial, sub_eq_zero] using
      (AdjoinRoot.eval₂_root (uniformizerRootPolynomial π (p ^ m)))
  have hy_ne_zero : y ≠ 0 := by
    -- If the quotient root were zero, then the image of the nonzero uniformizer `π` would vanish
    -- in the domain `R1`.
    intro hy0
    have hmap_zero : algebraMap A R1 π = 0 := by
      simpa [hy0] using hy_pow
    exact hπirr.ne_zero ((NoZeroSMulDivisors.algebraMap_injective A R1) hmap_zero)
  obtain ⟨k, hy_assoc⟩ := associated_uniformizer_pow_of_nonzero τ y hτ hy_ne_zero
  have hy_pow_assoc : Associated (y ^ (p ^ m)) (τ ^ (k * (p ^ m))) := by
    -- Rewrite the quotient root in terms of the chosen target uniformizer and then raise to the
    -- `q`th power.
    refine Associated.trans (associated_pow hy_assoc (p ^ m)) ?_
    exact associated_of_eq (pow_mul τ k (p ^ m)).symm
  have hpow_compare : Associated (τ ^ (k * (p ^ m))) (τ ^ (p ^ m)) := by
    -- Compare the two `q`th-power descriptions of the image of `π`.
    exact Associated.trans (Associated.symm hy_pow_assoc)
      (Associated.trans (associated_of_eq hy_pow) hτpow)
  have hk_mul : k * (p ^ m) = p ^ m :=
    uniformizer_power_associated_injective τ hτ hpow_compare
  have hk_eq_one : k = 1 := Nat.eq_of_mul_eq_mul_right hq_pos hk_mul
  have hy_uniformizer : Associated y τ := by
    -- The exponent comparison shows that the quotient root is itself a uniformizer.
    simpa [hk_eq_one] using hy_assoc
  calc
    maximalIdeal R1 = Ideal.span ({τ} : Set R1) := hτ
    _ = Ideal.span ({y} : Set R1) := by
      exact (Ideal.span_singleton_eq_span_singleton).mpr hy_uniformizer.symm

/-- Helper for Lemma 15.116.7: in characteristic zero, the radical extension `X^q - π` yields
the required totally ramified separable witness with vanishing correction terms. -/
private theorem exists_radical_extension_data_of_charZero
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n q : ℕ} (hn : 1 < n) (hq : ∃ m : ℕ, q = p ^ m) [CharZero K] :
    ∃ (L : Type (max u v)) (_ : Field L) (_ : Algebra A L) (_ : Algebra K L)
      (_ : IsScalarTower A K L) (_ : FiniteDimensional K L) (_ : Algebra.IsSeparable K L)
      (_ : IsTotallyRamifiedWithRespectTo A L),
      let B := integralClosure A L
      Module.finrank K L = q ∧
        ∃ πB b b' : B,
          ramificationIndex A B = q ∧
            maximalIdeal B = Ideal.span ({πB} : Set B) ∧
            πB ^ q = algebraMap A B π + algebraMap A B (π ^ n) * b ∧
            πB ^ q = algebraMap A B π + πB ^ (n * q) * b' := by
  let hπirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  rcases hq with ⟨m, hm⟩
  have hp_pos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hq_pos : 0 < q := by
    rw [hm]
    exact pow_pos hp_pos m
  letI : NeZero q := ⟨Nat.ne_of_gt hq_pos⟩
  letI : Fact (Irreducible π) := ⟨hπirr⟩
  let L := uniformizerRootExtension π q
  let B := integralClosure A L
  letI : Field L := inferInstance
  letI : Algebra.IsSeparable K L :=
    uniformizerRootExtension_isSeparable_of_charZero (A := A) (p := p) π hπ ⟨m, hm⟩
  letI : IsTotallyRamifiedWithRespectTo A L := by
    -- The radical extension is already the canonical totally ramified owner from Lemma `15.115.2`.
    simpa [L, hm] using
      (uniformizerRootExtensionField_isTotallyRamifiedWithRespectTo
        (A := A) (π := π) (n := q))
  letI : IsDiscreteValuationRing B :=
    integralClosure_isDiscreteValuationRing_of_totallyRamified (A := A) (K1 := L)
  letI : IsExtensionOfDiscreteValuationRings A B := inferInstance
  letI : IsIntegralClosure (uniformizerRootExtensionRing π q) A L :=
    uniformizerRootExtensionRing_isIntegralClosure
      (A := A) (π := π) (n := q) (hπ := hπirr) (hn := hq_pos)
  let e : uniformizerRootExtensionRing π q ≃ₐ[A] B :=
    IsIntegralClosure.equiv A (uniformizerRootExtensionRing π q) L B
  let yR : uniformizerRootExtensionRing π q :=
    AdjoinRoot.root (uniformizerRootPolynomial π q)
  let πB : B := e yR
  have hyR_pow : yR ^ q = algebraMap A (uniformizerRootExtensionRing π q) π := by
    -- The quotient root already satisfies `yR ^ q = π` before transporting to the owner `B`.
    simpa [yR, uniformizerRootPolynomial, sub_eq_zero] using
      (AdjoinRoot.eval₂_root (uniformizerRootPolynomial π q))
  have hramR1 : ramificationIndex A (uniformizerRootExtensionRing π q) = q := by
    -- The radical quotient ring has ramification index exactly `q`.
    simpa using
      (ramificationIndex_uniformizerRootExtensionRing
        (A := A) (π := π) (n := q) (hπ := hπirr) (hn := hq_pos))
  have hmapR1 :
      Ideal.map (algebraMap A (uniformizerRootExtensionRing π q)) (maximalIdeal A) =
        maximalIdeal (uniformizerRootExtensionRing π q) ^ q := by
    -- Repackage the ramification-index equality as the canonical maximal-ideal power identity.
    exact (ramificationIndex_eq_iff (A := A) (B := uniformizerRootExtensionRing π q) q).mp hramR1 |>.2
  have hmapB :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ q := by
    -- Transport the maximal-ideal power identity from the explicit quotient ring to the canonical
    -- integral closure via the owner equivalence `e`.
    calc
      Ideal.map (algebraMap A B) (maximalIdeal A)
          = Ideal.map (e.toRingHom.comp (algebraMap A (uniformizerRootExtensionRing π q)))
              (maximalIdeal A) := by
                congr 1
                ext a
                exact (e.commutes a).symm
      _ = Ideal.map e.toRingHom
            (Ideal.map (algebraMap A (uniformizerRootExtensionRing π q)) (maximalIdeal A)) := by
            rw [Ideal.map_map]
      _ = Ideal.map e.toRingHom (maximalIdeal (uniformizerRootExtensionRing π q) ^ q) := by
            rw [hmapR1]
      _ = (Ideal.map e.toRingHom (maximalIdeal (uniformizerRootExtensionRing π q))) ^ q := by
            rw [Ideal.map_pow]
      _ = maximalIdeal B ^ q := by
            rw [ringEquiv_map_maximalIdeal (e := e)]
  have hramB : ramificationIndex A B = q := by
    -- The transported maximal-ideal power identity identifies the ramification index in `B`.
    exact (ramificationIndex_eq_iff (A := A) (B := B) q).mpr ⟨hq_pos, hmapB⟩
  have hmaxB :
      maximalIdeal B = Ideal.span ({πB} : Set B) := by
    -- Transport the root-uniformizer statement from the explicit quotient ring to `B`.
    calc
      maximalIdeal B = Ideal.map e.toRingHom (maximalIdeal (uniformizerRootExtensionRing π q)) := by
        symm
        exact ringEquiv_map_maximalIdeal (e := e)
      _ = Ideal.map e.toRingHom
            (Ideal.span ({AdjoinRoot.root (uniformizerRootPolynomial π q)} :
              Set (uniformizerRootExtensionRing π q))) := by
            rw [uniformizer_root_generates_maximalIdeal (A := A) (p := p) π hπ ⟨m, hm⟩]
      _ = Ideal.span ({πB} : Set B) := by
            rw [Ideal.map_span]
            simp [πB, yR]
  have hπB_pow : πB ^ q = algebraMap A B π := by
    -- Applying the owner equivalence to the defining equation of the quotient root yields the
    -- displayed uniformizer identity in `B`.
    calc
      πB ^ q = e (yR ^ q) := by simp [πB]
      _ = e (algebraMap A (uniformizerRootExtensionRing π q) π) := by rw [hyR_pow]
      _ = algebraMap A B π := e.commutes π
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  -- Package the radical-extension witness with vanishing correction terms, exactly as in the
  -- source proof's characteristic-zero branch.
  refine ⟨by simpa [hm] using
      (uniformizerRootExtensionField_finrank_eq
        (A := A) (π := π) (n := q) (hπ := hπirr) (hn := hq_pos)),
    πB, 0, 0, hramB, hmaxB, ?_, ?_⟩
  · simpa [hπB_pow]
  · simpa [hπB_pow]

/-- Helper for Lemma 15.116.7: once the fraction field is not of characteristic zero, the branch
is equal characteristic `p`. -/
private theorem fractionRing_charP_of_not_charZero
    (hchar0 : ¬ CharZero K) : CharP K p := by
  -- Split the characteristic dichotomy for the field `K`; the characteristic-zero branch is
  -- excluded by hypothesis, and the positive-characteristic branch must agree with `p`.
  obtain hzero | ⟨q, hq, hchar⟩ := CharP.exists' K
  · exact False.elim (hchar0 hzero)
  · exact (ExpChar.eq (inferInstance : ExpChar K p) (ExpChar.prime hq.out)) ▸ hchar

/-- Helper for Lemma 15.116.7: the source additive polynomial over `K` is monic. -/
private theorem uniformizer_additive_fraction_polynomial_monic
    (π : A) {n q : ℕ} (hq_gt_one : 1 < q) :
    let fK : K[X] := X ^ q - C (algebraMap A K (π ^ (n + q - 1))) * X - C (algebraMap A K π)
    fK.Monic := by
  let c : K := algebraMap A K (π ^ (n + q - 1))
  let d : K := algebraMap A K π
  let fK : K[X] := X ^ q - C c * X - C d
  have hdeg : degree (C c * X + C d : K[X]) < q := by
    -- The lower-order correction term has degree at most `1`, so it is strictly below `q`.
    refine lt_of_le_of_lt (degree_add_le (C c * X : K[X]) (C d)) ?_
    have hq_one : (1 : WithBot ℕ) < q := by
      exact_mod_cast hq_gt_one
    simpa using hq_one
  -- Repackage the source polynomial as `X ^ q` minus a lower-degree term.
  simpa [fK, c, d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (Polynomial.monic_X_pow_sub (p := (C c * X + C d : K[X])) (n := q) hdeg)

/-- Helper for Lemma 15.116.7: the source additive polynomial over `A` is monic. -/
private theorem uniformizer_additive_polynomial_monic
    (π : A) {n q : ℕ} (hq_gt_one : 1 < q) :
    let fA : A[X] := X ^ q - C (π ^ (n + q - 1)) * X - C π
    fA.Monic := by
  let c : A := π ^ (n + q - 1)
  let fA : A[X] := X ^ q - C c * X - C π
  have hdeg : degree (C c * X + C π : A[X]) < q := by
    -- The correction term still has degree at most `1`, so the leading `X ^ q` term survives.
    refine lt_of_le_of_lt (degree_add_le (C c * X : A[X]) (C π)) ?_
    have hq_one : (1 : WithBot ℕ) < q := by
      exact_mod_cast hq_gt_one
    simpa using hq_one
  -- Repackage the source polynomial as `X ^ q` minus a lower-degree term over the DVR itself.
  simpa [fA, c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (Polynomial.monic_X_pow_sub (p := (C c * X + C π : A[X])) (n := q) hdeg)

/-- Helper for Lemma 15.116.7: divisibility by the additive owner polynomial after extending
coefficients to the fraction field already descends to divisibility over the base DVR. -/
private theorem uniformizer_additive_polynomial_dvd_of_fraction_map_dvd
    (π : A) {n q : ℕ} (hq_gt_one : 1 < q) {g : Polynomial A}
    (hg :
      (X ^ q - C (algebraMap A K (π ^ (n + q - 1))) * X - C (algebraMap A K π) : K[X]) ∣
        Polynomial.map (algebraMap A K) g) :
    (X ^ q - C (π ^ (n + q - 1)) * X - C π : A[X]) ∣ g := by
  let fA : A[X] := X ^ q - C (π ^ (n + q - 1)) * X - C π
  have hfA_monic : fA.Monic := by
    -- The additive owner polynomial is monic, so the remainder computation survives coefficient
    -- extension to the fraction field.
    simpa [fA] using
      (uniformizer_additive_polynomial_monic
        (A := A) (p := p) (π := π) (n := n) (q := q) hq_gt_one)
  have hmap_mod :
      Polynomial.map (algebraMap A K) (g %ₘ fA) =
        (Polynomial.map (algebraMap A K) g) %ₘ
          (X ^ q - C (algebraMap A K (π ^ (n + q - 1))) * X - C (algebraMap A K π) : K[X]) := by
    -- Mapping coefficients commutes with division by a monic polynomial.
    simpa [fA] using
      (Polynomial.map_modByMonic (f := g) (g := fA) (algebraMap A K) hfA_monic)
  have hmap_zero :
      Polynomial.map (algebraMap A K) (g %ₘ fA) = 0 := by
    -- Divisibility upstairs forces the remainder to vanish after coefficient extension.
    rw [hmap_mod, Polynomial.modByMonic_eq_zero_iff_dvd]
    · exact hg
    · simpa using
        (uniformizer_additive_fraction_polynomial_monic
          (A := A) (p := p) (π := π) (n := n) (q := q) hq_gt_one)
  have hmod_zero : g %ₘ fA = 0 := by
    -- Injectivity of `A → K` lets us read the vanishing remainder back on coefficients.
    ext m
    apply IsFractionRing.injective A K
    simpa [Polynomial.coeff_map] using congrArg (fun r : Polynomial K ↦ r.coeff m) hmap_zero
  -- Vanishing remainder is exactly divisibility by the monic owner polynomial over `A`.
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hfA_monic]
  simpa [fA] using hmod_zero

/-- Helper for Lemma 15.116.7: the source additive polynomial is irreducible over `A` by the same
Eisenstein argument as the radical branch. -/
private theorem uniformizer_additive_polynomial_irreducible
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n q : ℕ} (hn : 1 < n) (hq : ∃ m : ℕ, q = p ^ m) (hq_ne_one : q ≠ 1) :
    let fA : A[X] := X ^ q - C (π ^ (n + q - 1)) * X - C π
    Irreducible fA := by
  let fA : A[X] := X ^ q - C (π ^ (n + q - 1)) * X - C π
  let hπirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  have hq_pos : 0 < q := by
    -- A positive prime power cannot vanish.
    rcases hq with ⟨m, rfl⟩
    exact pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m
  have hq_gt_one : 1 < q := by
    -- The nontrivial branch of the source proof is exactly the `q > 1` branch.
    exact lt_of_le_of_ne (Nat.succ_le_of_lt hq_pos) hq_ne_one.symm
  let g : A[X] := C (π ^ (n + q - 1)) * X + C π
  have hdeg : degree g < q := by
    -- The correction term has degree at most `1`, so it lies strictly below the leading `X ^ q`.
    refine lt_of_le_of_lt (degree_add_le (C (π ^ (n + q - 1)) * X : A[X]) (C π)) ?_
    have hq_one : (1 : WithBot ℕ) < q := by
      exact_mod_cast hq_gt_one
    simpa [g] using hq_one
  have hmonic : fA.Monic := by
    -- Keep the owner polynomial monic over `A` before invoking Eisenstein.
    simpa [fA] using
      (uniformizer_additive_polynomial_monic
        (A := A) (p := p) (π := π) (n := n) (q := q) hq_gt_one)
  have hnatDegree : fA.natDegree = q := by
    -- Since the correction term has smaller degree, the source polynomial really has degree `q`.
    have hdeg_lt_X : degree g < degree (X ^ q : A[X]) := by
      simpa using hdeg
    apply Polynomial.natDegree_eq_of_degree_eq_some
    calc
      fA.degree = degree ((X ^ q : A[X]) - g) := by simp [fA, g]
      _ = degree (X ^ q : A[X]) := Polynomial.degree_sub_eq_left_of_degree_lt hdeg_lt_X
      _ = q := by simp
  have hcoeff_mem : ∀ {k : ℕ}, k < fA.natDegree → fA.coeff k ∈ maximalIdeal A := by
    intro k hk
    have hkq : k < q := by
      simpa [hnatDegree] using hk
    by_cases hk0 : k = 0
    · subst hk0
      have hπ_mem : π ∈ maximalIdeal A := by
        rw [hπ]
        exact Ideal.mem_span_singleton_self π
      have hcoeff0 : fA.coeff 0 = -π := by
        -- At degree `0`, only the constant coefficient `-π` survives.
        have h0q : 0 ≠ q := Nat.ne_of_lt hq_pos
        simp [fA, h0q]
      rw [hcoeff0]
      exact (Submodule.neg_mem_iff _).2 hπ_mem
    · by_cases hk1 : k = 1
      · subst hk1
        have hπ_mem : π ∈ maximalIdeal A := by
          rw [hπ]
          exact Ideal.mem_span_singleton_self π
        have hexp_pos : 0 < n + q - 1 := by
          omega
        have hpow_mem :
            π ^ (n + q - 1) ∈ maximalIdeal A := by
          -- The linear coefficient is divisible by the uniformizer because its exponent is
          -- positive.
          exact (Ideal.pow_le_self (I := maximalIdeal A) (Nat.ne_of_gt hexp_pos))
            (Ideal.pow_mem_pow hπ_mem (n + q - 1))
        have hcoeff1 : fA.coeff 1 = -(π ^ (n + q - 1)) := by
          -- At degree `1`, the only lower nonzero coefficient is the displayed linear term.
          have h1q : 1 ≠ q := Nat.ne_of_lt hq_gt_one
          simp [fA, h1q]
        rw [hcoeff1]
        exact (Submodule.neg_mem_iff _).2 hpow_mem
      · have hcoeff_zero : fA.coeff k = 0 := by
          -- All other coefficients below degree `q` vanish.
          have hk_ne_q : k ≠ q := Nat.ne_of_lt hkq
          simp [fA, hk0, hk1, hk_ne_q]
        rw [hcoeff_zero]
        exact (maximalIdeal A).zero_mem
  have hπ_not_mem_sq : π ∉ maximalIdeal A ^ 2 := by
    -- Route correction: keep the source Eisenstein obstruction on the constant term `π` itself.
    rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdiv
    rcases hdiv with ⟨a, ha⟩
    have hπ0 : π ≠ 0 := hπirr.ne_zero
    have hone : 1 = π * a := by
      apply mul_left_cancel₀ hπ0
      simpa [pow_two, mul_assoc, mul_one] using ha
    exact hπirr.1 <| isUnit_of_dvd_one ⟨a, hone⟩
  have hcoeff0_not_mem_sq : fA.coeff 0 ∉ maximalIdeal A ^ 2 := by
    -- The constant coefficient is `-π`, so nondivisibility by `π^2` transfers immediately.
    intro hcoeff
    have hcoeff0 : fA.coeff 0 = -π := by
      have h0q : 0 ≠ q := Nat.ne_of_lt hq_pos
      simp [fA, h0q]
    rw [hcoeff0] at hcoeff
    exact hπ_not_mem_sq ((Submodule.neg_mem_iff _).1 hcoeff)
  have hEis : fA.IsEisensteinAt (maximalIdeal A) := by
    -- Eisenstein at the maximal ideal is the source-proof mechanism for irreducibility.
    refine hmonic.isEisensteinAt_of_mem_of_notMem (maximalIdeal.isMaximal A).ne_top ?_ ?_
    · intro k hk
      exact hcoeff_mem hk
    · simpa [fA] using hcoeff0_not_mem_sq
  -- Once the coefficient package is fixed over `A`, irreducibility follows immediately.
  refine hEis.irreducible (maximalIdeal.isMaximal A).isPrime hmonic.isPrimitive ?_
  simpa [hnatDegree] using hq_pos

/-- Helper for Lemma 15.116.7: in equal characteristic `p`, the source additive polynomial has
constant derivative. -/
private theorem uniformizer_additive_fraction_polynomial_derivative
    (π : A) {n q : ℕ} (hq : ∃ m : ℕ, q = p ^ m) [CharP K p] :
    let fK : K[X] := X ^ q - C (algebraMap A K (π ^ (n + q - 1))) * X - C (algebraMap A K π)
    derivative fK = -C (algebraMap A K (π ^ (n + q - 1))) := by
  let c : K := algebraMap A K (π ^ (n + q - 1))
  let d : K := algebraMap A K π
  let fK : K[X] := X ^ q - C c * X - C d
  have hq_cast_zero : (q : K) = 0 := by
    -- A `p`-power exponent vanishes in characteristic `p`.
    rcases hq with ⟨m, rfl⟩
    have hp_cast_zero : (p : K) = 0 := CharP.cast_eq_zero K p
    simp [hp_cast_zero]
  -- Differentiate termwise, then kill the `X ^ q` derivative using `char K = p`.
  calc
    derivative fK = derivative (X ^ q : K[X]) - derivative (C c * X) - derivative (C d) := by
      simp [fK, sub_eq_add_neg, add_assoc]
    _ = C (q : K) * X ^ (q - 1) - C c := by
      simp [Polynomial.derivative_X_pow, mul_comm, mul_left_comm, mul_assoc]
    _ = -C c := by
      simp [hq_cast_zero]

/-- Helper for Lemma 15.116.7: the source additive polynomial over `K` is separable in the
equal-characteristic branch. -/
private theorem uniformizer_additive_fraction_polynomial_separable
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n q : ℕ} (hq : ∃ m : ℕ, q = p ^ m) [CharP K p] :
    let fK : K[X] := X ^ q - C (algebraMap A K (π ^ (n + q - 1))) * X - C (algebraMap A K π)
    fK.Separable := by
  let c : K := algebraMap A K (π ^ (n + q - 1))
  let d : K := algebraMap A K π
  let fK : K[X] := X ^ q - C c * X - C d
  let hπirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  have hc_ne_zero : c ≠ 0 := by
    -- The constant derivative coefficient is a nonzero power of the base uniformizer.
    exact map_ne_zero (IsFractionRing.injective A K) (pow_ne_zero _ hπirr.ne_zero)
  have hf_deriv : derivative fK = -C c := by
    -- Reuse the source derivative computation in the specialized notation.
    simpa [fK, c, d] using
      (uniformizer_additive_fraction_polynomial_derivative
        (A := A) (p := p) (π := π) (n := n) (q := q) hq)
  -- A nonzero constant derivative is a unit, so the polynomial is separable.
  rw [Polynomial.separable_def']
  refine ⟨0, -C c⁻¹, ?_⟩
  calc
    (0 : K[X]) * fK + (-C c⁻¹) * derivative fK = (-C c⁻¹) * derivative fK := by
      simp
    _ = (-C c⁻¹) * (-C c) := by
      rw [hf_deriv]
    _ = 1 := by
      simp [hc_ne_zero]

/-- Helper for Lemma 15.116.7: once the distinguished root `y` satisfies the source additive
equation, the image of the base uniformizer factors through `y`. -/
private theorem uniformizer_additive_uniformizer_factorization
    (π : A) {n q : ℕ} (hq_pos : 0 < q)
    {R : Type*} [CommRing R] [Algebra A R] (y : R)
    (hy_eq :
      y ^ q = algebraMap A R π + algebraMap A R (π ^ (n + q - 1)) * y) :
    algebraMap A R π =
      y * (y ^ (q - 1) - algebraMap A R (π ^ (n + q - 1))) := by
  rcases q with _ | q
  · exact (Nat.not_lt_zero _ hq_pos).elim
  -- Rewrite `y ^ (q + 1)` as `y * y ^ q`, then isolate the image of `π`.
  have hrewrite :
      algebraMap A R π + algebraMap A R (π ^ (n + Nat.succ q - 1)) * y =
        y * y ^ q := by
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hy_eq.symm
  calc
    algebraMap A R π =
        y * y ^ q - algebraMap A R (π ^ (n + Nat.succ q - 1)) * y := by
          exact eq_sub_of_add_eq hrewrite
    _ = y * (y ^ q - algebraMap A R (π ^ (n + Nat.succ q - 1))) := by
          ring

/-- Helper for Lemma 15.116.7: in the owner ring `A[y]`, the image of the base uniformizer lies in
the principal ideal generated by `y`. -/
private theorem uniformizer_additive_uniformizer_mem_root_span
    (π : A) {n q : ℕ} (hq_pos : 0 < q)
    {R : Type*} [CommRing R] [Algebra A R] (y : R)
    (hy_eq :
      y ^ q = algebraMap A R π + algebraMap A R (π ^ (n + q - 1)) * y) :
    algebraMap A R π ∈ Ideal.span ({y} : Set R) := by
  -- The factorization through `y` immediately places `π` in the principal ideal `(y)`.
  rw [uniformizer_additive_uniformizer_factorization
    (A := A) (π := π) (n := n) (q := q) hq_pos y hy_eq]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/-- Helper for Lemma 15.116.7: every element of the maximal ideal of `A` maps into the principal
ideal generated by the distinguished additive root. -/
private theorem uniformizer_additive_image_mem_root_span_of_mem_maximal
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n q : ℕ} (hq_pos : 0 < q)
    {R : Type*} [CommRing R] [Algebra A R] (y : R)
    (hy_eq :
      y ^ q = algebraMap A R π + algebraMap A R (π ^ (n + q - 1)) * y)
    {a : A} (ha : a ∈ maximalIdeal A) :
    algebraMap A R a ∈ Ideal.span ({y} : Set R) := by
  rw [hπ, Ideal.mem_span_singleton] at ha
  rcases ha with ⟨b, rfl⟩
  -- After expressing `a` as a multiple of `π`, reuse the already-proved containment for `π`.
  rw [map_mul]
  exact Ideal.mul_mem_right _ _
    (uniformizer_additive_uniformizer_mem_root_span
      (A := A) (π := π) (n := n) (q := q) hq_pos y hy_eq)

/-- Helper for Lemma 15.116.7: a surjective residue-field map whose kernel is `(y)` makes `(y)` a
maximal ideal. -/
private theorem span_singleton_isMaximal_of_surjective_residue_map
    {R : Type*} [CommRing R] [Algebra A R]
    (y : R) (φ : R →ₐ[A] ResidueField A)
    (hφ_surj : Function.Surjective φ)
    (hker : RingHom.ker φ.toRingHom = Ideal.span ({y} : Set R)) :
    Ideal.IsMaximal (Ideal.span ({y} : Set R)) := by
  let eker : (R ⧸ RingHom.ker φ.toRingHom) ≃+* ResidueField A :=
    RingHom.quotientKerEquivOfSurjective (f := φ.toRingHom) hφ_surj
  have hfield : IsField (R ⧸ RingHom.ker φ.toRingHom) :=
    eker.toRingEquiv.toMulEquiv.isField (Field.toIsField _)
  have hker_max : Ideal.IsMaximal (RingHom.ker φ.toRingHom) :=
    Ideal.Quotient.maximal_of_isField _ hfield
  simpa [hker] using hker_max

/-- Helper for Lemma 15.116.7: reducing the additive root equation modulo a maximal ideal forces
the distinguished root into that maximal ideal. -/
private theorem root_mem_of_isMaximal_of_additive_equation
    {R : Type*} [CommRing R] [IsDomain R] [Algebra A R] [Algebra.IsIntegral A R]
    {π c : A} {q : ℕ} {y : R}
    (hπ_mem : π ∈ maximalIdeal A) (hc_mem : c ∈ maximalIdeal A)
    (hy_eq : y ^ q = algebraMap A R π + algebraMap A R c * y)
    (P : Ideal R) (hP : P.IsMaximal) :
    y ∈ P := by
  letI : P.IsMaximal := hP
  have hcomap : Ideal.comap (algebraMap A R) P = maximalIdeal A := by
    -- Maximal ideals in an integral extension contract to maximal ideals downstairs.
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
  have hπ_mem_P : algebraMap A R π ∈ P := by
    -- Contract membership back to the base DVR.
    rw [← Ideal.mem_comap, hcomap]
    exact hπ_mem
  have hc_mem_P : algebraMap A R c ∈ P := by
    -- The higher additive coefficient contracts to the same maximal ideal.
    rw [← Ideal.mem_comap, hcomap]
    exact hc_mem
  have hcy_mem_P : algebraMap A R c * y ∈ P := by
    -- Ideals are closed under multiplication by ambient elements.
    exact P.mul_mem_left _ hc_mem_P
  have hy_pow_mem : y ^ q ∈ P := by
    -- The additive equation shows `y ^ q` lies in `P`.
    rw [hy_eq]
    exact P.add_mem hπ_mem_P hcy_mem_P
  -- Primality of a maximal ideal then forces the root itself into `P`.
  exact hP.isPrime.mem_of_pow_mem q hy_pow_mem

/-- Helper for Lemma 15.116.7: if `(y)` is maximal and every maximal ideal contains `y`, then the
owner ring is local with maximal ideal `(y)`. -/
private theorem isLocalRing_and_maximalIdeal_eq_of_span_singleton_isMaximal
    {R : Type*} [CommRing R] (y : R)
    (hspan_max : Ideal.IsMaximal (Ideal.span ({y} : Set R)))
    (hy_mem : ∀ I : Ideal R, I.IsMaximal → y ∈ I) :
    ∃ hlocal : IsLocalRing R,
      @maximalIdeal R inferInstance hlocal = Ideal.span ({y} : Set R) := by
  have hlocal : IsLocalRing R := by
    -- Every maximal ideal contains `y`, so maximality of `(y)` makes it the unique maximal ideal.
    refine IsLocalRing.of_unique_max_ideal ?_
    refine ⟨Ideal.span ({y} : Set R), hspan_max, ?_⟩
    intro I hI
    have hy_mem_I : y ∈ I := hy_mem I hI
    have hle : Ideal.span ({y} : Set R) ≤ I := by
      refine Ideal.span_le.2 ?_
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact hy_mem_I
    exact (Ideal.IsMaximal.eq_of_le hspan_max hI.ne_top hle).symm
  -- In a local ring, the unique maximal ideal is the one just identified.
  exact ⟨hlocal, (IsLocalRing.eq_maximalIdeal hspan_max).symm⟩

-- Proof sketch: split according to the characteristic of `K = FractionRing A`. In equal
-- characteristic zero, use the radical extension from Lemma `15.115.2`. In characteristic `p`,
-- adjoin a root `z` of `z ^ q - π ^ n * z = π ^ (1 - q)`, set `π_B = π z`, and compute directly
-- that the resulting degree-`q` extension is totally ramified and that `π_B` satisfies the two
-- displayed congruences in the integral closure.
/-- Helper for Lemma 15.116.7: in equal characteristic `p`, the source-faithful additive
polynomial `X^q - π^(n + q - 1) X - π` should supply the required witness. -/
private theorem exists_additive_extension_data_of_equal_characteristic
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n q : ℕ} (hn : 1 < n) (hq : ∃ m : ℕ, q = p ^ m)
    (hq_ne_one : q ≠ 1) (hchar0 : ¬ CharZero K) :
    ∃ (L : Type (max u v)) (_ : Field L) (_ : Algebra A L) (_ : Algebra K L)
      (_ : IsScalarTower A K L) (_ : FiniteDimensional K L) (_ : Algebra.IsSeparable K L)
      (_ : IsTotallyRamifiedWithRespectTo A L),
      let B := integralClosure A L
      Module.finrank K L = q ∧
        ∃ πB b b' : B,
          ramificationIndex A B = q ∧
            maximalIdeal B = Ideal.span ({πB} : Set B) ∧
            πB ^ q = algebraMap A B π + algebraMap A B (π ^ n) * b ∧
            πB ^ q = algebraMap A B π + πB ^ (n * q) * b' := by
  letI : CharP K p := fractionRing_charP_of_not_charZero (A := A) (p := p) hchar0
  let fA : A[X] := X ^ q - C (π ^ (n + q - 1)) * X - C π
  let fK : K[X] := fA.map (algebraMap A K)
  have hq_pos : 0 < q := by
    -- A positive prime power cannot vanish.
    rcases hq with ⟨m, rfl⟩
    exact pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m
  have hq_gt_one : 1 < q := by
    -- The nontrivial branch is exactly the `q > 1` branch of the source proof.
    exact lt_of_le_of_ne (Nat.succ_le_of_lt hq_pos) hq_ne_one.symm
  have hfK_monic : fK.Monic := by
    -- Lock in the source owner polynomial before the local-ring comparison.
    simpa [fA, fK, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C] using
      (uniformizer_additive_fraction_polynomial_monic
        (A := A) (p := p) (π := π) (n := n) (q := q) hq_gt_one)
  have hfK_deriv :
      derivative fK = -C (algebraMap A K (π ^ (n + q - 1))) := by
    -- The additive polynomial is already separable because its derivative is a nonzero constant.
    simpa [fA, fK, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C] using
      (uniformizer_additive_fraction_polynomial_derivative
        (A := A) (p := p) (π := π) (n := n) (q := q) hq)
  have hfK_sep : fK.Separable := by
    -- This closes the field-side separability package from the source route.
    simpa [fA, fK, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C] using
      (uniformizer_additive_fraction_polynomial_separable
        (A := A) (p := p) π hπ (n := n) (q := q) hq)
  have hfA_irr : Irreducible fA := by
    -- The source polynomial is already irreducible over `A` by the DVR Eisenstein argument.
    simpa [fA] using
      (uniformizer_additive_polynomial_irreducible
        (A := A) (p := p) (π := π) hπ (n := n) (q := q) hn hq hq_ne_one)
  have hfA_monic : fA.Monic := by
    -- Keep the ring-side owner monic so Gauss's lemma transports irreducibility to `K`.
    simpa [fA] using
      (uniformizer_additive_polynomial_monic
        (A := A) (p := p) (π := π) (n := n) (q := q) hq_gt_one)
  have hfK_irr : Irreducible fK := by
    -- The field-side owner polynomial is the fraction-field image of the irreducible ring-side
    -- polynomial.
    simpa [fA, fK, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C] using
      (hfA_monic.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hfA_irr
  let R := AdjoinRoot fA
  let y : R := AdjoinRoot.root fA
  have hy_eq :
      y ^ q = algebraMap A R π + algebraMap A R (π ^ (n + q - 1)) * y := by
    -- The distinguished quotient root already satisfies the source equation over the owner ring
    -- `R = A[y]`.
    have hroot :
        y ^ q - (algebraMap A R (π ^ (n + q - 1)) * y + algebraMap A R π) = 0 := by
      simpa [fA, y, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (AdjoinRoot.eval₂_root fA)
    exact by
      simpa [add_comm, add_left_comm, add_assoc] using sub_eq_zero.mp hroot
  have hpi_mem_span :
      algebraMap A R π ∈ Ideal.span ({y} : Set R) := by
    -- The source root equation already forces the image of the base uniformizer into `(y)`.
    exact uniformizer_additive_uniformizer_mem_root_span
      (A := A) (π := π) (n := n) (q := q) hq_pos y hy_eq
  have hmax_mem_span :
      ∀ {a : A}, a ∈ maximalIdeal A →
        algebraMap A R a ∈ Ideal.span ({y} : Set R) := by
    intro a ha
    -- This is the coefficient-level consequence needed for the later quotient-kernel computation.
    exact uniformizer_additive_image_mem_root_span_of_mem_maximal
      (A := A) (π := π) hπ (n := n) (q := q) hq_pos y hy_eq ha
  let eκ : (A ⧸ maximalIdeal A) ≃+* ResidueField A :=
    (RingEquiv.ofBijective
      (algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).trans <|
        (RingEquiv.ofBijective
          (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
          (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm
  have heκ_mk (a : A) :
      eκ (Ideal.Quotient.mk (maximalIdeal A) a) = residue A a := by
    -- Normalize the quotient class of `a` to the intrinsic residue field.
    let eκR : ResidueField A ≃+* (maximalIdeal A).ResidueField :=
      RingEquiv.ofBijective
        (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))
    change eκR.symm (algebraMap A (maximalIdeal A).ResidueField a) = residue A a
    rw [show algebraMap A (maximalIdeal A).ResidueField a = eκR (residue A a) by rfl]
    exact eκR.symm_apply_apply (residue A a)
  have hresidue_zero_iff (a : A) :
      residue A a = 0 ↔ a ∈ maximalIdeal A := by
    constructor
    · intro ha
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      apply eκ.injective
      rw [heκ_mk, ha, RingEquiv.map_zero]
    · intro ha
      rw [← heκ_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  have hres_pi : residue A π = 0 := by
    -- The chosen uniformizer dies in the residue field.
    exact (hresidue_zero_iff π).2 <| by
      rw [hπ]
      exact Ideal.mem_span_singleton_self π
  have hres_pi_pow : residue A (π ^ (n + q - 1)) = 0 := by
    -- Any positive power of the uniformizer still dies modulo the maximal ideal.
    simp [map_pow, hres_pi]
  have hφ_root :
      aeval (0 : ResidueField A) fA = 0 := by
    -- The additive owner polynomial reduces to `X ^ q` at `0`.
    simp [fA, hres_pi, hres_pi_pow]
  let φ : R →ₐ[A] ResidueField A :=
    AdjoinRoot.liftAlgHom fA (residue A) 0 hφ_root
  have hφ_of (a : A) :
      φ (algebraMap A R a) = residue A a := by
    -- The lifted residue map agrees with the base residue map on coefficients.
    simpa [φ] using
      (AdjoinRoot.liftAlgHom_of (p := fA) (i := residue A) (x := (0 : ResidueField A))
        (h := hφ_root) a)
  have hφ_root_apply : φ y = 0 := by
    -- The lift was defined to kill the distinguished root.
    simp [φ, y]
  have hφ_surj : Function.Surjective φ := by
    -- Every residue-field element is the image of a coefficient class.
    intro x
    obtain ⟨xbar, rfl⟩ := eκ.surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective xbar
    refine ⟨algebraMap A R a, ?_⟩
    simpa [hφ_of, heκ_mk]
  have hspan_le_ker :
      Ideal.span ({y} : Set R) ≤ RingHom.ker φ := by
    -- The kernel contains `(y)` because `φ y = 0`.
    refine Ideal.span_le.2 ?_
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    rw [RingHom.mem_ker]
    exact hφ_root_apply
  have hker_le_span :
      RingHom.ker φ ≤ Ideal.span ({y} : Set R) := by
    intro z hz
    revert hz
    refine AdjoinRoot.induction_on (f := fA) (x := z) ?_
    intro q
    intro hq
    rw [RingHom.mem_ker] at hq
    have hconst_zero : residue A (q.coeff 0) = 0 := by
      -- Evaluating at the killed root `0` leaves only the constant coefficient.
      have hq_eval :
          aeval (0 : ResidueField A) q = 0 := by
        simpa [φ, y] using hq
      simpa using hq_eval
    have hconst_mem : q.coeff 0 ∈ maximalIdeal A := by
      exact (hresidue_zero_iff (q.coeff 0)).1 hconst_zero
    have hconst_span :
        algebraMap A R (q.coeff 0) ∈ Ideal.span ({y} : Set R) := by
      exact hmax_mem_span hconst_mem
    have hmul_span :
        y * aeval y q.divX ∈ Ideal.span ({y} : Set R) := by
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    have hsplit : q = C (q.coeff 0) + X * q.divX := by
      -- Split off the constant term so the remaining summand is visibly divisible by `X`.
      ext k
      cases k with
      | zero =>
          simp
      | succ k =>
          simp [Polynomial.coeff_divX]
    have hrepr :
        (AdjoinRoot.mk fA q : R) =
          algebraMap A R (q.coeff 0) + y * aeval y q.divX := by
      -- Re-express the quotient class as constant term plus a visible multiple of `y`.
      calc
        (AdjoinRoot.mk fA q : R) = aeval y q := by
          simpa [y] using (AdjoinRoot.aeval_eq q)
        _ = aeval y (C (q.coeff 0) + X * q.divX) := by rw [hsplit]
        _ = algebraMap A R (q.coeff 0) + y * aeval y q.divX := by
          simp [y, mul_comm, mul_left_comm, mul_assoc]
    rw [hrepr]
    exact Ideal.add_mem _ hconst_span hmul_span
  have hker_eq :
      RingHom.ker φ = Ideal.span ({y} : Set R) := by
    -- The explicit residue-evaluation kernel is exactly the principal ideal `(y)`.
    exact le_antisymm hker_le_span hspan_le_ker
  let eker : (R ⧸ RingHom.ker φ) ≃+* ResidueField A :=
    RingHom.quotientKerEquivOfSurjective (f := φ.toRingHom) hφ_surj
  let equot : (R ⧸ Ideal.span ({y} : Set R)) ≃+* ResidueField A :=
    (Ideal.quotientEquivAlgOfEq A hker_eq.symm).toRingEquiv.trans eker
  letI : IsDomain R := by
    -- The owner quotient is a domain because the additive polynomial is irreducible over `A`.
    simpa [R] using (AdjoinRoot.isDomain_of_prime (f := fA) hfA_irr.prime)
  letI : Module.Finite A R := hfA_monic.finite_adjoinRoot
  letI : Algebra.IsIntegral A R := Algebra.IsIntegral.of_finite A R
  have hπ_mem_max : π ∈ maximalIdeal A := by
    -- The chosen uniformizer generates the maximal ideal of the DVR.
    rw [hπ]
    exact Ideal.mem_span_singleton_self π
  have hcoeff_mem_max : π ^ (n + q - 1) ∈ maximalIdeal A := by
    -- Any positive power of the uniformizer still lies in the maximal ideal.
    rw [hπ, Ideal.mem_span_singleton]
    refine ⟨π ^ (n + q - 2), ?_⟩
    have hexp : n + q - 1 = (n + q - 2) + 1 := by
      omega
    calc
      π ^ (n + q - 1) = π ^ ((n + q - 2) + 1) := by rw [hexp]
      _ = π ^ (n + q - 2) * π := by rw [pow_succ]
  have hspan_max :
      Ideal.IsMaximal (Ideal.span ({y} : Set R)) := by
    -- The quotient by `(y)` is the residue field, hence a field.
    exact span_singleton_isMaximal_of_surjective_residue_map
      (A := A) y φ hφ_surj (by simpa using hker_eq)
  have hroot_mem_every_maximal :
      ∀ I : Ideal R, I.IsMaximal → y ∈ I := by
    intro I hI
    -- Reduce the additive root equation modulo the maximal ideal `I`.
    exact root_mem_of_isMaximal_of_additive_equation
      (A := A) (R := R) (π := π) (c := π ^ (n + q - 1)) (q := q)
      hπ_mem_max hcoeff_mem_max hy_eq I hI
  rcases isLocalRing_and_maximalIdeal_eq_of_span_singleton_isMaximal
      (R := R) y hspan_max hroot_mem_every_maximal with
    ⟨hlocal, hmaxR⟩
  letI : IsLocalRing R := hlocal
  have hmaxR' : maximalIdeal R = Ideal.span ({y} : Set R) := by
    -- After installing the local-ring instance, the owner maximal ideal is exactly `(y)`.
    simpa using hmaxR
  have howner_clause_four :
      ∃ (_ : IsLocalRing R) (_ : IsNoetherianRing R) (_ : IsDomain R),
        maximalIdeal R ≠ ⊥ ∧ (maximalIdeal R).IsPrincipal := by
    letI : IsNoetherianRing R := IsNoetherianRing.of_finite A R
    have hy_ne_zero : y ≠ 0 := by
      -- If `y = 0`, then the defining equation would force the nonzero uniformizer `π` to vanish
      -- in the domain `R`.
      intro hy0
      have hpi0 : algebraMap A R π = 0 := by
        simpa [hy0] using hy_eq
      exact ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ).ne_zero <|
        (NoZeroSMulDivisors.algebraMap_injective A R) hpi0
    have hmax_ne_bot : maximalIdeal R ≠ ⊥ := by
      rw [hmaxR']
      intro hbot
      have hy_mem : y ∈ (⊥ : Ideal R) := by
        simpa [hbot, y] using
          (Ideal.mem_span_singleton_self y : y ∈ Ideal.span ({y} : Set R))
      exact hy_ne_zero (by simpa using hy_mem)
    have hprincipal : (maximalIdeal R).IsPrincipal := by
      rw [hmaxR']
      infer_instance
    -- This is exactly clause `(4)` in `discreteValuationRing_tfae`.
    exact ⟨inferInstance, inferInstance, inferInstance, hmax_ne_bot, hprincipal⟩
  have hDVRR :
      @IsDiscreteValuationRing R inferInstance inferInstance := by
    have htfae :=
      (show List.TFAE
          [ (∃ (_ : IsDomain R), IsDiscreteValuationRing R),
            ∃ (_ : IsDomain R) (_ : IsNoetherianRing R), ValuationRing R ∧ ¬ IsField R,
            IsRegularLocalRing R ∧ ringKrullDim R = 1,
            ∃ (_ : IsLocalRing R) (_ : IsNoetherianRing R) (_ : IsDomain R),
              maximalIdeal R ≠ ⊥ ∧ (maximalIdeal R).IsPrincipal,
            ∃ (_ : IsLocalRing R) (_ : IsNoetherianRing R) (_ : IsDomain R)
              (_ : IsIntegrallyClosed R), ringKrullDim R = 1 ] from
        discreteValuationRing_tfae (A := R))
    have hdvr : ∃ (_ : IsDomain R), IsDiscreteValuationRing R := by
      -- Route correction: use the already-isolated clause `(4)` witness instead of expanding the
      -- local Noetherian/principal package inline.
      exact (htfae.out 3 0).mp howner_clause_four
    exact hdvr.choose_spec
  letI : IsDiscreteValuationRing R := hDVRR
  letI : IsExtensionOfDiscreteValuationRings A R := by
    -- The owner quotient is finite integral over `A`, and injectivity comes from domainness.
    refine
      { toIsLocalHom := ?_
        algebraMap_injective := ?_ }
    · exact
        (algebraMap_isIntegral_iff.mpr (show Algebra.IsIntegral A R by infer_instance)).isLocalHom
          (NoZeroSMulDivisors.algebraMap_injective A R)
    · exact NoZeroSMulDivisors.algebraMap_injective A R
  have hpow_mem_R :
      algebraMap A R (π ^ (n + q - 2)) * y ∈ maximalIdeal R := by
    have hexp_pos : 0 < n + q - 2 := by
      omega
    have hpow_mem_A : π ^ (n + q - 2) ∈ maximalIdeal A := by
      -- Positive powers of a uniformizer stay in the maximal ideal.
      exact (Ideal.pow_le_self (I := maximalIdeal A) (Nat.ne_of_gt hexp_pos))
        (Ideal.pow_mem_pow hπ_mem_max (n + q - 2))
    have hcoeff_mem_R : algebraMap A R (π ^ (n + q - 2)) ∈ maximalIdeal R := by
      rw [hmaxR']
      exact hmax_mem_span hpow_mem_A
    exact Ideal.mul_mem_right _ _ hcoeff_mem_R
  have hy_factor :
      y ^ q = algebraMap A R π * (1 + algebraMap A R (π ^ (n + q - 2)) * y) := by
    -- Rewrite the additive equation as `π` times a unit correction factor.
    have hexp : n + q - 1 = (n + q - 2) + 1 := by
      omega
    calc
      y ^ q = algebraMap A R π + algebraMap A R (π ^ ((n + q - 2) + 1)) * y := by
        simpa [hexp] using hy_eq
      _ = algebraMap A R π + (algebraMap A R π * algebraMap A R (π ^ (n + q - 2))) * y := by
        simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
      _ = algebraMap A R π * (1 + algebraMap A R (π ^ (n + q - 2)) * y) := by
        ring
  have hJac : maximalIdeal R ≤ Ring.jacobson R := by
    simpa [Ideal.jacobson_bot] using
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  have hcorr_unit :
      IsUnit (1 + algebraMap A R (π ^ (n + q - 2)) * y) := by
    -- In a local ring, `1 + m` is a unit for every `m` in the maximal ideal.
    simpa using
      (ideal_le_ring_jacobson_iff_isUnit_one_add (R := R) (I := maximalIdeal R)).1 hJac
        (algebraMap A R (π ^ (n + q - 2)) * y) hpow_mem_R
  let u : Rˣ := hcorr_unit.unit
  have hy_unit :
      y ^ q = (u : R) * algebraMap A R π := by
    -- Replace the correction factor by its chosen unit representative.
    calc
      y ^ q = algebraMap A R π * (1 + algebraMap A R (π ^ (n + q - 2)) * y) := hy_factor
      _ = algebraMap A R π * (u : R) := by rw [u.unit_spec]
      _ = (u : R) * algebraMap A R π := by ring
  have hassoc_pi :
      Associated (algebraMap A R π) (y ^ q) := by
    -- The rewritten equation shows that the image of `π` differs from `y ^ q` by a unit.
    refine (Associated.trans ?_ (associated_of_eq hy_unit).symm)
    simpa [mul_comm] using associated_of_unit_mul_left u (algebraMap A R π)
  have hmapR :
      Ideal.map (algebraMap A R) (maximalIdeal A) = maximalIdeal R ^ q := by
    -- Compare both sides through the chosen generators `π` and `y`.
    calc
      Ideal.map (algebraMap A R) (maximalIdeal A)
          = Ideal.map (algebraMap A R) (Ideal.span ({π} : Set A)) := by
              rw [hπ]
      _ = Ideal.span ({algebraMap A R π} : Set R) := by
            rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.span ({y ^ q} : Set R) := by
            exact (Ideal.span_singleton_eq_span_singleton).mpr hassoc_pi
      _ = Ideal.span ({y} : Set R) ^ q := by
            simpa using (Ideal.span_singleton_pow y q).symm
      _ = maximalIdeal R ^ q := by
            rw [← hmaxR']
  have hramR : ramificationIndex A R = q := by
    -- The mapped-maximal-ideal equality identifies the owner ramification index.
    exact ramificationIndex_eq_of_map_maximalIdeal_eq_pow (A := A) (B := R) hmapR
  have hpi_n_mem_root_pow_span :
      algebraMap A R (π ^ n) ∈ Ideal.span ({y ^ (n * q)} : Set R) := by
    have hπn_mem :
        algebraMap A R (π ^ n) ∈ Ideal.map (algebraMap A R) (maximalIdeal A ^ n) := by
      exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hπ_mem_max n)
    have hmap_pow :
        Ideal.map (algebraMap A R) (maximalIdeal A ^ n) = maximalIdeal R ^ (n * q) := by
      calc
        Ideal.map (algebraMap A R) (maximalIdeal A ^ n)
            = Ideal.map (algebraMap A R) (maximalIdeal A) ^ n := by
                rw [Ideal.map_pow]
        _ = (maximalIdeal R ^ q) ^ n := by rw [hmapR]
        _ = maximalIdeal R ^ (n * q) := by rw [pow_mul]
    rw [hmap_pow] at hπn_mem
    rw [hmaxR', ← Ideal.span_singleton_pow] at hπn_mem
    simpa [mul_comm, mul_left_comm, mul_assoc] using hπn_mem
  -- TODO: the owner-ring frontier is now closed up to locality:
  -- `(R / (y)) ≃ ResidueField A`, `(y)` is maximal, `R` is local with maximal ideal `(y)`,
  -- `R` is now upgraded to a DVR, `ramificationIndex A R = q`, and `π ^ n` already lands in the
  -- principal ideal generated by `y ^ (nq)`.
  -- The remaining source-faithful work is the owner-to-field bridge:
  -- build the injective comparison `R →ₐ[A] AdjoinRoot fK`, show `AdjoinRoot fK` is the fraction
  -- field of `R`, identify `R` with the integral closure of `A` in that field, and then
  -- transport the finished owner-side data to the canonical normalization.
  sorry

/-- Lemma 15.116.7: if `A` is a discrete valuation ring with uniformizer `π` and residue
characteristic `p > 0`, then for every integer `n > 1` and every `p`-power `q` there exists a
degree-`q` separable extension `L / FractionRing A` that is totally ramified with respect to `A`
and whose integral closure `B = integralClosure A L` has ramification index `q` and a uniformizer
`π_B` satisfying `π_B ^ q = π + π ^ n * b` and `π_B ^ q = π + π_B ^ (nq) * b'` for some
`b, b' ∈ B`; the total-ramification witness is part of the produced extension data, so the
integral-closure DVR owner is explicit on the theorem surface. -/
@[stacks 09EW]
theorem exists_totallyRamified_separable_extension_with_prescribed_uniformizer_congruence
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n q : ℕ} (hn : 1 < n) (hq : ∃ m : ℕ, q = p ^ m) :
    ∃ (L : Type (max u v)) (_ : Field L) (_ : Algebra A L) (_ : Algebra K L)
      (_ : IsScalarTower A K L) (_ : FiniteDimensional K L) (_ : Algebra.IsSeparable K L)
      (_ : IsTotallyRamifiedWithRespectTo A L),
      let B := integralClosure A L
      Module.finrank K L = q ∧
        ∃ πB b b' : B,
          ramificationIndex A B = q ∧
            maximalIdeal B = Ideal.span ({πB} : Set B) ∧
            πB ^ q = algebraMap A B π + algebraMap A B (π ^ n) * b ∧
            πB ^ q = algebraMap A B π + πB ^ (n * q) * b' := by
  by_cases hq_one : q = 1
  · -- The degree-one branch is the trivial fraction-field extension.
    subst hq_one
    exact exists_trivial_extension_data_of_degree_one (A := A) (p := p) π hπ hn
  · by_cases hchar0 : CharZero K
    · letI : CharZero K := hchar0
      -- In mixed characteristic, the radical extension `X^q - π` is separable and already totally
      -- ramified with the required displayed equations.
      exact exists_radical_extension_data_of_charZero
        (A := A) (p := p) π hπ hn hq
    · -- Route correction: the remaining branch is the equal-characteristic `p` additive-polynomial
      -- construction from the source proof, not another Kummer-style radical extension.
      exact exists_additive_extension_data_of_equal_characteristic
        (A := A) (p := p) π hπ hn hq hq_one hchar0

end
