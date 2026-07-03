import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_144_1 (from Chap10) -/
universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Definition 10.144.1: the canonical notion that the ring map `R → S` is standard étale is
`IsStandardEtale R S`. The textbook's concrete presentation is the bridge object
`StandardEtalePresentation R S`, which extends a `StandardEtalePair R` by choosing the image of
`X` in `S` and an `R`-algebra identification of `S` with the associated standard étale algebra. -/
recall IsStandardEtale

/- A `StandardEtalePresentation R S` is the source-facing bridge from the textbook polynomial data
to the intrinsic owner predicate `IsStandardEtale R S`. -/
recall StandardEtalePresentation

end Algebra

/-! ### Lemma_10_144_2 (from Chap10) -/
open scoped TensorProduct

universe u v w

namespace Algebra

/- Domain triage:
* primary domain: standard étale morphisms of commutative rings;
* sampled declarations: `IsStandardEtale`, `StandardEtalePresentation`,
  `IsStandardEtale.of_isLocalizationAway`, and the tensor-product base-change instance
  `[IsStandardEtale R S] : IsStandardEtale R' (R' ⊗[R] S)`;
* source-facing layer: clause (4), which records the failure of composition stability;
* core/canonical owner: `IsStandardEtale`;
* bridge/view layer: `StandardEtalePresentation`;
* derived API: ordinary étaleness, base change, and principal-localization stability.

Primitive-vs-derived split:
* primitive data: only the `R`-algebra `S` equipped with the owner predicate
  `IsStandardEtale R S`;
* derived API: the induced `Etale R S` structure and its standard permanence properties.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsStandardEtale R S]

/- Lemma 10.144.2 (1): a standard étale `R`-algebra is étale over `R`. This is exactly the
canonical instance `[IsStandardEtale R S] : Etale R S`. -/
#check (inferInstance : Etale R S)

/- Lemma 10.144.2 (2): the base change of a standard étale `R`-algebra along `R → R'` is
standard étale over `R'`. This is exactly the canonical tensor-product base-change instance. -/
variable (R' : Type w) [CommRing R'] [Algebra R R']

#check (inferInstance : IsStandardEtale R' (R' ⊗[R] S))

/- Lemma 10.144.2 (3): any principal localization of a standard étale `R`-algebra is again
standard étale over `R`. This is exactly `IsStandardEtale.of_isLocalizationAway`. -/
recall IsStandardEtale.of_isLocalizationAway

end

-- Proof sketch: use the finite-field counterexample from the source: `𝔽₂ → 𝔽₄` and
-- `𝔽₄ → 𝔽₄ × 𝔽₄ × 𝔽₄ × 𝔽₄` are standard étale, while the composite
-- `𝔽₂ → 𝔽₄ × 𝔽₄ × 𝔽₄ × 𝔽₄` is not standard étale.
/-- Helper for Lemma 10.144.2: the lifted base field used in the finite-field counterexample. -/
abbrev BinaryField : Type u := ULift.{u, 0} (ZMod 2)

/-- Helper for Lemma 10.144.2: the lifted field with four elements used in the counterexample. -/
abbrev QuarticField : Type v := ULift.{v, 0} (GaloisField 2 2)

/-- Helper for Lemma 10.144.2: the unlifted function ring model of four copies of `𝔽₄`. -/
abbrev QuarticFunctionRing := GaloisField 2 2 → GaloisField 2 2

/-- Helper for Lemma 10.144.2: the lifted codomain so the final witness can live in `Type w`. -/
abbrev LiftedQuarticFunctionRing : Type w := ULift.{w, 0} QuarticFunctionRing

/-- Helper for Lemma 10.144.2: the polynomial ring over the lifted binary field, with universe
frozen to match the source counterexample. -/
abbrev BinaryPolynomial : Type u := Polynomial BinaryField

/-- Helper for Lemma 10.144.2: the four binary coefficients used in the explicit normal form. -/
abbrev BinaryCoefficientVector : Type u := Fin 4 → BinaryField

/-- Helper for Lemma 10.144.2: the quartic field itself is finite, so its function ring is finite. -/
noncomputable instance galoisFieldFintype : Fintype (GaloisField 2 2) := Fintype.ofFinite _

/-- Helper for Lemma 10.144.2: the lifted quartic field is finite, so Lean can use its cardinal. -/
noncomputable instance quarticFieldFintype : Fintype QuarticField := Fintype.ofFinite QuarticField

/-- Helper for Lemma 10.144.2: the function ring over the lifted quartic field is finite as well. -/
noncomputable instance quarticFunctionRingFintype : Fintype QuarticFunctionRing :=
  Fintype.ofFinite QuarticFunctionRing

/-- Helper for Lemma 10.144.2: the lifted base field acts on the underlying quartic field. -/
noncomputable instance binaryFieldAlgebraGaloisField : Algebra BinaryField (GaloisField 2 2) :=
  ULift.algebra' (ZMod 2) (GaloisField 2 2)

/-- Helper for Lemma 10.144.2: the lifted base field acts on the unlifted function ring. -/
noncomputable instance binaryFieldAlgebraQuarticFunctionRing : Algebra BinaryField QuarticFunctionRing :=
  ULift.algebra' (ZMod 2) QuarticFunctionRing

/-- Helper for Lemma 10.144.2: the lifted quartic field acts on the unlifted function ring. -/
noncomputable instance quarticFieldAlgebraQuarticFunctionRing : Algebra QuarticField QuarticFunctionRing :=
  ULift.algebra' (GaloisField 2 2) QuarticFunctionRing

/-- Helper for Lemma 10.144.2: the lifted base field still has two elements. -/
lemma binaryField_card : Fintype.card BinaryField = 2 := by
  rw [Fintype.card_ulift, ZMod.card]

/-- Helper for Lemma 10.144.2: the lifted quartic field still has four elements. -/
lemma quarticField_card : Fintype.card QuarticField = 4 := by
  -- Reduce the lifted field to the underlying `GaloisField`.
  have hcard :
      Fintype.card QuarticField = Fintype.card (GaloisField 2 2) := by
    simpa [QuarticField] using
      (Fintype.card_congr (ULift.ringEquiv : QuarticField ≃+* GaloisField 2 2).toEquiv)
  rw [hcard, Fintype.card_eq_nat_card, GaloisField.card 2 2 (by decide)]
  norm_num

/-- Helper for Lemma 10.144.2: the function ring has cardinality `4^4 = 256`. -/
lemma quarticFunctionRing_card : Fintype.card QuarticFunctionRing = 256 := by
  -- Route correction: the obstruction for `𝔽₂ → 𝔽₄^4` is the size of the whole function ring,
  -- not the degree of `𝔽₄` over `𝔽₂`.
  have hquartic : Nat.card (GaloisField 2 2) = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_nat_card, GaloisField.card 2 2 (by decide)]
    norm_num
  -- Count all functions on the four-element field.
  calc
    Fintype.card QuarticFunctionRing = Nat.card QuarticFunctionRing := by
      rw [Fintype.card_eq_nat_card]
    _ = Nat.card (GaloisField 2 2 → GaloisField 2 2) := by rfl
    _ = Nat.card (GaloisField 2 2) ^ Nat.card (GaloisField 2 2) := by rw [Nat.card_fun]
    _ = 4 ^ 4 := by rw [hquartic]
    _ = 256 := by norm_num

/-- Helper for Lemma 10.144.2: every element of the lifted quartic field satisfies `x^4 = x`. -/
lemma quarticField_pow_four (x : QuarticField) : x ^ 4 = x := by
  have hx := FiniteField.pow_card x
  rw [quarticField_card] at hx
  simpa using hx

/-- Helper for Lemma 10.144.2: the same Frobenius relation holds pointwise on the function ring. -/
lemma quarticFunctionRing_pow_four (x : QuarticFunctionRing) : x ^ 4 = x := by
  funext a
  have ha : (x a) ^ 4 = x a := by
    have hx := FiniteField.pow_card (x a)
    rw [show Fintype.card (GaloisField 2 2) = 4 by
      rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 (by decide)]
      norm_num] at hx
    simpa using hx
  exact ha

/-- Helper for Lemma 10.144.2: on the function ring, every unit inverse is a square because
every element satisfies `x^4 = x`. -/
lemma quarticFunctionRing_inv_eq_sq {x : QuarticFunctionRing} (hx : IsUnit x) : x⁻¹ = x ^ 2 := by
  have hx4 : x ^ 4 = x := quarticFunctionRing_pow_four x
  have hcube : x ^ 3 = 1 := by
    have hmul := congrArg (fun y => y * x⁻¹) hx4
    simpa [pow_succ, pow_two, mul_assoc, hx.mul_inv_cancel] using hmul
  exact hx.unit'.inv_eq_of_mul_eq_one_right <| by
    simpa [pow_succ, pow_two, mul_assoc, mul_left_comm, mul_comm] using hcube

/-- Helper for Lemma 10.144.2: a finite separable field extension is standard étale. -/
lemma finite_separable_field_standard_etale
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsStandardEtale K L := by
  -- First package the finite separable field extension as an étale algebra.
  letI : Algebra.FiniteType K L := inferInstance
  letI : Etale K L :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
      finitePresentation :=
        (Algebra.FinitePresentation.of_finiteType (R := K) (A := L)).mp inferInstance }
  have hzero_locus : Algebra.etaleLocus K L = Set.univ :=
    (Algebra.etaleLocus_eq_univ_iff_etale (R := K) (A := L)).2 inferInstance
  have hzero : Algebra.IsEtaleAt K (⊥ : Ideal L) := by
    change (⟨(⊥ : Ideal L), inferInstance⟩ : PrimeSpectrum L) ∈ Algebra.etaleLocus K L
    simpa [hzero_locus]
  letI : Algebra.IsEtaleAt K (⊥ : Ideal L) := hzero
  -- Local standard-étale structure at the zero prime of the field.
  obtain ⟨f, hf, hf_std⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := K) (S := L) (Q := (⊥ : Ideal L))
  have hf0 : f ≠ 0 := by
    simpa using hf
  -- Localizing a field away from a nonzero element gives back the field itself.
  let e : L ≃ₐ[K] Localization.Away f :=
    (IsLocalization.atUnits L (Submonoid.powers f)
      (by
        intro y hy
        rcases hy with ⟨n, rfl⟩
        exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hf0))).restrictScalars K
  exact Algebra.IsStandardEtale.of_equiv e.symm

/-- Helper for Lemma 10.144.2: polynomial evaluation at the identity function on `𝔽₄`
surjects onto the function ring `𝔽₄^4`. -/
lemma quarticFunctionRing_interpolation_surjective :
    Function.Surjective
      (Polynomial.aeval (fun a : GaloisField 2 2 => a) :
        Polynomial (GaloisField 2 2) →ₐ[GaloisField 2 2] QuarticFunctionRing) := by
  classical
  intro r
  refine ⟨Lagrange.interpolate Finset.univ (fun a : GaloisField 2 2 => a) r, ?_⟩
  funext a
  -- Evaluate the interpolating polynomial at the node `a`.
  rw [Polynomial.aeval_fn_apply]
  simpa [Lagrange.interpolate_apply, Polynomial.eval_finset_sum, Polynomial.eval_mul] using
    (Lagrange.eval_interpolate_at_node
      (s := Finset.univ) (v := fun b : GaloisField 2 2 => b) (r := r) (i := a)
      (by
        intro x hx y hy hxy
        simpa using hxy)
      (by simp : a ∈ (Finset.univ : Finset (GaloisField 2 2))))

/-- Helper for Lemma 10.144.2: mapping coefficients into the lifted quartic field does not change
evaluation at the identity function on `𝔽₄^4`. -/
lemma quarticFunctionRing_lifted_aeval_map_eq (q : Polynomial (GaloisField 2 2)) :
    Polynomial.aeval (R := QuarticField) (A := QuarticFunctionRing)
        (fun a : GaloisField 2 2 => a) (q.map ULift.ringEquiv.symm.toRingHom) =
      Polynomial.aeval (R := GaloisField 2 2) (A := QuarticFunctionRing)
        (fun a : GaloisField 2 2 => a) q := by
  letI : IsScalarTower (GaloisField 2 2) QuarticField QuarticFunctionRing :=
    IsScalarTower.of_algebraMap_eq fun x => by
      funext a
      rfl
  -- Transport the coefficients through the scalar tower before reusing the unlifted evaluation.
  rw [show ULift.ringEquiv.symm.toRingHom = algebraMap (GaloisField 2 2) QuarticField by rfl]
  exact
    (Polynomial.aeval_map_algebraMap (R := GaloisField 2 2) (A := QuarticField)
      (B := QuarticFunctionRing) (x := fun a : GaloisField 2 2 => a) q)

/-- Helper for Lemma 10.144.2: the lifted interpolation map over `QuarticField[X]` is still
surjective onto the function ring `𝔽₄^4`. -/
lemma quarticFunctionRing_lifted_interpolation_surjective :
    Function.Surjective
      (Polynomial.aeval (R := QuarticField) (A := QuarticFunctionRing)
        (fun a : GaloisField 2 2 => a) :
        Polynomial QuarticField →ₐ[QuarticField] QuarticFunctionRing) := by
  intro r
  rcases quarticFunctionRing_interpolation_surjective r with ⟨q, hq⟩
  refine ⟨q.map ULift.ringEquiv.symm.toRingHom, ?_⟩
  -- Reuse the unlifted interpolant after transporting its coefficients into `QuarticField`.
  rw [quarticFunctionRing_lifted_aeval_map_eq]
  exact hq

/-- Helper for Lemma 10.144.2: the function ring over the quartic field is standard étale. -/
lemma quarticFunctionRing_standard_etale :
    IsStandardEtale QuarticField QuarticFunctionRing := by
  -- Route correction: first keep interpolation on the unlifted `𝔽₄`-valued function ring, and
  -- only then transport the resulting polynomial presentation to the lifted base field.
  let P : StandardEtalePair QuarticField :=
    { f := Polynomial.X ^ 4 - Polynomial.X
      monic_f := by
        simpa using
          (Polynomial.monic_X_pow_sub (p := Polynomial.X) (n := 4)
            (by simpa using (show (Polynomial.X : Polynomial QuarticField).degree < 4 by simp)))
      g := 1
      cond := by
        refine ⟨-1, 0, 1, ?_⟩
        rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
        have h4 : (4 : QuarticField) = 0 :=
          (CharP.cast_eq_zero_iff QuarticField 2 4).2 (by decide)
        norm_num
        exact h4 }
  let x : QuarticFunctionRing := fun a => a
  have hx : P.HasMap x := by
    constructor
    · -- The identity function is a root of `X^4 - X` because every element of `𝔽₄` satisfies
      -- the Frobenius relation `a^4 = a`.
      simpa [P, x, quarticFunctionRing_pow_four x]
    · -- The localization polynomial is `1`, so its value is invertible.
      simpa [P, x]
  let ePi : (GaloisField 2 2 → QuarticField) ≃ₐ[QuarticField] QuarticFunctionRing :=
    { toFun := fun f a => (f a).down
      invFun := fun f a => ULift.up (f a)
      left_inv := by
        intro f
        funext a
        simpa using ULift.up_down (f a)
      right_inv := by
        intro f
        funext a
        simpa using ULift.down_up (f a)
      map_mul' := by
        intro f g
        funext a
        rfl
      map_add' := by
        intro f g
        funext a
        rfl
      commutes' := by
        intro r
        funext a
        rfl }
  letI : Etale QuarticField (GaloisField 2 2 → QuarticField) := inferInstance
  letI : Etale QuarticField QuarticFunctionRing := Algebra.Etale.of_equiv ePi
  let f : P.Ring →ₐ[QuarticField] QuarticFunctionRing := P.lift x hx
  -- Every function is already a polynomial in the identity function, so the standard-étale
  -- presentation surjects onto the function ring.
  refine Algebra.IsStandardEtale.of_surjective f ?_
  intro r
  rcases quarticFunctionRing_lifted_interpolation_surjective r with ⟨q, hq⟩
  refine ⟨Polynomial.aeval P.X q, ?_⟩
  calc
    f (Polynomial.aeval P.X q) = Polynomial.aeval (f P.X) q := by
      simpa using (Polynomial.aeval_algHom_apply f P.X q).symm
    _ = Polynomial.aeval x q := by simp [f]
    _ = r := hq

/-- Helper for Lemma 10.144.2: a standard étale presentation over `𝔽₂` makes polynomial
evaluation at the presentation coordinate surjective onto `𝔽₄^4`. -/
lemma standardEtalePresentation_aeval_surjective_of_function_ring
    (P : StandardEtalePresentation BinaryField.{u} QuarticFunctionRing) :
    Function.Surjective
      (Polynomial.aeval (R := BinaryField.{u}) (A := QuarticFunctionRing) P.x :
        Polynomial BinaryField.{u} →ₐ[BinaryField.{u}] QuarticFunctionRing) := by
  let evalx : Polynomial BinaryField.{u} →ₐ[BinaryField.{u}] QuarticFunctionRing :=
    Polynomial.aeval (R := BinaryField.{u}) (A := QuarticFunctionRing) P.x
  intro y
  obtain ⟨p, n, hp⟩ :
      ∃ p : Polynomial BinaryField.{u}, ∃ n, y * evalx P.g ^ n = evalx p := by
    simpa [evalx] using P.exists_mul_aeval_x_g_pow_eq_aeval_x y
  have hu : IsUnit (evalx P.g ^ n) := by
    simpa [evalx] using P.hasMap.2.pow n
  have hy :
      y = evalx p * (evalx P.g ^ n) ^ 2 := by
    -- Multiply the presentation equation by the inverse square to isolate `y`.
    calc
      y = y * 1 := by simp
      _ = y * (evalx P.g ^ n * (evalx P.g ^ n)⁻¹) := by
            rw [hu.mul_inv_cancel]
      _ = (y * evalx P.g ^ n) * (evalx P.g ^ n)⁻¹ := by rw [mul_assoc]
      _ = evalx p * (evalx P.g ^ n)⁻¹ := by rw [hp]
      _ = evalx p * (evalx P.g ^ n) ^ 2 := by
            rw [quarticFunctionRing_inv_eq_sq hu]
  let q : Polynomial BinaryField.{u} := p * P.g ^ (n * 2)
  refine ⟨q, ?_⟩
  -- Evaluate the corrected polynomial and rewrite its denominator factor as a square.
  calc
    evalx q = evalx p * (evalx P.g ^ n) ^ 2 := by
      simp [evalx, q, map_mul, map_pow, pow_mul]
    _ = y := hy.symm

/-- Helper for Lemma 10.144.2: every power of an element of `𝔽₄^4` collapses to a four-term
`𝔽₂`-linear combination because `x^4 = x` implies `x^(n + 4) = x^(n + 1)`. -/
lemma quarticFunctionRing_pow_eq_four_term (x : QuarticFunctionRing) :
    ∀ n : ℕ, ∃ c : Fin 4 → BinaryField.{u}, x ^ n = ∑ i : Fin 4, c i • x ^ (i : Nat) := by
  have hstep : ∀ m : ℕ, x ^ (m + 4) = x ^ (m + 1) := by
    intro m
    -- Rewrite the fourth power with `x^4 = x` and collapse one copy of `x`.
    calc
      x ^ (m + 4) = x ^ m * x ^ 4 := by rw [pow_add]
      _ = x ^ m * x := by rw [quarticFunctionRing_pow_four x]
      _ = x ^ (m + 1) := by rw [pow_succ]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hsmall : n < 4
      · -- The first four powers are the explicit basis terms `1, x, x^2, x^3`.
        interval_cases n
        · refine ⟨![1, 0, 0, 0], ?_⟩
          simp [Fin.sum_univ_four]
        · refine ⟨![0, 1, 0, 0], ?_⟩
          simp [Fin.sum_univ_four]
        · refine ⟨![0, 0, 1, 0], ?_⟩
          simp [Fin.sum_univ_four]
        · refine ⟨![0, 0, 0, 1], ?_⟩
          simp [Fin.sum_univ_four]
      · have h4 : 4 ≤ n := Nat.le_of_not_gt hsmall
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h4
        have hlt : m + 1 < 4 + m := by omega
        rcases ih (m + 1) hlt with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        -- The recurrence reduces `x^(m+4)` to the smaller power `x^(m+1)`.
        calc
          x ^ (4 + m) = x ^ (m + 1) := by simpa [Nat.add_comm] using hstep m
          _ = ∑ i : Fin 4, c i • x ^ (i : Nat) := hc

/-- Helper for Lemma 10.144.2: every polynomial value in `𝔽₄^4` is an explicit four-term
`𝔽₂`-linear combination of `1, x, x^2, x^3`. -/
lemma quarticFunctionRing_aeval_eq_four_term
    (x : QuarticFunctionRing) (p : Polynomial BinaryField.{u}) :
    ∃ c : Fin 4 → BinaryField.{u},
      Polynomial.aeval (R := BinaryField.{u}) (A := QuarticFunctionRing) x p =
        ∑ i : Fin 4, c i • x ^ (i : Nat) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rcases hp with ⟨cp, hcp⟩
    rcases hq with ⟨cq, hcq⟩
    refine ⟨fun i => cp i + cq i, ?_⟩
    -- Add the two normal forms coefficientwise.
    calc
      Polynomial.aeval (R := BinaryField.{u}) (A := QuarticFunctionRing) x (p + q)
          = Polynomial.aeval (R := BinaryField.{u}) (A := QuarticFunctionRing) x p
              + Polynomial.aeval (R := BinaryField.{u}) (A := QuarticFunctionRing) x q := by
                rw [Polynomial.aeval_add]
      _ = (∑ i : Fin 4, cp i • x ^ (i : Nat)) + ∑ i : Fin 4, cq i • x ^ (i : Nat) := by
            rw [hcp, hcq]
      _ = ∑ i : Fin 4, (cp i + cq i) • x ^ (i : Nat) := by
            rw [← Finset.sum_add_distrib]
            congr with i
            rw [add_smul]
  · intro n a
    obtain ⟨c, hc⟩ :
        ∃ c : Fin 4 → BinaryField.{u}, x ^ n = ∑ i : Fin 4, c i • x ^ (i : Nat) :=
      quarticFunctionRing_pow_eq_four_term x n
    refine (show ∃ c' : Fin 4 → BinaryField.{u},
      Polynomial.aeval (R := BinaryField.{u}) (A := QuarticFunctionRing) x
          (Polynomial.monomial n a) =
        ∑ i : Fin 4, c' i • x ^ (i : Nat) from ?_)
    refine ⟨((fun i : Fin 4 => a * c i) : Fin 4 → BinaryField.{u}), ?_⟩
    -- Evaluate a monomial and absorb its scalar into the four coefficients.
    calc
      Polynomial.aeval (R := BinaryField.{u}) (A := QuarticFunctionRing) x
          (Polynomial.monomial n a)
          = (algebraMap BinaryField.{u} QuarticFunctionRing a) * x ^ n := by
              rw [Polynomial.aeval_monomial]
      _ = a • x ^ n := by rw [Algebra.smul_def]
      _ = a • ∑ i : Fin 4, c i • x ^ (i : Nat) := by rw [hc]
      _ = ∑ i : Fin 4, ((fun i : Fin 4 => a * c i) : Fin 4 → BinaryField.{u}) i •
            x ^ (i : Nat) := by
            simpa [Finset.smul_sum, smul_smul]

/-- Helper for Lemma 10.144.2: if `𝔽₂ → 𝔽₄^4` were standard étale, then evaluation at one
element would already surject from four binary coefficients. -/
lemma quarticFunctionRing_four_term_map_surjective_of_standard_etale
    [IsStandardEtale BinaryField.{u} QuarticFunctionRing] :
    ∃ x : QuarticFunctionRing, Function.Surjective
      (fun c : Fin 4 → BinaryField.{u} => ∑ i : Fin 4, c i • x ^ (i : Nat)) := by
  let P : StandardEtalePresentation BinaryField.{u} QuarticFunctionRing :=
    IsStandardEtale.nonempty_standardEtalePresentation.some
  refine ⟨P.x, ?_⟩
  intro y
  obtain ⟨p, hp⟩ := standardEtalePresentation_aeval_surjective_of_function_ring P y
  obtain ⟨c, hc⟩ := quarticFunctionRing_aeval_eq_four_term P.x p
  -- First write `y` as a polynomial in the presentation coordinate, then compress to four terms.
  refine ⟨c, ?_⟩
  calc
    ∑ i : Fin 4, c i • P.x ^ (i : Nat)
        = Polynomial.aeval (R := BinaryField.{u}) (A := QuarticFunctionRing) P.x p := by
            simpa using hc.symm
    _ = y := hp

/-- Helper for Lemma 10.144.2: the composite `𝔽₂ → 𝔽₄^4` is not standard étale. -/
lemma quarticFunctionRing_not_standard_etale_over_binaryField :
    ¬ IsStandardEtale BinaryField.{u} QuarticFunctionRing := by
  intro hstd
  letI : IsStandardEtale BinaryField.{u} QuarticFunctionRing := hstd
  obtain ⟨x, hsurj⟩ := quarticFunctionRing_four_term_map_surjective_of_standard_etale
  have hle :
      Fintype.card QuarticFunctionRing ≤ Fintype.card (Fin 4 → BinaryField.{u}) :=
    Fintype.card_le_of_surjective _ hsurj
  have hcoeff : Fintype.card (Fin 4 → BinaryField.{u}) = 16 := by
    -- Count all four-tuples of binary coefficients explicitly.
    calc
      Fintype.card (Fin 4 → BinaryField.{u}) = Fintype.card BinaryField.{u} ^ Fintype.card (Fin 4) := by
        rw [Fintype.card_fun]
      _ = 2 ^ 4 := by rw [binaryField_card, Fintype.card_fin]
      _ = 16 := by norm_num
  have hcontra : 256 ≤ 16 := by
    simpa [quarticFunctionRing_card, hcoeff] using hle
  norm_num at hcontra

/-- Lemma 10.144.2: there exists a tower `R → S → T` of standard étale maps whose composite
`R → T` is not standard étale. -/
theorem exists_standardEtale_tower_with_nonstandardEtale_composite :
    ∃ (R : Type u) (S : Type v) (T : Type w)
      (_ : CommRing R) (_ : CommRing S) (_ : CommRing T)
      (_ : Algebra R S) (_ : Algebra S T) (_ : Algebra R T) (_ : IsScalarTower R S T),
        IsStandardEtale R S ∧ IsStandardEtale S T ∧ ¬ IsStandardEtale R T := by
  letI : Algebra BinaryField QuarticField := inferInstance
  letI : Algebra QuarticField LiftedQuarticFunctionRing := inferInstance
  letI : Algebra BinaryField LiftedQuarticFunctionRing := inferInstance
  letI : IsScalarTower BinaryField QuarticField LiftedQuarticFunctionRing := inferInstance
  refine ⟨BinaryField, QuarticField, LiftedQuarticFunctionRing,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  have hRS : IsStandardEtale BinaryField QuarticField :=
    finite_separable_field_standard_etale BinaryField QuarticField
  have hSTBase : IsStandardEtale QuarticField QuarticFunctionRing :=
    quarticFunctionRing_standard_etale
  letI : IsStandardEtale QuarticField QuarticFunctionRing := hSTBase
  have hST : IsStandardEtale QuarticField LiftedQuarticFunctionRing :=
    IsStandardEtale.of_equiv
      (ULift.algEquiv (R := QuarticField) (A := QuarticFunctionRing)).symm
  have hnot : ¬ IsStandardEtale BinaryField LiftedQuarticFunctionRing := by
    intro hT
    letI : IsStandardEtale BinaryField LiftedQuarticFunctionRing := hT
    have hbase : IsStandardEtale BinaryField QuarticFunctionRing :=
      IsStandardEtale.of_equiv
        (ULift.algEquiv (R := BinaryField) (A := QuarticFunctionRing))
    exact quarticFunctionRing_not_standard_etale_over_binaryField hbase
  -- Package the source-faithful tower `𝔽₂ → 𝔽₄ → ULift (𝔽₄^4)`.
  exact ⟨hRS, hST, hnot⟩

end Algebra

/-! ### Lemma_10_144_3 (from Chap10) -/
universe u v

open Polynomial
open scoped Polynomial

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
* source-facing layer: the present existence statement for an étale neighborhood realizing a
  prescribed finite separable extension of `κ(p)`;
* core/canonical owner: the `κ(p)`-algebra structure on `p'.ResidueField` induced by
  `[p'.LiesOver p]`, so the residue-field comparison should live as an algebra equivalence
  `p'.ResidueField ≃ₐ[p.ResidueField] L`;
* upstream existence owner: `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`
  as recalled in Lemma `10.143.13`;
* bridge/view data: `Field.powerBasisOfFiniteOfSeparable p.ResidueField L`, which packages the
  primitive-element reduction to one separable polynomial.

The public API stays source-facing. The polynomial presentation and the compatibility of the
residue-field comparison with structure maps are proof data derived from the owner abstractions
above, not primitive outputs of the theorem statement. Accordingly, the theorem should end with
the existence of a `κ(p)`-algebra equivalence itself, not a second equality restating the
`AlgEquiv` scalar-compatibility field.
-/

-- Proof sketch: use the canonical power basis of the finite separable field extension `L / κ(p)`
-- to view `L` as generated by one element with separable minimal polynomial `f`. Lift `f` to a
-- polynomial over `R`, apply the canonical étale lifting theorem from Lemma `10.143.13`, and
-- upgrade the resulting bijective residue-field map to the canonical `κ(p)`-algebra equivalence
-- with `L` through the power-basis identification. The compatibility with the structure maps is
-- then part of the `AlgEquiv` owner, not an extra primitive output.
/-- Helper for Lemma 10.144.3: a monic polynomial over the residue field of a local ring lifts to
a monic polynomial over the local ring. -/
lemma exists_monic_lift_of_residueField
    (A : Type u) [CommRing A] [IsLocalRing A]
    (g : (IsLocalRing.ResidueField A)[X]) (hg : g.Monic) :
    ∃ f : A[X], f.Monic ∧ f.map (algebraMap A (IsLocalRing.ResidueField A)) = g := by
  -- Lift each coefficient along the surjective residue map, then apply the monic lifting API.
  have hlifts : g ∈ Polynomial.lifts (algebraMap A (IsLocalRing.ResidueField A)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact IsLocalRing.residue_surjective (g.coeff n)
  obtain ⟨f, hfmap, _, hfmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hg
  exact ⟨f, hfmonic, hfmap⟩

/-- Helper for Lemma 10.144.3: after localizing at `p`, the primitive-element construction
produces a standard étale algebra whose residue field realizes the given finite separable
extension of `κ(p)`. -/
theorem exists_standard_etale_over_localizationAtPrime_with_residueField_equiv
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [Algebra.IsSeparable p.ResidueField L] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra (Localization.AtPrime p) S)
      (_ : Algebra.IsStandardEtale (Localization.AtPrime p) S)
      (q : Ideal S) (_ : q.IsPrime)
      (_ : q.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime p))),
      Nonempty (q.ResidueField ≃+* L) := by
  let A := Localization.AtPrime p
  let _ : Algebra A L :=
    RingHom.toAlgebra ((algebraMap p.ResidueField L).comp (algebraMap A p.ResidueField))
  let _ : IsScalarTower A p.ResidueField L := .of_algebraMap_eq' rfl
  let pb : PowerBasis p.ResidueField L := Field.powerBasisOfFiniteOfSeparable p.ResidueField L
  let g : (p.ResidueField)[X] := minpoly p.ResidueField pb.gen
  -- Lift the minimal polynomial from the residue field of `R_p` to a monic polynomial over `R_p`.
  obtain ⟨f, hfmonic, hfmap⟩ :=
    exists_monic_lift_of_residueField A g (minpoly.monic pb.isIntegral_gen)
  have hroot : aeval pb.gen f = 0 := by
    -- The lifted polynomial still vanishes at the primitive generator after mapping to `L`.
    rw [← aeval_map_algebraMap p.ResidueField pb.gen, hfmap, minpoly.aeval]
  have hderiv_unit : IsUnit (aeval pb.gen f.derivative) := by
    -- Separability makes the derivative nonzero at the primitive generator, hence invertible.
    apply isUnit_iff_ne_zero.mpr
    rw [← aeval_map_algebraMap p.ResidueField pb.gen, ← Polynomial.derivative_map, hfmap]
    exact (Algebra.IsSeparable.isSeparable p.ResidueField pb.gen).aeval_derivative_ne_zero
      (minpoly.aeval p.ResidueField pb.gen)
  let P : StandardEtalePair A :=
    ⟨f, hfmonic, f.derivative, ⟨1, 0, 1, by simp⟩⟩
  have hPmap : P.HasMap pb.gen := ⟨hroot, hderiv_unit⟩
  let phi : P.Ring →ₐ[A] L := P.lift pb.gen hPmap
  let q : Ideal P.Ring := RingHom.ker phi.toRingHom
  have hphi_surj : Function.Surjective phi := by
    intro y
    -- Every element of `L` is a polynomial in the primitive generator.
    obtain ⟨h, rfl⟩ := pb.exists_eq_aeval' y
    obtain ⟨hA, hhA⟩ := Polynomial.map_surjective
      (algebraMap A p.ResidueField) IsLocalRing.residue_surjective h
    refine ⟨aeval P.X hA, ?_⟩
    calc
      phi (aeval P.X hA) = aeval (phi P.X) hA := (Polynomial.aeval_algHom_apply phi P.X hA).symm
      _ = aeval pb.gen hA := by rw [P.lift_X _ hPmap]
      _ = aeval pb.gen h := by
        simpa [hhA] using (Polynomial.aeval_map_algebraMap p.ResidueField pb.gen hA).symm
  have hqprime : q.IsPrime := by
    -- The kernel of a map to a field is prime.
    simpa [q] using RingHom.ker_isPrime phi.toRingHom
  have hq_units : q.primeCompl ≤ (IsUnit.submonoid L).comap phi.toRingHom := by
    intro x hx
    -- Outside the kernel, the image is nonzero and hence a unit in the field `L`.
    exact isUnit_iff_ne_zero.mpr <| by
      intro hzero
      exact hx <| show x ∈ q by
        simpa [q] using hzero
  have hkerA :
      RingHom.ker (algebraMap A L) = IsLocalRing.maximalIdeal A := by
    -- The composite `A → κ(p) → L` kills exactly the maximal ideal of `A`.
    ext a
    rw [RingHom.mem_ker, ← IsLocalRing.residue_eq_zero_iff]
    change algebraMap p.ResidueField L (IsLocalRing.residue A a) = 0 ↔
      IsLocalRing.residue A a = 0
    constructor
    · intro h
      exact (FaithfulSMul.algebraMap_injective p.ResidueField L) <| by
        simpa using h
    · intro h
      simp [h]
  have hqover :
      q.LiesOver (IsLocalRing.maximalIdeal A) := by
    -- The prime over `R_p` is the kernel of the field-valued point.
    rw [Ideal.liesOver_iff]
    ext a
    change a ∈ IsLocalRing.maximalIdeal A ↔ algebraMap A P.Ring a ∈ q
    change a ∈ IsLocalRing.maximalIdeal A ↔ phi (algebraMap A P.Ring a) = 0
    constructor
    · intro ha
      have hzero : algebraMap A L a = 0 := by
        rw [← RingHom.mem_ker, hkerA]
        exact ha
      exact (phi.commutes a).trans hzero
    · intro ha
      have hzero : algebraMap A L a = 0 := by
        calc
          algebraMap A L a = phi (algebraMap A P.Ring a) := (phi.commutes a).symm
          _ = 0 := ha
      have hmem : a ∈ RingHom.ker (algebraMap A L) := by
        change algebraMap A L a = 0
        exact hzero
      simpa [hkerA] using hmem
  letI : q.IsPrime := hqprime
  letI : q.LiesOver (IsLocalRing.maximalIdeal A) := hqover
  let psi : q.ResidueField →+* L :=
    Ideal.ResidueField.lift q phi.toRingHom (by exact le_rfl) hq_units
  have hpsi_bij : Function.Bijective psi := by
    refine ⟨RingHom.injective _, ?_⟩
    intro y
    -- Surjectivity comes from the surjectivity of the standard étale point `phi`.
    obtain ⟨x, rfl⟩ := hphi_surj y
    refine ⟨algebraMap P.Ring q.ResidueField x, ?_⟩
    exact Ideal.ResidueField.lift_algebraMap q phi.toRingHom (by exact le_rfl) hq_units x
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance, q, hqprime, hqover, ?_⟩
  exact ⟨RingEquiv.ofBijective psi hpsi_bij⟩

/-- Helper for Lemma 10.144.3: using `g = f.derivative` satisfies the defining Bezout relation
for the standard étale pair attached to `f`. -/
lemma standard_etale_pair_derivative_cond (f : R[X]) :
    ∃ p₁ p₂ n, derivative f * p₁ + f * p₂ = (derivative f) ^ n := by
  -- Choosing `p₁ = 1`, `p₂ = 0`, and `n = 1` makes the standard-étale relation tautological.
  refine ⟨1, 0, 1, ?_⟩
  simp

/-- Helper for Lemma 10.144.3: a simple root of a monic polynomial defines a point of the
associated standard étale algebra. -/
lemma standard_etale_pair_has_map_of_root_and_derivative_unit
    {L : Type v} [Field L] [Algebra R L] (f : R[X]) (hfmonic : f.Monic) (β : L)
    (hroot : aeval β f = 0) (hderiv_unit : IsUnit (aeval β f.derivative)) :
    ∃ P : StandardEtalePair R, ∃ φ : P.Ring →ₐ[R] L, φ P.X = β := by
  -- Package `f` with `g = f.derivative`; then the derivative-unit hypothesis is exactly the
  -- `HasMap` condition needed to define the universal map out of the standard étale algebra.
  let P : StandardEtalePair R :=
    ⟨f, hfmonic, f.derivative, standard_etale_pair_derivative_cond f⟩
  have hunit : IsUnit (aeval β P.g) := by
    simp [P] at hderiv_unit ⊢
    exact hderiv_unit
  have hmap : P.HasMap β := ⟨hroot, hunit⟩
  refine ⟨P, ?_⟩
  refine ⟨P.lift β hmap, ?_⟩
  simpa [P] using P.lift_X β hmap

/-- Helper for Lemma 10.144.3: if `L` is viewed as an extension of `κ(p)`, then the composite
`R → κ(p) → L` has kernel exactly `p`. -/
lemma ker_algebraMap_of_residueField_extension
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L]
    [Algebra R L] [Algebra p.ResidueField L] [IsScalarTower R p.ResidueField L] :
    RingHom.ker (algebraMap R L) = p := by
  -- The residue-field map kills exactly `p`, and the second leg into the field `L` is injective.
  ext x
  constructor
  · intro hx
    have hx' : algebraMap p.ResidueField L (algebraMap R p.ResidueField x) = 0 := by
      simpa [IsScalarTower.algebraMap_eq R p.ResidueField L] using hx
    have hx'' : algebraMap R p.ResidueField x = 0 :=
      (FaithfulSMul.algebraMap_injective p.ResidueField L) (by simpa using hx')
    exact (Ideal.algebraMap_residueField_eq_zero (I := p)).mp hx''
  · intro hx
    have hx' : algebraMap R p.ResidueField x = 0 :=
      (Ideal.algebraMap_residueField_eq_zero (I := p)).mpr hx
    simpa [IsScalarTower.algebraMap_eq R p.ResidueField L] using
      congrArg (algebraMap p.ResidueField L) hx'

/-- Helper for Lemma 10.144.3: the kernel of an `R`-algebra map to a field is a prime lying over
the kernel of the structural map `R → L`. -/
lemma kernel_lies_over_of_field_point
    {S : Type v} [CommRing S] [Algebra R S] {L : Type*} [Field L] [Algebra R L]
    (p : Ideal R) [p.IsPrime] (φ : S →ₐ[R] L) (hker : RingHom.ker (algebraMap R L) = p) :
    let q : Ideal S := RingHom.ker φ.toRingHom
    q.IsPrime ∧ q.LiesOver p := by
  -- The kernel is prime because the codomain is a field, and its contraction is computed by
  -- comparing `φ ∘ algebraMap R S` with `algebraMap R L`.
  let q : Ideal S := RingHom.ker φ.toRingHom
  have hqprime : q.IsPrime := by
    simpa [q] using RingHom.ker_isPrime φ.toRingHom
  have hqover : q.LiesOver p := by
    rw [Ideal.liesOver_iff]
    ext x
    change x ∈ p ↔ algebraMap R S x ∈ q
    change x ∈ p ↔ φ (algebraMap R S x) = 0
    rw [φ.commutes]
    change x ∈ p ↔ x ∈ RingHom.ker (algebraMap R L)
    rw [hker]
  exact ⟨hqprime, hqover⟩

/-- Helper for Lemma 10.144.3: clearing the localization denominators yields a monic polynomial
over `R` whose reduction is the scaled minimal polynomial of the primitive generator. -/
lemma exists_scaled_minpoly_lift
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [Algebra.IsSeparable p.ResidueField L] :
    ∃ pb : PowerBasis p.ResidueField L, ∃ s : p.primeCompl, ∃ f : R[X],
      f.Monic ∧
        f.map (algebraMap R p.ResidueField) =
          (minpoly p.ResidueField pb.gen).scaleRoots (algebraMap R p.ResidueField s.1) := by
  let A := Localization.AtPrime p
  let _ : Algebra A L :=
    RingHom.toAlgebra ((algebraMap p.ResidueField L).comp (algebraMap A p.ResidueField))
  let _ : IsScalarTower A p.ResidueField L := .of_algebraMap_eq' rfl
  let pb : PowerBasis p.ResidueField L := Field.powerBasisOfFiniteOfSeparable p.ResidueField L
  let g : p.ResidueField[X] := minpoly p.ResidueField pb.gen
  -- Lift the minimal polynomial to the localization first, exactly as in the source proof.
  obtain ⟨fA, hfAmonic, hfAmap⟩ :=
    exists_monic_lift_of_residueField A g (minpoly.monic pb.isIntegral_gen)
  let s : p.primeCompl := IsLocalization.commonDenom p.primeCompl fA.support fA.coeff
  have hlead :
      fA.leadingCoeff ∈ (algebraMap R A).range := by
    refine ⟨1, ?_⟩
    rw [hfAmonic.leadingCoeff]
    simp
  have hs_lifts :
      fA.scaleRoots (algebraMap R A s.1) ∈ Polynomial.lifts (algebraMap R A) := by
    -- The only descent input is the common-denominator lift for `scaleRoots`.
    simpa [A, s] using
      (IsLocalization.scaleRoots_commonDenom_mem_lifts
        (R := R) (Rₘ := A) (M := p.primeCompl) fA hlead)
  have hs_monic : (fA.scaleRoots (algebraMap R A s.1)).Monic := by
    simpa using (Polynomial.monic_scaleRoots_iff (p := fA) (s := algebraMap R A s.1)).2 hfAmonic
  obtain ⟨f, hfmapA, _, hfmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hs_lifts hs_monic
  have hfmapκ :
      f.map (algebraMap R p.ResidueField) =
        (fA.scaleRoots (algebraMap R A s.1)).map (algebraMap A p.ResidueField) := by
    -- Map the lifted identity down to the residue field of `R_p`.
    simpa [Polynomial.map_map, IsScalarTower.algebraMap_eq R A p.ResidueField] using
      congrArg (Polynomial.map (algebraMap A p.ResidueField)) hfmapA
  have hscale :
      (fA.scaleRoots (algebraMap R A s.1)).map (algebraMap A p.ResidueField) =
        g.scaleRoots (algebraMap R p.ResidueField s.1) := by
    -- The scaled polynomial commutes with reduction modulo the maximal ideal.
    rw [Polynomial.map_scaleRoots fA (algebraMap R A s.1) (algebraMap A p.ResidueField)]
    · rw [hfAmap]
      simp [g, IsScalarTower.algebraMap_eq R A p.ResidueField]
    · simpa [hfAmonic.leadingCoeff] using
        (show algebraMap A p.ResidueField 1 ≠ 0 by simp)
  refine ⟨pb, s, f, hfmonic, ?_⟩
  simpa [g] using hfmapκ.trans hscale

/-- Helper for Lemma 10.144.3: the denominator-cleared polynomial still vanishes at the scaled
primitive generator, and its reduction is the minimal polynomial of that scaled generator. -/
lemma scaled_generator_root_and_minpoly
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [Algebra R L] [IsScalarTower R p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [Algebra.IsSeparable p.ResidueField L]
    (pb : PowerBasis p.ResidueField L) (s : p.primeCompl) (f : R[X])
    (hfmap : f.map (algebraMap R p.ResidueField) =
      (minpoly p.ResidueField pb.gen).scaleRoots (algebraMap R p.ResidueField s.1)) :
    let β : L := algebraMap R L s.1 * pb.gen
    aeval β f = 0 ∧ f.map (algebraMap R p.ResidueField) = minpoly p.ResidueField β := by
  let β : L := algebraMap R L s.1 * pb.gen
  have hβroot :
      aeval β (f.map (algebraMap R p.ResidueField)) = 0 := by
    -- The scaled-root identity is exactly the `scaleRoots` vanishing lemma on the minpoly.
    rw [hfmap]
    simpa [β, Algebra.smul_def, IsScalarTower.algebraMap_eq R p.ResidueField L] using
      (Polynomial.scaleRoots_aeval_eq_zero
        (A := L) (p := minpoly p.ResidueField pb.gen)
        (a := pb.gen) (r := algebraMap R p.ResidueField s.1)
        (minpoly.aeval p.ResidueField pb.gen))
  have hβ :
      aeval β f = 0 := by
    rw [← Polynomial.aeval_map_algebraMap p.ResidueField β f]
    exact hβroot
  have hs_ne_zero : algebraMap R p.ResidueField s.1 ≠ 0 := by
    simpa [Ideal.algebraMap_residueField_eq_zero] using (show s.1 ∉ p from s.2)
  have hminpoly :
      minpoly p.ResidueField β =
        (minpoly p.ResidueField pb.gen).scaleRoots (algebraMap R p.ResidueField s.1) := by
    -- Scaling an integral primitive generator scales its minimal polynomial by `scaleRoots`.
    simpa [β, Algebra.smul_def, IsScalarTower.algebraMap_eq R p.ResidueField L] using
      (IsIntegrallyClosed.minpoly_smul
        (R := p.ResidueField) (S := L) (r := algebraMap R p.ResidueField s.1)
        hs_ne_zero pb.isIntegral_gen)
  exact ⟨hβ, hfmap.trans hminpoly.symm⟩

/-- Helper for Lemma 10.144.3: separability makes the derivative of the denominator-cleared
polynomial invertible at the scaled primitive generator. -/
lemma scaled_generator_derivative_unit
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [Algebra R L] [IsScalarTower R p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [Algebra.IsSeparable p.ResidueField L]
    (pb : PowerBasis p.ResidueField L) (s : p.primeCompl) (f : R[X])
    (hfmap : f.map (algebraMap R p.ResidueField) =
      (minpoly p.ResidueField pb.gen).scaleRoots (algebraMap R p.ResidueField s.1)) :
    let β : L := algebraMap R L s.1 * pb.gen
    IsUnit (aeval β f.derivative) := by
  let β : L := algebraMap R L s.1 * pb.gen
  obtain ⟨_, hminpoly⟩ :=
    scaled_generator_root_and_minpoly (p := p) (L := L) pb s f hfmap
  -- Rewrite to the scaled generator's minimal polynomial, then apply separability.
  apply isUnit_iff_ne_zero.mpr
  rw [← Polynomial.aeval_map_algebraMap p.ResidueField β f.derivative,
    ← Polynomial.derivative_map, hminpoly]
  exact (Algebra.IsSeparable.isSeparable p.ResidueField β).aeval_derivative_ne_zero
    (minpoly.aeval p.ResidueField β)

/-- Helper for Lemma 10.144.3: the source proof packages denominator clearing, the root relation,
and the derivative-unit condition into one primitive-element witness over `R`. -/
lemma exists_scaled_generator_with_lifted_minpoly
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [Algebra R L] [IsScalarTower R p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [Algebra.IsSeparable p.ResidueField L] :
    ∃ pb : PowerBasis p.ResidueField L, ∃ s : p.primeCompl, ∃ f : R[X],
      f.Monic ∧
        aeval (algebraMap R L s.1 * pb.gen) f = 0 ∧
        IsUnit (aeval (algebraMap R L s.1 * pb.gen) f.derivative) := by
  obtain ⟨pb, s, f, hfmonic, hfmap⟩ :=
    exists_scaled_minpoly_lift (p := p) (L := L)
  obtain ⟨hroot, _hminpoly⟩ :=
    scaled_generator_root_and_minpoly (p := p) (L := L) pb s f hfmap
  have hderiv :
      IsUnit (aeval (algebraMap R L s.1 * pb.gen) f.derivative) :=
    scaled_generator_derivative_unit (p := p) (L := L) pb s f hfmap
  exact ⟨pb, s, f, hfmonic, hroot, hderiv⟩

/-- Lemma 10.144.3: for a prime `p` of a commutative ring `R` and a finite separable field
extension `L / κ(p)`, there exists an étale `R`-algebra `R'` with a prime `p'` lying over `p`
whose residue field is isomorphic to `L` as a `κ(p)`-algebra. -/
theorem exists_etale_liesOver_with_residueField_equiv
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [Algebra.IsSeparable p.ResidueField L] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p)
      , Nonempty (p'.ResidueField ≃ₐ[p.ResidueField] L) :=
  by
  -- Route correction: the denominator-clearing step now follows the source proof directly over
  -- `R`; the only remaining work is the final standard-étale assembly and the residue-field
  -- comparison as a `κ(p)`-algebra equivalence.
  let _ : Algebra R L :=
    RingHom.toAlgebra ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField))
  let _ : IsScalarTower R p.ResidueField L := .of_algebraMap_eq' rfl
  obtain ⟨pb, s, f, hfmonic, hroot, hderiv⟩ :=
    exists_scaled_generator_with_lifted_minpoly (p := p) (L := L)
  let β : L := algebraMap R L s.1 * pb.gen
  -- The source proof now produces the standard étale algebra over `R` and its field-valued point.
  obtain ⟨P, φ, hφX⟩ :=
    standard_etale_pair_has_map_of_root_and_derivative_unit f hfmonic β hroot hderiv
  let q : Ideal P.Ring := RingHom.ker φ.toRingHom
  have hker : RingHom.ker (algebraMap R L) = p :=
    ker_algebraMap_of_residueField_extension (p := p) (L := L)
  obtain ⟨hqprime, hqover⟩ :=
    kernel_lies_over_of_field_point (S := P.Ring) (L := L) p φ hker
  letI : q.IsPrime := hqprime
  letI : q.LiesOver p := hqover
  have hq_units : q.primeCompl ≤ (IsUnit.submonoid L).comap φ := by
    -- Outside the kernel, the image in the field `L` is automatically a unit.
    intro x hx
    exact isUnit_iff_ne_zero.mpr <| by
      intro hzero
      exact hx <| show x ∈ q by
        simpa [q] using hzero
  let θ : q.ResidueField →ₐ[R] L := Ideal.ResidueField.liftₐ q φ (by exact le_rfl) hq_units
  have hθ_comp :
      θ.comp (Ideal.ResidueField.mapₐ p q (Algebra.ofId R P.Ring) (Ideal.over_def q p)) =
        IsScalarTower.toAlgHom R p.ResidueField L := by
    -- The kernel lift agrees with the structural map on the image of `R`, hence on `κ(p)`.
    apply Ideal.ResidueField.algHom_ext
    exact Subsingleton.elim _ _
  let ψ : q.ResidueField →ₐ[p.ResidueField] L :=
    { toRingHom := θ.toRingHom
      commutes' := fun x ↦ by
        -- The compatibility above upgrades the residue-field lift to a `κ(p)`-algebra map.
        change
          θ ((Ideal.ResidueField.mapₐ p q (Algebra.ofId R P.Ring) (Ideal.over_def q p)) x) =
            algebraMap p.ResidueField L x
        have hx := congrArg (fun g => g x) hθ_comp
        simpa [AlgHom.comp_apply] using hx }
  have hs_ne_zero : algebraMap R p.ResidueField s.1 ≠ 0 := by
    -- The chosen denominator was taken from the complement of `p`.
    simpa [Ideal.algebraMap_residueField_eq_zero] using (show s.1 ∉ p from s.2)
  let c : p.ResidueField := algebraMap R p.ResidueField s.1
  have hβ_eq : β = algebraMap p.ResidueField L c * pb.gen := by
    -- Re-express the scaled generator through the `κ(p)`-algebra structure on `L`.
    simp [β, c, IsScalarTower.algebraMap_eq R p.ResidueField L]
  have hbeta_preimage : ∃ z : q.ResidueField, ψ z = β := by
    -- The residue class of the standard coordinate `X` maps to the chosen scaled generator.
    refine ⟨algebraMap P.Ring q.ResidueField P.X, ?_⟩
    calc
      ψ (algebraMap P.Ring q.ResidueField P.X)
          = θ (algebraMap P.Ring q.ResidueField P.X) := rfl
      _ = φ P.X := Ideal.ResidueField.liftₐ_algebraMap q φ (by exact le_rfl) hq_units P.X
      _ = β := hφX
  have hgen_preimage : ∃ z : q.ResidueField, ψ z = pb.gen := by
    -- Divide the scaled generator by the nonzero scalar coming from `s`.
    rcases hbeta_preimage with ⟨zβ, hzβ⟩
    refine ⟨(algebraMap p.ResidueField q.ResidueField c)⁻¹ * zβ, ?_⟩
    have hcL_ne_zero : algebraMap p.ResidueField L c ≠ 0 := by
      intro hc
      have hc' : c = 0 :=
        (FaithfulSMul.algebraMap_injective p.ResidueField L) (by simpa using hc)
      exact hs_ne_zero hc'
    calc
      ψ ((algebraMap p.ResidueField q.ResidueField c)⁻¹ * zβ)
          = algebraMap p.ResidueField L c⁻¹ * ψ zβ := by simp
      _ = algebraMap p.ResidueField L c⁻¹ * β := by rw [hzβ]
      _ = algebraMap p.ResidueField L c⁻¹ * (algebraMap p.ResidueField L c * pb.gen) := by
        rw [hβ_eq]
      _ = (algebraMap p.ResidueField L c⁻¹ * algebraMap p.ResidueField L c) * pb.gen := by
        rw [mul_assoc]
      _ = pb.gen := by simp [hcL_ne_zero]
  let _ : Algebra q.ResidueField L := RingHom.toAlgebra ψ.toRingHom
  let ψq : q.ResidueField →ₐ[q.ResidueField] L :=
    { toRingHom := ψ.toRingHom
      commutes' := fun x ↦ rfl }
  have hpsi_surj : Function.Surjective ψ := by
    intro y
    rcases hgen_preimage with ⟨z, hz⟩
    -- Once the primitive generator is in the image, every polynomial expression in it is too.
    rcases pb.exists_eq_aeval' y with ⟨h, rfl⟩
    refine ⟨aeval z (h.map (algebraMap p.ResidueField q.ResidueField)), ?_⟩
    calc
      ψ (aeval z (h.map (algebraMap p.ResidueField q.ResidueField)))
          = aeval (ψq z) (h.map (algebraMap p.ResidueField q.ResidueField)) := by
            simpa using
              (Polynomial.aeval_algHom_apply ψq z
                (h.map (algebraMap p.ResidueField q.ResidueField))).symm
      _ = aeval (ψ z) (h.map (algebraMap p.ResidueField q.ResidueField)) := rfl
      _ = aeval pb.gen (h.map (algebraMap p.ResidueField q.ResidueField)) := by rw [hz]
      _ = aeval pb.gen h := by
        simpa using (Polynomial.aeval_map_algebraMap p.ResidueField pb.gen h).symm
  have hpsi_bij : Function.Bijective ψ := ⟨RingHom.injective ψ.toRingHom, hpsi_surj⟩
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance, q, hqprime, hqover, ?_⟩
  exact ⟨AlgEquiv.ofBijective ψ hpsi_bij⟩

end

/-! ### Proposition_10_144_4 (from Chap10) -/
namespace Algebra

/- Domain triage:
* primary domain: local étaleness and standard étale neighborhoods of finitely presented
  commutative algebras;
* sampled declarations: `IsEtaleAt`, `IsStandardEtale`, `IsStandardEtale.of_isLocalizationAway`,
  and `IsEtaleAt.exists_isStandardEtale`;
* source-facing layer: the existence of a standard étale basic-open neighborhood of an étale
  point;
* core/canonical layer: `IsEtaleAt.exists_isStandardEtale`;
* bridge/view layer: `StandardEtalePresentation`, which presents `IsStandardEtale` by explicit
  polynomial data.

Primitive-vs-derived split:
* primitive data: a prime `Q : Ideal S` with `[Q.IsPrime]`, finite presentation of `S` over `R`,
  and local étaleness `[IsEtaleAt R Q]`;
* derived API: the witness `f ∉ Q` and the induced `IsStandardEtale R (Localization.Away f)`.
-/

/- Proposition 10.144.4: if `Q ⊂ S` is a prime ideal and `R → S` is étale at `Q`, then there
exists `f ∈ S \ Q` such that the localized `R`-algebra `Localization.Away f` is standard étale
over `R`. -/
recall IsEtaleAt.exists_isStandardEtale

end Algebra

/-! ### Lemma_10_144_5 (from Chap10) -/
universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsStandardEtale R S]

/- Domain-style sampling:
* primary domain: standard étale morphisms and prime lifting after finite flat base change in
  commutative algebra;
* sampled declarations:
  `IsStandardEtale`,
  `StandardEtalePresentation`,
  `Ideal.primesOver`,
  `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`,
  `Polynomial.exists_syntomic_finiteFree_faithfullyFlat_split_extension_of_monic`,
  `Algebra.HasGoingDown.of_flat`;
* best owner abstraction:
  the source algebra is controlled by the canonical owner `IsStandardEtale R S`, while the
  auxiliary extension should expose the existing owner predicates `Module.Finite`,
  `Algebra.FinitePresentation`, and `(algebraMap R S').FaithfullyFlat` directly, while primes over
  `p` should be indexed by the canonical owner fibers `p.asIdeal.primesOver _` instead of by raw
  spectrum points plus equalities;
* source/core/bridge triage:
  this lemma is `source-facing`; the extra localized prime-lifting clause is genuine new source
  content, while finiteness / finite presentation / faithful flatness are derived owner data on
  the chosen extension `S'`;
* primitive-vs-derived split:
  primitive existential data are only the extension ring `S'` and its `R`-algebra structure;
  the canonical algebraic properties above should remain separate owner witnesses, not primitive
  public fields of a new packaged predicate.
-/

-- Proof sketch: choose a standard étale presentation `S ≃ R[x, 1 / g]/(f)` with `f` monic.
-- Apply Lemma `10.136.14` to `f` to obtain a finite free faithfully flat extension `R → S'`
-- splitting `f`; this gives finite presentation and the canonical faithfully flat owner, from
-- which spectrum-surjectivity is derived by
-- `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`. For primes
-- `q ⊂ S` and `q' ⊂ S'` in the owner fibers over the same `p ⊂ R`, pick a root of the split polynomial over
-- `κ(q')` that lies on the irreducible factor corresponding to `q` and does not vanish on the
-- chosen denominator, yielding `g' ∉ q'` and an `R`-algebra map `S → S'_{g'}` whose inverse image
-- of the localized prime over `q'` is `q`.
/-- Lemma 10.144.5: for a standard étale morphism `R → S`, there exists an `R`-algebra `S'` that
is finite, finitely presented, and faithfully flat over `R`, hence has surjective spectrum map,
and such that for every prime `p` of `R`, every prime `q` of `S` over `p`, and every prime `q'`
of `S'` over `p`, one can localize `S'` away from an element outside `q'` so that the resulting
map `R → S'_{g'}` factors through an `R`-algebra map `S → S'_{g'}` carrying the localized prime
over `q'` back to `q`. -/
theorem exists_finitePresentation_flat_surjective_extension_lifting_primes :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : (algebraMap R S').FaithfullyFlat),
        ∀ (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S) (q' : p.asIdeal.primesOver S'),
          ∃ (g' : S') (_ : g' ∉ q'.1) (φ : S →ₐ[R] Localization.Away g'),
            Ideal.comap φ.toRingHom (Ideal.map (algebraMap S' (Localization.Away g')) q'.1) =
              q.1 := sorry

end

end Algebra

/-! ### Lemma_10_144_6 (from Chap10) -/
universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Etale R S]

/- Domain-style sampling:
* primary domain: étale morphisms of commutative rings, localized standard étale neighborhoods,
  and finite flat covers with surjective spectrum map;
* sampled declarations:
  `Etale`,
  `IsEtaleAt.exists_isStandardEtale`,
  `exists_finitePresentation_flat_surjective_extension_lifting_primes`,
  `Module.Finite`,
  `Algebra.FinitePresentation`,
  `Module.Flat`;
* best owner abstraction:
  the source map is already controlled by the canonical owner `Etale R S`, and the target
  extension data should stay in the existing owner predicates `Module.Finite`, `Algebra.FinitePresentation`,
  `Module.Flat`, and the canonical spectrum-surjectivity predicate, rather than being repackaged
  into a new local class;
* source/core/bridge triage:
  this lemma is `source-facing`; the local factorization clause is the genuinely new source
  content, while the finiteness / flatness conditions are derived owner data on the chosen
  extension `S'`;
* primitive-vs-derived split:
  primitive existential data are only the extension ring `S'` and its `R`-algebra structure;
  the algebraic properties of `S'` and the spectrum-surjectivity statement belong in separate
  canonical predicates in the theorem output.
-/

-- Proof sketch: use Proposition `10.144.4` and quasi-compactness of `Spec(S)` to cover `Spec(S)`
-- by finitely many basic opens on which `R → S` becomes standard étale. Apply Lemma `10.144.5` to
-- each standard étale localization, then tensor the resulting finite flat covers over `R`. For a
-- prime of the tensor product, pick one factor lying over its image in `Spec(R)` and use the
-- corresponding localized factorization through that standard étale piece.
/-- Lemma 10.144.6: if `R → S` is étale and `Spec(S) → Spec(R)` is surjective, then there exists a
finite, finitely presented, flat `R`-algebra `S'` whose spectrum still surjects onto `Spec(R)`
and such that for every prime `q' ⊂ S'` there is an element `g' ∉ q'` for which the localized map
`R → S'[1 / g']` factors as `R → S → S'[1 / g']`. -/
theorem exists_finitePresentation_flat_surjective_localFactorization_extension
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : Module.Flat R S')
      (_ : Function.Surjective (PrimeSpectrum.comap (algebraMap R S'))),
        ∀ q' : PrimeSpectrum S',
          ∃ (g' : S') (_ : g' ∉ q'.asIdeal), Nonempty (S →ₐ[R] Localization.Away g') := sorry

end

end Algebra
