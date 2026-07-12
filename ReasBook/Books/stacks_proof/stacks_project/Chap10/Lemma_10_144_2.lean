import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 00UC]
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
