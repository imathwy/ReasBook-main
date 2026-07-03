import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_10_27_1 (from Chap10) -/
open Polynomial PrimeSpectrum

local notation "Iquad" => Ideal.span ({X ^ 2 - C (4 : ℤ)} : Set ℤ[X])
local notation "A" => ℤ[X] ⧸ Iquad
local notation "xbar" => ((Ideal.Quotient.mk Iquad) X : A)

/- 
Domain-style sampling pass for Example 10.27.1.

Primary domain: commutative algebra of prime ideals and points of `Spec` for the quotient
`A = ℤ[X] ⧸ (X^2 - 4)`.

Sampled owner declarations:
* `PrimeSpectrum`;
* `PrimeSpectrum.asIdeal`;
* `PrimeSpectrum.range_asIdeal`;
* `Ideal.span`.

Best owner abstraction: the source-facing statement is a classification of points of `Spec(A)`, so
the canonical owner is `PrimeSpectrum A`. The ideal-valued formulation is only the bridge obtained
by unpacking `PrimeSpectrum.asIdeal`; there is no separate upstream owner for the listed ideal
shapes.

Primitive-vs-derived split:
* primitive data: the quotient ring `A` and the explicit ideals `(2, x)`, `(x - 2)`, `(x + 2)`,
  `(q, x - 2)`, `(q, x + 2)`;
* derived API: the point-level classification on `PrimeSpectrum A`, and the ideal-level
  reformulation via `PrimeSpectrum.asIdeal`.
-/

/- Layering for this item:
* source-facing: classify the points of `Spec(ℤ[X] ⧸ (X^2 - 4))`.
* core/canonical owner: `PrimeSpectrum A`.
* bridge/view: the ideal-level reformulation obtained by unpacking `PrimeSpectrum.asIdeal`.
-/

/-- Helper for Example 10.27.1: the lifted contraction of a prime ideal of `ℤ[X]` to `ℤ`
is either `(0)`, `(2)`, or `(q)` for a prime `q > 2`. -/
lemma contraction_to_Z_cases (P : Ideal ℤ[X]) (hP : P.IsPrime) :
    Ideal.comap C P = ⊥ ∨
      Ideal.comap C P = Ideal.span ({(2 : ℤ)} : Set ℤ) ∨
        ∃ q : ℕ, q.Prime ∧ 2 < q ∧ Ideal.comap C P = Ideal.span ({(q : ℤ)} : Set ℤ) := by
  let J : Ideal ℤ := Ideal.comap C P
  letI : P.IsPrime := hP
  have hJ : J.IsPrime := by
    dsimp [J]
    exact Ideal.comap_isPrime C P
  by_cases hbot : J = ⊥
  · exact Or.inl hbot
  · letI : J.IsPrime := hJ
    letI : NeZero J := ⟨hbot⟩
    let q : ℕ := Ideal.absNorm J
    have hq_prime : q.Prime := by
      simpa [q, Ideal.under_def] using Nat.absNorm_under_prime J
    have hJ_span : J = Ideal.span ({(q : ℤ)} : Set ℤ) := by
      -- The absolute norm identifies every nonzero prime ideal of `ℤ` with the span of a prime.
      simpa [J, q] using (Int.ideal_span_absNorm_eq_self J).symm
    by_cases hq_two : q = 2
    · right
      left
      simpa [hq_two] using hJ_span
    · right
      right
      refine ⟨q, hq_prime, ?_, hJ_span⟩
      -- A prime natural number different from `2` is necessarily strictly larger than `2`.
      exact lt_of_le_of_ne hq_prime.two_le fun hq_le => hq_two hq_le.symm

/-- Helper for Example 10.27.1: the quotient by an ideal isomorphic to a domain is prime. -/
lemma isPrime_of_quotient_ringEquiv_domain (I : Ideal A) {B : Type*} [CommRing B]
    [IsDomain B] (e : A ⧸ I ≃+* B) : I.IsPrime := by
  -- The quotient-domain criterion converts the constructed quotient equivalence into primeness.
  have hdomain : IsDomain (A ⧸ I) := by
    exact e.toMulEquiv.isDomain _
  exact (Ideal.Quotient.isDomain_iff_prime (I := I)).1 hdomain

/-- Helper for Example 10.27.1: `(X^2 - 4)` is contained in `(X - 2)`. -/
lemma iquad_le_span_X_sub_two :
    Iquad ≤ Ideal.span ({X - C (2 : ℤ)} : Set ℤ[X]) := by
  refine Ideal.span_le.mpr ?_
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  -- Factor the quadratic and keep the visible factor `X - 2`.
  have hC2sq : (C (2 : ℤ)) ^ 2 = C (4 : ℤ) := by
    norm_num
  exact Ideal.mem_span_singleton.mpr ⟨X + C (2 : ℤ), by
    calc
      X ^ 2 - C (4 : ℤ) = X ^ 2 - (C (2 : ℤ)) ^ 2 := by rw [hC2sq]
      _ = (X - C (2 : ℤ)) * (X + C (2 : ℤ)) := by ring⟩

/-- Helper for Example 10.27.1: `(X^2 - 4)` is contained in `(X + 2)`. -/
lemma iquad_le_span_X_add_two :
    Iquad ≤ Ideal.span ({X + C (2 : ℤ)} : Set ℤ[X]) := by
  refine Ideal.span_le.mpr ?_
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  -- The same factorization also shows divisibility by `X + 2`.
  have hC2sq : (C (2 : ℤ)) ^ 2 = C (4 : ℤ) := by
    norm_num
  exact Ideal.mem_span_singleton.mpr ⟨X - C (2 : ℤ), by
    calc
      X ^ 2 - C (4 : ℤ) = X ^ 2 - (C (2 : ℤ)) ^ 2 := by rw [hC2sq]
      _ = (X + C (2 : ℤ)) * (X - C (2 : ℤ)) := by ring⟩

/-- Helper for Example 10.27.1: `(X^2 - 4)` is contained in `(2, X)`. -/
lemma iquad_le_span_two_X :
    Iquad ≤ Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X]) := by
  refine Ideal.span_le.mpr ?_
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  have hX_mem : X ∈ Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X]) := by
    exact Ideal.subset_span (by simp)
  have hC4_mem : C (4 : ℤ) ∈ Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X]) := by
    have hC2_mem : (2 : ℤ[X]) ∈ Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X]) := by
      exact Ideal.subset_span (by simp)
    have hTwoMul : C (4 : ℤ) = (2 : ℤ[X]) * (2 : ℤ[X]) := by
      norm_num
    rw [hTwoMul]
    exact Ideal.mul_mem_left _ _ hC2_mem
  -- Membership is preserved under subtraction inside the ideal.
  have hXsq_mem : X * X ∈ Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X]) := by
    exact Ideal.mul_mem_left _ X hX_mem
  exact (Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X])).sub_mem (by simpa [pow_two] using hXsq_mem) hC4_mem

/-- Helper for Example 10.27.1: a prime over `(X^2 - 4)` contains one of the two linear factors. -/
lemma prime_contains_X_sub_two_or_X_add_two (P : Ideal ℤ[X]) (hP : P.IsPrime) (hIquad : Iquad ≤ P) :
    X - C (2 : ℤ) ∈ P ∨ X + C (2 : ℤ) ∈ P := by
  -- Route correction: the source proof first factors `X^2 - 4` and only then splits by primality.
  have hquad_mem : X ^ 2 - C (4 : ℤ) ∈ P := by
    exact hIquad (Ideal.subset_span (by simp))
  have hfactor :
      X ^ 2 - C (4 : ℤ) = (X - C (2 : ℤ)) * (X + C (2 : ℤ)) := by
    have hC2sq : (C (2 : ℤ)) ^ 2 = C (4 : ℤ) := by
      norm_num
    calc
      X ^ 2 - C (4 : ℤ) = X ^ 2 - (C (2 : ℤ)) ^ 2 := by rw [hC2sq]
      _ = (X - C (2 : ℤ)) * (X + C (2 : ℤ)) := by ring
  -- Primality now forces one of the two factors to lie in `P`.
  rw [hfactor] at hquad_mem
  exact hP.mem_or_mem hquad_mem

/-- Helper for Example 10.27.1: over a field, a prime ideal containing `X - a` is exactly `(X - a)`. -/
lemma prime_eq_span_X_sub_C_over_field {K : Type*} [Field K] {a : K} (J : Ideal K[X]) (hJ : J.IsPrime)
    (ha : X - C a ∈ J) :
    J = Ideal.span ({X - C a} : Set K[X]) := by
  letI : J.IsPrime := hJ
  let φ : K[X] →+* K := Polynomial.evalRingHom a
  have hspan_le : Ideal.span ({X - C a} : Set K[X]) ≤ J := by
    refine Ideal.span_le.mpr ?_
    intro f hf
    rcases Set.mem_singleton_iff.mp hf with rfl
    exact ha
  have hker_le : RingHom.ker φ ≤ J := by
    simpa [φ, Polynomial.ker_evalRingHom] using hspan_le
  have hmap_prime : (Ideal.map φ J).IsPrime := by
    exact Ideal.map_isPrime_of_surjective (f := φ) (Polynomial.eval_surjective a) hker_le
  have hmap_bot : Ideal.map φ J = ⊥ := by
    rcases Ideal.eq_bot_or_top (Ideal.map φ J) with hbot | htop
    · exact hbot
    · exact (hmap_prime.ne_top htop).elim
  -- Mapping to the field kills the image ideal, so the original ideal is the evaluation kernel.
  calc
    J = J ⊔ RingHom.ker φ := by
      exact (sup_eq_left.mpr hker_le).symm
    _ = Ideal.comap φ (Ideal.map φ J) := by
      rw [Ideal.comap_map_of_surjective' (f := φ) (Polynomial.eval_surjective a) J]
    _ = RingHom.ker φ := by rw [hmap_bot, ← RingHom.ker_eq_comap_bot]
    _ = Ideal.span ({X - C a} : Set K[X]) := by
      simpa [φ] using Polynomial.ker_evalRingHom a

/-- Helper for Example 10.27.1: in the zero-contraction fiber, evaluation at the visible root
forces the lifted prime to equal the corresponding linear ideal. -/
lemma eq_span_X_sub_C_of_comap_bot_of_mem (a : ℤ) (P : Ideal ℤ[X]) (_hP : P.IsPrime)
    (hcomap : Ideal.comap C P = ⊥) (ha : X - C a ∈ P) :
    P = Ideal.span ({X - C a} : Set ℤ[X]) := by
  let φ : ℤ[X] →+* ℤ := Polynomial.evalRingHom a
  have hspan_le : Ideal.span ({X - C a} : Set ℤ[X]) ≤ P := by
    refine Ideal.span_le.mpr ?_
    intro f hf
    rcases Set.mem_singleton_iff.mp hf with rfl
    exact ha
  have hker_le : RingHom.ker φ ≤ P := by
    simpa [φ, Polynomial.ker_evalRingHom] using hspan_le
  have hmap_bot : Ideal.map φ P = ⊥ := by
    apply le_antisymm
    · intro z hz
      rcases (Ideal.mem_map_iff_of_surjective φ (Polynomial.eval_surjective a)).1 hz with
        ⟨f, hf, hfz⟩
      have hdiff_ker : C z - f ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker]
        rw [show φ (C z - f) = z - φ f by simp [φ], hfz, sub_self]
      have hCz_mem : C z ∈ P := by
        -- The evaluation witness differs from the constant polynomial `C z` by an element of the kernel.
        have hdiff_mem : C z - f ∈ P := hker_le hdiff_ker
        simpa [sub_eq_add_neg, add_assoc] using P.add_mem hdiff_mem hf
      have hz_comap : z ∈ Ideal.comap C P := hCz_mem
      simpa [hcomap] using hz_comap
    · exact bot_le
  -- Since the evaluation image ideal is zero, `P` is exactly the evaluation kernel.
  calc
    P = P ⊔ RingHom.ker φ := by
      exact (sup_eq_left.mpr hker_le).symm
    _ = Ideal.comap φ (Ideal.map φ P) := by
      rw [Ideal.comap_map_of_surjective' (f := φ) (Polynomial.eval_surjective a) P]
    _ = RingHom.ker φ := by rw [hmap_bot, ← RingHom.ker_eq_comap_bot]
    _ = Ideal.span ({X - C a} : Set ℤ[X]) := by
      simpa [φ] using Polynomial.ker_evalRingHom a

/-- Helper for Example 10.27.1: in the zero-contraction fiber, the lifted prime is one of the
two linear ideals coming from the factorization of `X^2 - 4`. -/
lemma generic_prime_eq_span_linear (P : Ideal ℤ[X]) (hP : P.IsPrime) (hIquad : Iquad ≤ P)
    (hcomap : Ideal.comap C P = ⊥) :
    P = Ideal.span ({X - C (2 : ℤ)} : Set ℤ[X]) ∨
      P = Ideal.span ({X + C (2 : ℤ)} : Set ℤ[X]) := by
  rcases prime_contains_X_sub_two_or_X_add_two P hP hIquad with hminus | hplus
  · -- The `X - 2` branch closes by evaluation at `2`.
    left
    exact eq_span_X_sub_C_of_comap_bot_of_mem 2 P hP hcomap hminus
  · -- Rewrite `X + 2` as `X - (-2)` and evaluate at `-2`.
    right
    have hplus' : X - C (-2 : ℤ) ∈ P := by
      simpa [sub_eq_add_neg] using hplus
    simpa [sub_eq_add_neg] using eq_span_X_sub_C_of_comap_bot_of_mem (-2) P hP hcomap hplus'

/-- Helper for Example 10.27.1: quotienting `A = ℤ[X] / (X^2 - 4)` by the image of a larger ideal
is canonically the same as quotienting `ℤ[X]` by that larger ideal. -/
noncomputable def quotient_by_mapped_ideal_equiv_of_le (J : Ideal ℤ[X]) (hJ : Iquad ≤ J) :
    A ⧸ Ideal.map (Ideal.Quotient.mk Iquad) J ≃+* ℤ[X] ⧸ J :=
  DoubleQuot.quotQuotEquivQuotOfLE hJ

/-- Helper for Example 10.27.1: the image of `(X - 2)` in `A` is the ideal `(xbar - 2)`. -/
lemma map_span_X_sub_two :
    Ideal.map (Ideal.Quotient.mk Iquad) (Ideal.span ({X - C (2 : ℤ)} : Set ℤ[X])) =
      Ideal.span ({xbar - 2} : Set A) := by
  -- Mapping a span is the span of the mapped generators, and `X` becomes `xbar`.
  rw [Ideal.map_span, Set.image_singleton]
  congr 1

/-- Helper for Example 10.27.1: the image of `(X + 2)` in `A` is the ideal `(xbar + 2)`. -/
lemma map_span_X_add_two :
    Ideal.map (Ideal.Quotient.mk Iquad) (Ideal.span ({X + C (2 : ℤ)} : Set ℤ[X])) =
      Ideal.span ({xbar + 2} : Set A) := by
  -- The quotient map preserves addition and sends `X` to `xbar`.
  rw [Ideal.map_span, Set.image_singleton]
  congr 1

/-- Helper for Example 10.27.1: the image of `(2, X)` in `A` is the ideal `(2, xbar)`. -/
lemma map_span_two_X :
    Ideal.map (Ideal.Quotient.mk Iquad) (Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X])) =
      Ideal.span ({(2 : A), xbar} : Set A) := by
  -- The two generators map to `2` and `xbar` respectively.
  rw [Ideal.map_span]
  congr 1
  ext y
  constructor
  · intro hy
    simpa [eq_comm, or_left_comm, or_assoc] using hy
  · intro hy
    simpa [eq_comm, or_left_comm, or_assoc] using hy

/-- Helper for Example 10.27.1: the image of `(q, X - 2)` in `A` is the ideal `(q, xbar - 2)`. -/
lemma map_span_q_X_sub_two (q : ℕ) :
    Ideal.map (Ideal.Quotient.mk Iquad)
        (Ideal.span ({(q : ℤ[X]), X - C (2 : ℤ)} : Set ℤ[X])) =
      Ideal.span ({(q : A), xbar - 2} : Set A) := by
  -- The quotient map preserves both the scalar generator `q` and the linear factor.
  rw [Ideal.map_span]
  congr 1
  ext y
  constructor
  · intro hy
    simpa [eq_comm, or_left_comm, or_assoc] using hy
  · intro hy
    simpa [eq_comm, or_left_comm, or_assoc] using hy

/-- Helper for Example 10.27.1: the image of `(q, X + 2)` in `A` is the ideal `(q, xbar + 2)`. -/
lemma map_span_q_X_add_two (q : ℕ) :
    Ideal.map (Ideal.Quotient.mk Iquad)
        (Ideal.span ({(q : ℤ[X]), X + C (2 : ℤ)} : Set ℤ[X])) =
      Ideal.span ({(q : A), xbar + 2} : Set A) := by
  -- The same computation identifies the image of the `X + 2` branch.
  rw [Ideal.map_span]
  congr 1
  ext y
  constructor
  · intro hy
    simpa [eq_comm, or_left_comm, or_assoc] using hy
  · intro hy
    simpa [eq_comm, or_left_comm, or_assoc] using hy

/-- Helper for Example 10.27.1: the ideal `(x - 2)` of `A` is prime. -/
lemma span_xbar_sub_two_isPrime :
    (Ideal.span ({xbar - 2} : Set A)).IsPrime := by
  -- First transport the quotient back to the linear ideal `(X - 2)` in `ℤ[X]`.
  let e : A ⧸ Ideal.span ({xbar - 2} : Set A) ≃+* ℤ :=
    (Ideal.quotEquivOfEq map_span_X_sub_two.symm).trans <|
      (quotient_by_mapped_ideal_equiv_of_le
        (Ideal.span ({X - C (2 : ℤ)} : Set ℤ[X])) iquad_le_span_X_sub_two).trans <|
        Polynomial.quotientSpanXSubCAlgEquiv (2 : ℤ)
  -- The target quotient is isomorphic to the domain `ℤ`.
  exact isPrime_of_quotient_ringEquiv_domain (Ideal.span ({xbar - 2} : Set A)) e

/-- Helper for Example 10.27.1: the ideal `(x + 2)` of `A` is prime. -/
lemma span_xbar_add_two_isPrime :
    (Ideal.span ({xbar + 2} : Set A)).IsPrime := by
  have hlinear :
      Ideal.span ({X + C (2 : ℤ)} : Set ℤ[X]) =
        Ideal.span ({X - C (-2 : ℤ)} : Set ℤ[X]) := by
    -- Rewriting `X + 2` as `X - (-2)` aligns the quotient with evaluation at `-2`.
    congr 1
    ext f
    simp
  -- Transport the quotient to the `X - (-2)` presentation and evaluate at `-2`.
  let e : A ⧸ Ideal.span ({xbar + 2} : Set A) ≃+* ℤ :=
    (Ideal.quotEquivOfEq map_span_X_add_two.symm).trans <|
      (quotient_by_mapped_ideal_equiv_of_le
        (Ideal.span ({X + C (2 : ℤ)} : Set ℤ[X])) iquad_le_span_X_add_two).trans <|
        (Ideal.quotEquivOfEq hlinear).trans <|
          Polynomial.quotientSpanXSubCAlgEquiv (-2 : ℤ)
  -- This quotient is again isomorphic to the domain `ℤ`.
  exact isPrime_of_quotient_ringEquiv_domain (Ideal.span ({xbar + 2} : Set A)) e

/-- Helper for Example 10.27.1: the ideal `(2, x)` of `A` is prime. -/
lemma span_two_xbar_isPrime :
    (Ideal.span ({(2 : A), xbar} : Set A)).IsPrime := by
  have hspan :
      Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X]) =
        Ideal.span ({C (2 : ℤ), X - C (0 : ℤ)} : Set ℤ[X]) := by
    -- This is the same two-generator ideal, written in the form used by the quotient API.
    congr 1
    ext f
    simp
  -- First move from `A` back to the quotient by `(2, X)` in `ℤ[X]`.
  let e : A ⧸ Ideal.span ({(2 : A), xbar} : Set A) ≃+* ZMod 2 :=
    (Ideal.quotEquivOfEq map_span_two_X.symm).trans <|
      (quotient_by_mapped_ideal_equiv_of_le
        (Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X])) iquad_le_span_two_X).trans <|
        (Ideal.quotEquivOfEq hspan).trans <|
          (Polynomial.quotientSpanCXSubCAlgEquiv (2 : ℤ) (0 : ℤ)).toRingEquiv.trans <|
            Int.quotientSpanNatEquivZMod 2
  -- The quotient is isomorphic to the field `ZMod 2`, hence the ideal is prime.
  exact isPrime_of_quotient_ringEquiv_domain (Ideal.span ({(2 : A), xbar} : Set A)) e

/-- Helper for Example 10.27.1: for an odd prime `q`, the ideal `(q, x - 2)` of `A` is prime. -/
lemma span_q_xbar_sub_two_isPrime (q : ℕ) (hq : q.Prime) :
    (Ideal.span ({(q : A), xbar - 2} : Set A)).IsPrime := by
  have hspan :
      Ideal.span ({(q : ℤ[X]), X - C (2 : ℤ)} : Set ℤ[X]) =
        Ideal.span ({C (q : ℤ), X - C (2 : ℤ)} : Set ℤ[X]) := by
    -- This rewrites the scalar generator into the canonical `C q` form.
    congr 1
  have hle :
      Iquad ≤ Ideal.span ({(q : ℤ[X]), X - C (2 : ℤ)} : Set ℤ[X]) := by
    -- The quadratic ideal already lies in the linear factor ideal, hence in the larger two-generator ideal.
    refine le_trans iquad_le_span_X_sub_two ?_
    refine Ideal.span_le.mpr ?_
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    exact Ideal.subset_span (by simp)
  -- Pull the quotient back to `(q, X - 2)` and then evaluate at `2`.
  let e : A ⧸ Ideal.span ({(q : A), xbar - 2} : Set A) ≃+* ZMod q :=
    (Ideal.quotEquivOfEq (map_span_q_X_sub_two q).symm).trans <|
      (quotient_by_mapped_ideal_equiv_of_le
        (Ideal.span ({(q : ℤ[X]), X - C (2 : ℤ)} : Set ℤ[X]))
        hle).trans <|
        (Ideal.quotEquivOfEq hspan).trans <|
          (Polynomial.quotientSpanCXSubCAlgEquiv (q : ℤ) (2 : ℤ)).toRingEquiv.trans <|
            Int.quotientSpanNatEquivZMod q
  -- Since `q` is prime, `ZMod q` is a domain.
  letI : Fact q.Prime := ⟨hq⟩
  exact isPrime_of_quotient_ringEquiv_domain (Ideal.span ({(q : A), xbar - 2} : Set A)) e

/-- Helper for Example 10.27.1: for an odd prime `q`, the ideal `(q, x + 2)` of `A` is prime. -/
lemma span_q_xbar_add_two_isPrime (q : ℕ) (hq : q.Prime) :
    (Ideal.span ({(q : A), xbar + 2} : Set A)).IsPrime := by
  have hlinear :
      Ideal.span ({(q : ℤ[X]), X + C (2 : ℤ)} : Set ℤ[X]) =
        Ideal.span ({(q : ℤ[X]), X - C (-2 : ℤ)} : Set ℤ[X]) := by
    -- Rewriting the second generator aligns the quotient with evaluation at `-2`.
    congr 1
    ext f
    simp [sub_eq_add_neg]
  have hspan :
      Ideal.span ({(q : ℤ[X]), X - C (-2 : ℤ)} : Set ℤ[X]) =
        Ideal.span ({C (q : ℤ), X - C (-2 : ℤ)} : Set ℤ[X]) := by
    -- This again matches the exact source ideal required by `quotientSpanCXSubCAlgEquiv`.
    congr 1
  have hle :
      Iquad ≤ Ideal.span ({(q : ℤ[X]), X + C (2 : ℤ)} : Set ℤ[X]) := by
    -- The same containment argument works for the `X + 2` branch.
    refine le_trans iquad_le_span_X_add_two ?_
    refine Ideal.span_le.mpr ?_
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    exact Ideal.subset_span (by simp)
  -- Move to the pulled-back ideal and then evaluate at `-2`.
  let e : A ⧸ Ideal.span ({(q : A), xbar + 2} : Set A) ≃+* ZMod q :=
    (Ideal.quotEquivOfEq (map_span_q_X_add_two q).symm).trans <|
      (quotient_by_mapped_ideal_equiv_of_le
        (Ideal.span ({(q : ℤ[X]), X + C (2 : ℤ)} : Set ℤ[X]))
        hle).trans <|
        (Ideal.quotEquivOfEq hlinear).trans <|
          (Ideal.quotEquivOfEq hspan).trans <|
            (Polynomial.quotientSpanCXSubCAlgEquiv (q : ℤ) (-2 : ℤ)).toRingEquiv.trans <|
              Int.quotientSpanNatEquivZMod q
  -- Since `q` is prime, `ZMod q` is again a domain.
  letI : Fact q.Prime := ⟨hq⟩
  exact isPrime_of_quotient_ringEquiv_domain (Ideal.span ({(q : A), xbar + 2} : Set A)) e

/-- Helper for Example 10.27.1: the upstairs ideal `(2, X)` is maximal because its quotient is
`ZMod 2`. -/
lemma span_two_X_isMaximal :
    (Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X])).IsMaximal := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hspan :
      Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X]) =
        Ideal.span ({C (2 : ℤ), X - C (0 : ℤ)} : Set ℤ[X]) := by
    -- This matches the explicit quotient presentation used by `quotientSpanCXSubCAlgEquiv`.
    congr 1
    ext f
    simp
  -- The quotient identifies with `ZMod 2`, hence the ideal is maximal.
  let e : ℤ[X] ⧸ Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X]) ≃+* ZMod 2 :=
    (Ideal.quotEquivOfEq hspan).trans <|
      (Polynomial.quotientSpanCXSubCAlgEquiv (2 : ℤ) (0 : ℤ)).toRingEquiv.trans <|
        Int.quotientSpanNatEquivZMod 2
  exact Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))

/-- Helper for Example 10.27.1: for a prime `q`, the upstairs ideal `(q, X - 2)` is maximal
because its quotient is `ZMod q`. -/
lemma span_q_X_sub_two_isMaximal (q : ℕ) (hq : q.Prime) :
    (Ideal.span ({(q : ℤ[X]), X - C (2 : ℤ)} : Set ℤ[X])).IsMaximal := by
  letI : Fact q.Prime := ⟨hq⟩
  have hspan :
      Ideal.span ({(q : ℤ[X]), X - C (2 : ℤ)} : Set ℤ[X]) =
        Ideal.span ({C (q : ℤ), X - C (2 : ℤ)} : Set ℤ[X]) := by
    -- Rewriting the scalar generator puts the quotient in the canonical form.
    congr 1
  -- The quotient by this two-generator ideal is the finite field `ZMod q`.
  let e : ℤ[X] ⧸ Ideal.span ({(q : ℤ[X]), X - C (2 : ℤ)} : Set ℤ[X]) ≃+* ZMod q :=
    (Ideal.quotEquivOfEq hspan).trans <|
      (Polynomial.quotientSpanCXSubCAlgEquiv (q : ℤ) (2 : ℤ)).toRingEquiv.trans <|
        Int.quotientSpanNatEquivZMod q
  exact Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))

/-- Helper for Example 10.27.1: for a prime `q`, the upstairs ideal `(q, X + 2)` is maximal
because its quotient is `ZMod q`. -/
lemma span_q_X_add_two_isMaximal (q : ℕ) (hq : q.Prime) :
    (Ideal.span ({(q : ℤ[X]), X + C (2 : ℤ)} : Set ℤ[X])).IsMaximal := by
  letI : Fact q.Prime := ⟨hq⟩
  have hlinear :
      Ideal.span ({(q : ℤ[X]), X + C (2 : ℤ)} : Set ℤ[X]) =
        Ideal.span ({(q : ℤ[X]), X - C (-2 : ℤ)} : Set ℤ[X]) := by
    -- Rewriting `X + 2` as `X - (-2)` aligns the quotient with evaluation at `-2`.
    congr 1
    ext f
    simp [sub_eq_add_neg]
  have hspan :
      Ideal.span ({(q : ℤ[X]), X - C (-2 : ℤ)} : Set ℤ[X]) =
        Ideal.span ({C (q : ℤ), X - C (-2 : ℤ)} : Set ℤ[X]) := by
    -- This is the canonical two-generator presentation used by the quotient equivalence.
    congr 1
  -- The quotient again identifies with the field `ZMod q`.
  let e : ℤ[X] ⧸ Ideal.span ({(q : ℤ[X]), X + C (2 : ℤ)} : Set ℤ[X]) ≃+* ZMod q :=
    (Ideal.quotEquivOfEq hlinear).trans <|
      (Ideal.quotEquivOfEq hspan).trans <|
        (Polynomial.quotientSpanCXSubCAlgEquiv (q : ℤ) (-2 : ℤ)).toRingEquiv.trans <|
          Int.quotientSpanNatEquivZMod q
  exact Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))

/-- Helper for Example 10.27.1: a prime of `ℤ[X]` over `(2)` and containing `X^2 - 4`
is exactly `(2, X)`. -/
lemma prime_over_two_eq_span_two_X (P : Ideal ℤ[X]) (hP : P.IsPrime) (hIquad : Iquad ≤ P)
    (htwo : Ideal.comap C P = Ideal.span ({(2 : ℤ)} : Set ℤ)) :
    P = Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X]) := by
  -- Route correction: rather than pushing through repeated map/comap transport, use the source
  -- factorization to get `X ∈ P` and then compare with the explicit maximal ideal `(2, X)`.
  have htwo_mem_comap : (2 : ℤ) ∈ Ideal.comap C P := by
    rw [htwo]
    exact Ideal.subset_span (by simp)
  have htwo_mem : (2 : ℤ[X]) ∈ P := by
    simpa [Ideal.mem_comap] using htwo_mem_comap
  have hC4_mem : C (4 : ℤ) ∈ P := by
    -- Since `2 ∈ P`, the constant polynomial `4 = 2 * 2` also lies in `P`.
    have hC4 : C (4 : ℤ) = (2 : ℤ[X]) * (2 : ℤ[X]) := by
      norm_num
    rw [hC4]
    exact Ideal.mul_mem_left _ _ htwo_mem
  have hquad_mem : X ^ 2 - C (4 : ℤ) ∈ P := by
    exact hIquad (Ideal.subset_span (by simp))
  have hXsq_mem : X ^ 2 ∈ P := by
    -- Adding back the constant term turns the quadratic relation into `X^2 ∈ P`.
    simpa [sub_eq_add_neg] using P.add_mem hquad_mem hC4_mem
  have hX_mem : X ∈ P := by
    -- Primality of `P` now forces `X` itself into the ideal.
    have hXX_mem : X * X ∈ P := by
      simpa [pow_two] using hXsq_mem
    exact (hP.mem_or_mem hXX_mem).elim id id
  have hle :
      Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X]) ≤ P := by
    -- Both generators of `(2, X)` lie in `P`.
    refine Ideal.span_le.mpr ?_
    intro f hf
    rcases Set.mem_insert_iff.mp hf with h2 | hX
    · rcases Set.mem_singleton_iff.mp h2 with rfl
      exact htwo_mem
    · rcases Set.mem_singleton_iff.mp hX with rfl
      exact hX_mem
  -- Maximality of `(2, X)` turns the containment into equality.
  exact (Ideal.IsMaximal.eq_of_le span_two_X_isMaximal hP.ne_top hle).symm

/-- Helper for Example 10.27.1: a prime of `ℤ[X]` over `(q)` with `q > 2` and containing
`X^2 - 4` is one of `(q, X - 2)` or `(q, X + 2)`. -/
lemma prime_over_odd_prime_eq_span_q_linear (q : ℕ) (hq : q.Prime) (_hq_gt_two : 2 < q)
    (P : Ideal ℤ[X]) (hP : P.IsPrime) (hIquad : Iquad ≤ P)
    (hqeq : Ideal.comap C P = Ideal.span ({(q : ℤ)} : Set ℤ)) :
    P = Ideal.span ({(q : ℤ[X]), X - C (2 : ℤ)} : Set ℤ[X]) ∨
      P = Ideal.span ({(q : ℤ[X]), X + C (2 : ℤ)} : Set ℤ[X]) := by
  have hq_mem_comap : (q : ℤ) ∈ Ideal.comap C P := by
    rw [hqeq]
    exact Ideal.subset_span (by simp)
  have hq_mem : (q : ℤ[X]) ∈ P := by
    simpa [Ideal.mem_comap] using hq_mem_comap
  -- The source factorization forces one of the two linear factors into the prime ideal.
  rcases prime_contains_X_sub_two_or_X_add_two P hP hIquad with hminus | hplus
  · left
    have hle :
        Ideal.span ({(q : ℤ[X]), X - C (2 : ℤ)} : Set ℤ[X]) ≤ P := by
      -- Both generators of `(q, X - 2)` lie in `P`.
      refine Ideal.span_le.mpr ?_
      intro f hf
      rcases Set.mem_insert_iff.mp hf with hq' | hminus'
      · rcases Set.mem_singleton_iff.mp hq' with rfl
        exact hq_mem
      · rcases Set.mem_singleton_iff.mp hminus' with rfl
        exact hminus
    exact (Ideal.IsMaximal.eq_of_le (span_q_X_sub_two_isMaximal q hq) hP.ne_top hle).symm
  · right
    have hle :
        Ideal.span ({(q : ℤ[X]), X + C (2 : ℤ)} : Set ℤ[X]) ≤ P := by
      -- Both generators of `(q, X + 2)` lie in `P`.
      refine Ideal.span_le.mpr ?_
      intro f hf
      rcases Set.mem_insert_iff.mp hf with hq' | hplus'
      · rcases Set.mem_singleton_iff.mp hq' with rfl
        exact hq_mem
      · rcases Set.mem_singleton_iff.mp hplus' with rfl
        exact hplus
    exact (Ideal.IsMaximal.eq_of_le (span_q_X_add_two_isMaximal q hq) hP.ne_top hle).symm

/-- Example 10.27.1: the points of `Spec(ℤ[X] ⧸ (X^2 - 4))` are exactly `(2, x)`, `(x - 2)`,
`(x + 2)`, or, for some prime `q > 2`, one of `(q, x - 2)` and `(q, x + 2)`. -/
-- Proof sketch: analyze a prime `p` by its contraction to `ℤ`; the contraction is `(0)`, `(2)`,
-- or `(q)` for a prime `q > 2`. Then pass to the corresponding quotient of `ℤ[X]`, factor the
-- image of `X^2 - 4`, and classify the primes lying over each contracted ideal.
theorem prime_spectrum_Zx_mod_xsq_sub_four_cases (p : PrimeSpectrum A) :
    p.asIdeal = Ideal.span ({(2 : A), xbar} : Set A) ∨
      p.asIdeal = Ideal.span ({xbar - 2} : Set A) ∨
        p.asIdeal = Ideal.span ({xbar + 2} : Set A) ∨
          ∃ q : ℕ,
            q.Prime ∧ 2 < q ∧
              (p.asIdeal = Ideal.span ({(q : A), xbar - 2} : Set A) ∨
                p.asIdeal = Ideal.span ({(q : A), xbar + 2} : Set A)) := by
  let π : ℤ[X] →+* A := Ideal.Quotient.mk Iquad
  let P : Ideal ℤ[X] := Ideal.comap π p.asIdeal
  have hP : P.IsPrime := by
    dsimp [P]
    exact Ideal.comap_isPrime π p.asIdeal
  have hIquad : Iquad ≤ P := by
    -- The lifted prime automatically contains the kernel of the quotient map.
    refine Ideal.span_le.mpr ?_
    intro f hf
    rcases Set.mem_singleton_iff.mp hf with rfl
    exact (Ideal.ker_le_comap (K := p.asIdeal) π) <| by
      rw [RingHom.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hp_map : Ideal.map π P = p.asIdeal := by
    -- Mapping the lifted prime back down recovers the original prime ideal of `A`.
    simpa [P] using
      (Ideal.map_comap_of_surjective (f := π) Ideal.Quotient.mk_surjective p.asIdeal)
  rcases contraction_to_Z_cases P hP with hzero | htwo | ⟨q, hq, hq_gt_two, hqeq⟩
  · -- The zero-contraction fiber is now completely closed by the source evaluation argument.
    rcases generic_prime_eq_span_linear P hP hIquad hzero with hPeq | hPeq
    · right
      left
      calc
        p.asIdeal = Ideal.map π P := hp_map.symm
        _ = Ideal.map π (Ideal.span ({X - C (2 : ℤ)} : Set ℤ[X])) := by rw [hPeq]
        _ = Ideal.span ({xbar - 2} : Set A) := map_span_X_sub_two
    · right
      right
      left
      calc
        p.asIdeal = Ideal.map π P := hp_map.symm
        _ = Ideal.map π (Ideal.span ({X + C (2 : ℤ)} : Set ℤ[X])) := by rw [hPeq]
        _ = Ideal.span ({xbar + 2} : Set A) := map_span_X_add_two
  · -- The mod-2 fiber closes upstairs by forcing both generators `2` and `X` into the prime.
    have hPeq : P = Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X]) :=
      prime_over_two_eq_span_two_X P hP hIquad htwo
    left
    calc
      p.asIdeal = Ideal.map π P := hp_map.symm
      _ = Ideal.map π (Ideal.span ({(2 : ℤ[X]), X} : Set ℤ[X])) := by rw [hPeq]
      _ = Ideal.span ({(2 : A), xbar} : Set A) := map_span_two_X
  · -- In the odd-prime fiber, the lifted prime contains one linear factor and the scalar `q`.
    have hPeq :
        P = Ideal.span ({(q : ℤ[X]), X - C (2 : ℤ)} : Set ℤ[X]) ∨
          P = Ideal.span ({(q : ℤ[X]), X + C (2 : ℤ)} : Set ℤ[X]) :=
      prime_over_odd_prime_eq_span_q_linear q hq hq_gt_two P hP hIquad hqeq
    right
    right
    right
    refine ⟨q, hq, hq_gt_two, ?_⟩
    rcases hPeq with hPeq | hPeq
    · left
      calc
        p.asIdeal = Ideal.map π P := hp_map.symm
        _ = Ideal.map π (Ideal.span ({(q : ℤ[X]), X - C (2 : ℤ)} : Set ℤ[X])) := by rw [hPeq]
        _ = Ideal.span ({(q : A), xbar - 2} : Set A) := map_span_q_X_sub_two q
    · right
      calc
        p.asIdeal = Ideal.map π P := hp_map.symm
        _ = Ideal.map π (Ideal.span ({(q : ℤ[X]), X + C (2 : ℤ)} : Set ℤ[X])) := by rw [hPeq]
        _ = Ideal.span ({(q : A), xbar + 2} : Set A) := map_span_q_X_add_two q

/-- Ideal-level reformulation of Example 10.27.1 obtained by unpacking `PrimeSpectrum`. -/
theorem prime_ideal_Zx_mod_xsq_sub_four_cases (I : Ideal A) :
    I.IsPrime ↔
      I = Ideal.span ({(2 : A), xbar} : Set A) ∨
        I = Ideal.span ({xbar - 2} : Set A) ∨
          I = Ideal.span ({xbar + 2} : Set A) ∨
            ∃ q : ℕ,
              q.Prime ∧ 2 < q ∧
                (I = Ideal.span ({(q : A), xbar - 2} : Set A) ∨
                  I = Ideal.span ({(q : A), xbar + 2} : Set A)) := by
  constructor
  · intro hI
    simpa using prime_spectrum_Zx_mod_xsq_sub_four_cases ⟨I, hI⟩
  · intro hI
    rcases hI with hI | hI | hI | ⟨q, hq, _hq_gt_two, hI⟩
    · -- The first explicit ideal is prime because its quotient is `ℤ / (2)`.
      simpa [hI] using span_two_xbar_isPrime
    · -- The second explicit ideal is prime because its quotient is `ℤ`.
      simpa [hI] using span_xbar_sub_two_isPrime
    · -- The third explicit ideal is prime because its quotient is `ℤ`.
      simpa [hI] using span_xbar_add_two_isPrime
    · rcases hI with hI | hI
      · -- For a prime `q`, the quotient by `(q, x - 2)` is `ℤ / (q)`.
        simpa [hI] using span_q_xbar_sub_two_isPrime q hq
      · -- For a prime `q`, the quotient by `(q, x + 2)` is `ℤ / (q)`.
        simpa [hI] using span_q_xbar_add_two_isPrime q hq

/-! ### Example_10_27_2 (from Chap10) -/
open Polynomial PrimeSpectrum

/- 
Layering for this item:
* source-facing: the two atomic Example 10.27.2 clauses for primes over `(q)` and over `(0)`.
* core/canonical owner: `PrimeSpectrum ℤ[X]`, with the contracted prime in `ℤ` analyzed by
  `Ideal.isPrime_int_iff`.
* bridge/view: the private witness predicates and fiber lemmas below, used only to express the
  source-facing nondegenerate fiber clauses without a giant conjunction.
-/

section

variable (p : PrimeSpectrum ℤ[X])

/-- Internal predicate recording that `f` gives the nonzero fiber description over `(q)`. -/
private def IsPrimeFiberGenerator (p : PrimeSpectrum ℤ[X]) (q : ℕ) (f : ℤ[X]) : Prop :=
  Irreducible (f.map (Int.castRingHom (ZMod q))) ∧
    p.asIdeal = Ideal.span ({C (q : ℤ), f} : Set ℤ[X])

/-- Internal predicate recording that `f` generates a nonzero prime over `(0)`. -/
private def IsZeroFiberGenerator (p : PrimeSpectrum ℤ[X]) (f : ℤ[X]) : Prop :=
  0 < f.natDegree ∧ p.asIdeal = Ideal.span ({f} : Set ℤ[X])

/-- Helper for Example 10.27.2: a nonzero prime ideal of `K[X]` over a field is generated by a
monic irreducible polynomial. -/
private lemma prime_ideal_polynomial_over_field_eq_span_monic_irreducible
    {K : Type*} [Field K] (J : Ideal K[X]) (hJ : J.IsPrime) (hJ_ne : J ≠ ⊥) :
    ∃ g : K[X], g.Monic ∧ Irreducible g ∧ J = Ideal.span ({g} : Set K[X]) := by
  let g₀ : K[X] := Submodule.IsPrincipal.generator J
  have hg₀_prime : Prime g₀ := by
    -- A nonzero prime ideal in a PID is generated by a prime element.
    letI : J.IsPrime := hJ
    exact Submodule.IsPrincipal.prime_generator_of_isPrime J hJ_ne
  have hg₀_ne : g₀ ≠ 0 := hg₀_prime.ne_zero
  refine ⟨g₀ * C (leadingCoeff g₀)⁻¹, monic_mul_leadingCoeff_inv hg₀_ne, ?_, ?_⟩
  · -- Over a field, scaling by a unit preserves irreducibility.
    exact (irreducible_mul_leadingCoeff_inv).mpr hg₀_prime.irreducible
  · -- Normalizing the generator does not change the principal ideal.
    have hspan_gen : J = Ideal.span ({g₀} : Set K[X]) := by
      change J = Ideal.span ({Submodule.IsPrincipal.generator J} : Set K[X])
      simpa using (Ideal.span_singleton_generator J).symm
    have hspan_norm : Ideal.span ({g₀ * C (leadingCoeff g₀)⁻¹} : Set K[X]) =
        Ideal.span ({g₀} : Set K[X]) := by
      simpa [mul_comm] using Ideal.span_singleton_mul_left_unit
        (isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hg₀_ne)).isUnit) g₀
    exact hspan_gen.trans hspan_norm.symm

/-- Internal fiber classification over a nonzero prime `(q)` used in Example 10.27.2. -/
-- Proof sketch: pass to the corresponding prime ideal of `(ZMod q)[X]`, use that prime ideals in
-- a polynomial ring over a field are principal away from the zero ideal, and lift a minimal degree
-- generator back to `ℤ[X]`.
private theorem primeFiber_is_span_pair (q : ℕ)
    (hq : q.Prime)
    (hp : (comap C p).asIdeal = Ideal.span ({(q : ℤ)} : Set ℤ))
    (hp_ne : p.asIdeal ≠ Ideal.span ({C (q : ℤ)} : Set ℤ[X])) :
    ∃ f : ℤ[X], Irreducible f ∧ IsPrimeFiberGenerator p q f := by
  letI : Fact q.Prime := ⟨hq⟩
  let φ : ℤ →+* ZMod q := Int.castRingHom (ZMod q)
  let Φ : ℤ[X] →+* (ZMod q)[X] := Polynomial.mapRingHom φ
  have hkernel_eq : RingHom.ker Φ = Ideal.span ({C (q : ℤ)} : Set ℤ[X]) := by
    -- The coefficient map to `ZMod q` kills exactly the constant polynomial `q`.
    rw [Polynomial.ker_mapRingHom, ZMod.ker_intCastRingHom, Ideal.map_span]
    simp
  have hkernel_le : RingHom.ker Φ ≤ p.asIdeal := by
    rw [hkernel_eq]
    -- The contraction hypothesis says `q` lies in the prime ideal.
    refine Ideal.span_singleton_le_iff_mem _ |>.2 ?_
    have hp' : Ideal.comap C p.asIdeal = Ideal.span ({(q : ℤ)} : Set ℤ) := by
      simpa using hp
    have hq_mem : (q : ℤ) ∈ Ideal.comap C p.asIdeal := by
      rw [hp']
      exact Ideal.subset_span (by simp : (q : ℤ) ∈ ({(q : ℤ)} : Set ℤ))
    simpa [Ideal.mem_comap] using hq_mem
  have hmap_prime : (Ideal.map Φ p.asIdeal).IsPrime := by
    -- Surjective maps send primes containing the kernel to prime ideals.
    exact Ideal.map_isPrime_of_surjective (Polynomial.map_surjective _ ZMod.intCast_surjective)
      hkernel_le
  have hmap_ne_bot : Ideal.map Φ p.asIdeal ≠ ⊥ := by
    intro hbot
    have hle : p.asIdeal ≤ RingHom.ker Φ := by
      exact (Ideal.map_eq_bot_iff_le_ker Φ).mp hbot
    have hEq : p.asIdeal = RingHom.ker Φ := le_antisymm hle hkernel_le
    apply hp_ne
    rw [hEq, hkernel_eq]
  obtain ⟨g, hg_monic, hg_irreducible, hg_span⟩ :=
    prime_ideal_polynomial_over_field_eq_span_monic_irreducible (Ideal.map Φ p.asIdeal)
      hmap_prime hmap_ne_bot
  have hg_lifts : g ∈ Polynomial.lifts φ := by
    -- Every polynomial over `ZMod q` lifts coefficientwise from `ℤ`.
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective _ ZMod.intCast_surjective g
  obtain ⟨f, hf_map, -, hf_monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hg_lifts hg_monic
  have hf_map_irreducible : Irreducible (f.map φ) := by
    simpa [hf_map] using hg_irreducible
  have hf_irreducible : Irreducible f := by
    -- Monic irreducibility descends from the irreducible reduction mod `q`.
    haveI : (nilradical ℤ).IsPrime := by
      simpa [nilradical_eq_zero ℤ, Ideal.zero_eq_bot] using
        (inferInstance : (⊥ : Ideal ℤ).IsPrime)
    exact Polynomial.Monic.irreducible_of_irreducible_map_of_isPrime_nilradical
      φ f hf_monic hf_map_irreducible
  have hmap_eq : Ideal.map Φ p.asIdeal = Ideal.map Φ (Ideal.span ({f} : Set ℤ[X])) := by
    -- The mapped ideal is the principal ideal generated by the chosen lift.
    rw [hg_span, Ideal.map_span, Set.image_singleton]
    change Ideal.span ({g} : Set (ZMod q)[X]) = Ideal.span ({f.map φ} : Set (ZMod q)[X])
    rw [hf_map]
  have hcomap_eq := congrArg (Ideal.comap Φ) hmap_eq
  rw [Ideal.comap_map_of_surjective _ (Polynomial.map_surjective _ ZMod.intCast_surjective),
    Ideal.comap_map_of_surjective _ (Polynomial.map_surjective _ ZMod.intCast_surjective)] at hcomap_eq
  have hideal_eq : p.asIdeal = Ideal.span ({f} : Set ℤ[X]) ⊔ RingHom.ker Φ := by
    calc
      p.asIdeal = p.asIdeal ⊔ Ideal.comap Φ ⊥ := by
        symm
        simpa [RingHom.ker_eq_comap_bot] using sup_eq_left.mpr hkernel_le
      _ = Ideal.span ({f} : Set ℤ[X]) ⊔ Ideal.comap Φ ⊥ := hcomap_eq
      _ = Ideal.span ({f} : Set ℤ[X]) ⊔ RingHom.ker Φ := by
        simp [RingHom.ker_eq_comap_bot]
  refine ⟨f, hf_irreducible, ?_⟩
  constructor
  · exact hf_map_irreducible
  · -- Pulling the principal ideal back adds precisely the kernel `(q)`.
    rw [hideal_eq, hkernel_eq, sup_comm, ← Ideal.span_insert]

/-- Helper for Example 10.27.2: if a nonzero polynomial lies in a prime ideal of `ℤ[X]` whose
contraction to `ℤ` is zero, then its primitive part lies in the same ideal. -/
private lemma zero_fiber_primPart_mem_of_mem (I : Ideal ℤ[X]) (hI : I.IsPrime)
    (hcomap : Ideal.comap C I = ⊥) {g : ℤ[X]} (hg : g ∈ I) (hg0 : g ≠ 0) :
    g.primPart ∈ I := by
  -- The content factor cannot lie in `I`, because contraction to `ℤ` is the zero ideal.
  have hcontent_not_mem : C g.content ∉ I := by
    intro hcontent_mem
    have hcontent_zero : g.content = 0 := by
      have hcontent_comap : g.content ∈ Ideal.comap C I := by
        simpa [Ideal.mem_comap] using hcontent_mem
      simpa [hcomap] using hcontent_comap
    exact hg0 ((Polynomial.content_eq_zero_iff.mp hcontent_zero))
  -- Apply primality to the content decomposition `g = C(content g) * primPart g`.
  have hmul_mem : C g.content * g.primPart ∈ I := by
    exact g.eq_C_content_mul_primPart ▸ hg
  exact (hI.mem_or_mem hmul_mem).resolve_left hcontent_not_mem

/-- Internal fiber classification over `(0)` used in Example 10.27.2. -/
-- Proof sketch: extend scalars to `ℚ[X]`, use Gauss's lemma to transfer irreducibility between
-- `ℤ[X]` and `ℚ[X]`, and use that `ℚ[X]` is a PID to obtain a principal generator.
private theorem zeroFiber_is_span_singleton (hp : (comap C p).asIdeal = ⊥) (hp_ne : p.asIdeal ≠ ⊥) :
    ∃ f : ℤ[X], Irreducible f ∧ IsZeroFiberGenerator p f := by
  let I : Ideal ℤ[X] := p.asIdeal
  let M : Submonoid ℤ := nonZeroDivisors ℤ
  let φ : ℤ[X] →+* ℚ[X] := Polynomial.mapRingHom (Int.castRingHom ℚ)
  letI : Algebra ℤ[X] ℚ[X] := φ.toAlgebra
  letI : IsLocalization (M.map C) ℚ[X] := by
    simpa [φ, RingHom.algebraMap_toAlgebra] using (Polynomial.isLocalization M ℚ)
  have hI_prime : I.IsPrime := p.isPrime
  have hI_zero : Ideal.comap C I = ⊥ := by
    simpa [I] using hp
  have hφ_inj : Function.Injective φ := by
    exact Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have hdisj : Disjoint ((M.map C : Submonoid ℤ[X]) : Set ℤ[X]) (I : Set ℤ[X]) := by
    -- A nonzero integer constant cannot lie in `I`, because `I ∩ ℤ = (0)`.
    refine Set.disjoint_left.mpr ?_
    intro z hz hzI
    rcases hz with ⟨m, hm, rfl⟩
    have hm_comap : m ∈ Ideal.comap C I := by
      simpa [Ideal.mem_comap] using hzI
    have hm_zero : m = 0 := by
      simpa [hI_zero] using hm_comap
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hm) hm_zero
  have hmap_prime : (Ideal.map φ I).IsPrime := by
    -- Localizing a prime ideal disjoint from the denominators keeps it prime.
    simpa [φ, RingHom.algebraMap_toAlgebra] using
      (IsLocalization.isPrime_of_isPrime_disjoint (M := M.map C) (S := ℚ[X]) I hI_prime hdisj :
        (Ideal.map (algebraMap ℤ[X] ℚ[X]) I).IsPrime)
  have hcomap_map : Ideal.comap φ (Ideal.map φ I) = I := by
    -- The localization map is injective on this prime ideal because it avoids the denominators.
    simpa [φ, RingHom.algebraMap_toAlgebra] using
      (IsLocalization.comap_map_of_isPrime_disjoint (M := M.map C) (S := ℚ[X]) hI_prime hdisj :
        Ideal.comap (algebraMap ℤ[X] ℚ[X]) (Ideal.map (algebraMap ℤ[X] ℚ[X]) I) = I)
  have hmap_ne_bot : Ideal.map φ I ≠ ⊥ := by
    -- Injectivity of the localization map preserves nontriviality of the ideal.
    intro hbot
    have hle : I ≤ RingHom.ker φ := (Ideal.map_eq_bot_iff_le_ker φ).mp hbot
    have hker : RingHom.ker φ = ⊥ := by
      ext x
      constructor
      · intro hx
        change φ x = 0 at hx
        exact hφ_inj (by simpa using hx)
      · intro hx
        change φ x = 0
        simpa using congrArg φ hx
    apply hp_ne
    rw [hker] at hle
    exact bot_unique hle
  obtain ⟨g, hg_monic, hg_irreducible, hg_span⟩ :=
    prime_ideal_polynomial_over_field_eq_span_monic_irreducible (Ideal.map φ I) hmap_prime
      hmap_ne_bot
  let h : ℤ[X] := IsLocalization.integerNormalization M g
  obtain ⟨c, hcM, hc_eq_raw⟩ := IsLocalization.integerNormalization_spec (M := M) g
  have hg_mem_map : g ∈ Ideal.map φ I := by
    rw [hg_span]
    exact Ideal.subset_span (by simp : g ∈ ({g} : Set ℚ[X]))
  have hc_eq : φ h = C (c : ℚ) * g := by
    simpa [h, φ, Algebra.smul_def] using hc_eq_raw
  have hh_mem : h ∈ I := by
    -- The integer normalization still maps into the localized prime ideal, so it already lay in `I`.
    have hh_map_mem : φ h ∈ Ideal.map φ I := by
      rw [hc_eq]
      exact Ideal.mul_mem_left _ _ hg_mem_map
    have hh_comap : h ∈ Ideal.comap φ (Ideal.map φ I) := by
      simpa [Ideal.mem_comap] using hh_map_mem
    simpa [hcomap_map] using hh_comap
  have hg_ne_zero : g ≠ 0 := hg_irreducible.ne_zero
  have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hcM
  have hh_ne_zero : h ≠ 0 := by
    -- Clearing denominators of a nonzero polynomial cannot produce the zero polynomial.
    intro hh0
    have : φ h = 0 := by simpa [hh0]
    rw [hc_eq] at this
    exact hg_ne_zero ((mul_eq_zero.mp this).resolve_left (by simpa [Polynomial.C_eq_zero] using hc0))
  let f : ℤ[X] := h.primPart
  have hf_mem : f ∈ I := by
    -- Replace the chosen normalization by its primitive part without leaving `I`.
    exact zero_fiber_primPart_mem_of_mem I hI_prime hI_zero hh_mem hh_ne_zero
  have hf_primitive : f.IsPrimitive := by
    simpa [f] using h.isPrimitive_primPart
  have hc_rat0 : (c : ℚ) ≠ 0 := by
    exact_mod_cast hc0
  have hh_content0 : h.content ≠ 0 := by
    intro h0
    exact hh_ne_zero (Polynomial.content_eq_zero_iff.mp h0)
  have hh_content_rat0 : (h.content : ℚ) ≠ 0 := by
    exact_mod_cast hh_content0
  have hu_c : IsUnit (C (c : ℚ) : ℚ[X]) := by
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc_rat0)
  have hu_content : IsUnit (C (h.content : ℚ) : ℚ[X]) := by
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hh_content_rat0)
  have hmap_factor : φ h = C (h.content : ℚ) * φ f := by
    -- Mapping the content decomposition identifies the primitive factor in `ℚ[X]`.
    have hdecomp := congrArg (fun q : ℤ[X] ↦ q.map (Int.castRingHom ℚ))
      h.eq_C_content_mul_primPart
    simpa [f, φ] using hdecomp
  have hmap_eq : C (h.content : ℚ) * φ f = C (c : ℚ) * g := by
    calc
      C (h.content : ℚ) * φ f = φ h := hmap_factor.symm
      _ = C (c : ℚ) * g := hc_eq
  have hf_map_assoc : Associated (φ f) g := by
    -- The localization generator differs from `f` only by multiplication by units.
    have hmul_assoc : Associated (C (h.content : ℚ) * φ f) (C (c : ℚ) * g) := by
      rw [hmap_eq]
    have hleft_assoc : Associated (φ f) (C (c : ℚ) * g) := by
      exact (associated_isUnit_mul_left_iff hu_content).mp hmul_assoc
    exact (associated_isUnit_mul_right_iff hu_c).mp hleft_assoc
  have hf_map_irreducible : Irreducible (φ f) := by
    exact hf_map_assoc.symm.irreducible hg_irreducible
  have hf_irreducible : Irreducible f := by
    -- Gauss's lemma transfers irreducibility back from `ℚ[X]` to `ℤ[X]`.
    exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hf_primitive).2 <|
      by simpa [φ] using hf_map_irreducible
  have hf_natDegree_pos : 0 < f.natDegree := by
    -- The localized generator is irreducible over a field, hence nonconstant.
    have hdeg_map : 0 < (f.map (Int.castRingHom ℚ)).natDegree := by
      exact Polynomial.natDegree_pos_iff_degree_pos.mpr
        (Polynomial.degree_pos_of_irreducible <| by
          simpa [φ] using hf_map_irreducible)
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective] at hdeg_map
    exact hdeg_map
  have hdiv_all : ∀ k : ℤ[X], k ∈ I → f ∣ k := by
    intro k hk
    by_cases hk0 : k = 0
    · simpa [hk0]
    · -- Divisibility in the localized ideal descends to divisibility in `ℤ[X]` for primitive terms.
      have hk_map_mem : φ k ∈ Ideal.map φ I := by
        exact Ideal.mem_map_of_mem φ hk
      have hg_dvd_map : g ∣ φ k := by
        rw [hg_span] at hk_map_mem
        exact Ideal.mem_span_singleton.mp hk_map_mem
      have hf_dvd_map : φ f ∣ φ k := by
        exact (hf_map_assoc.dvd_iff_dvd_left).2 hg_dvd_map
      have hk_map_factor : φ k = C (k.content : ℚ) * φ k.primPart := by
        have hdecomp := congrArg (fun q : ℤ[X] ↦ q.map (Int.castRingHom ℚ))
          k.eq_C_content_mul_primPart
        simpa [φ] using hdecomp
      have hk_content0 : k.content ≠ 0 := by
        intro h0
        exact hk0 (Polynomial.content_eq_zero_iff.mp h0)
      have hk_content_rat0 : (k.content : ℚ) ≠ 0 := by
        exact_mod_cast hk_content0
      have hf_dvd_map_primPart : φ f ∣ φ k.primPart := by
        rcases hf_dvd_map with ⟨r, hr⟩
        rw [hk_map_factor] at hr
        refine ⟨C (k.content : ℚ)⁻¹ * r, ?_⟩
        calc
          φ k.primPart = (1 : ℚ[X]) * φ k.primPart := by simp
          _ = (C (k.content : ℚ)⁻¹ * C (k.content : ℚ)) * φ k.primPart := by
            congr 1
            calc
              (1 : ℚ[X]) = C ((k.content : ℚ)⁻¹ * k.content) := by
                rw [inv_mul_cancel₀ hk_content_rat0, C_1]
              _ = C (k.content : ℚ)⁻¹ * C (k.content : ℚ) := by
                rw [C_mul]
          _ = C (k.content : ℚ)⁻¹ * (C (k.content : ℚ) * φ k.primPart) := by ac_rfl
          _ = C (k.content : ℚ)⁻¹ * (φ f * r) := by rw [hr]
          _ = φ f * (C (k.content : ℚ)⁻¹ * r) := by ac_rfl
      have hf_dvd_primPart : f ∣ k.primPart := by
        exact (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast f k.primPart hf_primitive
          k.isPrimitive_primPart).2 <| by
            simpa [φ] using hf_dvd_map_primPart
      exact (hf_primitive.dvd_primPart_iff_dvd hk0).1 hf_dvd_primPart
  have hspan_le : Ideal.span ({f} : Set ℤ[X]) ≤ I := by
    -- The chosen generator already lies in the prime ideal.
    exact Ideal.span_singleton_le_iff_mem _ |>.2 hf_mem
  have hI_le : I ≤ Ideal.span ({f} : Set ℤ[X]) := by
    -- Every element of the prime ideal is a multiple of `f`.
    intro k hk
    rw [Ideal.mem_span_singleton]
    exact hdiv_all k hk
  refine ⟨f, hf_irreducible, ?_⟩
  constructor
  · exact hf_natDegree_pos
  · simpa [I] using le_antisymm hI_le hspan_le

/-- Example 10.27.2 (1): if a prime ideal of `ℤ[X]` lies over a nonzero prime `(q)` and is not
itself `(q)`, then it is generated by `(q)` together with a polynomial whose reductions in `ℤ[X]`
and `(ZMod q)[X]` are both irreducible. -/
-- Proof sketch: this is exactly the internal nonzero-fiber classification theorem above.
theorem prime_spectrum_int_polynomial_over_nonzero_prime
    (q : ℕ)
    (hq : q.Prime)
    (hp : (comap C p).asIdeal = Ideal.span ({(q : ℤ)} : Set ℤ))
    (hp_ne : p.asIdeal ≠ Ideal.span ({C (q : ℤ)} : Set ℤ[X])) :
    ∃ f : ℤ[X], Irreducible f ∧ IsPrimeFiberGenerator p q f := by
  -- The public statement is exactly the internal nonzero-fiber theorem.
  simpa using primeFiber_is_span_pair p q hq hp hp_ne

/-- Example 10.27.2 (2): if a prime ideal of `ℤ[X]` lies over `(0)` and is not itself `(0)`, then
it is generated by one nonconstant irreducible polynomial. -/
-- Proof sketch: this is exactly the internal zero-fiber classification theorem above.
theorem prime_spectrum_int_polynomial_over_zero
    (hp : (comap C p).asIdeal = ⊥)
    (hp_ne : p.asIdeal ≠ ⊥) :
    ∃ f : ℤ[X], Irreducible f ∧ IsZeroFiberGenerator p f := by
  -- The public statement is exactly the internal zero-fiber theorem.
  simpa using zeroFiber_is_span_singleton p hp hp_ne

end

/-! ### Example_10_27_3 (from Chap10) -/
open Polynomial PrimeSpectrum
open scoped Polynomial.Bivariate

universe u

section

variable {k : Type u} [Field k]

/-
Layering for this item:
* source-facing: classify the points of `Spec(k[x, y])`.
* core/canonical owner: `PrimeSpectrum k[X][Y]`.
* bridge/view: the ideal-level reformulation obtained by unpacking `PrimeSpectrum.asIdeal`.
-/

/-- An ideal of `k[x, y]` is in irreducible principal form if it is generated by one irreducible
polynomial. -/
inductive IrreduciblePrincipalIdealForm (I : Ideal k[X][Y]) : Prop
  | mk
      (generator : k[X][Y])
      (irreducible_generator : Irreducible generator)
      (eq_span_singleton : I = Ideal.span ({generator} : Set k[X][Y])) :
      IrreduciblePrincipalIdealForm I

/-- An ideal of `k[x, y]` is in irreducible pair form if it is generated by `C p` and `f`, where
`p` is irreducible in `k[x]` and the image of `f` in `(k[x] ⧸ (p))[y]` is irreducible. -/
inductive IrreduciblePairIdealForm (I : Ideal k[X][Y]) : Prop
  | mk
      (polynomial_x : k[X])
      (irreducible_polynomial_x : Irreducible polynomial_x)
      (polynomial_y : k[X][Y])
      (irreducible_quotient_image :
        Irreducible
          (polynomial_y.map
            (Ideal.Quotient.mk
              (Ideal.span ({polynomial_x} : Set k[X])))))
      (eq_span_pair : I = Ideal.span ({C polynomial_x, polynomial_y} : Set k[X][Y])) :
      IrreduciblePairIdealForm I

/-- Helper for Example 10.27.3: a prime ideal in `K[y]` over a field is either zero or generated
by one irreducible polynomial. -/
lemma prime_ideal_polynomial_over_field_eq_bot_or_span_irreducible
    {K : Type u} [Field K] (J : Ideal K[X]) (hJ : J.IsPrime) :
    J = ⊥ ∨ ∃ g : K[X], Irreducible g ∧ J = Ideal.span ({g} : Set K[X]) := by
  classical
  by_cases hbot : J = ⊥
  · exact Or.inl hbot
  · right
    letI : J.IsPrincipal := IsPrincipalIdealRing.principal J
    -- In a PID, a nonzero prime ideal is generated by a prime, hence irreducible, polynomial.
    have hprime_generator : Prime (Submodule.IsPrincipal.generator J) := by
      letI : J.IsPrime := hJ
      exact Submodule.IsPrincipal.prime_generator_of_isPrime J hbot
    refine ⟨Submodule.IsPrincipal.generator J, hprime_generator.irreducible, ?_⟩
    simpa using (Ideal.span_singleton_generator J).symm

/-- Helper for Example 10.27.3: an irreducible principal-form ideal in `k[x, y]` is prime. -/
lemma irreducible_principalIdealForm_isPrime {I : Ideal k[X][Y]}
    (hI : IrreduciblePrincipalIdealForm I) : I.IsPrime := by
  rcases hI with ⟨g, hg, rfl⟩
  -- A principal ideal generated by an irreducible element is prime in the UFD `k[x, y]`.
  exact (Ideal.span_singleton_prime hg.ne_zero).2 hg.prime

/-- Helper for Example 10.27.3: a nonprincipal prime of `k[x, y]` contains an irreducible
polynomial coming from the coefficient ring `k[x]`. -/
lemma nonprincipal_prime_contains_irreducible_constant
    (I : Ideal k[X][Y]) (hI : I.IsPrime) (hbot : I ≠ ⊥)
    (hnonprincipal : ∀ g : k[X][Y], I ≠ Ideal.span ({g} : Set k[X][Y])) :
    ∃ p : k[X], Irreducible p ∧ C p ∈ I := by
  -- TODO: follow the source proof via the localization `k[X][Y] → k(X)[Y]`.
  -- The key missing step is to show that zero contraction to `k[X]` would force `I` to be
  -- principal after passing to the PID `k(X)[Y]` and clearing denominators.
  sorry

/-- Helper for Example 10.27.3: once a prime ideal contains an irreducible `C p`, quotienting by
`(C p)` reduces the remaining classification to the one-variable PID case. -/
lemma prime_ideal_containing_irreducible_constant_eq_principal_or_pair
    (I : Ideal k[X][Y]) (hI : I.IsPrime) {p : k[X]} (hp : Irreducible p) (hp_mem : C p ∈ I) :
    IrreduciblePrincipalIdealForm I ∨ IrreduciblePairIdealForm I := by
  classical
  let P : Ideal k[X] := Ideal.span ({p} : Set k[X])
  let q : k[X][Y] →+* k[X][Y] ⧸ Ideal.map C P := Ideal.Quotient.mk (Ideal.map C P)
  let e : k[X][Y] ⧸ Ideal.map C P ≃+* Polynomial (k[X] ⧸ P) :=
    (P.polynomialQuotientEquivQuotientPolynomial).symm
  have hmapC : Ideal.map C P = Ideal.span ({C p} : Set k[X][Y]) := by
    simpa [P] using
      (Ideal.map_span (f := (C : k[X] →+* k[X][Y])) ({p} : Set k[X]))
  have hker_le : RingHom.ker q ≤ I := by
    -- The quotient map kills exactly the ideal generated by `C p`, and `hp_mem` puts that kernel
    -- inside the prime ideal we are classifying.
    have hker : RingHom.ker q = Ideal.map C P := by
      change RingHom.ker (Ideal.Quotient.mk (Ideal.map C P)) = Ideal.map C P
      simp
    rw [hker, hmapC]
    refine Ideal.span_le.mpr ?_
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hp_mem
  let _ : I.IsPrime := hI
  have hq_prime : (I.map q).IsPrime :=
    Ideal.map_isPrime_of_surjective (f := q) Ideal.Quotient.mk_surjective hker_le
  have he_prime : ((I.map q).map e).IsPrime := by
    infer_instance
  have hPmax : P.IsMaximal := by
    simpa [P] using (PrincipalIdealRing.isMaximal_of_irreducible hp)
  let _ : Field (k[X] ⧸ P) := Ideal.Quotient.field P
  rcases prime_ideal_polynomial_over_field_eq_bot_or_span_irreducible ((I.map q).map e) he_prime with
    hbot | ⟨g, hg, hg_span⟩
  · -- If the image in the quotient is zero, then the original prime ideal is exactly `(C p)`.
    have hmap_bot : I.map q = ⊥ := by
      exact (Ideal.map_eq_bot_iff_of_injective e.injective).1 (by simpa using hbot)
    have hcomap : (I.map q).comap q = I := by
      rw [Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective, sup_eq_left.mpr hker_le]
    have hIeq_map : I = Ideal.map C P := by
      calc
        I = (I.map q).comap q := hcomap.symm
        _ = RingHom.ker q := by rw [hmap_bot]; rfl
        _ = Ideal.map C P := by simp [q]
    have hIeq_span : I = Ideal.span ({C p} : Set k[X][Y]) := by
      rw [hmapC] at hIeq_map
      exact hIeq_map
    left
    -- The quotient-zero branch is the principal case `(C p)`.
    have hCp_prime : Prime (C p : k[X][Y]) := by
      simpa using (Polynomial.prime_C_iff.2 hp.prime)
    exact ⟨C p, hCp_prime.irreducible, hIeq_span⟩
  · obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (e.symm g)
    have hf_image : f.map (Ideal.Quotient.mk P) = g := by
      -- The chosen lift `f` maps to the classified irreducible polynomial in the quotient field.
      have hf' := congrArg e hf
      simpa [e] using hf'
    have hspan_map :
        (Ideal.span ({Ideal.Quotient.mk (Ideal.map C P) f} :
          Set (k[X][Y] ⧸ Ideal.map C P))).map e = Ideal.span ({g} : Set (Polynomial (k[X] ⧸ P))) := by
      simp [Ideal.map_span, hf]
    have hq_span : I.map q = Ideal.span ({Ideal.Quotient.mk (Ideal.map C P) f} :
        Set (k[X][Y] ⧸ Ideal.map C P)) := by
      simpa [Ideal.comap_map_of_bijective _ e.bijective] using
        congrArg (Ideal.comap e) (hg_span.trans hspan_map.symm)
    have hspan_q :
        (Ideal.span ({f} : Set k[X][Y])).map q =
          Ideal.span ({Ideal.Quotient.mk (Ideal.map C P) f} : Set (k[X][Y] ⧸ Ideal.map C P)) := by
      simpa [q] using (Ideal.map_span (f := q) ({f} : Set k[X][Y]))
    have hIeq_sup : I = Ideal.span ({f} : Set k[X][Y]) ⊔ Ideal.map C P := by
      -- Pulling the principal ideal back through the quotient map adds back the kernel `(C p)`.
      calc
        I = (I.map q).comap q := by
          rw [Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective, sup_eq_left.mpr hker_le]
        _ = (Ideal.span ({Ideal.Quotient.mk (Ideal.map C P) f} :
            Set (k[X][Y] ⧸ Ideal.map C P))).comap q := by rw [hq_span]
        _ = (((Ideal.span ({f} : Set k[X][Y])).map q).comap q) := by rw [hspan_q]
        _ = Ideal.span ({f} : Set k[X][Y]) ⊔ RingHom.ker q := by
          rw [Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective]
        _ = Ideal.span ({f} : Set k[X][Y]) ⊔ Ideal.map C P := by simp [q]
    have hIeq_pair : I = Ideal.span ({C p, f} : Set k[X][Y]) := by
      -- Repackage the kernel summand `Ideal.map C P` as the singleton span of `C p`.
      rw [hIeq_sup, hmapC]
      simpa [Ideal.span_insert, sup_comm, sup_left_comm, sup_assoc]
    right
    -- The nonzero quotient branch gives the pair form `(C p, f)`.
    exact ⟨p, hp, f, hf_image ▸ hg, hIeq_pair⟩

/-- Helper for Example 10.27.3: every irreducible pair-form ideal is prime. -/
lemma irreducible_pairIdealForm_isPrime {I : Ideal k[X][Y]}
    (hI : IrreduciblePairIdealForm I) : I.IsPrime := by
  classical
  rcases hI with ⟨p, hp, f, hf, hIeq⟩
  let P : Ideal k[X] := Ideal.span ({p} : Set k[X])
  have hPmax : P.IsMaximal := by
    simpa [P] using (PrincipalIdealRing.isMaximal_of_irreducible hp)
  let _ : Field (k[X] ⧸ P) := Ideal.Quotient.field P
  have hprime_span :
      (Ideal.span ({Polynomial.map (Ideal.Quotient.mk P) f} :
        Set (Polynomial (k[X] ⧸ P)))).IsPrime := by
    -- Over the quotient field, a singleton span generated by an irreducible polynomial is prime.
    exact (Ideal.span_singleton_prime hf.ne_zero).2 hf.prime
  let e₁ :
      (Polynomial (k[X] ⧸ P) ⧸
        Ideal.span ({Polynomial.map (Ideal.Quotient.mk P) f} : Set (Polynomial (k[X] ⧸ P)))) ≃+*
      ((k[X][Y] ⧸ Ideal.map C P) ⧸
        Ideal.span ({Ideal.Quotient.mk (Ideal.map C P) f} : Set (k[X][Y] ⧸ Ideal.map C P))) :=
    AdjoinRoot.Polynomial.quotQuotEquivComm P f
  have hspan_q :
      Ideal.span ({Ideal.Quotient.mk (Ideal.map C P) f} : Set (k[X][Y] ⧸ Ideal.map C P)) =
        Ideal.map (Ideal.Quotient.mk (Ideal.map C P)) (Ideal.span ({f} : Set k[X][Y])) := by
    simpa using
      (Ideal.map_span (f := Ideal.Quotient.mk (Ideal.map C P)) ({f} : Set k[X][Y])).symm
  let e₂a :
      ((k[X][Y] ⧸ Ideal.map C P) ⧸
        Ideal.span ({Ideal.Quotient.mk (Ideal.map C P) f} : Set (k[X][Y] ⧸ Ideal.map C P))) ≃+*
      ((k[X][Y] ⧸ Ideal.map C P) ⧸
        Ideal.map (Ideal.Quotient.mk (Ideal.map C P)) (Ideal.span ({f} : Set k[X][Y]))) :=
    Ideal.quotEquivOfEq hspan_q
  let e₂b :
      ((k[X][Y] ⧸ Ideal.map C P) ⧸
        Ideal.map (Ideal.Quotient.mk (Ideal.map C P)) (Ideal.span ({f} : Set k[X][Y]))) ≃+*
      (k[X][Y] ⧸ (Ideal.map C P ⊔ Ideal.span ({f} : Set k[X][Y]))) :=
    DoubleQuot.quotQuotEquivQuotSup (Ideal.map C P) (Ideal.span ({f} : Set k[X][Y]))
  have hmapC : Ideal.map C P = Ideal.span ({C p} : Set k[X][Y]) := by
    simpa [P] using
      (Ideal.map_span (f := (C : k[X] →+* k[X][Y])) ({p} : Set k[X]))
  have hpair_sup : Ideal.map C P ⊔ Ideal.span ({f} : Set k[X][Y]) = I := by
    rw [hIeq, hmapC]
    simpa [Ideal.span_insert, sup_comm, sup_left_comm, sup_assoc]
  let e₃ :
      (k[X][Y] ⧸ (Ideal.map C P ⊔ Ideal.span ({f} : Set k[X][Y]))) ≃+* (k[X][Y] ⧸ I) :=
    Ideal.quotEquivOfEq hpair_sup
  let e :
      (Polynomial (k[X] ⧸ P) ⧸
        Ideal.span ({Polynomial.map (Ideal.Quotient.mk P) f} : Set (Polynomial (k[X] ⧸ P)))) ≃+*
      (k[X][Y] ⧸ I) := e₁.trans (e₂a.trans (e₂b.trans e₃))
  have hdomain_left :
        IsDomain
        (Polynomial (k[X] ⧸ P) ⧸
          Ideal.span ({Polynomial.map (Ideal.Quotient.mk P) f} : Set (Polynomial (k[X] ⧸ P)))) := by
    exact (Ideal.Quotient.isDomain_iff_prime
      (I := Ideal.span ({Polynomial.map (Ideal.Quotient.mk P) f} : Set (Polynomial (k[X] ⧸ P))))).2
      hprime_span
  have hdomain_right : IsDomain (k[X][Y] ⧸ I) := by
    exact e.symm.toMulEquiv.isDomain _
  -- Quotient-domain characterization turns the constructed quotient equivalence back into primeness.
  exact (Ideal.Quotient.isDomain_iff_prime (I := I)).1 hdomain_right

/-- Example 10.27.3: every point of `Spec(k[x, y])`, modeled as `PrimeSpectrum k[X][Y]`, has one
of three canonical forms: the zero ideal, a principal ideal generated by an irreducible
polynomial (including `(C p)` when `p : k[X]` is irreducible), or an ideal of the form `(C p, f)`
where the coefficientwise image of `f` in `(k[x] ⧸ (p))[y]` is irreducible. -/
-- Proof sketch: use that `k[x, y]` is a Noetherian UFD. A nonzero principal prime is generated by
-- an irreducible polynomial. If a prime ideal is not principal, the UFD argument in the text shows
-- it contains a nonzero irreducible polynomial from `k[x]`; passing to the quotient by that
-- polynomial identifies the remaining prime with either `(0)`, which yields the principal case
-- `(C p)`, or a principal prime in a PID, giving `(C p, f)`.
theorem prime_spectrum_polynomial_polynomial_eq_bot_or_principal_or_pair
    (𝔭 : PrimeSpectrum k[X][Y]) :
    𝔭.asIdeal = ⊥ ∨
      IrreduciblePrincipalIdealForm 𝔭.asIdeal ∨
      IrreduciblePairIdealForm 𝔭.asIdeal := by
  classical
  let I : Ideal k[X][Y] := 𝔭.asIdeal
  have hI : I.IsPrime := by
    dsimp [I]
    infer_instance
  by_cases hbot : I = ⊥
  · simpa [I] using Or.inl hbot
  · by_cases hprincipal : ∃ g : k[X][Y], I = Ideal.span ({g} : Set k[X][Y])
    · rcases hprincipal with ⟨g, hg_span⟩
      -- A nonzero principal prime is generated by an irreducible polynomial.
      have hg_ne_zero : g ≠ 0 := by
        intro hg_zero
        apply hbot
        rw [hg_span, Ideal.span_singleton_eq_bot, hg_zero]
      have hg_prime : Prime g := by
        exact (Ideal.span_singleton_prime hg_ne_zero).1 (hg_span ▸ hI)
      have hform : IrreduciblePrincipalIdealForm I := by
        exact ⟨g, hg_prime.irreducible, hg_span⟩
      simpa [I] using Or.inr (Or.inl hform)
    · have hnonprincipal : ∀ g : k[X][Y], I ≠ Ideal.span ({g} : Set k[X][Y]) := by
        intro g hg
        exact hprincipal ⟨g, hg⟩
      -- The only remaining source-faithful input is the existence of a nonzero polynomial in `k[X]`.
      obtain ⟨p, hp, hp_mem⟩ :=
        nonprincipal_prime_contains_irreducible_constant I hI hbot hnonprincipal
      have hform :=
        prime_ideal_containing_irreducible_constant_eq_principal_or_pair I hI hp hp_mem
      simpa [I] using Or.inr hform

/-- Ideal-level reformulation of Example 10.27.3 obtained by unpacking the `PrimeSpectrum`
classification. -/
-- Proof sketch: translate between prime ideals and points of `Spec(k[x, y])`, then apply the
-- point-level classification and rewrite the result back in terms of the original ideal.
theorem prime_ideal_polynomial_polynomial_eq_bot_or_principal_or_pair
    (I : Ideal k[X][Y]) :
    I.IsPrime ↔
      I = ⊥ ∨
        IrreduciblePrincipalIdealForm I ∨
        IrreduciblePairIdealForm I := by
  constructor
  · intro hI
    let 𝔭 : PrimeSpectrum k[X][Y] := ⟨I, hI⟩
    -- The point-level classification applies directly to the prime spectrum point for `I`.
    simpa [𝔭] using prime_spectrum_polynomial_polynomial_eq_bot_or_principal_or_pair (k := k) 𝔭
  · rintro (rfl | hprincipal | hpair)
    · -- The zero ideal is prime because `k[x, y]` is a domain.
      exact Ideal.isPrime_bot
    · -- Principal form is prime by the standard singleton-span criterion.
      exact irreducible_principalIdealForm_isPrime hprincipal
    · -- Pair form is prime by reducing modulo `(C p)` to the one-variable field case.
      exact irreducible_pairIdealForm_isPrime hpair

end
