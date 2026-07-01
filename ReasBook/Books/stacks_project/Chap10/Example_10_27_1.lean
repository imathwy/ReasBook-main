import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
