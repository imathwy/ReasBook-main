import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Polynomial

section

variable {J : Type v} {A : J → Type u} [∀ j, CommRing (A j)]
variable (I : ∀ j, Ideal (A j))

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra and their behavior under finite products;
- sampled owner declarations:
  `HenselianRing`,
  `HenselianRing.jac`,
  `HenselianRing.is_henselian`,
  `inverseSystem_limit_henselianRing`;
- best owner abstraction: the canonical owner remains `HenselianRing`; this file should not
  introduce a product-specific wrapper for henselian pairs, only the product/component bridge for
  that owner;
- primitive data: the ideal family `I` and the owner instances `HenselianRing (A j) (I j)` or
  `HenselianRing ((j : J) → A j) (Ideal.pi I)`;
- derived API: the componentwise instance extracted from the product pair, the product instance
  assembled from the component pairs, and the source-facing textbook `iff`.

Source/core/bridge triage:
- `source-facing`: the textbook equivalence `henselianRing_pi_iff`;
- `core/canonical`: the owner `HenselianRing`;
- `bridge/view`: the two instance declarations transporting `HenselianRing` between the product
  pair and its components.
-/

/-- Helper for Lemma 15.11.11: projecting the product ideal to one coordinate recovers the
corresponding component ideal. -/
lemma ideal_map_evalRingHom_pi (j : J) :
    Ideal.map (Pi.evalRingHom A j) (Ideal.pi I) = I j := by
  classical
  ext x
  constructor
  · intro hx
    -- Proof comment: membership in the mapped ideal is witnessed by a product element whose
    -- coordinates already lie in the component ideals.
    rw [Ideal.mem_map_iff_of_surjective (Pi.evalRingHom A j) (Function.surjective_eval j)] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hy j
  · intro hx
    -- Proof comment: lift a component element to the product by placing it in the `j`-th
    -- coordinate and zeros elsewhere.
    rw [Ideal.mem_map_iff_of_surjective (Pi.evalRingHom A j) (Function.surjective_eval j)]
    let y : ∀ k, A k := Function.update 0 j x
    have hy : y ∈ Ideal.pi I := by
      intro k
      by_cases hk : k = j
      · subst hk
        simpa [y, Function.update_self] using hx
      · simp [y, hk, Ideal.zero_mem (I k)]
    have hyj : Pi.evalRingHom A j y = x := by
      simpa [y] using (Function.update_eq_self j (0 : ∀ k, A k) x)
    exact ⟨y, hy, hyj⟩

/-- Helper for Lemma 15.11.11: each coordinate projection from the product ring is integral
because it is surjective, hence finite. -/
private theorem evalRingHom_isIntegral (j : J) :
    (Pi.evalRingHom A j).IsIntegral := by
  -- Proof comment: surjective ring maps are finite, and finite maps are integral.
  have hfinite : (Pi.evalRingHom A j).Finite :=
    RingHom.Finite.of_surjective _ (Function.surjective_eval j)
  exact RingHom.Finite.to_isIntegral hfinite

/-- Helper for Lemma 15.11.11: any ideal in a subsingleton commutative ring is henselian. -/
private theorem henselianRing_of_subsingleton {R : Type*} [CommRing R] [Subsingleton R]
    (J : Ideal R) : HenselianRing R J := by
  refine
    { jac := ?_
      is_henselian := ?_ }
  · intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    -- Proof comment: in a subsingleton ring every element is equal to `1`, hence a unit.
    rw [show x * y + 1 = (1 : R) by exact Subsingleton.elim _ _]
    exact isUnit_one
  · intro f hf a₀ ha₀ hderiv
    -- Proof comment: in a subsingleton ring every element is equal, so the given approximate root
    -- is already an actual root and differs from itself by `0`.
    refine ⟨a₀, ?_, ?_⟩
    · rw [Polynomial.IsRoot]
      exact Subsingleton.elim _ _
    · simpa using Ideal.zero_mem J

/-- Helper for Lemma 15.11.11: the bounded mixed polynomial stores the first `n + 1`
coefficients of a family of component polynomials as coefficient functions. -/
noncomputable def boundedFamilyPolynomial (n : ℕ) (q : ∀ k, (A k)[X]) : ((k : J) → A k)[X] :=
  Finset.sum (Finset.range (n + 1)) fun m ↦ Polynomial.monomial m (fun k ↦ (q k).coeff m)

/-- Helper for Lemma 15.11.11: the coefficient of the bounded mixed polynomial is the corresponding
component coefficient below the bound and vanishes above it. -/
lemma boundedFamilyPolynomial_coeff (n : ℕ) (q : ∀ k, (A k)[X]) (m : ℕ) :
    (boundedFamilyPolynomial (A := A) n q).coeff m =
      if m ≤ n then (fun k ↦ (q k).coeff m) else 0 := by
  rw [boundedFamilyPolynomial, Polynomial.finset_sum_coeff]
  by_cases hm : m < n + 1
  · have hm' : m ≤ n := Nat.lt_succ_iff.mp hm
    rw [if_pos hm']
    ext k
    have hm_mem : m ∈ Finset.range (n + 1) := by
      simpa [Finset.mem_range] using hm
    -- Proof comment: within the truncation range, the `m`-th summand is the unique one
    -- contributing to the `m`-th coefficient.
    rw [Finset.sum_eq_single_of_mem m hm_mem]
    · simp
    · intro b hb hbm
      simp [Polynomial.coeff_monomial, hbm]
  · have hm' : ¬ m ≤ n := fun hmn ↦ hm (Nat.lt_succ_of_le hmn)
    rw [if_neg hm']
    ext k
    -- Proof comment: outside the truncation range every summand has zero `m`-th coefficient.
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero ?_
    intro b hb
    by_cases hbm : b = m
    · exact (hm (hbm ▸ (by simpa [Finset.mem_range] using hb))).elim
    · simp [Polynomial.coeff_monomial, hbm]

/-- Helper for Lemma 15.11.11: evaluating the bounded mixed polynomial at one coordinate recovers
that component polynomial when all component degrees are bounded by the truncation degree. -/
lemma boundedFamilyPolynomial_map_evalRingHom (n : ℕ) (q : ∀ k, (A k)[X])
    (hq : ∀ k, (q k).natDegree ≤ n) (k : J) :
    Polynomial.map (Pi.evalRingHom A k) (boundedFamilyPolynomial (A := A) n q) = q k := by
  ext m
  by_cases hm : m ≤ n
  · -- Proof comment: below the degree bound, the coefficient function simply evaluates at `k`.
    simp [Polynomial.coeff_map, boundedFamilyPolynomial_coeff, hm]
  · have hm' : n < m := Nat.lt_of_not_ge hm
    have hcoeff : (q k).coeff m = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hq k) hm')
    -- Proof comment: above the degree bound both the bounded polynomial and the target component
    -- have zero coefficient.
    simp [Polynomial.coeff_map, boundedFamilyPolynomial_coeff, hm, hcoeff]

/-- Helper for Lemma 15.11.11: the standard off-coordinate filler polynomial has a simple root at
`1`. -/
noncomputable def projectionFillPolynomial {R : Type*} [CommRing R] (n : ℕ) : R[X] :=
  Polynomial.X ^ (n - 1) * (Polynomial.X - 1)

/-- Helper for Lemma 15.11.11: the off-coordinate filler polynomial is monic. -/
lemma projectionFillPolynomial_monic {R : Type*} [CommRing R] (n : ℕ) :
    (projectionFillPolynomial (R := R) n).Monic := by
  -- Proof comment: both factors are monic, so their product is monic.
  simpa [projectionFillPolynomial] using
    (Polynomial.monic_X_pow (n - 1)).mul (Polynomial.monic_X_sub_C (1 : R))

/-- Helper for Lemma 15.11.11: once `n > 0`, the off-coordinate filler polynomial has degree
exactly `n`. -/
lemma projectionFillPolynomial_natDegree {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (hn : 0 < n) :
    (projectionFillPolynomial (R := R) n).natDegree = n := by
  -- Proof comment: the monic product formula reduces the degree to `(n - 1) + 1`.
  have hdeg :=
    (Polynomial.monic_X_pow (n - 1)).natDegree_mul (Polynomial.monic_X_sub_C (1 : R))
  have hdeg' :
      (projectionFillPolynomial (R := R) n).natDegree =
        n - 1 + Polynomial.natDegree (Polynomial.X - (1 : R[X])) := by
    simpa [projectionFillPolynomial, Polynomial.natDegree_X_pow] using hdeg
  have hXsub : Polynomial.natDegree (Polynomial.X - (1 : R[X])) = 1 := by
    simpa using (Polynomial.natDegree_X_sub_C (1 : R))
  calc
    (projectionFillPolynomial (R := R) n).natDegree
        = n - 1 + Polynomial.natDegree (Polynomial.X - (1 : R[X])) := hdeg'
    _ = n - 1 + 1 := by rw [hXsub]
    _ = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)

/-- Helper for Lemma 15.11.11: the off-coordinate filler polynomial vanishes at `1`. -/
lemma projectionFillPolynomial_eval_one {R : Type*} [CommRing R] (n : ℕ) :
    (projectionFillPolynomial (R := R) n).eval 1 = 0 := by
  -- Proof comment: the second factor is `X - 1`, so evaluation at `1` kills the product.
  simp [projectionFillPolynomial]

/-- Helper for Lemma 15.11.11: the derivative of the off-coordinate filler polynomial evaluates to
`1` at the root `1`. -/
lemma projectionFillPolynomial_derivative_eval_one {R : Type*} [CommRing R] {n : ℕ}
    (hn : 0 < n) :
    (projectionFillPolynomial (R := R) n).derivative.eval 1 = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  -- Proof comment: at `1`, the Leibniz-rule term containing `X - 1` vanishes, leaving only the
  -- derivative of the linear factor.
  have hroot : Polynomial.eval 1 (Polynomial.X - (1 : R[X])) = 0 := by
    simp
  calc
    (projectionFillPolynomial (R := R) (m + 1)).derivative.eval 1
        = ((Polynomial.X ^ m).derivative * (Polynomial.X - (1 : R[X])) +
            Polynomial.X ^ m * 1).eval 1 := by
              simp [projectionFillPolynomial, Polynomial.derivative_mul]
    _ = Polynomial.eval 1 ((Polynomial.X ^ m).derivative) *
          Polynomial.eval 1 (Polynomial.X - (1 : R[X])) +
          Polynomial.eval 1 (Polynomial.X ^ m) * 1 := by
            simp [Polynomial.eval_add, Polynomial.eval_mul]
    _ = Polynomial.eval 1 ((Polynomial.X ^ m).derivative) * 0 + 1 * 1 := by
          rw [hroot]
          simp
    _ = 1 := by
          simp

/-- Helper for Lemma 15.11.11: the off-coordinate filler polynomial has degree at most `n` once
`n > 0`, even in the subsingleton case. -/
lemma projectionFillPolynomial_natDegree_le {R : Type*} [CommRing R] {n : ℕ} (hn : 0 < n) :
    (projectionFillPolynomial (R := R) n).natDegree ≤ n := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI : Subsingleton R := hR
    have hzero : (projectionFillPolynomial (R := R) n) = 0 := Subsingleton.elim _ _
    simpa [hzero] using (Nat.zero_le n)
  · letI : Nontrivial R := hR
    simpa [projectionFillPolynomial_natDegree (R := R) hn] using le_rfl

/-- Helper for Lemma 15.11.11: the mixed product polynomial uses the given polynomial in the
`j`-coordinate and the standard filler polynomial off that coordinate. -/
lemma mixed_projection_polynomial_update (j : J) (f : (A j)[X]) (hf : f.Monic)
    (hn : 0 < f.natDegree) :
    ∃ F : ((k : J) → A k)[X],
      F.Monic ∧
        Polynomial.map (Pi.evalRingHom A j) F = f ∧
          ∀ k, k ≠ j →
            Polynomial.map (Pi.evalRingHom A k) F =
              projectionFillPolynomial (R := A k) f.natDegree := by
  classical
  let q : ∀ k, (A k)[X] :=
    Function.update (fun k ↦ projectionFillPolynomial (R := A k) f.natDegree) j f
  let F : ((k : J) → A k)[X] := boundedFamilyPolynomial (A := A) f.natDegree q
  have hqdeg : ∀ k, (q k).natDegree ≤ f.natDegree := by
    intro k
    by_cases hk : k = j
    · subst hk
      simp [q]
    · simpa [q, hk] using
        projectionFillPolynomial_natDegree_le (R := A k) hn
  have hmapj : Polynomial.map (Pi.evalRingHom A j) F = f := by
    -- Proof comment: the bounded constructor recovers the distinguished coordinate polynomial.
    simpa [F, q] using
      boundedFamilyPolynomial_map_evalRingHom (A := A) f.natDegree q hqdeg j
  have hmapoff :
      ∀ k, k ≠ j →
        Polynomial.map (Pi.evalRingHom A k) F =
          projectionFillPolynomial (R := A k) f.natDegree := by
    intro k hk
    -- Proof comment: every off-coordinate projection recovers the filler polynomial.
    simpa [F, q, hk] using
      boundedFamilyPolynomial_map_evalRingHom (A := A) f.natDegree q hqdeg k
  have hmonic : F.Monic := by
    refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one f.natDegree ?_ ?_
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      have hm' : ¬ m ≤ f.natDegree := not_le.mpr hm
      ext k
      by_cases hk : k = j
      · subst hk
        have hcoeff : f.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hm
        simpa [F, q, boundedFamilyPolynomial_coeff, hm', hcoeff]
      · have hcoeff :
            (projectionFillPolynomial (R := A k) f.natDegree).coeff m = 0 := by
          exact Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt (projectionFillPolynomial_natDegree_le (R := A k) hn) hm)
        simpa [F, q, hk, boundedFamilyPolynomial_coeff, hm', hcoeff]
    · ext k
      by_cases hk : k = j
      · subst hk
        simpa [F, q, boundedFamilyPolynomial_coeff] using hf.coeff_natDegree
      · rcases subsingleton_or_nontrivial (A k) with hsub | hnontriv
        · letI : Subsingleton (A k) := hsub
          exact Subsingleton.elim _ _
        · letI : Nontrivial (A k) := hnontriv
          have hcoeff :
              (projectionFillPolynomial (R := A k) f.natDegree).coeff f.natDegree = 1 := by
            simpa [projectionFillPolynomial_natDegree (R := A k) hn] using
              (projectionFillPolynomial_monic (R := A k) f.natDegree).coeff_natDegree
          simpa [F, q, hk, boundedFamilyPolynomial_coeff] using hcoeff
  exact ⟨F, hmonic, hmapj, hmapoff⟩

/-- Helper for Lemma 15.11.11: explicit inverse data at one coordinate gives a unit in the product
quotient. -/
lemma isUnit_quotient_of_inverse_data_at_coordinate (j : J) {d y : ∀ k, A k}
    (hjy : d j * y j - 1 ∈ I j)
    (hd : ∀ k, k ≠ j → d k = 1)
    (hy : ∀ k, k ≠ j → y k = 1) :
    IsUnit ((Ideal.Quotient.mk (Ideal.pi I)) d) := by
  let q : ((∀ k, A k) ⧸ Ideal.pi I) := (Ideal.Quotient.mk (Ideal.pi I)) d
  let qy : ((∀ k, A k) ⧸ Ideal.pi I) := (Ideal.Quotient.mk (Ideal.pi I)) y
  have hmul_mem : d * y - 1 ∈ Ideal.pi I := by
    intro k
    by_cases hk : k = j
    · subst hk
      simpa using hjy
    · simp [hd k hk, hy k hk]
  have hmul : q * qy = 1 := by
    -- Proof comment: the chosen inverse data becomes an actual inverse after quotienting by the
    -- product ideal.
    have hzero : ((Ideal.Quotient.mk (Ideal.pi I)) (d * y - 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmul_mem
    have hmul' : q * qy - 1 = 0 := by
      simpa [q, qy, map_mul, map_sub] using hzero
    exact sub_eq_zero.mp hmul'
  refine ⟨⟨q, qy, hmul, ?_⟩, rfl⟩
  simpa [mul_comm] using hmul

/-- Helper for Lemma 15.11.11: the Jacobson-radical containment from a henselian product pair
restricts to each component ideal. -/
lemma le_jacobson_bot_of_pi_henselianRing (j : J)
    [HenselianRing (∀ j, A j) (Ideal.pi I)] :
    I j ≤ Ideal.jacobson (⊥ : Ideal (A j)) := by
  classical
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  -- Proof comment: test the product Jacobson condition on the element supported in the
  -- `j`-th coordinate.
  let x' : ∀ k, A k := Function.update 0 j x
  let y' : ∀ k, A k := Function.update 0 j y
  have hx' : x' ∈ Ideal.pi I := by
    intro k
    by_cases hk : k = j
    · subst hk
      simpa [x', Function.update_self] using hx
    · simp [x', hk, Ideal.zero_mem (I k)]
  have hUnitProd : IsUnit (x' * y' + 1) :=
    Ideal.mem_jacobson_bot.mp (HenselianRing.jac (I := Ideal.pi I) hx') y'
  have hUnitComp : IsUnit ((1 + y' * x') j) := by
    simpa [add_comm, mul_comm] using (Pi.isUnit_iff.mp hUnitProd j)
  simpa [x', y', add_comm, mul_comm] using hUnitComp

/-- Helper for Lemma 15.11.11: if the simple-derivative hypothesis holds for a monic polynomial
over a nontrivial coordinate ring, then the polynomial has positive degree. -/
lemma natDegree_pos_of_isUnit_derivative_eval_quotient (j : J)
    [Nontrivial (A j)] [HenselianRing (∀ j, A j) (Ideal.pi I)]
    (f : (A j)[X]) (hf : f.Monic) (a₀ : A j)
    (ha₀ : f.eval a₀ ∈ I j)
    (_hderiv : IsUnit ((Ideal.Quotient.mk (I j)) (f.derivative.eval a₀))) :
    0 < f.natDegree := by
  by_contra hdeg
  have hdeg0 : f.natDegree = 0 := Nat.eq_zero_of_not_pos hdeg
  have hconst : f = 1 := by
    ext m
    cases m with
    | zero =>
        simpa [hdeg0] using hf.coeff_natDegree
    | succ m =>
        have hcoeff : f.coeff (Nat.succ m) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          simpa [hdeg0]
        rw [hcoeff]
        simp [Polynomial.coeff_one]
  have hone_mem : (1 : A j) ∈ I j := by
    simpa [hconst] using ha₀
  have hone_jac : (1 : A j) ∈ Ideal.jacobson (⊥ : Ideal (A j)) :=
    le_jacobson_bot_of_pi_henselianRing (I := I) j hone_mem
  have hzero_unit : IsUnit (0 : A j) := by
    -- Proof comment: testing Jacobson membership of `1` against `-1` would force `0` to be a
    -- unit, impossible in a nontrivial ring.
    simpa using (Ideal.mem_jacobson_bot.mp hone_jac (-1 : A j))
  exact hzero_unit.ne_zero rfl

/-- If the product pair is henselian, then each component pair is henselian. -/
instance henselianRing_of_pi_henselianRing (j : J)
    [HenselianRing (∀ j, A j) (Ideal.pi I)] : HenselianRing (A j) (I j) := by
  rcases subsingleton_or_nontrivial (A j) with hsub | hnontriv
  · letI : Subsingleton (A j) := hsub
    exact henselianRing_of_subsingleton (I j)
  · letI : Nontrivial (A j) := hnontriv
    refine
      { jac := le_jacobson_bot_of_pi_henselianRing (I := I) j
        is_henselian := ?_ }
    intro f hf a₀ ha₀ hderiv
    classical
    have hnat :
        0 < f.natDegree :=
      natDegree_pos_of_isUnit_derivative_eval_quotient (I := I) j f hf a₀ ha₀ hderiv
    obtain ⟨F, hFmonic, hmapj, hmapoff⟩ :=
      mixed_projection_polynomial_update (A := A) j f hf hnat
    let b₀ : ∀ k, A k := Function.update 1 j a₀
    have hEval : F.eval b₀ ∈ Ideal.pi I := by
      intro k
      by_cases hk : k = j
      · subst k
        -- Proof comment: on the distinguished coordinate the product polynomial reduces to `f`.
        have hproj :
            (Polynomial.map (Pi.evalRingHom A j) F).eval (b₀ j) = (F.eval b₀) j := by
          simpa using (Polynomial.eval_map_apply (p := F) (f := Pi.evalRingHom A j) b₀)
        rw [← hproj]
        simpa [hmapj, b₀] using ha₀
      · -- Proof comment: off the distinguished coordinate the filler polynomial vanishes at `1`.
        have hproj :
            (Polynomial.map (Pi.evalRingHom A k) F).eval (b₀ k) = (F.eval b₀) k := by
          simpa using (Polynomial.eval_map_apply (p := F) (f := Pi.evalRingHom A k) b₀)
        have hb₀k : b₀ k = 1 := by
          simp [b₀, hk]
        rw [← hproj, hmapoff k hk, hb₀k, projectionFillPolynomial_eval_one]
        exact Ideal.zero_mem (I k)
    have hderiv_prod :
        IsUnit ((Ideal.Quotient.mk (Ideal.pi I)) (F.derivative.eval b₀)) := by
      rcases hderiv with ⟨u, hu⟩
      obtain ⟨yj, hyj⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : A j ⧸ I j)
      let y : ∀ k, A k := Function.update 1 j yj
      have hderivj :
          (F.derivative.eval b₀) j = f.derivative.eval a₀ := by
        have hproj :
            ((Polynomial.map (Pi.evalRingHom A j) F).derivative).eval (b₀ j) =
              (F.derivative.eval b₀) j := by
          rw [Polynomial.derivative_map]
          simpa using
            (Polynomial.eval_map_apply (p := F.derivative) (f := Pi.evalRingHom A j) b₀)
        rw [← hproj]
        simpa [hmapj, b₀]
      have hderiv_off : ∀ k, k ≠ j → (F.derivative.eval b₀) k = 1 := by
        intro k hk
        have hproj :
            ((Polynomial.map (Pi.evalRingHom A k) F).derivative).eval (b₀ k) =
              (F.derivative.eval b₀) k := by
          rw [Polynomial.derivative_map]
          simpa using
            (Polynomial.eval_map_apply (p := F.derivative) (f := Pi.evalRingHom A k) b₀)
        have hb₀k : b₀ k = 1 := by
          simp [b₀, hk]
        rw [← hproj, hmapoff k hk, hb₀k, projectionFillPolynomial_derivative_eval_one hnat]
      have hjy : (F.derivative.eval b₀) j * y j - 1 ∈ I j := by
        have hyj' : (Ideal.Quotient.mk (I j)) (y j) = ↑u⁻¹ := by
          simpa [y] using hyj
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        calc
          (Ideal.Quotient.mk (I j)) ((F.derivative.eval b₀) j * y j - 1)
              = (Ideal.Quotient.mk (I j)) ((F.derivative.eval b₀) j) *
                  (Ideal.Quotient.mk (I j)) (y j) - 1 := by
                    simp
          _ = (Ideal.Quotient.mk (I j)) (f.derivative.eval a₀) * ↑u⁻¹ - 1 := by
                rw [hderivj, hyj']
          _ = (↑u : A j ⧸ I j) * ↑u⁻¹ - 1 := by
                rw [← hu]
          _ = 0 := by
                simp
      have hy : ∀ k, k ≠ j → y k = 1 := by
        intro k hk
        simp [y, hk]
      exact isUnit_quotient_of_inverse_data_at_coordinate (I := I) j hjy hderiv_off hy
    obtain ⟨b, hbroot, hbmem⟩ :=
      HenselianRing.is_henselian (I := Ideal.pi I) F hFmonic b₀ hEval hderiv_prod
    refine ⟨b j, ?_, ?_⟩
    · -- Proof comment: projecting the lifted product root back to the `j`-coordinate solves the
      -- original Hensel problem.
      rw [Polynomial.IsRoot] at hbroot ⊢
      have hrootj : (F.eval b) j = 0 := congrArg (fun z : ∀ k, A k ↦ z j) hbroot
      have hproj :
          (Polynomial.map (Pi.evalRingHom A j) F).eval (b j) = (F.eval b) j := by
        simpa using (Polynomial.eval_map_apply (p := F) (f := Pi.evalRingHom A j) b)
      rw [← hproj, hmapj] at hrootj
      exact hrootj
    · -- Proof comment: the product-ideal congruence is also coordinatewise.
      simpa [b₀] using hbmem j

/-- Helper for Lemma 15.11.11: componentwise Jacobson-radical containment implies Jacobson-radical
containment for the product ideal. -/
lemma pi_le_jacobson_bot_of_forall
    (hjac : ∀ j, I j ≤ Ideal.jacobson (⊥ : Ideal (A j))) :
    Ideal.pi I ≤ Ideal.jacobson (⊥ : Ideal ((j : J) → A j)) := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  -- Proof comment: the Jacobson criterion in a product ring is checked coordinatewise.
  rw [Pi.isUnit_iff]
  intro j
  exact Ideal.mem_jacobson_bot.mp ((hjac j) (hx j)) (y j)

/-- Helper for Lemma 15.11.11: a unit in the quotient by the product ideal stays a unit in each
component quotient. -/
lemma isUnit_component_quotient_of_pi_isUnit (j : J) {x : (∀ j, A j)}
    (hx : IsUnit ((Ideal.Quotient.mk (Ideal.pi I)) x)) :
    IsUnit ((Ideal.Quotient.mk (I j)) (x j)) := by
  -- Proof comment: apply the quotient map induced by the coordinate evaluation morphism.
  let φ : ((∀ j, A j) ⧸ Ideal.pi I) →+* A j ⧸ I j :=
    Ideal.quotientMap (I j) (Pi.evalRingHom A j) fun x hx ↦ hx j
  simpa [φ] using IsUnit.map φ hx

/-- If each component pair is henselian, then the product pair is henselian. -/
instance pi_henselianRing [∀ j, HenselianRing (A j) (I j)] :
    HenselianRing (∀ j, A j) (Ideal.pi I) := by
  refine
    { jac := ?_
      is_henselian := ?_ }
  · -- Proof comment: the Jacobson-radical field is the source proof's componentwise unit test.
    exact pi_le_jacobson_bot_of_forall (I := I) fun j ↦ HenselianRing.jac (I := I j)
  · intro f hf a₀ ha₀ hderiv
    classical
    -- Proof comment: reduce the approximate-root and simple-derivative hypotheses to each
    -- coordinate, solve the component Hensel problems, and reassemble the lifted root.
    have ha₀_comp :
        ∀ j, (f.map (Pi.evalRingHom A j)).eval (a₀ j) ∈ I j := by
      intro j
      rw [show (f.map (Pi.evalRingHom A j)).eval (a₀ j) = (f.eval a₀) j by
        simpa using (Polynomial.eval_map_apply (p := f) (f := Pi.evalRingHom A j) a₀)]
      exact ha₀ j
    have hderiv_comp :
        ∀ j, IsUnit
          ((Ideal.Quotient.mk (I j)) (((f.map (Pi.evalRingHom A j)).derivative).eval (a₀ j))) := by
      intro j
      have hcomponent :=
        isUnit_component_quotient_of_pi_isUnit (I := I) j
          (x := f.derivative.eval a₀) hderiv
      rw [show ((f.map (Pi.evalRingHom A j)).derivative).eval (a₀ j) = ((f.derivative.eval a₀) j) by
        rw [Polynomial.derivative_map]
        simpa using
          (Polynomial.eval_map_apply (p := f.derivative) (f := Pi.evalRingHom A j) a₀)]
      exact hcomponent
    choose a ha_root ha_mem using
      fun j ↦
        HenselianRing.is_henselian (I := I j) (f.map (Pi.evalRingHom A j))
          (by simpa using hf.map (Pi.evalRingHom A j))
          (a₀ j) (ha₀_comp j) (hderiv_comp j)
    refine ⟨fun j ↦ a j, ?_, ?_⟩
    · -- Proof comment: roothood in the product ring is exactly coordinatewise roothood.
      ext j
      rw [show (f.eval (fun j ↦ a j)) j = (f.map (Pi.evalRingHom A j)).eval (a j) by
        simpa using
          (Polynomial.eval_map_apply (p := f) (f := Pi.evalRingHom A j) (fun j ↦ a j)).symm]
      simpa [Polynomial.IsRoot] using ha_root j
    · -- Proof comment: membership in `Ideal.pi I` is pointwise membership in each `I j`.
      intro j
      exact ha_mem j

-- Proof sketch: for the forward implication, apply henselianity along each projection
-- `Π j, A j → A i`, which sends `Ideal.pi I` to `I i`. For the reverse implication, use that the
-- Jacobson-radical condition and the Hensel lifting property are both checked componentwise in a
-- product ring.
/-- Lemma 15.11.11: the product pair `((j : J) → A j, Ideal.pi I)` is henselian if and only if
each component pair `(A j, I j)` is henselian. -/
@[stacks 0ATD]
theorem henselianRing_pi_iff :
    HenselianRing (∀ j, A j) (Ideal.pi I) ↔ ∀ j, HenselianRing (A j) (I j) := by
  constructor
  · intro h j
    let _ : HenselianRing (∀ j, A j) (Ideal.pi I) := h
    infer_instance
  · intro h
    let _ : ∀ j, HenselianRing (A j) (I j) := h
    infer_instance

end
