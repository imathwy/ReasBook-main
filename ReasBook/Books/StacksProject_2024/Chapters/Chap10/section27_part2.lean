import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_10_27_4 (from Chap10) -/
noncomputable section

open IsLocalRing
open Polynomial
open PrimeSpectrum
open Topology
open scoped Polynomial.Bivariate

local notation "R" => equal_endpoint_poly_subring ℚ

private theorem equal_endpoint_C_mem (q : ℚ) : C q ∈ R := by
  rw [mem_equal_endpoint_poly_subring_iff]
  simp

instance : Algebra ℚ R :=
  (C.codRestrict R equal_endpoint_C_mem).toAlgebra

private theorem equal_endpoint_quad_mem : (X ^ 2 - X : Polynomial ℚ) ∈ R := by
  rw [mem_equal_endpoint_poly_subring_iff]
  norm_num

private theorem equal_endpoint_cubic_mem : (X ^ 3 - X ^ 2 : Polynomial ℚ) ∈ R := by
  rw [mem_equal_endpoint_poly_subring_iff]
  norm_num

private def equal_endpoint_quad : R :=
  ⟨X ^ 2 - X, equal_endpoint_quad_mem⟩

private def equal_endpoint_cubic : R :=
  ⟨X ^ 3 - X ^ 2, equal_endpoint_cubic_mem⟩

/-- The relation `A^3 - B^2 + AB` from the quotient presentation of Example 10.27.4, modeled in
`ℚ[X][Y]` with `A = C X` and `B = Y`. -/
def equal_endpoint_relation : ℚ[X][Y] :=
  C (X ^ 3) - Y ^ 2 + C X * Y

/-- The map `φ : ℚ[A, B] → R` from Example 10.27.4, modeled as a bivariate polynomial map
`ℚ[X][Y] →ₐ[ℚ] R` sending `A` to `z^2 - z` and `B` to `z^3 - z^2`. -/
def equal_endpoint_presentation : ℚ[X][Y] →ₐ[ℚ] R :=
  Polynomial.aevalAeval equal_endpoint_quad equal_endpoint_cubic

/-- Helper for Example 10.27.4: every polynomial of the form `(X^2 - X) * g + C a` lies in the
equal-endpoint subring. -/
private theorem equal_endpoint_quad_mul_add_constant_mem (g : Polynomial ℚ) (a : ℚ) :
    (X ^ 2 - X) * g + C a ∈ R := by
  -- The quadratic factor vanishes at both endpoints, so only the constant term survives.
  rw [mem_equal_endpoint_poly_subring_iff]
  simp

/-- Helper for Example 10.27.4: dividing by `X^2 - X` leaves a remainder of degree at most `1`. -/
private theorem equal_endpoint_division_remainder_degree_lt_two (g : Polynomial ℚ) :
    ∃ b₁ b₀ : ℚ, g = (X ^ 2 - X) * (g /ₘ (X ^ 2 - X)) + C b₁ * X + C b₀ := by
  let r : Polynomial ℚ := g %ₘ (X ^ 2 - X)
  have hmonic : (X ^ 2 - X : Polynomial ℚ).Monic := by
    -- We use the factorization `X^2 - X = X * (X - 1)` to read off monicity.
    simpa [pow_two, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using
      (Polynomial.monic_X_sub_C (0 : ℚ)).mul (Polynomial.monic_X_sub_C (1 : ℚ))
  have hquad_deg : (X ^ 2 - X : Polynomial ℚ).degree = 2 := by
    -- The quadratic has nonzero leading coefficient, so its degree is exactly `2`.
    simpa [sub_eq_add_neg, pow_two, mul_assoc, mul_comm, mul_left_comm, add_comm, add_left_comm,
      add_assoc] using
      (Polynomial.degree_quadratic (a := (1 : ℚ)) (b := (-1 : ℚ)) (c := (0 : ℚ))
        (by norm_num : (1 : ℚ) ≠ 0))
  have hrdeg : r.natDegree ≤ 1 := by
    -- The division remainder has degree strictly less than `2`, hence is linear.
    by_cases hr0 : r = 0
    · simp [hr0]
    · have hrlt : r.degree < 2 := by
        simpa [r, hquad_deg] using (Polynomial.degree_modByMonic_lt g hmonic)
      have hnat : r.natDegree < 2 := (Polynomial.natDegree_lt_iff_degree_lt hr0).2 hrlt
      omega
  rcases Polynomial.exists_eq_X_add_C_of_natDegree_le_one hrdeg with ⟨b₁, b₀, hr⟩
  refine ⟨b₁, b₀, ?_⟩
  -- Replace the remainder by its explicit linear normal form.
  calc
    g = r + (X ^ 2 - X) * (g /ₘ (X ^ 2 - X)) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (Polynomial.modByMonic_add_div g (X ^ 2 - X)).symm
    _ = (C b₁ * X + C b₀) + (X ^ 2 - X) * (g /ₘ (X ^ 2 - X)) := by rw [hr]
    _ = (X ^ 2 - X) * (g /ₘ (X ^ 2 - X)) + (C b₁ * X + C b₀) := by rw [add_comm]
    _ = (X ^ 2 - X) * (g /ₘ (X ^ 2 - X)) + C b₁ * X + C b₀ := by
      rw [add_assoc]

/-- Helper for Example 10.27.4: the quadratic `X^2 - X` is monic. -/
private theorem equal_endpoint_quadratic_monic : (X ^ 2 - X : Polynomial ℚ).Monic := by
  -- The factorization `X^2 - X = X * (X - 1)` makes monicity immediate.
  simpa [pow_two, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using
    (Polynomial.monic_X_sub_C (0 : ℚ)).mul (Polynomial.monic_X_sub_C (1 : ℚ))

/-- Helper for Example 10.27.4: the quadratic `X^2 - X` has natDegree `2`. -/
private theorem equal_endpoint_quadratic_natDegree : (X ^ 2 - X : Polynomial ℚ).natDegree = 2 := by
  have hX1 : (X - C (1 : ℚ) : Polynomial ℚ) ≠ 0 := by
    -- Evaluating at `0` rules out the zero polynomial.
    intro h
    have hEval := congrArg (fun p : Polynomial ℚ => p.eval 0) h
    norm_num at hEval
  have hfactor : (X ^ 2 - X : Polynomial ℚ) = X * (X - C (1 : ℚ)) := by
    rw [pow_two]
    simp [sub_eq_add_neg, mul_add]
  rw [hfactor]
  rw [Polynomial.natDegree_mul (by simp) hX1]
  rw [Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C]

/-- Helper for Example 10.27.4: the scalar `ℚ`-algebra map into `R` is the constant-polynomial
embedding. -/
private theorem equal_endpoint_algebraMap_val (q : ℚ) :
    ((algebraMap ℚ R q : R) : Polynomial ℚ) = C q := rfl

/-- Helper for Example 10.27.4: the linear remainder case is already a polynomial in
`A = z^2 - z` and `B = z^3 - z^2`. -/
private theorem equal_endpoint_presentation_linear_normal_form (b₁ b₀ a : ℚ) :
    equal_endpoint_presentation (C (C b₁) * Y + C (C b₀) * C X + C (C a)) =
      ⟨(X ^ 2 - X) * (C b₁ * X + C b₀) + C a,
        equal_endpoint_quad_mul_add_constant_mem (C b₁ * X + C b₀) a⟩ := by
  -- The displayed bivariate polynomial evaluates to the textbook linear normal form.
  apply Subtype.ext
  simp only [equal_endpoint_presentation, map_add, map_mul, Polynomial.aevalAeval_C,
    Polynomial.aevalAeval_Y, Polynomial.aeval_C, Polynomial.aeval_X, equal_endpoint_quad,
    equal_endpoint_cubic]
  simp [equal_endpoint_algebraMap_val]
  ring

/-- Helper for Example 10.27.4: multiplying an existing presenter by `A` upstairs matches
multiplication by `X^2 - X` downstairs, after adding the linear remainder terms. -/
private theorem equal_endpoint_presentation_recursive_step
    (P : ℚ[X][Y]) (h : Polynomial ℚ) (b₁ b₀ a : ℚ)
    (hP :
      equal_endpoint_presentation P =
        ⟨(X ^ 2 - X) * h + C 0, equal_endpoint_quad_mul_add_constant_mem h 0⟩) :
    equal_endpoint_presentation
        (C X * P + C (C b₁) * Y + C (C b₀) * C X + C (C a)) =
      ⟨(X ^ 2 - X) * ((X ^ 2 - X) * h + C b₁ * X + C b₀) + C a,
        equal_endpoint_quad_mul_add_constant_mem ((X ^ 2 - X) * h + C b₁ * X + C b₀) a⟩ := by
  -- Route correction: package the recursive multiplication-by-`A` step once so the induction
  -- only rewrites a single algebraic identity.
  apply Subtype.ext
  have hPval := congrArg Subtype.val hP
  simp only [equal_endpoint_presentation, map_add, map_mul, Polynomial.aevalAeval_C,
    Polynomial.aevalAeval_Y, Polynomial.aeval_C, Polynomial.aeval_X, equal_endpoint_quad,
    equal_endpoint_cubic] at hPval ⊢
  simp [equal_endpoint_algebraMap_val] at hPval ⊢
  rw [hPval]
  ring

/-- Helper for Example 10.27.4: a natDegree-bounded induction realizes every polynomial of the
form `(X^2 - X) * g + C a` as a polynomial in `A` and `B`. -/
private theorem equal_endpoint_presentation_surjective_aux_degree :
    ∀ n : ℕ, ∀ g : Polynomial ℚ, ∀ a : ℚ, g.natDegree ≤ n →
      ∃ P : ℚ[X][Y],
        equal_endpoint_presentation P =
          ⟨(X ^ 2 - X) * g + C a, equal_endpoint_quad_mul_add_constant_mem g a⟩
  | 0, g, a, hg => by
      have hlin : g.natDegree ≤ 1 := le_trans hg (by omega)
      rcases Polynomial.exists_eq_X_add_C_of_natDegree_le_one hlin with ⟨b₁, b₀, rfl⟩
      -- At degree at most one, the base normal form closes the proof.
      refine ⟨C (C b₁) * Y + C (C b₀) * C X + C (C a), ?_⟩
      simpa [mul_add, add_mul, add_assoc, add_left_comm, add_comm, mul_assoc] using
        equal_endpoint_presentation_linear_normal_form b₁ b₀ a
  | n + 1, g, a, hg => by
      by_cases hlin : g.natDegree ≤ 1
      · rcases Polynomial.exists_eq_X_add_C_of_natDegree_le_one hlin with ⟨b₁, b₀, rfl⟩
        -- The low-degree branch is the same explicit linear calculation.
        refine ⟨C (C b₁) * Y + C (C b₀) * C X + C (C a), ?_⟩
        simpa [mul_add, add_mul, add_assoc, add_left_comm, add_comm, mul_assoc] using
          equal_endpoint_presentation_linear_normal_form b₁ b₀ a
      · have hge : 2 ≤ g.natDegree := by omega
        rcases equal_endpoint_division_remainder_degree_lt_two g with ⟨b₁, b₀, hgdiv⟩
        have hqdeg : (g /ₘ (X ^ 2 - X)).natDegree ≤ n := by
          rw [Polynomial.natDegree_divByMonic g equal_endpoint_quadratic_monic]
          rw [equal_endpoint_quadratic_natDegree]
          have : g.natDegree - 2 ≤ n := by omega
          simpa using this
        rcases equal_endpoint_presentation_surjective_aux_degree n (g /ₘ (X ^ 2 - X)) 0 hqdeg with
          ⟨P, hP⟩
        -- The recursive presenter for the quotient lifts to one for `g` after adjoining the
        -- linear remainder.
        refine ⟨C X * P + C (C b₁) * Y + C (C b₀) * C X + C (C a), ?_⟩
        calc
          equal_endpoint_presentation
              (C X * P + C (C b₁) * Y + C (C b₀) * C X + C (C a)) =
              ⟨(X ^ 2 - X) * ((X ^ 2 - X) * (g /ₘ (X ^ 2 - X)) + C b₁ * X + C b₀) + C a,
                equal_endpoint_quad_mul_add_constant_mem
                  ((X ^ 2 - X) * (g /ₘ (X ^ 2 - X)) + C b₁ * X + C b₀) a⟩ := by
                simpa using
                  equal_endpoint_presentation_recursive_step
                    P (g /ₘ (X ^ 2 - X)) b₁ b₀ a hP
          _ = ⟨(X ^ 2 - X) * g + C a, equal_endpoint_quad_mul_add_constant_mem g a⟩ := by
              apply Subtype.ext
              conv_rhs => rw [hgdiv]

/-- Helper for Example 10.27.4: a polynomial with equal values at `0` and `1` differs from its
common value by a multiple of `X^2 - X`. -/
private theorem equal_endpoint_factor_through_quadratic (f : R) :
    ∃ g : Polynomial ℚ, f.1 = (X ^ 2 - X) * g + C (f.1.eval 0) := by
  have hx : (X : Polynomial ℚ) ∣ f.1 - C (f.1.eval 0) := by
    -- Evaluation at `0` kills `f - f(0)`.
    simpa using (Polynomial.X_sub_C_dvd_sub_C_eval (p := f.1) (a := (0 : ℚ)))
  have hx1 : (X - 1 : Polynomial ℚ) ∣ f.1 - C (f.1.eval 0) := by
    -- The equal-endpoint condition identifies `f(1)` with `f(0)`.
    rw [show (1 : Polynomial ℚ) = C (1 : ℚ) by simp]
    have hf : f.1.eval 1 = f.1.eval 0 := by
      symm
      simpa [Polynomial.coeff_zero_eq_eval_zero] using
        (mem_equal_endpoint_poly_subring_iff ℚ f.1).mp f.2
    simpa [hf] using (Polynomial.X_sub_C_dvd_sub_C_eval (p := f.1) (a := (1 : ℚ)))
  have hcoprime : IsCoprime (X : Polynomial ℚ) (X - 1) := by
    -- The linear factors are coprime because their roots are distinct.
    simpa using
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (a := (0 : ℚ)) (b := (1 : ℚ))
        (show IsUnit ((0 : ℚ) - 1) by
          exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr zero_ne_one)))
  rcases hcoprime.mul_dvd hx hx1 with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  -- Rewrite the product of the two coprime linear factors as `X^2 - X`.
  calc
    f.1 = (f.1 - C (f.1.eval 0)) + C (f.1.eval 0) := by abel
    _ = X * (X - 1) * g + C (f.1.eval 0) := by rw [hg]
    _ = (X ^ 2 - X) * g + C (f.1.eval 0) := by ring

/-- Helper for Example 10.27.4: the source-faithful recursive normal form expresses every
polynomial `(X^2 - X) * g + C a` as a polynomial in `A = X^2 - X` and `B = X^3 - X^2`. -/
private theorem equal_endpoint_presentation_surjective_aux (g : Polynomial ℚ) (a : ℚ) :
    ∃ P : ℚ[X][Y],
      equal_endpoint_presentation P =
        ⟨(X ^ 2 - X) * g + C a, equal_endpoint_quad_mul_add_constant_mem g a⟩ := by
  -- The bounded induction engine removes the elaboration-heavy direct recursion on `g`.
  exact equal_endpoint_presentation_surjective_aux_degree g.natDegree g a le_rfl

/-- The presentation map from Example 10.27.4 is surjective. -/
-- Proof sketch: every polynomial `f` with `f(0) = f(1)` factors through the parameterization
-- `A = z^2 - z`, `B = z^3 - z^2`, so `f` lies in the image of `equal_endpoint_presentation`.
theorem equal_endpoint_presentation_surjective :
    Function.Surjective equal_endpoint_presentation := by
  intro f
  rcases equal_endpoint_factor_through_quadratic f with ⟨g, hg⟩
  rcases equal_endpoint_presentation_surjective_aux g (f.1.eval 0) with ⟨P, hP⟩
  refine ⟨P, ?_⟩
  -- The auxiliary theorem hits exactly the quadratic-factor form of `f`.
  calc
    equal_endpoint_presentation P =
        ⟨(X ^ 2 - X) * g + C (f.1.eval 0),
          equal_endpoint_quad_mul_add_constant_mem g (f.1.eval 0)⟩ := hP
    _ = f := by
        apply Subtype.ext
        exact hg.symm

/-- Helper for Example 10.27.4: the monic `Y`-relation attached to the presentation. -/
private def equal_endpoint_monic_relation : ℚ[X][Y] :=
  Y ^ 2 - C X * Y - C (X ^ 3)

/-- Helper for Example 10.27.4: the textbook relation differs from the monic partner by `-1`. -/
private theorem equal_endpoint_relation_eq_neg_monic_relation :
    equal_endpoint_relation = -equal_endpoint_monic_relation := by
  -- We rewrite once so the kernel proof can divide by a monic polynomial in `Y`.
  dsimp [equal_endpoint_relation, equal_endpoint_monic_relation]
  ring

/-- Helper for Example 10.27.4: the monic `Y`-relation has outer degree `2`. -/
private theorem equal_endpoint_monic_relation_degree :
    (equal_endpoint_monic_relation : ℚ[X][Y]).degree = 2 := by
  have hlinear' :
      degree (C X * Y + C (X ^ 3) : ℚ[X][Y]) < 2 := by
    -- The correction term is only linear in the outer variable `Y`.
    simpa using
      (Polynomial.degree_linear_lt (a := (X : Polynomial ℚ)) (b := X ^ 3) :
        degree (C (X : Polynomial ℚ) * (X : Polynomial (Polynomial ℚ)) + C (X ^ 3) :
          Polynomial (Polynomial ℚ)) < 2)
  have hlinear :
      degree (C X * Y + C (X ^ 3) : ℚ[X][Y]) < degree (Y ^ 2 : ℚ[X][Y]) := by
    simpa using hlinear'
  -- Subtracting a strictly lower-degree term does not change the degree of `Y^2`.
  calc
    degree (equal_endpoint_monic_relation : ℚ[X][Y]) =
        degree (Y ^ 2 - (C X * Y + C (X ^ 3)) : ℚ[X][Y]) := by
          dsimp [equal_endpoint_monic_relation]
          ring_nf
    _ = degree (Y ^ 2 : ℚ[X][Y]) := Polynomial.degree_sub_eq_left_of_degree_lt hlinear
    _ = 2 := by simp

/-- Helper for Example 10.27.4: the monic partner is monic in the outer variable `Y`. -/
private theorem equal_endpoint_monic_relation_monic :
    (equal_endpoint_monic_relation : ℚ[X][Y]).Monic := by
  have hlinear :
      degree (C X * Y + C (X ^ 3) : ℚ[X][Y]) < 2 := by
    -- Again the lower-order term is linear in `Y`.
    simpa using
      (Polynomial.degree_linear_lt (a := (X : Polynomial ℚ)) (b := X ^ 3) :
        degree (C (X : Polynomial ℚ) * (X : Polynomial (Polynomial ℚ)) + C (X ^ 3) :
          Polynomial (Polynomial ℚ)) < 2)
  -- The leading coefficient comes from the `Y^2` term.
  dsimp [equal_endpoint_monic_relation]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (Polynomial.monic_X_pow_sub (n := 2)
      (p := (C X * Y + C (X ^ 3) : ℚ[X][Y])) hlinear)

/-- Helper for Example 10.27.4: the cubic generator `z^3 - z^2` has degree `3`. -/
private theorem equal_endpoint_cubic_natDegree :
    (X ^ 3 - X ^ 2 : Polynomial ℚ).natDegree = 3 := by
  have hquad_ne : (X ^ 2 - X : Polynomial ℚ) ≠ 0 := equal_endpoint_quadratic_monic.ne_zero
  -- We use the source relation `B = A * z`.
  calc
    (X ^ 3 - X ^ 2 : Polynomial ℚ).natDegree = ((X ^ 2 - X : Polynomial ℚ) * X).natDegree := by
      congr 1
      ring
    _ = (X ^ 2 - X : Polynomial ℚ).natDegree + X.natDegree := by
      rw [Polynomial.natDegree_mul hquad_ne (by simp)]
    _ = 3 := by
      rw [equal_endpoint_quadratic_natDegree, Polynomial.natDegree_X]

/-- Helper for Example 10.27.4: composing a nonzero polynomial with `X^2 - X` stays nonzero. -/
private theorem equal_endpoint_comp_quadratic_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) :
    p.comp (X ^ 2 - X) ≠ 0 := by
  intro hcomp
  rcases (Polynomial.comp_eq_zero_iff (p := p) (q := (X ^ 2 - X : Polynomial ℚ))).1 hcomp with
    hp0 | hconst
  · exact hp hp0
  · exact equal_endpoint_quadratic_monic.ne_zero (by simpa using hconst.2)

/-- Helper for Example 10.27.4: forgetting the subtype after evaluating at `A = z^2 - z` gives
ordinary composition by `X^2 - X`. -/
private theorem equal_endpoint_aeval_quadratic_val (p : ℚ[X]) :
    ↑((Polynomial.aeval equal_endpoint_quad) p) = p.comp (X ^ 2 - X) := by
  let valAlgHom : R →ₐ[ℚ] Polynomial ℚ :=
    { toRingHom := (equal_endpoint_poly_subring ℚ).subtype
      commutes' := by intro q; rfl }
  -- We evaluate in the subring and then forget to the ambient polynomial ring.
  simpa [valAlgHom, Polynomial.comp_eq_aeval, equal_endpoint_quad] using
    (Polynomial.aeval_algHom_apply valAlgHom equal_endpoint_quad p).symm

/-- Helper for Example 10.27.4: the monic `Y`-relation vanishes under
`A = z^2 - z`, `B = z^3 - z^2`. -/
private theorem equal_endpoint_monic_relation_mem_ker :
    equal_endpoint_presentation equal_endpoint_monic_relation = 0 := by
  -- Evaluating the monic relation gives the algebraic identity `B^2 - A * B - A^3 = 0`.
  apply Subtype.ext
  simp only [equal_endpoint_presentation, equal_endpoint_monic_relation, map_sub, map_mul, map_pow,
    Polynomial.aevalAeval_C, Polynomial.aevalAeval_Y, Polynomial.aeval_X,
    equal_endpoint_quad, equal_endpoint_cubic]
  simp
  ring

/-- Helper for Example 10.27.4: the principal ideals generated by the textbook relation and the
monic partner coincide. -/
private theorem equal_endpoint_relation_span_eq_span_monic_partner :
    Ideal.span ({equal_endpoint_relation} : Set ℚ[X][Y]) =
      Ideal.span ({equal_endpoint_monic_relation} : Set ℚ[X][Y]) := by
  -- Passing to the monic partner only changes the generator by the unit `-1`.
  rw [equal_endpoint_relation_eq_neg_monic_relation, Ideal.span_singleton_neg]

/-- Helper for Example 10.27.4: a linear remainder in `Y` vanishes after evaluation only when both
coefficients vanish. -/
private theorem equal_endpoint_presentation_linear_remainder_eq_zero_iff
    (p q : ℚ[X]) :
    equal_endpoint_presentation (C p + C q * Y) = 0 ↔ p = 0 ∧ q = 0 := by
  constructor
  · intro h
    have hval : p.comp (X ^ 2 - X) + q.comp (X ^ 2 - X) * (X ^ 3 - X ^ 2) = 0 := by
      -- We first translate the kernel condition into an identity in `ℚ[z]`.
      have hval' := congrArg Subtype.val h
      simp only [equal_endpoint_presentation, map_add, map_mul, Polynomial.aevalAeval_C,
        Polynomial.aevalAeval_Y, equal_endpoint_quad,
        equal_endpoint_cubic] at hval'
      have hval'' :
          (↑((Polynomial.aeval equal_endpoint_quad) p) : Polynomial ℚ) +
              ↑((Polynomial.aeval equal_endpoint_quad) q) *
                (X ^ 3 - X ^ 2 : Polynomial ℚ) = (0 : Polynomial ℚ) := by
        simpa [Subring.coe_add, Subring.coe_mul, Subring.coe_zero] using hval'
      rw [equal_endpoint_aeval_quadratic_val, equal_endpoint_aeval_quadratic_val] at hval''
      exact hval''
    have hq0 : q = 0 := by
      by_contra hq
      have hqcomp_ne : q.comp (X ^ 2 - X) ≠ 0 := equal_endpoint_comp_quadratic_ne_zero hq
      have hp_ne : p ≠ 0 := by
        intro hp
        have hprod : q.comp (X ^ 2 - X) * (X ^ 3 - X ^ 2) = 0 := by
          simpa [hp] using hval
        rcases mul_eq_zero.mp hprod with hqcomp0 | hcubic0
        · exact hqcomp_ne hqcomp0
        · exact (by
            have : (X ^ 3 - X ^ 2 : Polynomial ℚ) ≠ 0 := by
              intro hzero
              simpa [hzero] using equal_endpoint_cubic_natDegree
            exact this hcubic0)
      have hdeg : p.natDegree * 2 = q.natDegree * 2 + 3 := by
        have hpeq : p.comp (X ^ 2 - X) = -(q.comp (X ^ 2 - X) * (X ^ 3 - X ^ 2)) := by
          simpa using eq_neg_of_add_eq_zero_left hval
        -- The left-hand side has even degree, while the right-hand side has odd degree.
        calc
          p.natDegree * 2 = (p.comp (X ^ 2 - X)).natDegree := by
            rw [Polynomial.natDegree_comp, equal_endpoint_quadratic_natDegree]
          _ = (-(q.comp (X ^ 2 - X) * (X ^ 3 - X ^ 2))).natDegree := by rw [hpeq]
          _ = (q.comp (X ^ 2 - X) * (X ^ 3 - X ^ 2)).natDegree := by simp
          _ = (q.comp (X ^ 2 - X)).natDegree + (X ^ 3 - X ^ 2 : Polynomial ℚ).natDegree := by
            rw [Polynomial.natDegree_mul hqcomp_ne (by
              intro hzero
              simpa [hzero] using equal_endpoint_cubic_natDegree)]
          _ = q.natDegree * 2 + 3 := by
            rw [Polynomial.natDegree_comp, equal_endpoint_quadratic_natDegree,
              equal_endpoint_cubic_natDegree]
      omega
    have hp0 : p = 0 := by
      by_contra hp
      exact equal_endpoint_comp_quadratic_ne_zero hp (by simpa [hq0] using hval)
    exact ⟨hp0, hq0⟩
  · rintro ⟨rfl, rfl⟩
    -- The converse is immediate from the zero remainder.
    simp

/-- Helper for Example 10.27.4: every kernel element is a multiple of the monic `Y`-relation. -/
private theorem equal_endpoint_mem_span_monic_relation_of_mem_ker (F : ℚ[X][Y])
    (hF : equal_endpoint_presentation F = 0) :
    F ∈ Ideal.span ({equal_endpoint_monic_relation} : Set ℚ[X][Y]) := by
  let G : ℚ[X][Y] := equal_endpoint_monic_relation
  let r : ℚ[X][Y] := F %ₘ G
  have hdecomp : F = r + G * (F /ₘ G) := by
    -- Divide by the monic relation in the outer variable `Y`.
    simpa [G, r, add_comm, add_left_comm, add_assoc] using
      (Polynomial.modByMonic_add_div F G).symm
  have hrker : equal_endpoint_presentation r = 0 := by
    -- The quotient term vanishes because `G` itself lies in the kernel.
    rw [hdecomp, map_add, map_mul, equal_endpoint_monic_relation_mem_ker, zero_mul, add_zero] at hF
    exact hF
  have hrdeg : r.natDegree ≤ 1 := by
    by_cases hr0 : r = 0
    · simp [hr0]
    · have hrlt : r.degree < 2 := by
        simpa [r, G, equal_endpoint_monic_relation_degree] using
          (Polynomial.degree_modByMonic_lt F equal_endpoint_monic_relation_monic)
      have hnat : r.natDegree < 2 := (Polynomial.natDegree_lt_iff_degree_lt hr0).2 hrlt
      omega
  rcases Polynomial.exists_eq_X_add_C_of_natDegree_le_one hrdeg with ⟨q, p, hr⟩
  have hrker' : equal_endpoint_presentation (C p + C q * Y) = 0 := by
    -- We rewrite the remainder into the linear normal form handled above.
    simpa [r, hr, add_comm, add_left_comm, add_assoc] using hrker
  have hpq0 :
      p = 0 ∧ q = 0 := (equal_endpoint_presentation_linear_remainder_eq_zero_iff p q).1 hrker'
  have hr0 : r = 0 := by
    -- The remainder vanishes, so the original polynomial is divisible by `G`.
    rcases hpq0 with ⟨hp0, hq0⟩
    rw [hr, hp0, hq0]
    simp
  -- We now package the divisibility statement as membership in the principal ideal.
  rw [Ideal.mem_span_singleton]
  refine ⟨F /ₘ G, ?_⟩
  simpa [G, r, hr0, add_comm, add_left_comm, add_assoc]
    using hdecomp

/-- Example 10.27.4 (1): the kernel of `φ` is the principal ideal
`(A^3 - B^2 + AB)`. -/
-- Proof sketch: the displayed relation vanishes under `A = z^2 - z`, `B = z^3 - z^2`, and the
-- example shows that this single relation generates all polynomial relations among those two
-- generators.
theorem equal_endpoint_presentation_ker :
    RingHom.ker equal_endpoint_presentation =
      Ideal.span ({equal_endpoint_relation} : Set ℚ[X][Y]) := by
  -- Route correction: instead of attacking `ker = span` directly, we divide by the monic
  -- `Y`-relation, force the linear remainder to vanish by natDegree parity, and only then
  -- translate back to the textbook generator.
  refine le_antisymm ?_ ?_
  · intro F hF
    have hF0 : equal_endpoint_presentation F = 0 := by
      simpa using hF
    -- Kernel elements are divisible by the monic partner, hence by the original relation.
    rw [equal_endpoint_relation_span_eq_span_monic_partner]
    exact equal_endpoint_mem_span_monic_relation_of_mem_ker F hF0
  · refine Ideal.span_le.2 ?_
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change equal_endpoint_presentation equal_endpoint_relation = 0
    -- The original relation is just `-G`, and `G` is already known to vanish.
    calc
      equal_endpoint_presentation equal_endpoint_relation =
          -equal_endpoint_presentation equal_endpoint_monic_relation := by
            rw [equal_endpoint_relation_eq_neg_monic_relation, map_neg]
      _ = 0 := by simp [equal_endpoint_monic_relation_mem_ker]

private theorem equal_endpoint_presentation_range_eq_top :
    equal_endpoint_presentation.range = (⊤ : Subalgebra ℚ R) := by
  rw [eq_top_iff]
  intro x _
  rcases equal_endpoint_presentation_surjective x with ⟨f, rfl⟩
  exact equal_endpoint_presentation.mem_range_self f

/-- Hence `R ≃ ℚ[A, B] / (A^3 - B^2 + AB)`; in Lean, `ℚ[A, B]` is modeled by `ℚ[X][Y]`. -/
noncomputable def equal_endpoint_presentation_quotientEquiv :
    (ℚ[X][Y] ⧸ Ideal.span ({equal_endpoint_relation} : Set ℚ[X][Y])) ≃ₐ[ℚ] R := by
  exact
    (Ideal.quotientEquivAlgOfEq ℚ equal_endpoint_presentation_ker.symm).trans <|
      (Ideal.quotientKerEquivRange equal_endpoint_presentation).trans <|
        (Subalgebra.equivOfEq _ _ equal_endpoint_presentation_range_eq_top).trans
          Subalgebra.topEquiv

private theorem evalAt_X_sub_C_isUnit (a r : ℚ) (h : a ≠ r) :
    IsUnit (evalRingHom r (X - C a)) := by
  -- Over `ℚ`, every nonzero value is a unit, so evaluation is enough.
  simpa [sub_eq_add_neg] using
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h.symm))

/-- The evaluation map on `ℚ[z, 1 / (z - a)]` induced by `z ↦ r`, defined when `a ≠ r`. -/
private noncomputable def awayEval (a r : ℚ) (h : a ≠ r) :
    Localization.Away (X - C a) →ₐ[ℚ] ℚ where
  toRingHom := Localization.awayLift (evalRingHom r) (X - C a) (evalAt_X_sub_C_isUnit a r h)
  commutes' q := by simp

@[simp] private theorem awayEval_algebraMap (a r : ℚ) (h : a ≠ r) (f : Polynomial ℚ) :
    awayEval a r h (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) f) =
      evalRingHom r f :=
  by simp [awayEval, Localization.awayLift]

/-- Helper for Example 10.27.4: evaluating the distinguished inverse in the localization gives the
expected scalar inverse. -/
private theorem awayEval_invSelf (a r : ℚ) (h : a ≠ r) :
    awayEval a r h (IsLocalization.Away.invSelf (X - C a)) = (r - a)⁻¹ := by
  let v : ℚ := (r - a)⁻¹
  have hr0 : r - a ≠ 0 := sub_ne_zero.mpr h.symm
  have hv : evalRingHom r (X - C a) * v = 1 := by
    -- This is the defining inverse relation in the target field `ℚ`.
    simpa [v, sub_eq_add_neg] using (mul_inv_cancel₀ hr0)
  -- The localization lift sends the formal inverse of `X - a` to the scalar inverse of `r - a`.
  simpa [awayEval, v, sub_eq_add_neg, IsLocalization.Away.invSelf, Localization.mk_eq_mk'] using
    (Localization.awayLift_mk (evalRingHom r) (X - C a) 1 v hv 1)

/-- The ring `R_a = {f ∈ ℚ[z, 1 / (z - a)] | f(0) = f(1)}` from the example, realized as the
equalizer of the two extended evaluation maps as a `ℚ`-subalgebra. -/
noncomputable def equal_endpoint_away (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Subalgebra ℚ (Localization.Away (X - C a)) :=
  AlgHom.equalizer (awayEval a 0 h0) (awayEval a 1 h1)

/-- A polynomial in `R` maps into `R_a` under the localization map. -/
-- Proof sketch: the two localized evaluations of the image reduce to the evaluations at `0` and
-- `1` on the original polynomial via `awayEval_algebraMap`, and these agree
-- because `f ∈ R`.
private theorem algebraMap_mem_equal_endpoint_away (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1)
    (f : R) :
    algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) f.1 ∈
      equal_endpoint_away a h0 h1 := by
  change awayEval a 0 h0 (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) f.1) =
      awayEval a 1 h1 (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) f.1)
  simpa [awayEval_algebraMap, Polynomial.coeff_zero_eq_eval_zero] using
    (mem_equal_endpoint_poly_subring_iff ℚ f.1).mp f.2

/-- The point of `Spec(R)` corresponding to the evaluation ideal `m_r`. -/
def equal_endpoint_eval_point (r : ℚ) : PrimeSpectrum R :=
  comap ((evalRingHom r).comp (equal_endpoint_poly_subring ℚ).subtype) (closedPoint ℚ)

/-- The localized equal-endpoint ring carries its canonical algebra structure over `R`. -/
instance (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Algebra R (equal_endpoint_away a h0 h1) :=
  (((algebraMap (Polynomial ℚ) (Localization.Away (X - C a))).comp
        (equal_endpoint_poly_subring ℚ).subtype).codRestrict
      (equal_endpoint_away a h0 h1)
      (algebraMap_mem_equal_endpoint_away a h0 h1)).toAlgebra

/-- The element `z^2 - z` of `R_a`. -/
noncomputable def equal_endpoint_away_quadratic (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    equal_endpoint_away a h0 h1 :=
  ⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X),
    algebraMap_mem_equal_endpoint_away a h0 h1 equal_endpoint_quad⟩

private theorem equal_endpoint_cube_minus_linear_mem :
    (X ^ 3 - X : Polynomial ℚ) ∈ R := by
  rw [mem_equal_endpoint_poly_subring_iff]
  norm_num

private def equal_endpoint_cube_minus_linear : R :=
  ⟨X ^ 3 - X, equal_endpoint_cube_minus_linear_mem⟩

/-- The element `z^3 - z` of `R_a`. -/
noncomputable def equal_endpoint_away_cubicMinusLinear
    (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    equal_endpoint_away a h0 h1 :=
  ⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 3 - X),
    algebraMap_mem_equal_endpoint_away a h0 h1 equal_endpoint_cube_minus_linear⟩

private theorem equal_endpoint_away_linearFractional_mem (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) :
    algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) X +
        algebraMap ℚ (Localization.Away (X - C a)) (a ^ 2 - a) *
          IsLocalization.Away.invSelf (X - C a) ∈
      equal_endpoint_away a h0 h1 := by
  -- Both endpoint evaluations reduce to the same scalar `1 - a`.
  change awayEval a 0 h0 _ = awayEval a 1 h1 _
  simp [awayEval_algebraMap]
  rw [awayEval_invSelf (a := a) (r := 0) h0, awayEval_invSelf (a := a) (r := 1) h1]
  have h1' : (1 - a : ℚ) ≠ 0 := sub_ne_zero.mpr h1.symm
  field_simp [h0, h1']
  ring

/-- The element `(a^2 - a)/(z - a) + z` of `R_a`. -/
noncomputable def equal_endpoint_away_linearFractional
    (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    equal_endpoint_away a h0 h1 :=
  ⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) X +
      algebraMap ℚ (Localization.Away (X - C a)) (a ^ 2 - a) *
        IsLocalization.Away.invSelf (X - C a),
    equal_endpoint_away_linearFractional_mem a h0 h1⟩

/-- Example 10.27.4 (2): for `a ≠ 0, 1`, the ring `R_a` is generated as a `ℚ`-algebra by the three
displayed elements `z^2 - z`, `z^3 - z`, and `(a^2 - a)/(z - a) + z`. -/
theorem equal_endpoint_away_adjoin_eq_top (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Algebra.adjoin ℚ
        ({ equal_endpoint_away_quadratic a h0 h1
         , equal_endpoint_away_cubicMinusLinear a h0 h1
         , equal_endpoint_away_linearFractional a h0 h1 } :
          Set (equal_endpoint_away a h0 h1)) =
      ⊤ := by
  sorry

/-- Example 10.27.4 (3): for `a ≠ 0, 1`, the ring `R_a` is a finitely generated `ℚ`-algebra. -/
theorem equal_endpoint_away_finiteType (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Algebra.FiniteType ℚ (equal_endpoint_away a h0 h1) := by
  let s : Set (equal_endpoint_away a h0 h1) :=
    { equal_endpoint_away_quadratic a h0 h1
    , equal_endpoint_away_cubicMinusLinear a h0 h1
    , equal_endpoint_away_linearFractional a h0 h1 }
  have hs : s.Finite := by
    simp [s]
  let hft : Algebra.FiniteType ℚ (Algebra.adjoin ℚ s) :=
    Algebra.FiniteType.adjoin_of_finite hs
  let e : Algebra.adjoin ℚ s ≃ₐ[ℚ] equal_endpoint_away a h0 h1 :=
    (Subalgebra.equivOfEq _ _ (equal_endpoint_away_adjoin_eq_top a h0 h1)).trans
      Subalgebra.topEquiv
  exact hft.equiv e

instance (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Algebra.FiniteType ℚ (equal_endpoint_away a h0 h1) :=
  equal_endpoint_away_finiteType a h0 h1

/-- Example 10.27.4 (4): for `a ∈ ℚ \ {0, 1/2, 1}`, the inclusion `R ⊆ R_a` induces a
map on prime spectra that is an open embedding, and its image is the complement of the point
corresponding to the evaluation ideal `m_a`. -/
-- Proof sketch: cover `Spec(R_a)` by the two distinguished opens described in the example,
-- identify each restriction with a localization of `R` via Lemma `10.17.5`, and glue the
-- resulting local open embeddings; the image calculation is exactly the statement that only `m_a`
-- is omitted.
theorem equal_endpoint_away_prime_spectrum_openEmbedding_range_eq (a : ℚ)
    (h0 : a ≠ 0) (hhalf : a ≠ (1 / 2 : ℚ)) (h1 : a ≠ 1) :
    IsOpenEmbedding
        (comap (algebraMap R (equal_endpoint_away a h0 h1))) ∧
      Set.range
          (comap (algebraMap R (equal_endpoint_away a h0 h1))) =
        ({equal_endpoint_eval_point a} : Set (PrimeSpectrum R))ᶜ :=
  sorry

/-- The ring `R_a` is not a localization of `R` at any multiplicative subset. -/
-- Proof sketch: as explained in the example, every localization of `R` introduces additional
-- units, while the units of `R_a` are still exactly the nonzero rationals because
-- `a ≠ 0, 1, 1/2`.
theorem equal_endpoint_away_not_isLocalization (a : ℚ)
    (h0 : a ≠ 0) (hhalf : a ≠ (1 / 2 : ℚ)) (h1 : a ≠ 1)
    (S : Submonoid R) :
    ¬ IsLocalization S (equal_endpoint_away a h0 h1) := sorry
