import Mathlib
import stacks_proof.stacks_project.Chap10.EqualEndpointRing

-- Declarations for this item will be appended below by the statement pipeline.

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
  simp only [equal_endpoint_algebraMap_val, aevalAevalEquiv_apply_apply, Subring.coe_add,
    Subring.coe_mul] at hPval ⊢
  rw [hPval]
  simp only [C_0, add_zero]
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
@[stacks 00F1]
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
  simp only [map_sub, map_pow, map_add, awayEval_algebraMap, coe_evalRingHom, eval_X, map_mul,
    AlgHom.commutes, Algebra.algebraMap_self, eq_ratCast, Rat.cast_eq_id, id_eq, zero_add]
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

/-- Helper for Chap10 Example 10 27 4: multiplying by `X^2 - X` forces membership in the
equal-endpoint away subalgebra. -/
private theorem equal_endpoint_away_quadratic_mul_mem (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1)
    (y : Localization.Away (X - C a)) :
    algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) * y ∈
      equal_endpoint_away a h0 h1 := by
  -- The quadratic factor vanishes at both endpoint evaluations, so the product does too.
  change awayEval a 0 h0 _ = awayEval a 1 h1 _
  simp [awayEval_algebraMap]

/-- Helper for Chap10 Example 10 27 4: the divided quadratic `((X^2-X)/(X-a))` is generated by
the displayed linear-fractional element. -/
private theorem equal_endpoint_away_quadratic_inv_mem_adjoin (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) :
    (⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
        IsLocalization.Away.invSelf (X - C a),
      equal_endpoint_away_quadratic_mul_mem a h0 h1
        (IsLocalization.Away.invSelf (X - C a))⟩ :
        equal_endpoint_away a h0 h1) ∈
      Algebra.adjoin ℚ
        ({ equal_endpoint_away_quadratic a h0 h1
         , equal_endpoint_away_cubicMinusLinear a h0 h1
         , equal_endpoint_away_linearFractional a h0 h1 } :
          Set (equal_endpoint_away a h0 h1)) := by
  let A : Subalgebra ℚ (equal_endpoint_away a h0 h1) :=
    Algebra.adjoin ℚ
      ({ equal_endpoint_away_quadratic a h0 h1
       , equal_endpoint_away_cubicMinusLinear a h0 h1
       , equal_endpoint_away_linearFractional a h0 h1 } :
        Set (equal_endpoint_away a h0 h1))
  have hlin : equal_endpoint_away_linearFractional a h0 h1 ∈ A := by
    -- One of the displayed generators is the linear-fractional element itself.
    exact Algebra.subset_adjoin (by simp)
  have hconst : algebraMap ℚ (equal_endpoint_away a h0 h1) (a - 1) ∈ A := by
    -- Scalar constants are always in a `ℚ`-subalgebra.
    exact Subalgebra.algebraMap_mem A (a - 1)
  have hsum :
      equal_endpoint_away_linearFractional a h0 h1 +
          algebraMap ℚ (equal_endpoint_away a h0 h1) (a - 1) ∈ A :=
    A.add_mem hlin hconst
  -- The polynomial identity `X^2-X = (X-a)(X+a-1)+(a^2-a)` identifies this element.
  convert hsum using 1
  apply Subtype.ext
  change
    algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
        IsLocalization.Away.invSelf (X - C a) =
      (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) X +
          algebraMap ℚ (Localization.Away (X - C a)) (a ^ 2 - a) *
            IsLocalization.Away.invSelf (X - C a)) +
        algebraMap ℚ (Localization.Away (X - C a)) (a - 1)
  have hv : algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X - C a) *
      IsLocalization.Away.invSelf (X - C a) = 1 :=
    IsLocalization.Away.mul_invSelf (S := Localization.Away (X - C a)) (X - C a)
  have hCsub : C (a - 1) = (C a - 1 : Polynomial ℚ) := by
    rw [← C_1, ← C_sub]
  have hCquad : C (a ^ 2 - a) = (C a * C a - C a : Polynomial ℚ) := by
    rw [← C_mul, ← C_sub]
    congr 1
    ring
  have hpoly :
      (X ^ 2 - X : Polynomial ℚ) = (X - C a) * (X + C (a - 1)) + C (a ^ 2 - a) := by
    -- Normalize the scalar coefficients before using the ring tactic.
    rw [hCsub, hCquad]
    ring
  rw [hpoly]
  simp only [map_add, map_mul]
  rw [add_mul]
  rw [mul_comm (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X - C a))
    (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) X +
      algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (C (a - 1)))]
  rw [mul_assoc, hv, mul_one]
  have hscalar₁ :
      algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (C (a - 1)) =
        algebraMap ℚ (Localization.Away (X - C a)) (a - 1) := by
    rw [Polynomial.C_eq_algebraMap]
    exact IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (Localization.Away (X - C a)) (a - 1)
  have hscalar₂ :
      algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (C (a ^ 2 - a)) =
        algebraMap ℚ (Localization.Away (X - C a)) (a ^ 2 - a) := by
    rw [Polynomial.C_eq_algebraMap]
    exact IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (Localization.Away (X - C a)) (a ^ 2 - a)
  rw [hscalar₁, hscalar₂]
  ring

/-- Helper for Chap10 Example 10 27 4: the product `(X^2-X)(X-a)` is generated by the quadratic
and cubic-minus-linear displayed elements. -/
private theorem equal_endpoint_away_quadratic_linearFactor_mem_adjoin (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) :
    (⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
        algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X - C a),
      equal_endpoint_away_quadratic_mul_mem a h0 h1
        (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X - C a))⟩ :
        equal_endpoint_away a h0 h1) ∈
      Algebra.adjoin ℚ
        ({ equal_endpoint_away_quadratic a h0 h1
         , equal_endpoint_away_cubicMinusLinear a h0 h1
         , equal_endpoint_away_linearFractional a h0 h1 } :
          Set (equal_endpoint_away a h0 h1)) := by
  let A : Subalgebra ℚ (equal_endpoint_away a h0 h1) :=
    Algebra.adjoin ℚ
      ({ equal_endpoint_away_quadratic a h0 h1
       , equal_endpoint_away_cubicMinusLinear a h0 h1
       , equal_endpoint_away_linearFractional a h0 h1 } :
        Set (equal_endpoint_away a h0 h1))
  have hcubic : equal_endpoint_away_cubicMinusLinear a h0 h1 ∈ A := by
    -- One of the displayed generators is `X^3-X`.
    exact Algebra.subset_adjoin (by simp)
  have hquad : equal_endpoint_away_quadratic a h0 h1 ∈ A := by
    -- One of the displayed generators is `X^2-X`.
    exact Algebra.subset_adjoin (by simp)
  have hscaled :
      algebraMap ℚ (equal_endpoint_away a h0 h1) (a + 1) *
          equal_endpoint_away_quadratic a h0 h1 ∈ A :=
    A.mul_mem (Subalgebra.algebraMap_mem A (a + 1)) hquad
  have hdiff :
      equal_endpoint_away_cubicMinusLinear a h0 h1 -
          algebraMap ℚ (equal_endpoint_away a h0 h1) (a + 1) *
            equal_endpoint_away_quadratic a h0 h1 ∈ A :=
    A.sub_mem hcubic hscaled
  -- Expand `(X^2-X)(X-a)` as `(X^3-X) - (a+1)(X^2-X)`.
  convert hdiff using 1
  apply Subtype.ext
  change
    algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
        algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X - C a) =
      algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 3 - X) -
        algebraMap ℚ (Localization.Away (X - C a)) (a + 1) *
          algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X)
  have hC : C (1 + a) = (1 : Polynomial ℚ) + C a := by
    rw [← C_1, ← C_add]
  have hpoly :
      ((X ^ 2 - X : Polynomial ℚ) * (X - C a)) =
        (X ^ 3 - X) - C (a + 1) * (X ^ 2 - X) := by
    -- The only non-normal part is the scalar `C (a+1)`.
    ring_nf
    rw [hC]
    ring_nf
  rw [← map_mul, hpoly, map_sub, map_mul]
  have hscalar :
      algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (C (a + 1)) =
        algebraMap ℚ (Localization.Away (X - C a)) (a + 1) := by
    rw [Polynomial.C_eq_algebraMap]
    exact IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (Localization.Away (X - C a)) (a + 1)
  rw [hscalar]

/-- Helper for Chap10 Example 10 27 4: after matching the two endpoint values of a cleared
numerator, the difference is divisible by the quadratic `X^2 - X`. -/
private theorem polynomial_sub_endpoint_scaled_linearFactor_pow_quadratic_factor
    (a c : ℚ) (n : ℕ) (p : Polynomial ℚ)
    (h0 : p.eval 0 = c * ((0 : ℚ) - a) ^ n)
    (h1 : p.eval 1 = c * ((1 : ℚ) - a) ^ n) :
    ∃ g : Polynomial ℚ,
      p = C c * (X - C a) ^ n + (X ^ 2 - X) * g := by
  let f : Polynomial ℚ := p - C c * (X - C a) ^ n
  have hf0 : f.eval 0 = 0 := by
    -- The chosen scalar cancels the cleared numerator at the endpoint `0`.
    simp [f, h0]
  have hf1 : f.eval 1 = 0 := by
    -- The same scalar cancels the cleared numerator at the endpoint `1`.
    simp [f, h1]
  have hx : (X : Polynomial ℚ) ∣ f := by
    -- Vanishing at `0` gives divisibility by `X`.
    have h := Polynomial.X_sub_C_dvd_sub_C_eval (p := f) (a := (0 : ℚ))
    simpa [hf0] using h
  have hx1 : (X - 1 : Polynomial ℚ) ∣ f := by
    -- Vanishing at `1` gives divisibility by `X - 1`.
    rw [show (1 : Polynomial ℚ) = C (1 : ℚ) by simp]
    have h := Polynomial.X_sub_C_dvd_sub_C_eval (p := f) (a := (1 : ℚ))
    simpa [hf1] using h
  have hcoprime : IsCoprime (X : Polynomial ℚ) (X - 1) := by
    -- The two linear factors have distinct roots, so their product divides `f`.
    simpa using
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (a := (0 : ℚ)) (b := (1 : ℚ))
        (show IsUnit ((0 : ℚ) - 1) by
          exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr zero_ne_one)))
  rcases hcoprime.mul_dvd hx hx1 with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  have hf : f = (X ^ 2 - X) * g := by
    -- Rewrite the product of the two coprime linear factors as the quadratic.
    calc
      f = X * (X - 1) * g := hg
      _ = (X ^ 2 - X) * g := by ring
  -- Undo the subtraction that defined `f`.
  calc
    p = C c * (X - C a) ^ n + f := by
      simp [f]
    _ = C c * (X - C a) ^ n + (X ^ 2 - X) * g := by rw [hf]

/-- Helper for Chap10 Example 10 27 4: every element of `R_a` has the source normal form
`c + (X^2-X) y` in the away localization. -/
private theorem equal_endpoint_away_constant_add_quadratic_mul (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1)
    (x : equal_endpoint_away a h0 h1) :
    ∃ c : ℚ, ∃ y : Localization.Away (X - C a),
      (x : Localization.Away (X - C a)) =
        algebraMap ℚ (Localization.Away (X - C a)) c +
          algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) * y := by
  let L := Localization.Away (X - C a)
  let v : Polynomial ℚ := X - C a
  let q : Polynomial ℚ := X ^ 2 - X
  let sec := IsLocalization.Away.sec v (x : L)
  let p : Polynomial ℚ := sec.1
  let n : ℕ := sec.2
  let c : ℚ := awayEval a 0 h0 (x : L)
  have hxsec :
      (x : L) * algebraMap (Polynomial ℚ) L (v ^ n) =
        algebraMap (Polynomial ℚ) L p := by
    -- Clear one power of `X-a` using the canonical section for the away localization.
    simpa [L, v, sec, p, n] using
      IsLocalization.Away.sec_spec (x := v) (S := L) (s := (x : L))
  have hxendpoint :
      awayEval a 0 h0 (x : L) = awayEval a 1 h1 (x : L) := by
    -- Membership in the equalizer is exactly equality of the two extended endpoint maps.
    exact x.property
  have hp0 : p.eval 0 = c * ((0 : ℚ) - a) ^ n := by
    -- Evaluating the cleared equation at `0` determines the numerator value there.
    have h := congrArg (awayEval a 0 h0) hxsec
    simpa [L, c, v, p, n, awayEval_algebraMap, map_pow, sub_eq_add_neg] using h.symm
  have hp1 : p.eval 1 = c * ((1 : ℚ) - a) ^ n := by
    -- The equalizer condition identifies the scalar used at the endpoint `1`.
    have h := congrArg (awayEval a 1 h1) hxsec
    simpa [L, c, hxendpoint, v, p, n, awayEval_algebraMap, map_pow, sub_eq_add_neg] using h.symm
  rcases polynomial_sub_endpoint_scaled_linearFactor_pow_quadratic_factor a c n p hp0 hp1 with
    ⟨g, hp⟩
  let t : L := IsLocalization.Away.invSelf v ^ n
  refine ⟨c, algebraMap (Polynomial ℚ) L g * t, ?_⟩
  have hcancel : algebraMap (Polynomial ℚ) L (v ^ n) * t = 1 := by
    -- Multiplying by the matching power of the distinguished inverse divides by the
    -- cleared denominator.
    have hv : algebraMap (Polynomial ℚ) L v * IsLocalization.Away.invSelf v = 1 :=
      IsLocalization.Away.mul_invSelf (S := L) v
    change algebraMap (Polynomial ℚ) L (v ^ n) * IsLocalization.Away.invSelf v ^ n = 1
    rw [map_pow, ← mul_pow, hv, one_pow]
  have hscalar :
      algebraMap (Polynomial ℚ) L (C c) = algebraMap ℚ L c := by
    simpa [Polynomial.C_eq_algebraMap] using
      IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) L c
  -- Multiply the cleared numerator identity by the inverse power to recover `x`.
  calc
    (x : L) = (x : L) * (algebraMap (Polynomial ℚ) L (v ^ n) * t) := by
      rw [hcancel, mul_one]
    _ = ((x : L) * algebraMap (Polynomial ℚ) L (v ^ n)) * t := by
      rw [mul_assoc]
    _ = algebraMap (Polynomial ℚ) L p * t := by rw [hxsec]
    _ = algebraMap (Polynomial ℚ) L (C c * v ^ n + q * g) * t := by rw [hp]
    _ =
        (algebraMap (Polynomial ℚ) L (C c) * algebraMap (Polynomial ℚ) L (v ^ n) +
            algebraMap (Polynomial ℚ) L q * algebraMap (Polynomial ℚ) L g) * t := by
      rw [map_add, map_mul, map_mul]
    _ =
        algebraMap (Polynomial ℚ) L (C c) *
            (algebraMap (Polynomial ℚ) L (v ^ n) * t) +
          algebraMap (Polynomial ℚ) L q *
            (algebraMap (Polynomial ℚ) L g * t) := by
      rw [add_mul]
      rw [mul_assoc]
      rw [mul_assoc]
    _ =
        algebraMap ℚ L c +
          algebraMap (Polynomial ℚ) L (X ^ 2 - X) *
            (algebraMap (Polynomial ℚ) L g * t) := by
      rw [hcancel, hscalar, mul_one]

/-- Helper for Chap10 Example 10 27 4: the quadratic is expressed in powers of the shifted
linear factor `X - a`. -/
private theorem equal_endpoint_quadratic_eq_shifted_linearFactor (a : ℚ) :
    (X ^ 2 - X : Polynomial ℚ) =
      (X - C a) ^ 2 + C (2 * a - 1) * (X - C a) + C (a ^ 2 - a) := by
  -- This is the polynomial identity driving the inverse-power recurrence.
  have hb : C (2 * a - 1) = (2 : Polynomial ℚ) * C a - 1 := by
    rw [← C_ofNat 2, ← C_mul, ← C_1, ← C_sub]
  have hd : C (a ^ 2 - a) = C a ^ 2 - C a := by
    rw [← C_pow, ← C_sub]
  rw [hb, hd]
  ring

/-- Helper for Chap10 Example 10 27 4: the scalar `a^2 - a` is nonzero away from the endpoints. -/
private theorem equal_endpoint_endpointProduct_ne_zero (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    a ^ 2 - a ≠ 0 := by
  -- Factor the scalar as `a * (a - 1)` and use the two endpoint exclusions.
  have hsub : a - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hmul : a * (a - 1) ≠ 0 := mul_ne_zero h0 hsub
  simpa [pow_two, mul_sub] using hmul

/-- Helper for Chap10 Example 10 27 4: multiplying by `X-a` cancels one matching power of
`invSelf (X-a)`. -/
private theorem equal_endpoint_away_linearFactor_mul_invSelf_pow_cancel (a : ℚ) (m : ℕ) :
    algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X - C a) *
        IsLocalization.Away.invSelf (X - C a) ^ (m + 1) =
      IsLocalization.Away.invSelf (X - C a) ^ m := by
  let L := Localization.Away (X - C a)
  let v : Polynomial ℚ := X - C a
  let i : L := IsLocalization.Away.invSelf v
  have hv : algebraMap (Polynomial ℚ) L v * i = 1 :=
    IsLocalization.Away.mul_invSelf (S := L) v
  -- Commute the distinguished inverse power next to the factor it inverts.
  calc
    algebraMap (Polynomial ℚ) L v * i ^ (m + 1) = i ^ m * (algebraMap (Polynomial ℚ) L v * i) := by
      ring
    _ = i ^ m := by rw [hv, mul_one]

/-- Helper for Chap10 Example 10 27 4: two powers of `X-a` cancel two matching powers of
`invSelf (X-a)`. -/
private theorem equal_endpoint_away_linearFactor_sq_mul_invSelf_pow_cancel (a : ℚ) (m : ℕ) :
    algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X - C a) ^ 2 *
        IsLocalization.Away.invSelf (X - C a) ^ (m + 2) =
      IsLocalization.Away.invSelf (X - C a) ^ m := by
  let L := Localization.Away (X - C a)
  let v : Polynomial ℚ := X - C a
  let i : L := IsLocalization.Away.invSelf v
  -- Cancel one inverse at a time so later recurrence proofs avoid broad unfolding.
  calc
    algebraMap (Polynomial ℚ) L v ^ 2 * i ^ (m + 2) =
        algebraMap (Polynomial ℚ) L v * (algebraMap (Polynomial ℚ) L v * i ^ (m + 2)) := by
      ring
    _ = algebraMap (Polynomial ℚ) L v *
          (algebraMap (Polynomial ℚ) L v * i ^ ((m + 1) + 1)) := by
      rw [show m + 2 = (m + 1) + 1 by omega]
    _ = algebraMap (Polynomial ℚ) L v * i ^ (m + 1) := by
      rw [equal_endpoint_away_linearFactor_mul_invSelf_pow_cancel a (m + 1)]
    _ = i ^ m := equal_endpoint_away_linearFactor_mul_invSelf_pow_cancel a m

/-- Helper for Chap10 Example 10 27 4: the inverse-power recurrence for
`(X^2-X) * invSelf (X-a)^n`. -/
private theorem equal_endpoint_away_quadratic_invSelf_recurrence (a : ℚ) (n : ℕ)
    (hd : a ^ 2 - a ≠ 0) :
    algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
        IsLocalization.Away.invSelf (X - C a) ^ (n + 2) =
      algebraMap ℚ (Localization.Away (X - C a)) (a ^ 2 - a)⁻¹ *
        ((algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
            IsLocalization.Away.invSelf (X - C a)) *
          (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
            IsLocalization.Away.invSelf (X - C a) ^ (n + 1)) -
          algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
            IsLocalization.Away.invSelf (X - C a) ^ n -
          algebraMap ℚ (Localization.Away (X - C a)) (2 * a - 1) *
            (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
              IsLocalization.Away.invSelf (X - C a) ^ (n + 1))) := by
  let L := Localization.Away (X - C a)
  let v : Polynomial ℚ := X - C a
  let i : L := IsLocalization.Away.invSelf v
  let q : L := algebraMap (Polynomial ℚ) L (X ^ 2 - X)
  let b : ℚ := 2 * a - 1
  let d : ℚ := a ^ 2 - a
  have hq :
      q =
        algebraMap (Polynomial ℚ) L v ^ 2 +
          algebraMap ℚ L b * algebraMap (Polynomial ℚ) L v +
          algebraMap ℚ L d := by
    -- Transport the shifted quadratic identity to the away localization.
    dsimp [q, v, b, d]
    rw [equal_endpoint_quadratic_eq_shifted_linearFactor a]
    simp only [map_add, map_mul, map_pow, Polynomial.C_eq_algebraMap]
    rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) L (2 * a - 1),
      IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) L (a ^ 2 - a)]
  have hprod :
      (q * i) * (q * i ^ (n + 1)) =
        q * i ^ n + algebraMap ℚ L b * (q * i ^ (n + 1)) +
          algebraMap ℚ L d * (q * i ^ (n + 2)) := by
    -- Expand one copy of the quadratic and cancel the matching inverse powers.
    calc
      (q * i) * (q * i ^ (n + 1)) = q * (q * i ^ (n + 2)) := by ring
      _ =
          q *
            ((algebraMap (Polynomial ℚ) L v ^ 2 +
                algebraMap ℚ L b * algebraMap (Polynomial ℚ) L v +
                algebraMap ℚ L d) *
              i ^ (n + 2)) := by rw [hq]
      _ =
          q *
            (algebraMap (Polynomial ℚ) L v ^ 2 * i ^ (n + 2) +
              algebraMap ℚ L b * (algebraMap (Polynomial ℚ) L v * i ^ (n + 2)) +
              algebraMap ℚ L d * i ^ (n + 2)) := by ring
      _ = q * (i ^ n + algebraMap ℚ L b * i ^ (n + 1) + algebraMap ℚ L d * i ^ (n + 2)) := by
        rw [equal_endpoint_away_linearFactor_sq_mul_invSelf_pow_cancel a n,
          equal_endpoint_away_linearFactor_mul_invSelf_pow_cancel a (n + 1)]
      _ =
          q * i ^ n + algebraMap ℚ L b * (q * i ^ (n + 1)) +
            algebraMap ℚ L d * (q * i ^ (n + 2)) := by
        ring
  -- Solve the recurrence by dividing by the nonzero rational scalar `a^2-a`.
  calc
    q * i ^ (n + 2) = 1 * (q * i ^ (n + 2)) := by rw [one_mul]
    _ = (algebraMap ℚ L d⁻¹ * algebraMap ℚ L d) * (q * i ^ (n + 2)) := by
      rw [← map_mul]
      simp [d, hd]
    _ = algebraMap ℚ L d⁻¹ * (algebraMap ℚ L d * (q * i ^ (n + 2))) := by ring
    _ =
        algebraMap ℚ L d⁻¹ *
          ((q * i) * (q * i ^ (n + 1)) - q * i ^ n -
            algebraMap ℚ L b * (q * i ^ (n + 1))) := by
      rw [hprod]
      ring

/-- Helper for Chap10 Example 10 27 4: all inverse powers of the divided quadratic lie in the
displayed adjoin. -/
private theorem equal_endpoint_away_quadratic_invSelf_pow_mem_adjoin (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) (n : ℕ) :
    (⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
        IsLocalization.Away.invSelf (X - C a) ^ n,
      equal_endpoint_away_quadratic_mul_mem a h0 h1
        (IsLocalization.Away.invSelf (X - C a) ^ n)⟩ :
        equal_endpoint_away a h0 h1) ∈
      Algebra.adjoin ℚ
        ({ equal_endpoint_away_quadratic a h0 h1
         , equal_endpoint_away_cubicMinusLinear a h0 h1
         , equal_endpoint_away_linearFractional a h0 h1 } :
          Set (equal_endpoint_away a h0 h1)) := by
  let A : Subalgebra ℚ (equal_endpoint_away a h0 h1) :=
    Algebra.adjoin ℚ
      ({ equal_endpoint_away_quadratic a h0 h1
       , equal_endpoint_away_cubicMinusLinear a h0 h1
       , equal_endpoint_away_linearFractional a h0 h1 } :
        Set (equal_endpoint_away a h0 h1))
  let T : ℕ → equal_endpoint_away a h0 h1 := fun m =>
    ⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
        IsLocalization.Away.invSelf (X - C a) ^ m,
      equal_endpoint_away_quadratic_mul_mem a h0 h1
        (IsLocalization.Away.invSelf (X - C a) ^ m)⟩
  have hquad : T 0 ∈ A := by
    -- The zeroth inverse power is the quadratic generator.
    have hgen : equal_endpoint_away_quadratic a h0 h1 ∈ A :=
      Algebra.subset_adjoin (by simp)
    simpa [T, equal_endpoint_away_quadratic] using hgen
  have hinv : T 1 ∈ A := by
    -- The first inverse power is the previously established divided quadratic.
    simpa [T, pow_one] using equal_endpoint_away_quadratic_inv_mem_adjoin a h0 h1
  have hd : a ^ 2 - a ≠ 0 := equal_endpoint_endpointProduct_ne_zero a h0 h1
  have hrec : ∀ m : ℕ, T m ∈ A → T (m + 1) ∈ A → T (m + 2) ∈ A := by
    intro m hm hm1
    have hprod : T 1 * T (m + 1) ∈ A := A.mul_mem hinv hm1
    have hsub : T 1 * T (m + 1) - T m -
        algebraMap ℚ (equal_endpoint_away a h0 h1) (2 * a - 1) * T (m + 1) ∈ A := by
      -- The recurrence uses only subalgebra closure under multiplication, subtraction, and scalars.
      exact A.sub_mem (A.sub_mem hprod hm) (A.mul_mem (Subalgebra.algebraMap_mem A (2 * a - 1)) hm1)
    have hscaled :
        algebraMap ℚ (equal_endpoint_away a h0 h1) (a ^ 2 - a)⁻¹ *
            (T 1 * T (m + 1) - T m -
              algebraMap ℚ (equal_endpoint_away a h0 h1) (2 * a - 1) * T (m + 1)) ∈ A :=
      A.mul_mem (Subalgebra.algebraMap_mem A (a ^ 2 - a)⁻¹) hsub
    -- The ambient recurrence identifies the scaled combination with the next inverse power.
    convert hscaled using 1
    apply Subtype.ext
    simpa [T] using equal_endpoint_away_quadratic_invSelf_recurrence a m hd
  -- A two-step induction propagates the two seed elements through all inverse powers.
  exact Nat.twoStepInduction hquad hinv hrec n

/-- Helper for Chap10 Example 10 27 4: multiplying inverse powers by powers of `X` keeps the
quadratic multiple in the displayed adjoin. -/
private theorem equal_endpoint_away_quadratic_X_pow_invSelf_pow_mem_adjoin (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) (m n : ℕ) :
    (⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
        (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) X ^ m *
          IsLocalization.Away.invSelf (X - C a) ^ n),
      equal_endpoint_away_quadratic_mul_mem a h0 h1
        (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) X ^ m *
          IsLocalization.Away.invSelf (X - C a) ^ n)⟩ :
        equal_endpoint_away a h0 h1) ∈
      Algebra.adjoin ℚ
        ({ equal_endpoint_away_quadratic a h0 h1
         , equal_endpoint_away_cubicMinusLinear a h0 h1
         , equal_endpoint_away_linearFractional a h0 h1 } :
          Set (equal_endpoint_away a h0 h1)) := by
  let A : Subalgebra ℚ (equal_endpoint_away a h0 h1) :=
    Algebra.adjoin ℚ
      ({ equal_endpoint_away_quadratic a h0 h1
       , equal_endpoint_away_cubicMinusLinear a h0 h1
       , equal_endpoint_away_linearFractional a h0 h1 } :
        Set (equal_endpoint_away a h0 h1))
  let U : ℕ → ℕ → equal_endpoint_away a h0 h1 := fun r s =>
    ⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
        (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) X ^ r *
          IsLocalization.Away.invSelf (X - C a) ^ s),
      equal_endpoint_away_quadratic_mul_mem a h0 h1
        (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) X ^ r *
          IsLocalization.Away.invSelf (X - C a) ^ s)⟩
  have hlin : equal_endpoint_away_linearFractional a h0 h1 ∈ A :=
    Algebra.subset_adjoin (by simp)
  -- Induct on the power of `X`; multiplication by the linear-fractional generator raises it by
  -- one, up to a controlled next inverse-power term.
  have hU : ∀ r s : ℕ, U r s ∈ A := by
    intro r
    induction r with
    | zero =>
      intro s
      simpa [U, pow_zero, one_mul] using
        equal_endpoint_away_quadratic_invSelf_pow_mem_adjoin a h0 h1 s
    | succ r ih =>
      intro s
      have hcurrent : U r s ∈ A := ih s
      have hnextInv : U r (s + 1) ∈ A := ih (s + 1)
      have hprod : equal_endpoint_away_linearFractional a h0 h1 * U r s ∈ A :=
        A.mul_mem hlin hcurrent
      have hscaled : algebraMap ℚ (equal_endpoint_away a h0 h1) (a ^ 2 - a) * U r (s + 1) ∈ A :=
        A.mul_mem (Subalgebra.algebraMap_mem A (a ^ 2 - a)) hnextInv
      have hdiff : equal_endpoint_away_linearFractional a h0 h1 * U r s -
          algebraMap ℚ (equal_endpoint_away a h0 h1) (a ^ 2 - a) * U r (s + 1) ∈ A :=
        A.sub_mem hprod hscaled
      -- Expand the linear-fractional generator to isolate the next `X`-power.
      convert hdiff using 1
      apply Subtype.ext
      simp [U, equal_endpoint_away_linearFractional, pow_succ]
      ring
  exact hU m n

/-- Helper for Chap10 Example 10 27 4: arbitrary polynomial numerators times an inverse power,
after multiplication by `X^2-X`, lie in the displayed adjoin. -/
private theorem equal_endpoint_away_quadratic_poly_invSelf_pow_mem_adjoin (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) (p : Polynomial ℚ) (n : ℕ) :
    (⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
        (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) p *
          IsLocalization.Away.invSelf (X - C a) ^ n),
      equal_endpoint_away_quadratic_mul_mem a h0 h1
        (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) p *
          IsLocalization.Away.invSelf (X - C a) ^ n)⟩ :
        equal_endpoint_away a h0 h1) ∈
      Algebra.adjoin ℚ
        ({ equal_endpoint_away_quadratic a h0 h1
         , equal_endpoint_away_cubicMinusLinear a h0 h1
         , equal_endpoint_away_linearFractional a h0 h1 } :
          Set (equal_endpoint_away a h0 h1)) := by
  let A : Subalgebra ℚ (equal_endpoint_away a h0 h1) :=
    Algebra.adjoin ℚ
      ({ equal_endpoint_away_quadratic a h0 h1
       , equal_endpoint_away_cubicMinusLinear a h0 h1
       , equal_endpoint_away_linearFractional a h0 h1 } :
        Set (equal_endpoint_away a h0 h1))
  -- Polynomial induction reduces numerator closure to monomials and additivity.
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
      have hsum :
          (⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
              (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) p *
                IsLocalization.Away.invSelf (X - C a) ^ n),
            equal_endpoint_away_quadratic_mul_mem a h0 h1
              (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) p *
                IsLocalization.Away.invSelf (X - C a) ^ n)⟩ :
              equal_endpoint_away a h0 h1) +
            (⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
              (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) r *
                IsLocalization.Away.invSelf (X - C a) ^ n),
            equal_endpoint_away_quadratic_mul_mem a h0 h1
              (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) r *
                IsLocalization.Away.invSelf (X - C a) ^ n)⟩ :
              equal_endpoint_away a h0 h1) ∈ A := A.add_mem hp hr
      -- The ambient equality is distributivity of the numerator map over addition.
      convert hsum using 1
      apply Subtype.ext
      simp [map_add]
      ring
  | monomial m c =>
      have hpow := equal_endpoint_away_quadratic_X_pow_invSelf_pow_mem_adjoin a h0 h1 m n
      have hscaled :
          algebraMap ℚ (equal_endpoint_away a h0 h1) c *
              (⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) *
                (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) X ^ m *
                  IsLocalization.Away.invSelf (X - C a) ^ n),
              equal_endpoint_away_quadratic_mul_mem a h0 h1
                (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) X ^ m *
                  IsLocalization.Away.invSelf (X - C a) ^ n)⟩ :
                equal_endpoint_away a h0 h1) ∈ A :=
        A.mul_mem (Subalgebra.algebraMap_mem A c) hpow
      -- A monomial numerator is just a scalar multiple of the corresponding `X`-power case.
      convert hscaled using 1
      apply Subtype.ext
      rw [← C_mul_X_pow_eq_monomial]
      simp only [map_mul]
      have hscalar :
          algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (C c) =
            algebraMap ℚ (Localization.Away (X - C a)) c := by
        change
          algebraMap (Polynomial ℚ) (Localization.Away (X - C a))
              (algebraMap ℚ (Polynomial ℚ) c) =
            algebraMap ℚ (Localization.Away (X - C a)) c
        exact (IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ)
          (Localization.Away (X - C a)) c).symm
      rw [hscalar]
      simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
      rw [map_pow]
      ring_nf

/-- Helper for Chap10 Example 10 27 4: every quadratic multiple in the away localization lies in
the algebra generated by the three displayed elements. -/
private theorem equal_endpoint_away_quadratic_mul_mem_adjoin (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1)
    (y : Localization.Away (X - C a)) :
    (⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) * y,
      equal_endpoint_away_quadratic_mul_mem a h0 h1 y⟩ :
        equal_endpoint_away a h0 h1) ∈
      Algebra.adjoin ℚ
        ({ equal_endpoint_away_quadratic a h0 h1
         , equal_endpoint_away_cubicMinusLinear a h0 h1
         , equal_endpoint_away_linearFractional a h0 h1 } :
          Set (equal_endpoint_away a h0 h1)) := by
  let L := Localization.Away (X - C a)
  let v : Polynomial ℚ := X - C a
  let i : L := IsLocalization.Away.invSelf v
  let q : L := algebraMap (Polynomial ℚ) L (X ^ 2 - X)
  rcases IsLocalization.Away.surj v y with ⟨n, p, hy⟩
  have hcancel : algebraMap (Polynomial ℚ) L v ^ n * i ^ n = 1 := by
    -- The denominator supplied by `Away.surj` is canceled by the matching inverse power.
    have hv : algebraMap (Polynomial ℚ) L v * i = 1 :=
      IsLocalization.Away.mul_invSelf (S := L) v
    rw [← mul_pow, hv, one_pow]
  have hy' : y = algebraMap (Polynomial ℚ) L p * i ^ n := by
    -- Rewrite the localized element as a polynomial numerator times the inverse denominator.
    calc
      y = y * (algebraMap (Polynomial ℚ) L v ^ n * i ^ n) := by
        rw [hcancel, mul_one]
      _ = (y * algebraMap (Polynomial ℚ) L v ^ n) * i ^ n := by rw [mul_assoc]
      _ = algebraMap (Polynomial ℚ) L p * i ^ n := by rw [hy]
  have hpoly :=
    equal_endpoint_away_quadratic_poly_invSelf_pow_mem_adjoin a h0 h1 p n
  -- The polynomial-numerator helper is exactly the cleared form of the original element.
  convert hpoly using 1
  apply Subtype.ext
  simp [L, v, i, hy']

/-- Example 10.27.4 (2): for `a ≠ 0, 1`, the ring `R_a` is generated as a `ℚ`-algebra by the three
displayed elements `z^2 - z`, `z^3 - z`, and `(a^2 - a)/(z - a) + z`. -/
@[stacks 00F1]
theorem equal_endpoint_away_adjoin_eq_top (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Algebra.adjoin ℚ
        ({ equal_endpoint_away_quadratic a h0 h1
         , equal_endpoint_away_cubicMinusLinear a h0 h1
         , equal_endpoint_away_linearFractional a h0 h1 } :
          Set (equal_endpoint_away a h0 h1)) =
      ⊤ := by
  rw [eq_top_iff]
  intro x _
  rcases equal_endpoint_away_constant_add_quadratic_mul a h0 h1 x with ⟨c, y, hx⟩
  let z : equal_endpoint_away a h0 h1 :=
    ⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X) * y,
      equal_endpoint_away_quadratic_mul_mem a h0 h1 y⟩
  have hz :
      z ∈ Algebra.adjoin ℚ
        ({ equal_endpoint_away_quadratic a h0 h1
         , equal_endpoint_away_cubicMinusLinear a h0 h1
         , equal_endpoint_away_linearFractional a h0 h1 } :
          Set (equal_endpoint_away a h0 h1)) := by
    -- The Laurent-recursion helper supplies the nonconstant part of the normal form.
    simpa [z] using equal_endpoint_away_quadratic_mul_mem_adjoin a h0 h1 y
  have hc :
      algebraMap ℚ (equal_endpoint_away a h0 h1) c ∈
        Algebra.adjoin ℚ
          ({ equal_endpoint_away_quadratic a h0 h1
           , equal_endpoint_away_cubicMinusLinear a h0 h1
           , equal_endpoint_away_linearFractional a h0 h1 } :
            Set (equal_endpoint_away a h0 h1)) := by
    -- Constants are part of every `ℚ`-subalgebra.
    exact Subalgebra.algebraMap_mem _ c
  have hx' : x = algebraMap ℚ (equal_endpoint_away a h0 h1) c + z := by
    -- Equality in the subtype is checked in the ambient away localization.
    apply Subtype.ext
    simpa [z] using hx
  rw [hx']
  exact Subalgebra.add_mem _ hc hz

/-- Example 10.27.4 (3): for `a ≠ 0, 1`, the ring `R_a` is a finitely generated `ℚ`-algebra. -/
@[stacks 00F1]
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

/-- Helper for Chap10 Example 10 27 4: the left chart denominator
`(X + (a - 1))(X - a)` belongs to the equal-endpoint subring. -/
private theorem equal_endpoint_chartLeft_mem (a : ℚ) :
    ((X + C (a - 1)) * (X - C a) : Polynomial ℚ) ∈ R := by
  -- The two endpoint evaluations agree by the defining polynomial identity.
  rw [mem_equal_endpoint_poly_subring_iff]
  norm_num
  ring

/-- Helper for Chap10 Example 10 27 4: the left chart denominator as an element of `R`. -/
private def equal_endpoint_chartLeft (a : ℚ) : R :=
  ⟨(X + C (a - 1)) * (X - C a), equal_endpoint_chartLeft_mem a⟩

/-- Helper for Chap10 Example 10 27 4: the right chart denominator
`(X^2 + X + (2a - 2))(X - a)` belongs to the equal-endpoint subring. -/
private theorem equal_endpoint_chartRight_mem (a : ℚ) :
    (((X ^ 2 + X + C (2 * a - 2)) * (X - C a)) : Polynomial ℚ) ∈ R := by
  -- This is the second source denominator; its endpoint values are both `2a - 2a^2`.
  rw [mem_equal_endpoint_poly_subring_iff]
  norm_num
  ring

/-- Helper for Chap10 Example 10 27 4: the right chart denominator as an element of `R`. -/
private def equal_endpoint_chartRight (a : ℚ) : R :=
  ⟨(X ^ 2 + X + C (2 * a - 2)) * (X - C a), equal_endpoint_chartRight_mem a⟩

/-- Helper for Chap10 Example 10 27 4: the left cleared numerator is in `R`. -/
private theorem equal_endpoint_chartLeft_linearFractional_numerator_mem (a : ℚ) :
    (X * ((X + C (a - 1)) * (X - C a)) +
        C (a ^ 2 - a) * (X + C (a - 1)) :
      Polynomial ℚ) ∈ R := by
  -- After clearing the pole of the linear-fractional generator, the endpoints still agree.
  rw [mem_equal_endpoint_poly_subring_iff]
  simp only [coe_eval₂RingHom, eval₂_add, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C,
    RingHom.id_apply]
  ring

/-- Helper for Chap10 Example 10 27 4: the base element obtained by clearing the left chart. -/
private def equal_endpoint_chartLeft_linearFractional_numerator (a : ℚ) : R :=
  ⟨X * ((X + C (a - 1)) * (X - C a)) +
      C (a ^ 2 - a) * (X + C (a - 1)),
    equal_endpoint_chartLeft_linearFractional_numerator_mem a⟩

/-- Helper for Chap10 Example 10 27 4: the right cleared numerator is in `R`. -/
private theorem equal_endpoint_chartRight_linearFractional_numerator_mem (a : ℚ) :
    (X * (((X ^ 2 + X + C (2 * a - 2)) * (X - C a))) +
        C (a ^ 2 - a) * (X ^ 2 + X + C (2 * a - 2)) :
      Polynomial ℚ) ∈ R := by
  -- The same endpoint calculation clears the pole on the right chart.
  rw [mem_equal_endpoint_poly_subring_iff]
  simp only [coe_eval₂RingHom, eval₂_add, eval₂_mul, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C, RingHom.id_apply]
  ring

/-- Helper for Chap10 Example 10 27 4: the base element obtained by clearing the right chart. -/
private def equal_endpoint_chartRight_linearFractional_numerator (a : ℚ) : R :=
  ⟨X * (((X ^ 2 + X + C (2 * a - 2)) * (X - C a))) +
      C (a ^ 2 - a) * (X ^ 2 + X + C (2 * a - 2)),
    equal_endpoint_chartRight_linearFractional_numerator_mem a⟩

/-- Helper for Chap10 Example 10 27 4: a generic cleared-denominator identity used on both
distinguished charts. -/
private theorem equal_endpoint_linearFractional_cleared_identity
    {A : Type*} [CommRing A] (z d w v i : A) (hv : v * i = 1) :
    z * (w * v) + d * w = (z + d * i) * (w * v) := by
  -- Once the denominator inverse is named, the remaining equality is ordinary ring algebra.
  calc
    z * (w * v) + d * w = z * (w * v) + d * w * (v * i) := by
      rw [hv]
      ring
    _ = (z + d * i) * (w * v) := by
      ring

/-- Helper for Chap10 Example 10 27 4: the two chart denominators satisfy the source Bezout
identity after adjoining the displayed inverse-denominator term. -/
private theorem equal_endpoint_chart_source_bezout_identity
    {A : Type*} [CommRing A] (z ca i : A) (hv : (z - ca) * i = 1) :
    ((z ^ 2 + z + (2 * ca - 2)) * (z - ca)) -
        ((z + (ca ^ 2 - ca) * i) + (2 - ca)) * ((z + (ca - 1)) * (z - ca)) =
      (ca ^ 2 - ca) * (1 - 2 * ca) := by
  let d : A := ca ^ 2 - ca
  let w : A := z + (ca - 1)
  let v : A := z - ca
  let c : A := 2 - ca
  have hclear : z * (w * v) + d * w = (z + d * i) * (w * v) := by
    -- The generic cleared-fraction identity removes the only denominator-bearing term.
    exact equal_endpoint_linearFractional_cleared_identity z d w v i hv
  have hprod :
      ((z + d * i) + c) * (w * v) = (z * (w * v) + d * w) + c * (w * v) := by
    -- Add the remaining scalar term after the cleared identity has normalized `z + d*i`.
    calc
      ((z + d * i) + c) * (w * v) = (z + d * i) * (w * v) + c * (w * v) := by
        ring
      _ = (z * (w * v) + d * w) + c * (w * v) := by rw [← hclear]
  -- The rest is the polynomial Bezout calculation in the denominator-free variables.
  calc
    ((z ^ 2 + z + (2 * ca - 2)) * (z - ca)) -
        ((z + (ca ^ 2 - ca) * i) + (2 - ca)) * ((z + (ca - 1)) * (z - ca)) =
        (z ^ 2 + z + (2 * ca - 2)) * v - ((z + d * i) + c) * (w * v) := by
          simp [d, w, v, c]
    _ = (z ^ 2 + z + (2 * ca - 2)) * v - ((z * (w * v) + d * w) + c * (w * v)) := by
          rw [hprod]
    _ = (ca ^ 2 - ca) * (1 - 2 * ca) := by
          simp [d, w, v, c]
          ring

/-- Helper for Chap10 Example 10 27 4: on each source chart, multiplying the
linear-fractional generator by the chart denominator lands in the image of `R`. -/
private theorem equal_endpoint_chart_linearFractional_mul_mem_range (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) :
    (∃ r : R,
        algebraMap R (equal_endpoint_away a h0 h1) r =
          equal_endpoint_away_linearFractional a h0 h1 *
            algebraMap R (equal_endpoint_away a h0 h1) (equal_endpoint_chartLeft a)) ∧
      ∃ r : R,
        algebraMap R (equal_endpoint_away a h0 h1) r =
          equal_endpoint_away_linearFractional a h0 h1 *
            algebraMap R (equal_endpoint_away a h0 h1) (equal_endpoint_chartRight a) := by
  constructor
  · refine ⟨equal_endpoint_chartLeft_linearFractional_numerator a, ?_⟩
    -- Equality is checked in the ambient away localization, where the pole is explicitly cleared.
    apply Subtype.ext
    change
      algebraMap (Polynomial ℚ) (Localization.Away (X - C a))
          ((equal_endpoint_chartLeft_linearFractional_numerator a : R) : Polynomial ℚ) =
        (equal_endpoint_away_linearFractional a h0 h1 : Localization.Away (X - C a)) *
          algebraMap (Polynomial ℚ) (Localization.Away (X - C a))
            ((equal_endpoint_chartLeft a : R) : Polynomial ℚ)
    simp only [equal_endpoint_chartLeft_linearFractional_numerator, equal_endpoint_chartLeft,
      equal_endpoint_away_linearFractional, Subtype.coe_mk, map_add, map_mul, map_sub, map_pow,
      map_one]
    have hC :
        algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (C a) =
          algebraMap ℚ (Localization.Away (X - C a)) a := by
      rw [Polynomial.C_eq_algebraMap]
      exact IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ)
        (Localization.Away (X - C a)) a
    rw [hC]
    let L := Localization.Away (X - C a)
    let z : L := algebraMap (Polynomial ℚ) L X
    let ca : L := algebraMap ℚ L a
    let d : L := ca ^ 2 - ca
    let w : L := z + (ca - 1)
    let v : L := z - ca
    let i : L := IsLocalization.Away.invSelf (X - C a)
    have hv : v * i = 1 := by
      -- The remaining calculation uses exactly the inverse of the localized denominator.
      have hv0 :
          algebraMap (Polynomial ℚ) L (X - C a) * i = 1 :=
        IsLocalization.Away.mul_invSelf (S := L) (X - C a)
      have hv1 :
          (algebraMap (Polynomial ℚ) L X -
              algebraMap (Polynomial ℚ) L (C a)) * i = 1 := by
        simpa [L, i, map_sub] using hv0
      rw [hC] at hv1
      change (algebraMap (Polynomial ℚ) L X - algebraMap ℚ L a) * i = 1
      exact hv1
    change z * (w * v) + d * w = (z + d * i) * (w * v)
    exact equal_endpoint_linearFractional_cleared_identity z d w v i hv
  · refine ⟨equal_endpoint_chartRight_linearFractional_numerator a, ?_⟩
    -- The right chart has the same cleared-fraction calculation with the quadratic denominator.
    apply Subtype.ext
    change
      algebraMap (Polynomial ℚ) (Localization.Away (X - C a))
          ((equal_endpoint_chartRight_linearFractional_numerator a : R) : Polynomial ℚ) =
        (equal_endpoint_away_linearFractional a h0 h1 : Localization.Away (X - C a)) *
          algebraMap (Polynomial ℚ) (Localization.Away (X - C a))
            ((equal_endpoint_chartRight a : R) : Polynomial ℚ)
    simp only [equal_endpoint_chartRight_linearFractional_numerator, equal_endpoint_chartRight,
      equal_endpoint_away_linearFractional, Subtype.coe_mk, map_add, map_mul, map_sub, map_pow,
      C_ofNat]
    have hC :
        algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (C a) =
          algebraMap ℚ (Localization.Away (X - C a)) a := by
      rw [Polynomial.C_eq_algebraMap]
      exact IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ)
        (Localization.Away (X - C a)) a
    rw [hC]
    let L := Localization.Away (X - C a)
    let z : L := algebraMap (Polynomial ℚ) L X
    let ca : L := algebraMap ℚ L a
    let d : L := ca ^ 2 - ca
    let two : L := algebraMap (Polynomial ℚ) L (C 2)
    let w : L := z ^ 2 + z + (two * ca - two)
    let v : L := z - ca
    let i : L := IsLocalization.Away.invSelf (X - C a)
    have hv : v * i = 1 := by
      -- Again the only localization-specific step is cancellation of `X - a`.
      have hv0 :
          algebraMap (Polynomial ℚ) L (X - C a) * i = 1 :=
        IsLocalization.Away.mul_invSelf (S := L) (X - C a)
      have hv1 :
          (algebraMap (Polynomial ℚ) L X -
              algebraMap (Polynomial ℚ) L (C a)) * i = 1 := by
        simpa [L, i, map_sub] using hv0
      rw [hC] at hv1
      change (algebraMap (Polynomial ℚ) L X - algebraMap ℚ L a) * i = 1
      exact hv1
    change z * (w * v) + d * w = (z + d * i) * (w * v)
    exact equal_endpoint_linearFractional_cleared_identity z d w v i hv

/-- Helper for Chap10 Example 10 27 4: over the base ring `R`, the single
linear-fractional element generates the whole away algebra. -/
private theorem equal_endpoint_away_adjoin_linearFractional_eq_top (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Algebra.adjoin R ({equal_endpoint_away_linearFractional a h0 h1} :
        Set (equal_endpoint_away a h0 h1)) =
      ⊤ := by
  let B := equal_endpoint_away a h0 h1
  let t : B := equal_endpoint_away_linearFractional a h0 h1
  let A : Subalgebra R B := Algebra.adjoin R ({t} : Set B)
  have hquad : equal_endpoint_away_quadratic a h0 h1 ∈ A := by
    -- The quadratic generator is already a base element of `R`, hence belongs to every
    -- `R`-subalgebra.
    have hquad_eq :
        equal_endpoint_away_quadratic a h0 h1 = algebraMap R B equal_endpoint_quad := by
      apply Subtype.ext
      rfl
    rw [hquad_eq]
    exact Subalgebra.algebraMap_mem A equal_endpoint_quad
  have hcubic : equal_endpoint_away_cubicMinusLinear a h0 h1 ∈ A := by
    -- The cubic-minus-linear generator is also the image of an element of the base ring.
    have hcubic_eq :
        equal_endpoint_away_cubicMinusLinear a h0 h1 =
          algebraMap R B equal_endpoint_cube_minus_linear := by
      apply Subtype.ext
      rfl
    rw [hcubic_eq]
    exact Subalgebra.algebraMap_mem A equal_endpoint_cube_minus_linear
  have ht : equal_endpoint_away_linearFractional a h0 h1 ∈ A := by
    -- The remaining generator is the chosen singleton generator.
    simpa [A, B, t] using
      (Algebra.subset_adjoin (Set.mem_singleton t))
  have hmono :
      ∀ x ∈
        Algebra.adjoin ℚ
          ({ equal_endpoint_away_quadratic a h0 h1
           , equal_endpoint_away_cubicMinusLinear a h0 h1
           , equal_endpoint_away_linearFractional a h0 h1 } :
            Set B),
        x ∈ A := by
    intro x hx
    -- Induct through the already established `ℚ`-algebra generation theorem, transporting
    -- constants through the scalar tower `ℚ → R → B`.
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with hq | hc | ht'
        · simpa [B, hq] using hquad
        · simpa [B, hc] using hcubic
        · simpa [B, ht'] using ht
    | algebraMap q =>
        have hconst : algebraMap ℚ B q = algebraMap R B (algebraMap ℚ R q) := by
          exact (IsScalarTower.algebraMap_apply ℚ R B q).symm
        rw [hconst]
        exact Subalgebra.algebraMap_mem A (algebraMap ℚ R q)
    | add x y _ _ hx hy =>
        exact A.add_mem hx hy
    | mul x y _ _ hx hy =>
        exact A.mul_mem hx hy
  rw [eq_top_iff]
  intro x _
  -- The previous three-generator theorem puts `x` in the `ℚ`-adjoin, and the induction
  -- above moves that membership into the singleton `R`-adjoin.
  exact hmono x (by
    rw [equal_endpoint_away_adjoin_eq_top a h0 h1]
    exact trivial)

/-- Helper for Chap10 Example 10 27 4: the two source chart denominators generate the unit ideal
in the away algebra. -/
private theorem equal_endpoint_chart_source_span_eq_top (a : ℚ)
    (h0 : a ≠ 0) (hhalf : a ≠ (1 / 2 : ℚ)) (h1 : a ≠ 1) :
    Ideal.span
        ({ algebraMap R (equal_endpoint_away a h0 h1) (equal_endpoint_chartLeft a)
         , algebraMap R (equal_endpoint_away a h0 h1) (equal_endpoint_chartRight a) } :
          Set (equal_endpoint_away a h0 h1)) =
      ⊤ := by
  let B := equal_endpoint_away a h0 h1
  let L := Localization.Away (X - C a)
  let t : B := equal_endpoint_away_linearFractional a h0 h1
  let u : B := algebraMap R B (equal_endpoint_chartLeft a)
  let v : B := algebraMap R B (equal_endpoint_chartRight a)
  let scalar : ℚ := (a ^ 2 - a) * (1 - 2 * a)
  let I : Ideal B := Ideal.span ({u, v} : Set B)
  have hu : u ∈ I := by
    -- The left denominator is one of the two ideal generators.
    exact Ideal.subset_span (by simp [u])
  have hvI : v ∈ I := by
    -- The right denominator is the other ideal generator.
    exact Ideal.subset_span (by simp [v])
  have hcomb : v - (t + algebraMap ℚ B (2 - a)) * u ∈ I := by
    -- Ideals absorb multiplication by arbitrary coefficients, so the Bezout combination is in `I`.
    exact I.sub_mem hvI (I.mul_mem_left (t + algebraMap ℚ B (2 - a)) hu)
  have hidentity : v - (t + algebraMap ℚ B (2 - a)) * u = algebraMap ℚ B scalar := by
    -- Check the Bezout identity in the ambient away localization, where the inverse denominator
    -- has its canonical cancellation relation.
    apply Subtype.ext
    let z : L := algebraMap (Polynomial ℚ) L X
    let ca : L := algebraMap ℚ L a
    let i : L := IsLocalization.Away.invSelf (X - C a)
    have hmap_rat (r : ℚ) :
        algebraMap (Polynomial ℚ) L (algebraMap ℚ (Polynomial ℚ) r) =
          algebraMap ℚ L r :=
      (IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) L r).symm
    have hcancel : (z - ca) * i = 1 := by
      have hv0 :
          algebraMap (Polynomial ℚ) L (X - C a) * i = 1 :=
        IsLocalization.Away.mul_invSelf (S := L) (X - C a)
      change (algebraMap (Polynomial ℚ) L X - algebraMap ℚ L a) * i = 1
      simpa only [map_sub, Polynomial.C_eq_algebraMap, hmap_rat] using hv0
    have hbezout := equal_endpoint_chart_source_bezout_identity z ca i hcancel
    change
      algebraMap (Polynomial ℚ) L
            (((X ^ 2 + X + C (2 * a - 2)) * (X - C a))) -
          (((algebraMap (Polynomial ℚ) L X +
                algebraMap ℚ L (a ^ 2 - a) * i) +
              algebraMap ℚ L (2 - a)) *
            algebraMap (Polynomial ℚ) L (((X + C (a - 1)) * (X - C a)))) =
        algebraMap ℚ L scalar
    calc
      algebraMap (Polynomial ℚ) L
            (((X ^ 2 + X + C (2 * a - 2)) * (X - C a))) -
          (((algebraMap (Polynomial ℚ) L X +
                algebraMap ℚ L (a ^ 2 - a) * i) +
              algebraMap ℚ L (2 - a)) *
            algebraMap (Polynomial ℚ) L (((X + C (a - 1)) * (X - C a)))) =
          ((z ^ 2 + z + (2 * ca - 2)) * (z - ca)) -
            ((z + (ca ^ 2 - ca) * i) + (2 - ca)) *
              ((z + (ca - 1)) * (z - ca)) := by
            simp only [z, ca, i, map_add, map_sub, map_mul, map_pow,
              Polynomial.C_eq_algebraMap, hmap_rat, map_ofNat, map_one]
      _ = (ca ^ 2 - ca) * (1 - 2 * ca) := hbezout
      _ = algebraMap ℚ L scalar := by
            simp only [ca, scalar, map_mul, map_sub, map_pow, map_ofNat, map_one]
  have hscalar_mem : algebraMap ℚ B scalar ∈ I := by
    -- The Bezout combination is the nonzero rational scalar.
    rw [← hidentity]
    exact hcomb
  have hlinear_ne : (1 - 2 * a : ℚ) ≠ 0 := by
    -- The extra hypothesis `a ≠ 1/2` is exactly the nonvanishing of this factor.
    intro h
    apply hhalf
    linarith
  have hscalar_ne : scalar ≠ 0 := by
    -- Both rational factors in the scalar are nonzero.
    exact mul_ne_zero (equal_endpoint_endpointProduct_ne_zero a h0 h1) hlinear_ne
  have hone : (1 : B) ∈ I := by
    -- A nonzero rational scalar is a unit in any `ℚ`-algebra, so the ideal contains `1`.
    have hmem := I.mul_mem_left (algebraMap ℚ B scalar⁻¹) hscalar_mem
    have hinv :
        algebraMap ℚ B scalar⁻¹ * algebraMap ℚ B scalar = 1 := by
      rw [← map_mul]
      rw [inv_mul_cancel₀ hscalar_ne, map_one]
    simpa [hinv] using hmem
  exact I.eq_top_iff_one.mpr hone

/-- Helper for Chap10 Example 10 27 4: a singleton algebra generator whose product with the
chosen denominator comes from the base ring makes the induced away map bijective. -/
private theorem awayMap_bijective_of_adjoin_singleton_and_clear
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (s : A) (t : B)
    (hinj : Function.Injective (algebraMap A B))
    (hgen : Algebra.adjoin A ({t} : Set B) = ⊤)
    (hclear : ∃ r : A, algebraMap A B r = t * algebraMap A B s) :
    Function.Bijective (Localization.awayMap (algebraMap A B) s) := by
  refine ⟨?_, ?_⟩
  · rw [Localization.awayMap_injective_iff]
    intro a ha
    -- Injectivity of the original algebra map already kills the kernel of the away map.
    have hzero : a = 0 := hinj (by simpa using ha)
    refine ⟨0, ?_⟩
    simp [hzero]
  · rw [Localization.awayMap_surjective_iff]
    intro b
    have hbgen : b ∈ Algebra.adjoin A ({t} : Set B) := by
      rw [hgen]
      exact Set.mem_univ b
    -- Induct through the singleton algebra generation, carrying one common denominator.
    induction hbgen using Algebra.adjoin_induction with
    | mem x hx =>
        have hx' : x = t := by simpa using hx
        rcases hclear with ⟨r, hr⟩
        subst x
        refine ⟨r, 1, ?_⟩
        simpa [pow_one, mul_comm] using hr
    | algebraMap a =>
        refine ⟨a, 0, ?_⟩
        simp
    | add x y _ _ hx hy =>
        rcases hx with ⟨a, m, ha⟩
        rcases hy with ⟨b, n, hb⟩
        refine ⟨a * s ^ n + b * s ^ m, m + n, ?_⟩
        -- Put the two summands over the same denominator power.
        calc
          algebraMap A B (a * s ^ n + b * s ^ m)
              = (algebraMap A B a) * (algebraMap A B s) ^ n +
                  (algebraMap A B b) * (algebraMap A B s) ^ m := by
                    simp [map_add, map_mul, map_pow]
          _ = ((algebraMap A B s) ^ m * x) * (algebraMap A B s) ^ n +
                  ((algebraMap A B s) ^ n * y) * (algebraMap A B s) ^ m := by
                    rw [ha, hb]
          _ = (algebraMap A B s) ^ (m + n) * (x + y) := by
                    ring
    | mul x y _ _ hx hy =>
        rcases hx with ⟨a, m, ha⟩
        rcases hy with ⟨b, n, hb⟩
        refine ⟨a * b, m + n, ?_⟩
        -- Products multiply the denominator powers.
        calc
          algebraMap A B (a * b) = algebraMap A B a * algebraMap A B b := by simp
          _ = ((algebraMap A B s) ^ m * x) * ((algebraMap A B s) ^ n * y) := by
                    rw [ha, hb]
          _ = (algebraMap A B s) ^ (m + n) * (x * y) := by
                    ring

/-- Helper for Chap10 Example 10 27 4: the base map from the equal-endpoint ring into `R_a`
is injective. -/
private theorem equal_endpoint_away_algebraMap_injective (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Function.Injective (algebraMap R (equal_endpoint_away a h0 h1)) := by
  intro x y hxy
  apply Subtype.ext
  have hval := congrArg
    (fun z : equal_endpoint_away a h0 h1 => (z : Localization.Away (X - C a))) hxy
  change
    algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (x : Polynomial ℚ) =
      algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (y : Polynomial ℚ) at hval
  have hpow_le :
      Submonoid.powers (X - C a : Polynomial ℚ) ≤ nonZeroDivisors (Polynomial ℚ) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (Polynomial.X_sub_C_ne_zero a)
  have hinj_ambient :
      Function.Injective (algebraMap (Polynomial ℚ) (Localization.Away (X - C a))) :=
    IsLocalization.injective (Localization.Away (X - C a)) hpow_le
  -- The subtype map factors through the ambient polynomial away localization, where the
  -- denominator is a non-zero-divisor.
  exact hinj_ambient hval

/-- Helper for Chap10 Example 10 27 4: the singleton-generator and clearing hypotheses identify
the chart as the expected away localization of the base ring. -/
private theorem isLocalizationAway_of_adjoin_singleton_and_clear
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (s : A) (t : B)
    (hinj : Function.Injective (algebraMap A B))
    (hgen : Algebra.adjoin A ({t} : Set B) = ⊤)
    (hclear : ∃ r : A, algebraMap A B r = t * algebraMap A B s) :
    IsLocalization.Away s (Localization.Away (algebraMap A B s)) := by
  have hbij : Function.Bijective (Localization.awayMap (algebraMap A B) s) :=
    awayMap_bijective_of_adjoin_singleton_and_clear s t hinj hgen hclear
  let e : Localization.Away s ≃ₐ[A] Localization.Away (algebraMap A B s) :=
    AlgEquiv.ofBijective (Localization.awayMapₐ (Algebra.ofId A B) s) (by
      simpa [Localization.awayMapₐ] using hbij)
  -- Transport the standard localization structure across the bijective away comparison map.
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers s) e

/-- Helper for Chap10 Example 10 27 4: the endpoint values of positive powers of `X-a` are
different unless `a = 1/2`. -/
private theorem equal_endpoint_endpoint_pow_ne (a : ℚ) (hhalf : a ≠ (1 / 2 : ℚ))
    {n : ℕ} (hn : 0 < n) :
    (-a) ^ n ≠ (1 - a) ^ n := by
  intro h
  have hn0 : n ≠ 0 := by omega
  have hcases := (pow_eq_pow_iff_of_ne_zero (a := -a) (b := 1 - a) hn0).1 h
  -- Positive powers in a linear ordered field are equal only at equal endpoints, or at opposite
  -- endpoints in even degree; both alternatives contradict the hypotheses.
  rcases hcases with hlin | ⟨hneg, _⟩
  · linarith
  · apply hhalf
    linarith

/-- Helper for Chap10 Example 10 27 4: an equal-endpoint polynomial is not associated to a
positive power of `X-a`. -/
private theorem equal_endpoint_not_associated_linearFactor_pow_pos (a : ℚ)
    (hhalf : a ≠ (1 / 2 : ℚ)) (r : R) {n : ℕ} (hn : 0 < n) :
    ¬ Associated (r : Polynomial ℚ) ((X - C a : Polynomial ℚ) ^ n) := by
  rintro ⟨u, hu⟩
  rcases Polynomial.isUnit_iff.mp u.isUnit with ⟨c, _hcunit, hc⟩
  have hr01 : (r : Polynomial ℚ).eval 0 = (r : Polynomial ℚ).eval 1 :=
    (mem_equal_endpoint_poly_subring_iff ℚ (r : Polynomial ℚ)).mp r.property
  have h0pow : (r : Polynomial ℚ).eval 0 * c = (-a) ^ n := by
    have h := congrArg (fun p : Polynomial ℚ => p.eval 0) hu
    simpa [← hc, sub_eq_add_neg] using h
  have h1pow : (r : Polynomial ℚ).eval 1 * c = (1 - a) ^ n := by
    have h := congrArg (fun p : Polynomial ℚ => p.eval 1) hu
    simpa [← hc, sub_eq_add_neg] using h
  have hpows : (-a) ^ n = (1 - a) ^ n := by
    -- The associated unit is constant, so the equal-endpoint condition transfers to powers of
    -- the two endpoint values of `X-a`.
    calc
      (-a) ^ n = (r : Polynomial ℚ).eval 0 * c := h0pow.symm
      _ = (r : Polynomial ℚ).eval 1 * c := by rw [hr01]
      _ = (1 - a) ^ n := h1pow
  exact equal_endpoint_endpoint_pow_ne a hhalf hn hpows

/-- Helper for Chap10 Example 10 27 4: a polynomial unit lying in the equal-endpoint subring is
already a unit of that subring. -/
private theorem equal_endpoint_isUnit_of_polynomial_isUnit (r : R)
    (hunit : IsUnit (r : Polynomial ℚ)) : IsUnit r := by
  rcases Polynomial.isUnit_iff.mp hunit with ⟨c, hcunit, hc⟩
  have hcne : c ≠ 0 := isUnit_iff_ne_zero.mp hcunit
  refine isUnit_iff_exists_inv.mpr ⟨⟨C c⁻¹, equal_endpoint_C_mem c⁻¹⟩, ?_⟩
  apply Subtype.ext
  -- The inverse is the reciprocal constant polynomial, which still has equal endpoint values.
  change (r : Polynomial ℚ) * C c⁻¹ = 1
  rw [← hc, ← C_mul]
  rw [mul_inv_cancel₀ hcne]
  simp

/-- Helper for Chap10 Example 10 27 4: base elements become units in `R_a` exactly when they are
already units in the equal-endpoint ring. -/
private theorem equal_endpoint_away_algebraMap_isUnit_iff (a : ℚ)
    (h0 : a ≠ 0) (hhalf : a ≠ (1 / 2 : ℚ)) (h1 : a ≠ 1) (r : R) :
    IsUnit (algebraMap R (equal_endpoint_away a h0 h1) r) ↔ IsUnit r := by
  constructor
  · intro hunit
    let L := Localization.Away (X - C a)
    let v : Polynomial ℚ := X - C a
    have hambient : IsUnit (algebraMap (Polynomial ℚ) L (r : Polynomial ℚ)) := by
      simpa [L] using hunit.map (equal_endpoint_away a h0 h1).val.toRingHom
    have hdvd : ∃ n, (r : Polynomial ℚ) ∣ v ^ n := by
      simpa [L, v] using
        (IsLocalization.Away.algebraMap_isUnit_iff (S := L) (x := v)
          (y := (r : Polynomial ℚ))).mp hambient
    rcases hdvd with ⟨n, hdvd⟩
    rcases (dvd_prime_pow (Polynomial.prime_X_sub_C a) n).mp hdvd with ⟨i, _hi, hassoc⟩
    by_cases hi0 : i = 0
    · have hpoly_unit : IsUnit (r : Polynomial ℚ) :=
        associated_one_iff_isUnit.mp (by simpa [hi0] using hassoc)
      exact equal_endpoint_isUnit_of_polynomial_isUnit r hpoly_unit
    · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
      exact (equal_endpoint_not_associated_linearFactor_pow_pos a hhalf r hpos hassoc).elim
  · intro hunit
    -- Units in the base stay units after applying any ring homomorphism.
    exact hunit.map (algebraMap R (equal_endpoint_away a h0 h1))

/-- Helper for Chap10 Example 10 27 4: the displayed linear-fractional generator of `R_a`
does not come from the base equal-endpoint ring. -/
private theorem equal_endpoint_away_linearFractional_not_mem_range (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) :
    equal_endpoint_away_linearFractional a h0 h1 ∉
      Set.range (algebraMap R (equal_endpoint_away a h0 h1)) := by
  rintro ⟨r, hr⟩
  let L := Localization.Away (X - C a)
  let v : Polynomial ℚ := X - C a
  let i : L := IsLocalization.Away.invSelf v
  let d : ℚ := a ^ 2 - a
  have hval := congrArg (fun z : equal_endpoint_away a h0 h1 => (z : L)) hr
  change
    algebraMap (Polynomial ℚ) L (r : Polynomial ℚ) =
      algebraMap (Polynomial ℚ) L X + algebraMap ℚ L d * i at hval
  have hcancel : algebraMap (Polynomial ℚ) L v * i = 1 :=
    IsLocalization.Away.mul_invSelf (S := L) v
  have hcancel' : i * algebraMap (Polynomial ℚ) L v = 1 := by
    rw [mul_comm, hcancel]
  have hscalar : algebraMap (Polynomial ℚ) L (C d) = algebraMap ℚ L d := by
    simpa [Polynomial.C_eq_algebraMap] using
      (IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) L d).symm
  have hprod :
      algebraMap (Polynomial ℚ) L ((r : Polynomial ℚ) * v) =
        algebraMap (Polynomial ℚ) L (X * v + C d) := by
    -- If the linear-fractional element were a base image, clearing its denominator would give a
    -- polynomial identity in the ambient away localization.
    calc
      algebraMap (Polynomial ℚ) L ((r : Polynomial ℚ) * v)
          = algebraMap (Polynomial ℚ) L (r : Polynomial ℚ) *
              algebraMap (Polynomial ℚ) L v := by
                simp [map_mul]
      _ = (algebraMap (Polynomial ℚ) L X + algebraMap ℚ L d * i) *
              algebraMap (Polynomial ℚ) L v := by
                rw [hval]
      _ = algebraMap (Polynomial ℚ) L X * algebraMap (Polynomial ℚ) L v +
              algebraMap ℚ L d := by
                rw [add_mul, mul_assoc, hcancel', mul_one]
      _ = algebraMap (Polynomial ℚ) L (X * v + C d) := by
                simp [map_add, map_mul, hscalar]
  have hpow_le : Submonoid.powers v ≤ nonZeroDivisors (Polynomial ℚ) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors
      (by simpa [v] using Polynomial.X_sub_C_ne_zero a)
  have hinj_ambient : Function.Injective (algebraMap (Polynomial ℚ) L) :=
    IsLocalization.injective L hpow_le
  have hpoly : (r : Polynomial ℚ) * v = X * v + C d := hinj_ambient hprod
  have heval := congrArg (fun p : Polynomial ℚ => p.eval a) hpoly
  have hd : d ≠ 0 := by
    simpa [d] using equal_endpoint_endpointProduct_ne_zero a h0 h1
  -- Evaluating the cleared identity at `a` says that the nonzero scalar `a^2-a` is zero.
  apply hd
  symm
  simpa [v, d, sub_eq_add_neg] using heval

/-- Helper for Chap10 Example 10 27 4: the left chart denominator vanishes at the evaluation
point `m_a`. -/
private theorem equal_endpoint_chartLeft_mem_eval_point (a : ℚ) :
    equal_endpoint_chartLeft a ∈ (equal_endpoint_eval_point a).asIdeal := by
  rw [equal_endpoint_eval_point, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  -- Membership in the contracted closed point is just vanishing after evaluation at `a`.
  simp [equal_endpoint_chartLeft]

/-- Helper for Chap10 Example 10 27 4: the right chart denominator vanishes at the evaluation
point `m_a`. -/
private theorem equal_endpoint_chartRight_mem_eval_point (a : ℚ) :
    equal_endpoint_chartRight a ∈ (equal_endpoint_eval_point a).asIdeal := by
  rw [equal_endpoint_eval_point, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  -- The explicit factor `X-a` makes the evaluation vanish.
  simp [equal_endpoint_chartRight]

/-- Helper for Chap10 Example 10 27 4: the ideal generated by the two chart denominators is
contained in the evaluation ideal `m_a`. -/
private theorem equal_endpoint_chart_span_le_eval_point (a : ℚ) :
    Ideal.span ({equal_endpoint_chartLeft a, equal_endpoint_chartRight a} : Set R) ≤
      (equal_endpoint_eval_point a).asIdeal := by
  rw [Ideal.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · simpa [hx] using equal_endpoint_chartLeft_mem_eval_point a
  · simpa [hx] using equal_endpoint_chartRight_mem_eval_point a

/-- Helper for Chap10 Example 10 27 4: evaluating after the presentation map is the same as
evaluating the bivariate polynomial at the corresponding point upstairs. -/
private theorem equal_endpoint_presentation_eval_at (a : ℚ) (F : ℚ[X][Y]) :
    ((equal_endpoint_presentation F : R) : Polynomial ℚ).eval a =
      (F.eval (C (a * (a ^ 2 - a)))).eval (a ^ 2 - a) := by
  -- The presentation sends the two upstairs coordinates to `z^2-z` and `z^3-z^2`, whose
  -- values at `z = a` are the displayed coordinates.
  induction F using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp [map_add, hP, hQ]
  | monomial n p =>
      have hp : eval a ↑((aeval equal_endpoint_quad) p) = eval (a ^ 2 - a) p := by
        rw [equal_endpoint_aeval_quadratic_val, Polynomial.eval_comp]
        congr 1
        simp
      have hy : a ^ 3 - a ^ 2 = a * (a ^ 2 - a) := by
        ring
      simpa [equal_endpoint_presentation, Polynomial.aeval_monomial, Polynomial.eval_monomial,
        equal_endpoint_cubic, hp, hy]

/-- Helper for Chap10 Example 10 27 4: the two upstairs point-ideal generators map to the two
chart denominators, up to an elementary linear combination. -/
private theorem equal_endpoint_presentation_chart_generators (a : ℚ) :
    equal_endpoint_presentation (C (X - C (a ^ 2 - a)) : ℚ[X][Y]) =
        equal_endpoint_chartLeft a ∧
      equal_endpoint_presentation (Y - C (C (a * (a ^ 2 - a))) : ℚ[X][Y]) =
        equal_endpoint_chartRight a - algebraMap ℚ R (2 - a) * equal_endpoint_chartLeft a := by
  constructor
  · -- The first generator is exactly `(z+a-1)(z-a)`.
    apply Subtype.ext
    simp only [equal_endpoint_presentation, map_sub, Polynomial.aevalAeval_C,
      Polynomial.aeval_C, equal_endpoint_quad,
      equal_endpoint_chartLeft, Subtype.coe_mk]
    simp [equal_endpoint_algebraMap_val]
    ring
  · -- The second generator differs from the right chart denominator by the left chart multiple.
    apply Subtype.ext
    have hpoly :
        (X ^ 3 - X ^ 2 : Polynomial ℚ) - C a * (C a ^ 2 - C a) =
          (X ^ 2 + X + (C 2 * C a - C 2)) * (X - C a) -
            (C 2 - C a) * ((X + (C a - 1)) * (X - C a)) := by
      rw [Polynomial.C_ofNat]
      ring
    -- After forgetting the subtype, the statement is exactly the displayed polynomial identity.
    simp only [equal_endpoint_presentation, map_sub, map_mul, Polynomial.aevalAeval_Y,
      Polynomial.aevalAeval_C, Polynomial.aeval_C, equal_endpoint_cubic,
      equal_endpoint_chartRight, equal_endpoint_chartLeft]
    simp only [map_pow, AddSubgroupClass.coe_sub, Subring.coe_mul, SubmonoidClass.coe_pow, map_one]
    exact hpoly

/-- Helper for Chap10 Example 10 27 4: the evaluation ideal `m_a` is generated by the two chart
denominators. -/
private theorem equal_endpoint_eval_point_le_chart_span (a : ℚ) :
    (equal_endpoint_eval_point a).asIdeal ≤
      Ideal.span ({equal_endpoint_chartLeft a, equal_endpoint_chartRight a} : Set R) := by
  intro x hx
  let d : ℚ := a ^ 2 - a
  let e : ℚ := a * (a ^ 2 - a)
  let J : Ideal R :=
    Ideal.span ({equal_endpoint_chartLeft a, equal_endpoint_chartRight a} : Set R)
  rcases equal_endpoint_presentation_surjective x with ⟨F, hF⟩
  have hxvanish : ((x : R) : Polynomial ℚ).eval a = 0 := by
    -- Membership in the contracted closed point is exactly vanishing under evaluation at `a`.
    rw [equal_endpoint_eval_point, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hx
    simpa [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot] using hx
  have hFvanish : (F.eval (C e)).eval d = 0 := by
    -- The presentation-evaluation bridge transfers vanishing from `R` to the upstairs point.
    rw [← equal_endpoint_presentation_eval_at a F, hF]
    exact hxvanish
  have hFmem :
      F ∈ Ideal.span ({C (X - C d), Y - C (C e)} : Set ℚ[X][Y]) := by
    -- The upstairs point ideal in `ℚ[X][Y]` is generated by the two coordinate differences.
    simpa [d, e] using
      (Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero
        (a := d) (b := C e) (P := F)).2 hFvanish
  have hmap_le :
      Ideal.map equal_endpoint_presentation.toRingHom
          (Ideal.span ({C (X - C d), Y - C (C e)} : Set ℚ[X][Y])) ≤ J := by
    -- The two upstairs generators map to the left chart and to a right-chart linear combination.
    rw [Ideal.map_span, Ideal.span_le]
    rintro y ⟨g, hg, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · subst g
      simp only [d]
      change equal_endpoint_presentation (C (X - C (a ^ 2 - a)) : ℚ[X][Y]) ∈ J
      rw [(equal_endpoint_presentation_chart_generators a).1]
      exact Ideal.subset_span (by simp)
    · subst g
      simp only [e]
      change equal_endpoint_presentation (Y - C (C (a * (a ^ 2 - a))) : ℚ[X][Y]) ∈ J
      rw [(equal_endpoint_presentation_chart_generators a).2]
      have hright : equal_endpoint_chartRight a ∈ J := by
        exact Ideal.subset_span (by simp)
      have hleft : equal_endpoint_chartLeft a ∈ J := by
        exact Ideal.subset_span (by simp)
      exact J.sub_mem hright (J.mul_mem_left _ hleft)
  have hpresented :
      equal_endpoint_presentation F ∈ J :=
    hmap_le (Ideal.mem_map_of_mem equal_endpoint_presentation.toRingHom hFmem)
  -- Replace the chosen presenter by the original element `x`.
  simpa [J, hF] using hpresented

/-- Helper for Chap10 Example 10 27 4: an open embedding can be checked on two target opens
covering the range. -/
private theorem isOpenEmbedding_of_range_subset_union_and_restrictPreimage
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
    (hf : Continuous f) (U V : TopologicalSpace.Opens β)
    (hrange : Set.range f ⊆ (U : Set β) ∪ (V : Set β))
    (hU : IsOpenEmbedding ((U : Set β).restrictPreimage f))
    (hV : IsOpenEmbedding ((V : Set β).restrictPreimage f)) :
    IsOpenEmbedding f := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap hf ?_ ?_
  · intro x z hxz
    -- If two source points have the same image, that image lies in one of the two chart opens,
    -- where injectivity of the restricted map identifies the points.
    have hxmem : f x ∈ (U : Set β) ∪ (V : Set β) := hrange ⟨x, rfl⟩
    rcases hxmem with hxU | hxV
    · have hzU : f z ∈ (U : Set β) := by simpa [hxz] using hxU
      have hEq :
          (U.1.restrictPreimage f ⟨x, hxU⟩) =
            (U.1.restrictPreimage f ⟨z, hzU⟩) := by
        ext
        exact hxz
      exact congrArg Subtype.val (hU.injective hEq)
    · have hzV : f z ∈ (V : Set β) := by simpa [hxz] using hxV
      have hEq :
          (V.1.restrictPreimage f ⟨x, hxV⟩) =
            (V.1.restrictPreimage f ⟨z, hzV⟩) := by
        ext
        exact hxz
      exact congrArg Subtype.val (hV.injective hEq)
  · intro s hs
    have hsplit :
        f '' s =
          f '' (s ∩ f ⁻¹' (U : Set β)) ∪ f '' (s ∩ f ⁻¹' (V : Set β)) := by
      ext y
      constructor
      · rintro ⟨x, hxs, rfl⟩
        have hxmem : f x ∈ (U : Set β) ∪ (V : Set β) := hrange ⟨x, rfl⟩
        rcases hxmem with hxU | hxV
        · exact Or.inl ⟨x, ⟨hxs, hxU⟩, rfl⟩
        · exact Or.inr ⟨x, ⟨hxs, hxV⟩, rfl⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ⟨x, hx.1, rfl⟩
        · exact ⟨x, hx.1, rfl⟩
    rw [hsplit]
    apply IsOpen.union
    · have hsU : IsOpen (Subtype.val ⁻¹' s : Set (f ⁻¹' (U : Set β))) := by
        exact isOpen_induced hs
      have hImU :
          IsOpen (((U : Set β).restrictPreimage f) ''
            (Subtype.val ⁻¹' s : Set (f ⁻¹' (U : Set β)))) :=
        hU.isOpenMap _ hsU
      have hOpenY :
          IsOpen (Subtype.val '' (((U : Set β).restrictPreimage f) ''
            (Subtype.val ⁻¹' s : Set (f ⁻¹' (U : Set β))))) := by
        exact U.2.isOpenEmbedding_subtypeVal.isOpenMap _ hImU
      -- Transport openness from the target chart subtype back to the ambient target.
      convert hOpenY using 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨f x, hx.2⟩, ⟨⟨x, hx.2⟩, hx.1, rfl⟩, rfl⟩
      · rintro ⟨uy, ⟨x, hx, hux⟩, hy⟩
        refine ⟨x.1, ?_, ?_⟩
        · exact ⟨hx, x.2⟩
        · calc
            f x.1 = ↑((U.1.restrictPreimage f) x) := rfl
            _ = ↑uy := congrArg Subtype.val hux
            _ = y := hy
    · have hsV : IsOpen (Subtype.val ⁻¹' s : Set (f ⁻¹' (V : Set β))) := by
        exact isOpen_induced hs
      have hImV :
          IsOpen (((V : Set β).restrictPreimage f) ''
            (Subtype.val ⁻¹' s : Set (f ⁻¹' (V : Set β)))) :=
        hV.isOpenMap _ hsV
      have hOpenY :
          IsOpen (Subtype.val '' (((V : Set β).restrictPreimage f) ''
            (Subtype.val ⁻¹' s : Set (f ⁻¹' (V : Set β))))) := by
        exact V.2.isOpenEmbedding_subtypeVal.isOpenMap _ hImV
      -- The second chart is identical after replacing `U` by `V`.
      convert hOpenY using 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨f x, hx.2⟩, ⟨⟨x, hx.2⟩, hx.1, rfl⟩, rfl⟩
      · rintro ⟨vy, ⟨x, hx, hvx⟩, hy⟩
        refine ⟨x.1, ?_, ?_⟩
        · exact ⟨hx, x.2⟩
        · calc
            f x.1 = ↑((V.1.restrictPreimage f) x) := rfl
            _ = ↑vy := congrArg Subtype.val hvx
            _ = y := hy

/-- Helper for Chap10 Example 10 27 4: a common away localization makes the target basic open
lie in the image of the intermediate spectrum map. -/
private theorem primeSpectrum_basicOpen_subset_comap_range_of_isLocalizationAway
    {A B S : Type*} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    (s : A) [IsLocalization.Away s S] [IsLocalization.Away (algebraMap A B s) S] :
    (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum A)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap A B)) := by
  intro p hp
  have hp_range :
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap A S)) := by
    -- First lift the point through the known localization chart over the base.
    rw [PrimeSpectrum.localization_away_comap_range S s]
    exact hp
  rcases hp_range with ⟨q, hq⟩
  refine ⟨PrimeSpectrum.comap (algebraMap B S) q, ?_⟩
  -- The two spectrum maps compose to the direct map by the scalar tower.
  rw [← PrimeSpectrum.comap_comp_apply]
  simpa [IsScalarTower.algebraMap_eq A B S] using hq

/-- Helper for Chap10 Example 10 27 4: a common away localization identifies one restricted
basic-open chart map as an open embedding. -/
private theorem primeSpectrum_comap_restrict_basicOpen_isOpenEmbedding_of_isLocalizationAway
    {A B S : Type*} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    (s : A) [IsLocalization.Away s S] [IsLocalization.Away (algebraMap A B s) S] :
    IsOpenEmbedding
      ((PrimeSpectrum.basicOpen s : Set (PrimeSpectrum A)).restrictPreimage
        (PrimeSpectrum.comap (algebraMap A B))) := by
  let U : Set (PrimeSpectrum A) := PrimeSpectrum.basicOpen s
  let D : Set (PrimeSpectrum B) :=
    (PrimeSpectrum.comap (algebraMap A B)) ⁻¹' U
  let fAB : PrimeSpectrum B → PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B)
  let fBS : PrimeSpectrum S → PrimeSpectrum B := PrimeSpectrum.comap (algebraMap B S)
  let fAS : PrimeSpectrum S → PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A S)
  have hDopen : IsOpen D := by
    exact (PrimeSpectrum.basicOpen s).2.preimage (PrimeSpectrum.continuous_comap (algebraMap A B))
  have hBS : IsOpenEmbedding fBS := by
    simpa [fBS] using
      (PrimeSpectrum.localization_away_isOpenEmbedding S (algebraMap A B s))
  let g : PrimeSpectrum S → D := fun x => ⟨fBS x, by
    have hx : fAS x ∈ U := by
      have hxrange : fAS x ∈ Set.range fAS := ⟨x, rfl⟩
      simpa [U, fAS] using
        (by
          rw [PrimeSpectrum.localization_away_comap_range S s] at hxrange
          exact hxrange)
    -- The point lands in the restricted-preimage domain because the composite agrees with
    -- the direct `A`-spectrum map.
    simpa [D, U, fAB, fBS, fAS, IsScalarTower.algebraMap_eq A B S,
      PrimeSpectrum.comap_comp_apply] using hx
    ⟩
  have hg : IsOpenEmbedding g := by
    have hsub : IsOpenEmbedding (fun x : D => (x : PrimeSpectrum B)) :=
      hDopen.isOpenEmbedding_subtypeVal
    exact IsOpenEmbedding.of_comp g hsub (by
      simpa [g, fBS, Function.comp_def] using hBS)
  have hgsurj : Function.Surjective g := by
    intro y
    have hyB : y.1 ∈ (PrimeSpectrum.basicOpen (algebraMap A B s) : Set (PrimeSpectrum B)) := by
      simpa [D, U, fAB, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal,
        Ideal.mem_comap] using y.2
    have hyrange : y.1 ∈ Set.range fBS := by
      change y.1 ∈ Set.range fBS
      have hrangeEq :
          Set.range fBS =
            (PrimeSpectrum.basicOpen (algebraMap A B s) : Set (PrimeSpectrum B)) := by
        simpa [fBS] using
          (PrimeSpectrum.localization_away_comap_range S (algebraMap A B s))
      rw [hrangeEq]
      exact hyB
    rcases hyrange with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  let e : PrimeSpectrum S ≃ₜ D := hg.isEmbedding.toHomeomorphOfSurjective hgsurj
  have hAS : IsOpenEmbedding fAS := by
    simpa [fAS] using (PrimeSpectrum.localization_away_isOpenEmbedding S s)
  have hASmem (x : PrimeSpectrum S) : fAS x ∈ U := by
    have hxrange : fAS x ∈ Set.range fAS := ⟨x, rfl⟩
    simpa [U, fAS] using
      (by
        rw [PrimeSpectrum.localization_away_comap_range S s] at hxrange
        exact hxrange)
  let k : PrimeSpectrum S → U := fun x => ⟨fAS x, hASmem x⟩
  have hk : IsOpenEmbedding k := by
    have hsubU : IsOpenEmbedding (fun x : U => (x : PrimeSpectrum A)) :=
      (PrimeSpectrum.basicOpen s).2.isOpenEmbedding_subtypeVal
    exact IsOpenEmbedding.of_comp k hsubU (by
      simpa [k, fAS, Function.comp_def] using hAS)
  have hfinal : IsOpenEmbedding (k ∘ e.symm) := hk.comp e.symm.isOpenEmbedding
  -- Transport the chart open embedding across the homeomorphism from the common localization
  -- to the restricted-preimage source.
  convert hfinal using 1
  funext y
  apply Subtype.ext
  have hey : (e (e.symm y) : D) = y := e.apply_symm_apply y
  have hval : fBS (e.symm y) = (y : PrimeSpectrum B) := by
    have heg : (e (e.symm y) : D) = g (e.symm y) := rfl
    calc
      fBS (e.symm y) = (g (e.symm y) : PrimeSpectrum B) := rfl
      _ = (e (e.symm y) : PrimeSpectrum B) := by
            exact (congrArg Subtype.val heg).symm
      _ = (y : PrimeSpectrum B) := congrArg Subtype.val hey
  calc
    fAB (y : PrimeSpectrum B) = fAB (fBS (e.symm y)) := by rw [hval]
    _ = fAS (e.symm y) := by
      simp [fAB, fBS, fAS, IsScalarTower.algebraMap_eq A B S]

/-- Helper for Chap10 Example 10 27 4: two common away-localization charts compute the range as
the union of the two target basic opens. -/
private theorem primeSpectrum_comap_range_eq_basicOpen_union_of_source_span_eq_top
    {A B SL SR : Type*} [CommRing A] [CommRing B] [CommRing SL] [CommRing SR]
    [Algebra A B] [Algebra A SL] [Algebra B SL] [IsScalarTower A B SL]
    [Algebra A SR] [Algebra B SR] [IsScalarTower A B SR]
    (u v : A)
    [IsLocalization.Away u SL] [IsLocalization.Away (algebraMap A B u) SL]
    [IsLocalization.Away v SR] [IsLocalization.Away (algebraMap A B v) SR]
    (hsource : Ideal.span ({algebraMap A B u, algebraMap A B v} : Set B) = ⊤) :
    Set.range (PrimeSpectrum.comap (algebraMap A B)) =
      (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum A)) ∪ PrimeSpectrum.basicOpen v := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨r, hr, hqr⟩ :
        ∃ r ∈ ({algebraMap A B u, algebraMap A B v} : Set B),
          q ∈ PrimeSpectrum.basicOpen r := by
      -- The source chart denominators generate the unit ideal, hence their basic opens cover.
      simpa using
        (PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hsource).ge
          (TopologicalSpace.Opens.mem_top q)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · left
      simpa [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hqr
    · right
      simpa [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hqr
  · intro hp
    -- Each target chart is in the range by the corresponding common-localization adapter.
    rcases hp with hp | hp
    · exact primeSpectrum_basicOpen_subset_comap_range_of_isLocalizationAway (S := SL) u hp
    · exact primeSpectrum_basicOpen_subset_comap_range_of_isLocalizationAway (S := SR) v hp

/-- Helper for Chap10 Example 10 27 4: if two elements generate a maximal point ideal, the
corresponding basic opens are exactly the complement of that point. -/
private theorem primeSpectrum_basicOpen_pair_union_eq_compl_of_span_eq
    {A : Type*} [CommRing A] (u v : A) (p : PrimeSpectrum A)
    [p.asIdeal.IsMaximal]
    (hspan : Ideal.span ({u, v} : Set A) = p.asIdeal) :
    (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum A)) ∪
        PrimeSpectrum.basicOpen v = ({p} : Set (PrimeSpectrum A))ᶜ := by
  ext x
  constructor
  · intro hx hxp
    have hu : u ∈ p.asIdeal := by
      rw [← hspan]
      exact Ideal.subset_span (by simp)
    have hv : v ∈ p.asIdeal := by
      rw [← hspan]
      exact Ideal.subset_span (by simp)
    -- A point in either basic open cannot be the maximal point containing both generators.
    rcases hx with huX | hvX
    · exact (PrimeSpectrum.mem_basicOpen u x).1 huX
        (by simpa [Set.mem_singleton_iff.mp hxp] using hu)
    · exact (PrimeSpectrum.mem_basicOpen v x).1 hvX
        (by simpa [Set.mem_singleton_iff.mp hxp] using hv)
  · intro hxnot
    by_contra hxuv
    simp only [Set.mem_union, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, not_or,
      Classical.not_not] at hxuv
    have hxle : p.asIdeal ≤ x.asIdeal := by
      rw [← hspan]
      rw [Ideal.span_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hxuv.1
      · exact hxuv.2
    -- Maximality forces any prime containing both generators to be the point `p`.
    have hideal : p.asIdeal = x.asIdeal := Ideal.IsMaximal.eq_of_le inferInstance x.2.ne_top hxle
    exact hxnot (by simpa [Set.mem_singleton_iff] using (PrimeSpectrum.ext hideal).symm)

/-- Chap10 Example 10 27 4: for `a ∈ ℚ \ {0, 1/2, 1}`, the inclusion `R ⊆ R_a` induces a
map on prime spectra that is an open embedding, and its image is the complement of the point
corresponding to the evaluation ideal `m_a`. -/
-- Proof sketch: cover `Spec(R_a)` by the two distinguished opens described in the example,
-- identify each restriction with a localization of `R` via Lemma `10.17.5`, and glue the
-- resulting local open embeddings; the image calculation is exactly the statement that only `m_a`
-- is omitted.
@[stacks 00F1]
theorem equal_endpoint_away_prime_spectrum_openEmbedding_range_eq (a : ℚ)
    (h0 : a ≠ 0) (hhalf : a ≠ (1 / 2 : ℚ)) (h1 : a ≠ 1) :
    IsOpenEmbedding
        (comap (algebraMap R (equal_endpoint_away a h0 h1))) ∧
      Set.range
          (comap (algebraMap R (equal_endpoint_away a h0 h1))) =
        ({equal_endpoint_eval_point a} : Set (PrimeSpectrum R))ᶜ :=
by
  -- Route correction: the global-localization route for `R → R_a` is false; the remaining proof
  -- must glue the two chart localizations using the closed source cover below.
  have hgen := equal_endpoint_away_adjoin_linearFractional_eq_top a h0 h1
  have hsourceCover := equal_endpoint_chart_source_span_eq_top a h0 hhalf h1
  have hclearing := equal_endpoint_chart_linearFractional_mul_mem_range a h0 h1
  have htargetSpanLower := equal_endpoint_chart_span_le_eval_point a
  have htargetSpanUpper := equal_endpoint_eval_point_le_chart_span a
  have htargetSpanEq :
      Ideal.span ({equal_endpoint_chartLeft a, equal_endpoint_chartRight a} : Set R) =
        (equal_endpoint_eval_point a).asIdeal := by
    -- The two chart denominators cut out exactly the omitted evaluation point.
    exact le_antisymm htargetSpanLower htargetSpanUpper
  have hleftChart :
      IsLocalization.Away (equal_endpoint_chartLeft a)
        (Localization.Away
          (algebraMap R (equal_endpoint_away a h0 h1) (equal_endpoint_chartLeft a))) := by
    -- The left chart is now a genuine base away localization by the generic clearing lemma.
    exact isLocalizationAway_of_adjoin_singleton_and_clear
      (equal_endpoint_chartLeft a)
      (equal_endpoint_away_linearFractional a h0 h1)
      (equal_endpoint_away_algebraMap_injective a h0 h1) hgen hclearing.1
  have hrightChart :
      IsLocalization.Away (equal_endpoint_chartRight a)
        (Localization.Away
          (algebraMap R (equal_endpoint_away a h0 h1) (equal_endpoint_chartRight a))) := by
    -- The same bridge applies to the right chart using the second clearing identity.
    exact isLocalizationAway_of_adjoin_singleton_and_clear
      (equal_endpoint_chartRight a)
      (equal_endpoint_away_linearFractional a h0 h1)
      (equal_endpoint_away_algebraMap_injective a h0 h1) hgen hclearing.2
  let B := equal_endpoint_away a h0 h1
  let left := equal_endpoint_chartLeft a
  let right := equal_endpoint_chartRight a
  have hrangeUnion :
      Set.range (comap (algebraMap R B)) =
        (PrimeSpectrum.basicOpen left : Set (PrimeSpectrum R)) ∪
          PrimeSpectrum.basicOpen right := by
    -- The range is computed before passing to the complement: the two source chart opens cover
    -- `Spec(B)`, and each target chart is hit by the matching common localization.
    letI :
        IsLocalization.Away left
          (Localization.Away (algebraMap R B left)) := by
      simpa [B, left] using hleftChart
    letI :
        IsLocalization.Away right
          (Localization.Away (algebraMap R B right)) := by
      simpa [B, right] using hrightChart
    simpa [B, left, right] using
      (primeSpectrum_comap_range_eq_basicOpen_union_of_source_span_eq_top
        (A := R) (B := B)
        (SL := Localization.Away (algebraMap R B left))
        (SR := Localization.Away (algebraMap R B right))
        left right hsourceCover)
  have hleftRestrict :
      IsOpenEmbedding
        ((PrimeSpectrum.basicOpen left : Set (PrimeSpectrum R)).restrictPreimage
          (comap (algebraMap R B))) := by
    -- The left restricted map is the base away-localization chart transported through `B`.
    letI :
        IsLocalization.Away left
          (Localization.Away (algebraMap R B left)) := by
      simpa [B, left] using hleftChart
    exact
      primeSpectrum_comap_restrict_basicOpen_isOpenEmbedding_of_isLocalizationAway
        (A := R) (B := B) (S := Localization.Away (algebraMap R B left)) left
  have hrightRestrict :
      IsOpenEmbedding
        ((PrimeSpectrum.basicOpen right : Set (PrimeSpectrum R)).restrictPreimage
          (comap (algebraMap R B))) := by
    -- The same one-chart adapter handles the right restricted map.
    letI :
        IsLocalization.Away right
          (Localization.Away (algebraMap R B right)) := by
      simpa [B, right] using hrightChart
    exact
      primeSpectrum_comap_restrict_basicOpen_isOpenEmbedding_of_isLocalizationAway
        (A := R) (B := B) (S := Localization.Away (algebraMap R B right)) right
  have hopen :
      IsOpenEmbedding (comap (algebraMap R B)) := by
    -- Glue the two restricted open embeddings along the chart union that contains the range.
    exact
      isOpenEmbedding_of_range_subset_union_and_restrictPreimage
        (PrimeSpectrum.continuous_comap (algebraMap R B))
        (PrimeSpectrum.basicOpen left) (PrimeSpectrum.basicOpen right)
        (by
          intro p hp
          simpa [hrangeUnion] using hp)
        hleftRestrict hrightRestrict
  have hpointMax : (equal_endpoint_eval_point a).asIdeal.IsMaximal := by
    let φ : R →+* ℚ := (evalRingHom a).comp (equal_endpoint_poly_subring ℚ).subtype
    have hsurj : Function.Surjective φ := by
      intro q
      refine ⟨⟨Polynomial.C q, ?_⟩, ?_⟩
      · rw [mem_equal_endpoint_poly_subring_iff]
        simp
      · simp [φ]
    have hker : (RingHom.ker φ).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective φ hsurj
    -- The evaluation point is the contraction of the closed point of `Spec(ℚ)`, i.e. this kernel.
    simpa [φ, equal_endpoint_eval_point, PrimeSpectrum.comap_asIdeal, IsLocalRing.closedPoint,
      IsLocalRing.maximalIdeal_eq_bot] using hker
  have hchartUnionComplement :
      (PrimeSpectrum.basicOpen left : Set (PrimeSpectrum R)) ∪
          PrimeSpectrum.basicOpen right =
        ({equal_endpoint_eval_point a} : Set (PrimeSpectrum R))ᶜ := by
    -- The two chart denominators generate the maximal evaluation ideal, so their basic opens
    -- are precisely the complement of that point.
    letI : (equal_endpoint_eval_point a).asIdeal.IsMaximal := hpointMax
    simpa [left, right] using
      primeSpectrum_basicOpen_pair_union_eq_compl_of_span_eq
        (equal_endpoint_chartLeft a) (equal_endpoint_chartRight a)
        (equal_endpoint_eval_point a) htargetSpanEq
  refine ⟨?_, ?_⟩
  · simpa [B] using hopen
  · -- Rewrite the chart-union range as the desired omitted-point complement.
    simpa [B, left, right] using hrangeUnion.trans hchartUnionComplement

/-- Consequence of Chap10 Example 10 27 4: the ring `R_a` is not a localization of `R` at any
multiplicative subset. -/
-- Proof sketch: as explained in the example, every localization of `R` introduces additional
-- units, while the units of `R_a` are still exactly the nonzero rationals because
-- `a ≠ 0, 1, 1/2`.
theorem equal_endpoint_away_not_isLocalization (a : ℚ)
    (h0 : a ≠ 0) (hhalf : a ≠ (1 / 2 : ℚ)) (h1 : a ≠ 1)
    (S : Submonoid R) :
    ¬ IsLocalization S (equal_endpoint_away a h0 h1) := by
  -- Route correction: this cannot use a global localization structure from the previous theorem;
  -- it needs unit reflection for base elements and the range obstruction for the linear-fractional
  -- generator.
  have hnotRange := equal_endpoint_away_linearFractional_not_mem_range a h0 h1
  intro hloc
  letI : IsLocalization S (equal_endpoint_away a h0 h1) := hloc
  have hS_units : S ≤ IsUnit.submonoid R := by
    intro s hs
    exact (equal_endpoint_away_algebraMap_isUnit_iff a h0 hhalf h1 s).mp
      (IsLocalization.map_units (S := equal_endpoint_away a h0 h1) ⟨s, hs⟩)
  let e : R ≃ₐ[R] equal_endpoint_away a h0 h1 :=
    IsLocalization.atUnits R S (S := equal_endpoint_away a h0 h1) hS_units
  have hsurj : Function.Surjective (algebraMap R (equal_endpoint_away a h0 h1)) := by
    intro y
    refine ⟨e.symm y, ?_⟩
    -- The localization at elements that were already units is just the original base ring.
    calc
      algebraMap R (equal_endpoint_away a h0 h1) (e.symm y) = e (e.symm y) := by
        simpa using (e.commutes (e.symm y)).symm
      _ = y := e.apply_symm_apply y
  exact hnotRange (hsurj (equal_endpoint_away_linearFractional a h0 h1))
