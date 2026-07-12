import StacksProject_2024.Chap10.Example_10_55_5.ProjectiveClutching.DiagonalClutching

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: the standard affine generator of the endpoint-ratio
Milnor line. -/
abbrev equalEndpointLinePolynomial (u : kˣ) : equalEndpointPolynomialMulModule k :=
  ((1 + Polynomial.C ((u : k) - 1) * Polynomial.X : Polynomial k) :
    equalEndpointPolynomialMulModule k)

/-- Helper for Chap10 Example 10 55 5: the affine generator belongs to its endpoint-ratio line. -/
theorem equalEndpointLinePolynomial_mem (u : kˣ) :
    equalEndpointLinePolynomial k u ∈ equalEndpointLineSubmodule k u := by
  -- Evaluating the affine generator at `0` and `1` gives the prescribed unit ratio.
  rw [mem_equalEndpointLineSubmodule]
  unfold equalEndpointLineCondition equalEndpointPolynomialMulModule.toPolynomial
    equalEndpointLinePolynomial
  simp

/-- Helper for Chap10 Example 10 55 5: every conductor multiple belongs to every endpoint-ratio
line. -/
theorem equalEndpointLineSubmodule_conductor_mul_mem (u : kˣ) (q : Polynomial k) :
    (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * q : Polynomial k) :
      equalEndpointPolynomialMulModule k) ∈ equalEndpointLineSubmodule k u := by
  -- The conductor vanishes at both endpoints, so the ratio condition is automatic.
  let f : equalEndpointPolynomialMulModule k :=
    (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * q : Polynomial k) :
      equalEndpointPolynomialMulModule k)
  change f ∈ equalEndpointLineSubmodule k u
  exact (mem_equalEndpointLineSubmodule (k := k) u f).mpr
    (equalEndpointLineCondition_conductor_mul (k := k) u q)

/-- Helper for Chap10 Example 10 55 5: products of elements of two Milnor lines lie in the
line with multiplied endpoint ratio. -/
theorem equalEndpointLineSubmodule_mul_le (u v : kˣ) :
    equalEndpointLineSubmodule k u * equalEndpointLineSubmodule k v ≤
      equalEndpointLineSubmodule k (u * v) := by
  -- Reduce membership in the product submodule to products of generators and use the endpoint
  -- ratio multiplication law.
  intro f hf
  exact Submodule.mul_induction_on hf
    (fun x hx y hy => by
      have hxcond :
          equalEndpointLineCondition k u (equalEndpointPolynomialMulModule.toPolynomial k x) :=
        (mem_equalEndpointLineSubmodule (k := k) u x).mp hx
      have hycond :
          equalEndpointLineCondition k v (equalEndpointPolynomialMulModule.toPolynomial k y) :=
        (mem_equalEndpointLineSubmodule (k := k) v y).mp hy
      exact (mem_equalEndpointLineSubmodule (k := k) (u * v) (x * y)).mpr
        (by simpa [equalEndpointPolynomialMulModule.toPolynomial] using
          equalEndpointLineCondition_mul_line (k := k) u v hxcond hycond))
    (fun _ _ hx hy =>
      (equalEndpointLineSubmodule k (u * v)).add_mem hx hy)

/-- Helper for Chap10 Example 10 55 5: every endpoint-ratio line lies in the expected
three-generator span. -/
theorem equalEndpointLineSubmodule_le_span_three (u : kˣ) :
    equalEndpointLineSubmodule k u ≤
      Submodule.span R
        ({(((1 + Polynomial.C ((u : k) - 1) * Polynomial.X : Polynomial k)) :
            equalEndpointPolynomialMulModule k),
          (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) : Polynomial k) :
            equalEndpointPolynomialMulModule k),
          ((((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X : Polynomial k)) :
            equalEndpointPolynomialMulModule k)} :
          Set (equalEndpointPolynomialMulModule k)) := by
  let E : Polynomial k := Polynomial.X ^ 2 - Polynomial.X
  let line : Polynomial k := 1 + Polynomial.C ((u : k) - 1) * Polynomial.X
  let S : Submodule R (equalEndpointPolynomialMulModule k) :=
    Submodule.span R
      ({((line : Polynomial k) : equalEndpointPolynomialMulModule k),
        ((E : Polynomial k) : equalEndpointPolynomialMulModule k),
        ((E * Polynomial.X : Polynomial k) : equalEndpointPolynomialMulModule k)} :
        Set (equalEndpointPolynomialMulModule k))
  intro f hf
  have hfcond :
      equalEndpointLineCondition k u (equalEndpointPolynomialMulModule.toPolynomial k f) := by
    exact (mem_equalEndpointLineSubmodule (k := k) u f).mp hf
  rcases equalEndpointLineCondition_exists_conductor_decomposition (k := k) u hfcond with
    ⟨q, hq⟩
  have hline :
      ((Polynomial.C (Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k f)) *
          line : Polynomial k) : equalEndpointPolynomialMulModule k) ∈ S := by
    let rC : R :=
      ⟨Polynomial.C (Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k f)), by
        rw [mem_equal_endpoint_poly_subring_iff]
        simp⟩
    have hgen : ((line : Polynomial k) : equalEndpointPolynomialMulModule k) ∈ S :=
      Submodule.subset_span (Set.mem_insert _ _)
    have h := S.smul_mem rC hgen
    simpa [rC, line, equalEndpointPolynomialMulModule_smul_eq_mul,
      equalEndpointPolynomialMulModule.toPolynomial] using h
  have hcondPair :
      ((E * q : Polynomial k) : equalEndpointPolynomialMulModule k) ∈
        Submodule.span R
          ({((E : Polynomial k) : equalEndpointPolynomialMulModule k),
            ((E * Polynomial.X : Polynomial k) : equalEndpointPolynomialMulModule k)} :
            Set (equalEndpointPolynomialMulModule k)) := by
    simpa [E] using equalEndpointConductorMul_mem_span_pair (k := k) q
  have hpair_le :
      Submodule.span R
          ({((E : Polynomial k) : equalEndpointPolynomialMulModule k),
            ((E * Polynomial.X : Polynomial k) : equalEndpointPolynomialMulModule k)} :
            Set (equalEndpointPolynomialMulModule k)) ≤ S := by
    apply Submodule.span_mono
    intro x hx
    rcases hx with hx | hx
    · subst hx
      exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · rcases hx with hx
      subst hx
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hcond : ((E * q : Polynomial k) : equalEndpointPolynomialMulModule k) ∈ S :=
    hpair_le hcondPair
  have hsum := S.add_mem hline hcond
  convert hsum using 1

/-- Helper for Chap10 Example 10 55 5: every endpoint-ratio line is generated by its affine
generator and the two conductor generators. -/
theorem equalEndpointLineSubmodule_eq_span_three (u : kˣ) :
    equalEndpointLineSubmodule k u =
      Submodule.span R
        ({(((1 + Polynomial.C ((u : k) - 1) * Polynomial.X : Polynomial k)) :
            equalEndpointPolynomialMulModule k),
          (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) : Polynomial k) :
            equalEndpointPolynomialMulModule k),
          ((((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X : Polynomial k)) :
            equalEndpointPolynomialMulModule k)} :
          Set (equalEndpointPolynomialMulModule k)) := by
  -- The decomposition lemma gives one inclusion; each displayed generator satisfies the
  -- endpoint-ratio condition for the reverse inclusion.
  apply le_antisymm
  · exact equalEndpointLineSubmodule_le_span_three (k := k) u
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · subst hx
      exact equalEndpointLinePolynomial_mem (k := k) u
    · rcases hx with hx | hx
      · subst hx
        simpa using equalEndpointLineSubmodule_conductor_mul_mem (k := k) u 1
      · rcases hx with hx
        subst hx
        simpa [mul_assoc] using
          equalEndpointLineSubmodule_conductor_mul_mem (k := k) u Polynomial.X

/-- Helper for Chap10 Example 10 55 5: every endpoint-ratio Milnor line is finitely generated
over the equal-endpoint ring. -/
theorem equalEndpointLineSubmodule_finite (u : kˣ) :
    Module.Finite R (equalEndpointLineSubmodule k u) := by
  -- The ambient polynomial owner is finite over the Noetherian equal-endpoint ring.
  let _ : IsNoetherianRing R := equal_endpoint_poly_subring_isNoetherian k
  let _ : Module.Finite R (equalEndpointPolynomialMulModule k) := by
    simpa [equalEndpointPolynomialMulModule] using equal_endpoint_polynomial_finite (k := k)
  -- Noetherianity then makes every submodule of that finite ambient module finitely generated.
  apply Module.Finite.of_fg
  have htop : (⊤ : Submodule R (equalEndpointPolynomialMulModule k)).FG := Module.Finite.fg_top
  exact Submodule.FG.of_le htop le_top

/-- Helper for Chap10 Example 10 55 5: every endpoint-ratio Milnor line satisfies the
finitely-generated object property. -/
theorem equalEndpointLineSubmodule_isFG (u : kˣ) :
    ModuleCat.isFG R (ModuleCat.of R (equalEndpointLineSubmodule k u)) := by
  -- Translate finite generation into the object property used by `FGModuleCat`.
  rw [ModuleCat.isFG_iff]
  exact equalEndpointLineSubmodule_finite (k := k) u

/-- Helper for Chap10 Example 10 55 5: package an endpoint-ratio Milnor line as a finitely
generated module. -/
abbrev equalEndpointLineFGModule (u : kˣ) : FGModuleCat R :=
  ⟨ModuleCat.of R (equalEndpointLineSubmodule k u), equalEndpointLineSubmodule_isFG k u⟩

/-- Helper for Chap10 Example 10 55 5: the unit-ratio line consists exactly of the
equal-endpoint polynomials. -/
theorem mem_equalEndpointLineSubmodule_one_iff
    (f : equalEndpointPolynomialMulModule k) :
    f ∈ equalEndpointLineSubmodule k 1 ↔
      equalEndpointPolynomialMulModule.toPolynomial k f ∈ R := by
  -- At ratio `1`, the line condition is precisely equality of the two endpoint evaluations.
  rw [mem_equalEndpointLineSubmodule, mem_equal_endpoint_poly_subring_iff]
  simp [equalEndpointLineCondition, Polynomial.coeff_zero_eq_eval_zero, eq_comm]

/-- Helper for Chap10 Example 10 55 5: the ratio-one Milnor line is the unit submodule. -/
theorem equalEndpointLineSubmodule_one_eq_one :
    equalEndpointLineSubmodule k 1 = (1 : Submodule R (equalEndpointPolynomialMulModule k)) := by
  -- Compare membership: ratio one is the equal-endpoint condition, while `1` is the image of `R`.
  ext f
  constructor
  · intro hf
    have hfR : equalEndpointPolynomialMulModule.toPolynomial k f ∈ R :=
      (mem_equalEndpointLineSubmodule_one_iff (k := k) f).mp hf
    refine Submodule.mem_one.mpr ⟨⟨equalEndpointPolynomialMulModule.toPolynomial k f, hfR⟩, ?_⟩
    rfl
  · intro hf
    rcases Submodule.mem_one.mp hf with ⟨r, hr⟩
    rw [← hr]
    apply (mem_equalEndpointLineSubmodule
      (k := k) 1 (algebraMap R (equalEndpointPolynomialMulModule k) r)).mpr
    unfold equalEndpointLineCondition equalEndpointPolynomialMulModule.toPolynomial
    have hr' :
        (r : Polynomial k).eval 1 = (r : Polynomial k).eval 0 :=
      ((mem_equal_endpoint_poly_subring_iff (k := k) (r : Polynomial k)).mp r.2).symm
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hr'

/-- Helper for Chap10 Example 10 55 5: multiplying on the left by the ratio-one line does not
change a Milnor line. -/
theorem equalEndpointLineSubmodule_one_mul_eq (u : kˣ) :
    equalEndpointLineSubmodule k 1 * equalEndpointLineSubmodule k u =
      equalEndpointLineSubmodule k u := by
  -- Rewrite the ratio-one line to the unit submodule and use the ambient submodule semiring law.
  rw [equalEndpointLineSubmodule_one_eq_one]
  exact one_mul (equalEndpointLineSubmodule k u)

/-- Helper for Chap10 Example 10 55 5: multiplying on the right by the ratio-one line does not
change a Milnor line. -/
theorem equalEndpointLineSubmodule_mul_one_eq (u : kˣ) :
    equalEndpointLineSubmodule k u * equalEndpointLineSubmodule k 1 =
      equalEndpointLineSubmodule k u := by
  -- Rewrite the ratio-one line to the unit submodule and use the ambient submodule semiring law.
  rw [equalEndpointLineSubmodule_one_eq_one]
  exact mul_one (equalEndpointLineSubmodule k u)

/-- Helper for Chap10 Example 10 55 5: the product of two affine linear polynomials has the
expected quadratic normal form. -/
private theorem polynomial_affine_mul_affine (a b : k) :
    (1 + Polynomial.C a * Polynomial.X) * (1 + Polynomial.C b * Polynomial.X) =
      1 + Polynomial.C (a + b) * Polynomial.X +
        Polynomial.C (a * b) * Polynomial.X ^ 2 := by
  -- Expand the product and collect the two linear terms into a single constant coefficient.
  simp only [left_distrib, right_distrib, one_mul, mul_one]
  rw [mul_assoc (Polynomial.C a) Polynomial.X (Polynomial.C b * Polynomial.X)]
  rw [← mul_assoc Polynomial.X (Polynomial.C b) Polynomial.X]
  rw [Polynomial.X_mul_C]
  rw [mul_assoc (Polynomial.C b) Polynomial.X Polynomial.X]
  rw [← mul_assoc (Polynomial.C a) (Polynomial.C b) (Polynomial.X * Polynomial.X)]
  rw [← Polynomial.C_mul]
  rw [← pow_two]
  have hlin :
      Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X =
        Polynomial.C (a + b) * Polynomial.X := by
    rw [← add_mul, ← Polynomial.C_add]
  rw [add_assoc (1 : Polynomial k) (Polynomial.C a * Polynomial.X)
    (Polynomial.C b * Polynomial.X + Polynomial.C (a * b) * Polynomial.X ^ 2)]
  rw [← add_assoc (Polynomial.C a * Polynomial.X) (Polynomial.C b * Polynomial.X)
    (Polynomial.C (a * b) * Polynomial.X ^ 2)]
  rw [hlin]
  rw [← add_assoc]

/-- Helper for Chap10 Example 10 55 5: the product of two Milnor affine generators in expanded
quadratic form. -/
theorem equalEndpointLinePolynomial_mul_expanded (u v : kˣ) :
    equalEndpointPolynomialMulModule.toPolynomial k
        (equalEndpointLinePolynomial k u * equalEndpointLinePolynomial k v) =
      1 + Polynomial.C (((u : k) - 1) + ((v : k) - 1)) * Polynomial.X +
        Polynomial.C (((u : k) - 1) * ((v : k) - 1)) * Polynomial.X ^ 2 := by
  -- This is the affine product formula with the endpoint-ratio coefficients substituted.
  simpa [equalEndpointLinePolynomial, equalEndpointPolynomialMulModule.toPolynomial] using
    (polynomial_affine_mul_affine (k := k) ((u : k) - 1) ((v : k) - 1))

/-- Helper for Chap10 Example 10 55 5: the product of two Milnor affine generators is the
product-ratio affine generator plus a conductor correction. -/
theorem equalEndpointLinePolynomial_mul_line_add_conductor (u v : kˣ) :
    equalEndpointPolynomialMulModule.toPolynomial k
        (equalEndpointLinePolynomial k u * equalEndpointLinePolynomial k v) =
      equalEndpointPolynomialMulModule.toPolynomial k (equalEndpointLinePolynomial k (u * v)) +
        Polynomial.C (((u : k) - 1) * ((v : k) - 1)) *
          (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) := by
  -- Rewrite the expanded quadratic form as the product-ratio generator plus `E = X^2 - X`.
  rw [equalEndpointLinePolynomial_mul_expanded (k := k)]
  dsimp [equalEndpointLinePolynomial, equalEndpointPolynomialMulModule.toPolynomial]
  simp
  ring_nf

/-- Helper for Chap10 Example 10 55 5: the product-ratio affine generator plus its conductor
correction belongs to the product of the two Milnor lines. -/
theorem equalEndpointLineSubmodule_line_add_conductor_mem_mul (u v : kˣ) :
    ((equalEndpointPolynomialMulModule.toPolynomial k (equalEndpointLinePolynomial k (u * v)) +
        Polynomial.C (((u : k) - 1) * ((v : k) - 1)) *
          (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) : Polynomial k) :
      equalEndpointPolynomialMulModule k) ∈
      equalEndpointLineSubmodule k u * equalEndpointLineSubmodule k v := by
  -- The product of the two affine generators is in the product submodule; the polynomial
  -- identity above changes only its normal form.
  have hprod :
      equalEndpointLinePolynomial k u * equalEndpointLinePolynomial k v ∈
        equalEndpointLineSubmodule k u * equalEndpointLineSubmodule k v :=
    Submodule.mul_mem_mul (equalEndpointLinePolynomial_mem (k := k) u)
      (equalEndpointLinePolynomial_mem (k := k) v)
  convert hprod using 1
  exact (equalEndpointLinePolynomial_mul_line_add_conductor (k := k) u v).symm

/-- Helper for Chap10 Example 10 55 5: multiplying `E X` by an affine generator gives
`(1 + a) E X + a E^2`, where `E = X^2 - X`. -/
private theorem polynomial_affine_mul_conductor_X (a : k) :
    (1 + Polynomial.C a * Polynomial.X) *
        ((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X) =
      Polynomial.C (1 + a) *
          ((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X) +
        Polynomial.C a * (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) ^ 2 := by
  -- First move the extra `X` onto the conductor term, then use `E X^2 = E X + E^2`.
  have hstep :
      (1 + Polynomial.C a * Polynomial.X) *
          ((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X) =
        (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X +
          Polynomial.C a *
            ((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X ^ 2) := by
    ring_nf
  have hconductor :
      (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X ^ 2 =
        (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X +
          (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) ^ 2 := by
    ring_nf
  have hcollect (P : Polynomial k) :
      P + Polynomial.C a * P = Polynomial.C (1 + a) * P := by
    rw [Polynomial.C_add, Polynomial.C_1, add_mul, one_mul]
  rw [hstep, hconductor]
  rw [mul_add]
  rw [← add_assoc]
  rw [hcollect]

/-- Helper for Chap10 Example 10 55 5: the conductor generator `E X` belongs to
`I_u * I_v`. -/
theorem equalEndpointLineSubmodule_conductor_X_mem_mul (u v : kˣ) :
    ((((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X : Polynomial k)) :
      equalEndpointPolynomialMulModule k) ∈
      equalEndpointLineSubmodule k u * equalEndpointLineSubmodule k v := by
  let P : Submodule R (equalEndpointPolynomialMulModule k) :=
    equalEndpointLineSubmodule k u * equalEndpointLineSubmodule k v
  let E : equalEndpointPolynomialMulModule k :=
    (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) : Polynomial k) :
      equalEndpointPolynomialMulModule k)
  let EX : equalEndpointPolynomialMulModule k :=
    ((((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X : Polynomial k)) :
      equalEndpointPolynomialMulModule k)
  let E2 : equalEndpointPolynomialMulModule k :=
    ((((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) ^ 2 : Polynomial k)) :
      equalEndpointPolynomialMulModule k)
  let scaledE2 : equalEndpointPolynomialMulModule k :=
    (((Polynomial.C ((u : k) - 1) *
        (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) ^ 2 : Polynomial k)) :
      equalEndpointPolynomialMulModule k)
  have hEXv : EX ∈ equalEndpointLineSubmodule k v := by
    simpa [EX] using equalEndpointLineSubmodule_conductor_mul_mem (k := k) v Polynomial.X
  have hlineEX : equalEndpointLinePolynomial k u * EX ∈ P := by
    exact Submodule.mul_mem_mul (equalEndpointLinePolynomial_mem (k := k) u) hEXv
  have hEu : E ∈ equalEndpointLineSubmodule k u := by
    simpa [E] using equalEndpointLineSubmodule_conductor_mul_mem (k := k) u 1
  have hEv : E ∈ equalEndpointLineSubmodule k v := by
    simpa [E] using equalEndpointLineSubmodule_conductor_mul_mem (k := k) v 1
  have hE2 : E * E ∈ P := by
    exact Submodule.mul_mem_mul hEu hEv
  have hE2poly : E2 ∈ P := by
    simpa [E, E2, pow_two] using hE2
  have hscaledE2 : scaledE2 ∈ P := by
    have h := P.smul_mem (equal_endpoint_constant (k := k) ((u : k) - 1)) hE2poly
    simpa [P, E2, scaledE2, equal_endpoint_constant,
      equalEndpointPolynomialMulModule_smul_eq_mul,
      equalEndpointPolynomialMulModule.toPolynomial] using h
  have hdiff : equalEndpointLinePolynomial k u * EX - scaledE2 ∈ P := by
    exact P.sub_mem hlineEX hscaledE2
  have hunitScaled := P.smul_mem (equal_endpoint_constant (k := k) ((u : k)⁻¹)) hdiff
  convert hunitScaled using 1
  change (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X =
      Polynomial.C ((u : k)⁻¹) *
        (((1 + Polynomial.C ((u : k) - 1) * Polynomial.X) *
            ((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X)) -
          Polynomial.C ((u : k) - 1) * (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) ^ 2)
  rw [polynomial_affine_mul_conductor_X (k := k)]
  have hone : (1 + ((u : k) - 1)) = (u : k) := by
    ring
  rw [hone]
  rw [add_sub_cancel_right]
  rw [← mul_assoc, ← Polynomial.C_mul]
  have hunit : ((u : k)⁻¹ * (u : k)) = 1 :=
    inv_mul_cancel₀ (Units.ne_zero u)
  rw [hunit, Polynomial.C_1, one_mul]

/-- Helper for Chap10 Example 10 55 5: multiplying the conductor by an affine generator only
adds the displayed `E X` term. -/
private theorem polynomial_affine_mul_conductor_sub_conductor_X (a : k) :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) =
      (1 + Polynomial.C a * Polynomial.X) *
          (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) -
        Polynomial.C a * ((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X) := by
  -- This polynomial identity isolates `E` from the product of an affine generator with `E`.
  ring_nf

/-- Helper for Chap10 Example 10 55 5: the conductor generator `E` belongs to `I_u * I_v`. -/
theorem equalEndpointLineSubmodule_conductor_mem_mul (u v : kˣ) :
    (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) : Polynomial k) :
      equalEndpointPolynomialMulModule k) ∈
      equalEndpointLineSubmodule k u * equalEndpointLineSubmodule k v := by
  let P : Submodule R (equalEndpointPolynomialMulModule k) :=
    equalEndpointLineSubmodule k u * equalEndpointLineSubmodule k v
  let E : equalEndpointPolynomialMulModule k :=
    (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) : Polynomial k) :
      equalEndpointPolynomialMulModule k)
  let EX : equalEndpointPolynomialMulModule k :=
    ((((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X : Polynomial k)) :
      equalEndpointPolynomialMulModule k)
  let scaledEX : equalEndpointPolynomialMulModule k :=
    (((Polynomial.C ((u : k) - 1) *
        ((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X) : Polynomial k)) :
      equalEndpointPolynomialMulModule k)
  have hEv : E ∈ equalEndpointLineSubmodule k v := by
    simpa [E] using equalEndpointLineSubmodule_conductor_mul_mem (k := k) v 1
  have hlineE : equalEndpointLinePolynomial k u * E ∈ P := by
    exact Submodule.mul_mem_mul (equalEndpointLinePolynomial_mem (k := k) u) hEv
  have hEX : EX ∈ P := by
    simpa [EX] using equalEndpointLineSubmodule_conductor_X_mem_mul (k := k) u v
  have hscaledEX : scaledEX ∈ P := by
    have h := P.smul_mem (equal_endpoint_constant (k := k) ((u : k) - 1)) hEX
    simpa [P, EX, scaledEX, equal_endpoint_constant,
      equalEndpointPolynomialMulModule_smul_eq_mul,
      equalEndpointPolynomialMulModule.toPolynomial] using h
  have hdiff : equalEndpointLinePolynomial k u * E - scaledEX ∈ P := by
    exact P.sub_mem hlineE hscaledEX
  rw [polynomial_affine_mul_conductor_sub_conductor_X (k := k) ((u : k) - 1)]
  simpa [P, E, EX, scaledEX, equalEndpointLinePolynomial,
    equalEndpointPolynomialMulModule.toPolynomial] using hdiff

/-- Helper for Chap10 Example 10 55 5: endpoint-ratio Milnor lines multiply by multiplying
their endpoint units. -/
theorem equalEndpointLineSubmodule_mul_eq (u v : kˣ) :
    equalEndpointLineSubmodule k u * equalEndpointLineSubmodule k v =
      equalEndpointLineSubmodule k (u * v) := by
  -- The easy inclusion is multiplicativity of endpoint ratios; the reverse inclusion uses the
  -- three-generator normal form and the two conductor-generator membership lemmas above.
  apply le_antisymm
  · exact equalEndpointLineSubmodule_mul_le (k := k) u v
  · rw [equalEndpointLineSubmodule_eq_span_three (k := k) (u * v)]
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · subst hx
      let P : Submodule R (equalEndpointPolynomialMulModule k) :=
        equalEndpointLineSubmodule k u * equalEndpointLineSubmodule k v
      let c : k := ((u : k) - 1) * ((v : k) - 1)
      let cE : equalEndpointPolynomialMulModule k :=
        (((Polynomial.C c * (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) :
          Polynomial k)) : equalEndpointPolynomialMulModule k)
      let linePlus : equalEndpointPolynomialMulModule k :=
        ((equalEndpointPolynomialMulModule.toPolynomial k (equalEndpointLinePolynomial k (u * v)) +
          Polynomial.C c * (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) : Polynomial k) :
          equalEndpointPolynomialMulModule k)
      have hsum : linePlus ∈ P := by
        simpa [P, c, linePlus] using
          equalEndpointLineSubmodule_line_add_conductor_mem_mul (k := k) u v
      have hE :
          (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) : Polynomial k) :
            equalEndpointPolynomialMulModule k) ∈ P := by
        simpa [P] using equalEndpointLineSubmodule_conductor_mem_mul (k := k) u v
      have hscaledE : cE ∈ P := by
        have h := P.smul_mem (equal_endpoint_constant (k := k) c) hE
        simpa [P, c, cE, equal_endpoint_constant,
          equalEndpointPolynomialMulModule_smul_eq_mul,
          equalEndpointPolynomialMulModule.toPolynomial] using h
      have hdiff : linePlus - cE ∈ P := by
        exact P.sub_mem hsum hscaledE
      have hcancel : linePlus - cE = equalEndpointLinePolynomial k (u * v) := by
        change (equalEndpointPolynomialMulModule.toPolynomial k
              (equalEndpointLinePolynomial k (u * v)) +
            Polynomial.C c * (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) -
            Polynomial.C c * (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) :
            Polynomial k) =
          equalEndpointPolynomialMulModule.toPolynomial k (equalEndpointLinePolynomial k (u * v))
        abel
      change equalEndpointLinePolynomial k (u * v) ∈ P
      rw [← hcancel]
      exact hdiff
    · rcases hx with hx | hx
      · subst hx
        simpa using equalEndpointLineSubmodule_conductor_mem_mul (k := k) u v
      · rcases hx with hx
        subst hx
        simpa using equalEndpointLineSubmodule_conductor_X_mem_mul (k := k) u v

/-- Helper for Chap10 Example 10 55 5: multiplying a Milnor line by the inverse-ratio line gives
the unit submodule. -/
theorem equalEndpointLineSubmodule_mul_inv_eq_one (u : kˣ) :
    equalEndpointLineSubmodule k u * equalEndpointLineSubmodule k (u⁻¹) =
      (1 : Submodule R (equalEndpointPolynomialMulModule k)) := by
  -- The product law reduces the inverse product to the already identified ratio-one line.
  rw [equalEndpointLineSubmodule_mul_eq]
  simpa using equalEndpointLineSubmodule_one_eq_one (k := k)

/-- Helper for Chap10 Example 10 55 5: the inverse-ratio line multiplied by a Milnor line gives
the unit submodule. -/
theorem equalEndpointLineSubmodule_inv_mul_eq_one (u : kˣ) :
    equalEndpointLineSubmodule k (u⁻¹) * equalEndpointLineSubmodule k u =
      (1 : Submodule R (equalEndpointPolynomialMulModule k)) := by
  -- The product law reduces the inverse product to the already identified ratio-one line.
  rw [equalEndpointLineSubmodule_mul_eq]
  simpa using equalEndpointLineSubmodule_one_eq_one (k := k)

/-- Helper for Chap10 Example 10 55 5: package a Milnor line as a unit in the submodule monoid. -/
noncomputable def equalEndpointLineSubmoduleUnit (u : kˣ) :
    (Submodule R (equalEndpointPolynomialMulModule k))ˣ :=
  { val := equalEndpointLineSubmodule k u
    inv := equalEndpointLineSubmodule k (u⁻¹)
    val_inv := equalEndpointLineSubmodule_mul_inv_eq_one k u
    inv_val := equalEndpointLineSubmodule_inv_mul_eq_one k u }

/-- Helper for Chap10 Example 10 55 5: the underlying submodule of the packaged unit is the
corresponding Milnor line. -/
@[simp]
theorem equalEndpointLineSubmoduleUnit_coe (u : kˣ) :
    ((equalEndpointLineSubmoduleUnit k u :
        (Submodule R (equalEndpointPolynomialMulModule k))ˣ) :
        Submodule R (equalEndpointPolynomialMulModule k)) =
      equalEndpointLineSubmodule k u := rfl

/-- Helper for Chap10 Example 10 55 5: the unit package sends the ratio-one element to the
trivial submodule unit. -/
theorem equalEndpointLineSubmoduleUnit_one :
    equalEndpointLineSubmoduleUnit k 1 =
      (1 : (Submodule R (equalEndpointPolynomialMulModule k))ˣ) := by
  -- Units are equal once their underlying submodules are equal.
  apply Units.ext
  exact equalEndpointLineSubmodule_one_eq_one (k := k)

/-- Helper for Chap10 Example 10 55 5: every unit of the polynomial multiplication owner has an
underlying polynomial lying in the equal-endpoint subring. -/
theorem equalEndpointPolynomialMulModule_unit_toPolynomial_mem
    (x : (equalEndpointPolynomialMulModule k)ˣ) :
    equalEndpointPolynomialMulModule.toPolynomial k x ∈ R := by
  have hxunit : IsUnit (equalEndpointPolynomialMulModule.toPolynomial k x) := by
    -- The multiplication owner is definitionally `k[X]`, so a unit in the owner is a polynomial
    -- unit.
    exact ⟨x, rfl⟩
  rcases Polynomial.isUnit_iff.mp hxunit with ⟨c, _hc, hC⟩
  -- Polynomial units over a field are constants, and constants have equal endpoint values.
  rw [← hC]
  rw [mem_equal_endpoint_poly_subring_iff]
  simp

/-- Helper for Chap10 Example 10 55 5: the principal submodule generated by a unit of the
polynomial multiplication owner is the unit submodule. -/
theorem equalEndpointPolynomialMulModule_unit_spanSingleton_eq_one
    (x : (equalEndpointPolynomialMulModule k)ˣ) :
    Submodule.spanSingleton R (x : equalEndpointPolynomialMulModule k) =
      (1 : Submodule R (equalEndpointPolynomialMulModule k)) := by
  letI : FaithfulSMul R (equalEndpointPolynomialMulModule k) :=
    equalEndpointPolynomialMulModule_faithfulSMul k
  let hxR : equalEndpointPolynomialMulModule.toPolynomial k x ∈ R :=
    equalEndpointPolynomialMulModule_unit_toPolynomial_mem (k := k) x
  let xinv : (equalEndpointPolynomialMulModule k)ˣ := x⁻¹
  let hxInvR : equalEndpointPolynomialMulModule.toPolynomial k xinv ∈ R :=
    equalEndpointPolynomialMulModule_unit_toPolynomial_mem (k := k) xinv
  let r : R := ⟨equalEndpointPolynomialMulModule.toPolynomial k x, hxR⟩
  let s : R := ⟨equalEndpointPolynomialMulModule.toPolynomial k xinv, hxInvR⟩
  have hrs : r * s = 1 := by
    -- The inverse polynomial is again equal-endpoint, so the unit equation takes place in `R`.
    apply Subtype.ext
    exact x.val_inv
  let ru : Rˣ := Units.mkOfMulEqOne r s hrs
  rw [Submodule.spanSingleton_apply]
  -- The generator is the image of a unit of `R`; mathlib's span-singleton criterion applies.
  refine Submodule.span_singleton_eq_one_iff.mpr ⟨ru, ?_⟩
  change equalEndpointPolynomialMulModule.toPolynomial k x = (r : Polynomial k)
  rfl

/-- Helper for Chap10 Example 10 55 5: the principal submodule unit generated by an ambient
polynomial unit is the trivial submodule unit. -/
theorem equalEndpointPolynomialMulModule_unit_spanSingletonUnit_eq_one
    (x : (equalEndpointPolynomialMulModule k)ˣ) :
    Units.map (Submodule.spanSingleton R).toMonoidHom x =
      (1 : (Submodule R (equalEndpointPolynomialMulModule k))ˣ) := by
  -- The underlying submodule is the span of a polynomial unit, hence the unit submodule.
  apply Units.ext
  exact equalEndpointPolynomialMulModule_unit_spanSingleton_eq_one (k := k) x

/-- Helper for Chap10 Example 10 55 5: multiplying a Milnor-line unit by a principal ambient
unit does not change it. -/
theorem equalEndpointPrincipalUnit_mul_lineSubmoduleUnit
    (x : (equalEndpointPolynomialMulModule k)ˣ) (unitRatio : kˣ) :
    Units.map (Submodule.spanSingleton R).toMonoidHom x *
        equalEndpointLineSubmoduleUnit k unitRatio =
      equalEndpointLineSubmoduleUnit k unitRatio := by
  -- The principal ambient-unit factor is already the identity in the submodule-unit group.
  rw [equalEndpointPolynomialMulModule_unit_spanSingletonUnit_eq_one, one_mul]

/-- Helper for Chap10 Example 10 55 5: a Milnor line unit is principal exactly for endpoint
ratio `1`. -/
theorem equalEndpointLineUnit_principal_iff (unitRatio : kˣ) :
    equalEndpointLineSubmoduleUnit k unitRatio ∈
        (Units.map (Submodule.spanSingleton R).toMonoidHom).range ↔
      unitRatio = 1 := by
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    have hxone : Units.map (Submodule.spanSingleton R).toMonoidHom x =
        (1 : (Submodule R (equalEndpointPolynomialMulModule k))ˣ) := by
      -- Principal submodules generated by ambient units are all the unit submodule here.
      apply Units.ext
      exact equalEndpointPolynomialMulModule_unit_spanSingleton_eq_one (k := k) x
    have hunit : equalEndpointLineSubmoduleUnit k unitRatio =
        (1 : (Submodule R (equalEndpointPolynomialMulModule k))ˣ) := by
      exact hx.symm.trans hxone
    have hsub : equalEndpointLineSubmodule k unitRatio =
        (1 : Submodule R (equalEndpointPolynomialMulModule k)) := by
      -- Compare the underlying submodules of the two units.
      simpa using congrArg
        (fun z : (Submodule R (equalEndpointPolynomialMulModule k))ˣ =>
          (z : Submodule R (equalEndpointPolynomialMulModule k))) hunit
    have hmem_one : equalEndpointLinePolynomial k unitRatio ∈
        equalEndpointLineSubmodule k 1 := by
      -- The affine generator of `I_u` becomes an element of the ratio-one line.
      rw [equalEndpointLineSubmodule_one_eq_one]
      rw [← hsub]
      exact equalEndpointLinePolynomial_mem (k := k) unitRatio
    have hcond := (mem_equalEndpointLineSubmodule (k := k) 1
      (equalEndpointLinePolynomial k unitRatio)).mp hmem_one
    apply Units.ext
    -- Evaluating the affine generator at `0` and `1` forces the ratio to be `1`.
    unfold equalEndpointLineCondition equalEndpointLinePolynomial
      equalEndpointPolynomialMulModule.toPolynomial at hcond
    simpa using hcond
  · intro h
    rw [h]
    -- The diagonal ratio line is the principal unit submodule generated by `1`.
    refine ⟨1, ?_⟩
    simpa [equalEndpointLineSubmoduleUnit_one]

/-- Helper for Chap10 Example 10 55 5: the unit package is multiplicative in endpoint ratios. -/
theorem equalEndpointLineSubmoduleUnit_mul (u v : kˣ) :
    equalEndpointLineSubmoduleUnit k (u * v) =
      equalEndpointLineSubmoduleUnit k u * equalEndpointLineSubmoduleUnit k v := by
  -- Equality of units is checked on underlying submodules, where it is exactly the product law.
  apply Units.ext
  exact (equalEndpointLineSubmodule_mul_eq (k := k) u v).symm

/-- Helper for Chap10 Example 10 55 5: endpoint-unit ratios act multiplicatively on invertible
Milnor line submodules. -/
noncomputable def equalEndpointLineSubmoduleUnitHom :
    kˣ →* (Submodule R (equalEndpointPolynomialMulModule k))ˣ :=
  { toFun := equalEndpointLineSubmoduleUnit k
    map_one' := equalEndpointLineSubmoduleUnit_one k
    map_mul' := equalEndpointLineSubmoduleUnit_mul k }

/-- Helper for Chap10 Example 10 55 5: every Milnor line is an invertible submodule of the
normalization. -/
theorem equalEndpointLineSubmodule_isUnit (u : kˣ) :
    IsUnit (equalEndpointLineSubmodule k u) := by
  -- The explicit unit package has underlying value `I_u`.
  exact ⟨equalEndpointLineSubmoduleUnit k u, rfl⟩

end
