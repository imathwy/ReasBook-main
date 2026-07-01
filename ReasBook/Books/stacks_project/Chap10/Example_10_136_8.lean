import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial

/-- The polynomial-ring map `ℤ[a₁, \ldots, aₙ] → ℤ[α₁, \ldots, αₙ]` sending `aᵢ` to the
`i`th elementary symmetric polynomial in the variables `α₁, \ldots, αₙ`. It is the source-facing
map obtained by composing the canonical owner `MvPolynomial.esymmAlgHom` with the inclusion of the
symmetric subalgebra into the full polynomial ring. -/
noncomputable def elementary_symmetric_ring_hom (n : ℕ) :
    MvPolynomial (Fin n) ℤ →ₐ[ℤ] MvPolynomial (Fin n) ℤ :=
  (symmetricSubalgebra (Fin n) ℤ).val.comp (esymmAlgHom (Fin n) ℤ n)

/-- The elementary-symmetric map sends the source variable `aᵢ` to the corresponding elementary
symmetric polynomial in the root variables. -/
@[simp] theorem elementary_symmetric_ring_hom_apply_X (n : ℕ) (i : Fin n) :
    elementary_symmetric_ring_hom n (X i) = esymm (Fin n) ℤ (i + 1) := by
  simp [elementary_symmetric_ring_hom, esymmAlgHom]

/-- Helper for Example 10.136.8: the elementary-symmetric map is injective because it is the
canonical embedding of the universal coefficient ring into the symmetric subalgebra. -/
theorem elementary_symmetric_ring_hom_injective (n : ℕ) :
    Function.Injective (elementary_symmetric_ring_hom n) := by
  intro p q hpq
  have hsub :
      esymmAlgHom (Fin n) ℤ n p = esymmAlgHom (Fin n) ℤ n q := by
    -- Forgetting from the symmetric subalgebra to the full polynomial ring is faithful.
    exact Subtype.ext hpq
  exact
    (esymmAlgHom_injective (R := ℤ) (σ := Fin n) (n := n) (by simp : n ≤ Fintype.card (Fin n)))
      hsub

/-- Helper for Example 10.136.8: after reversing the source coefficient variables to match
`Polynomial.freeMonic`, the elementary-symmetric map sends the universal monic polynomial to the
split product `∏ i, (X + αᵢ)`. -/
theorem freeMonic_map_elementary_symmetric_ring_hom_rev (n : ℕ) :
    (Polynomial.freeMonic ℤ n).map
        (((elementary_symmetric_ring_hom n).comp (rename Fin.rev)).toRingHom) =
      ∏ i : Fin n, (Polynomial.X + Polynomial.C (MvPolynomial.X i)) := by
  -- Route correction: `Polynomial.freeMonic` stores coefficients in ascending degree order,
  -- so we precompose with `rename Fin.rev` to match the textbook descending-order convention.
  ext k m
  by_cases hk : k < n
  · -- For coefficients below the top degree, Vieta identifies the product coefficient directly.
    have hk' : k ≤ Fintype.card (Fin n) := by
      simpa using Nat.le_of_lt hk
    rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic, dif_pos hk,
      MvPolynomial.prod_X_add_C_coeff (R := ℤ) (σ := Fin n) k hk']
    have hindex : n - (k + 1) + 1 = n - k := by
      omega
    simp [AlgHom.comp_apply, hindex]
  · have hkn : n ≤ k := Nat.le_of_not_gt hk
    cases Nat.eq_or_lt_of_le hkn with
    | inl hEq =>
        -- At the top degree, both polynomials are monic.
        subst hEq
        rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic, dif_neg (Nat.lt_irrefl _)]
        simp [MvPolynomial.prod_X_add_C_coeff (R := ℤ) (σ := Fin n) n (by simp)]
    | inr hlt =>
        -- Above degree `n`, both sides have zero coefficient.
        rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic, dif_neg hk]
        have hkne : k ≠ n := by
          omega
        have hleft :
            (((elementary_symmetric_ring_hom n).comp (rename Fin.rev)).toRingHom)
              (if k = n then 1 else 0) = 0 := by
          simp [hkne]
        rw [hleft]
        simp
        have hnat :
            ((∏ i : Fin n, (Polynomial.X + Polynomial.C (MvPolynomial.X i))) :
              Polynomial (MvPolynomial (Fin n) ℤ)).natDegree = n := by
          rw [Polynomial.natDegree_prod_of_monic]
          · simp
          · intro i _
            exact Polynomial.monic_X_add_C (MvPolynomial.X i : MvPolynomial (Fin n) ℤ)
        have hcoeff :
            (((∏ i : Fin n, (Polynomial.X + Polynomial.C (MvPolynomial.X i))) :
              Polynomial (MvPolynomial (Fin n) ℤ)).coeff k) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (p := ((∏ i : Fin n,
            (Polynomial.X + Polynomial.C (MvPolynomial.X i))) :
            Polynomial (MvPolynomial (Fin n) ℤ))) (by
              simpa [hnat] using hlt)
        exact (congrArg (fun q : MvPolynomial (Fin n) ℤ => q.coeff m) hcoeff).symm

/-- Helper for Example 10.136.8: after transporting the successor target through
`MvPolynomial.finSuccEquiv`, the split universal polynomial isolates the distinguished linear
factor corresponding to the `0`th root variable. -/
noncomputable def freeMonic_succ_remainder (n : ℕ) :
    Polynomial (Polynomial (MvPolynomial (Fin n) ℤ)) :=
  ∏ i : Fin n,
    ((Polynomial.X : Polynomial (Polynomial (MvPolynomial (Fin n) ℤ))) +
      Polynomial.C (Polynomial.C (MvPolynomial.X i)))

/-- Helper for Example 10.136.8: the transported successor split polynomial factors as the
distinguished linear factor times the concrete remainder `freeMonic_succ_remainder n`. -/
theorem freeMonic_succ_factorization_under_finSuccEquiv (n : ℕ) :
    Polynomial.map (MvPolynomial.finSuccEquiv ℤ n).toRingHom
        ((Polynomial.freeMonic ℤ (n + 1)).map
          (((elementary_symmetric_ring_hom (n + 1)).comp (rename Fin.revPerm)).toRingHom)) =
      (((Polynomial.X : Polynomial (Polynomial (MvPolynomial (Fin n) ℤ))) +
          Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin n) ℤ))) *
        freeMonic_succ_remainder n) := by
  -- Route correction: normalize the successor step first under `finSuccEquiv`, so the singled-out
  -- root variable becomes the outer polynomial variable and the remaining variables stay in the
  -- coefficient ring.
  have hmap :=
    congrArg (Polynomial.map (MvPolynomial.finSuccEquiv ℤ n).toRingHom)
      (freeMonic_map_elementary_symmetric_ring_hom_rev (n + 1))
  -- Mapping coefficients through `finSuccEquiv` turns the `0`th root variable into `X` and each
  -- successor variable into a coefficient variable.
  simpa [freeMonic_succ_remainder, Fin.prod_univ_succ, Polynomial.map_prod,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
    MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ] using hmap

/-- Helper for Example 10.136.8: the concrete remainder polynomial in the successor factorization
is monic, since it is a product of monic linear factors. -/
theorem freeMonic_succ_remainder_monic (n : ℕ) :
    (freeMonic_succ_remainder n).Monic := by
  -- Each displayed factor is monic in the outer polynomial variable, so their product is monic.
  refine Polynomial.monic_prod_of_monic _ _ ?_
  intro i hi
  exact Polynomial.monic_X_add_C (Polynomial.C (MvPolynomial.X i))

/-- Helper for Example 10.136.8: after the `finSuccEquiv` transport, the distinguished outer
variable `-X` is a root of the successor free monic polynomial. -/
theorem freeMonic_succ_eval_neg_X_eq_zero (n : ℕ) :
    Polynomial.eval (-(Polynomial.X : Polynomial (MvPolynomial (Fin n) ℤ)))
      (Polynomial.map (MvPolynomial.finSuccEquiv ℤ n).toRingHom
        ((Polynomial.freeMonic ℤ (n + 1)).map
          (((elementary_symmetric_ring_hom (n + 1)).comp (rename Fin.revPerm)).toRingHom))) = 0 := by
  -- Evaluating at the negated distinguished variable kills the first linear factor directly.
  rw [freeMonic_succ_factorization_under_finSuccEquiv]
  simp [freeMonic_succ_remainder]

/-- Helper for Example 10.136.8: this is the transported successor algebra structure on
`Polynomial (MvPolynomial (Fin n) ℤ)` coming from the reversed elementary-symmetric map after the
`finSuccEquiv` normalization. -/
@[reducible]
noncomputable def freeMonic_succ_normalizedAlgebra (n : ℕ) :
    Algebra (MvPolynomial (Fin (n + 1)) ℤ) (Polynomial (MvPolynomial (Fin n) ℤ)) :=
  (RingHom.comp (MvPolynomial.finSuccEquiv ℤ n).toRingHom
    (((elementary_symmetric_ring_hom (n + 1)).comp (rename Fin.revPerm)).toRingHom)).toAlgebra

/-- Helper for Example 10.136.8: in the normalized successor presentation, the distinguished outer
variable `-X` is integral over the transported reversed coefficient ring because it is a root of
the universal monic polynomial. -/
theorem freeMonic_succ_isIntegral_neg_X (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let B := Polynomial (MvPolynomial (Fin n) ℤ)
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    IsIntegral A (-(Polynomial.X : B)) := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let B := Polynomial (MvPolynomial (Fin n) ℤ)
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  -- Repackage the already-proved `eval` identity as the `aeval` root relation over `A`.
  have hroot : Polynomial.aeval (-(Polynomial.X : B)) (Polynomial.freeMonic ℤ (n + 1)) = 0 := by
    have hEval :
        (Polynomial.map (algebraMap A B) (Polynomial.freeMonic ℤ (n + 1))).eval
          (-(Polynomial.X : B)) = 0 := by
      simpa only [freeMonic_succ_normalizedAlgebra, A, B, RingHom.comp_assoc, Polynomial.map_map] using
        freeMonic_succ_eval_neg_X_eq_zero n
    -- Replace the mapped-polynomial evaluation by the corresponding `aeval`.
    rw [Polynomial.eval_map_algebraMap] at hEval
    exact hEval
  have hzero : IsIntegral A (0 : B) := isIntegral_zero
  have haeval : IsIntegral A (Polynomial.aeval (-(Polynomial.X : B)) (Polynomial.freeMonic ℤ (n + 1))) := by
    simpa [hroot] using hzero
  -- Apply the standard monic-root criterion to the universal monic polynomial.
  simpa using
    (IsIntegral.of_aeval_monic (x := -(Polynomial.X : B))
      (p := Polynomial.freeMonic ℤ (n + 1))
      (Polynomial.monic_freeMonic ℤ (n + 1))
      (by simpa [Polynomial.natDegree_freeMonic] using Nat.succ_ne_zero n) haeval)

/-- Helper for Example 10.136.8: once the normalized successor ring is known to be generated by
`-(Polynomial.X)`, the one-root successor stage is free by the standard power-basis package. -/
theorem freeMonic_succ_free_of_adjoin_neg_X_eq_top (n : ℕ)
    (hTop :
      let A := MvPolynomial (Fin (n + 1)) ℤ
      let B := Polynomial (MvPolynomial (Fin n) ℤ)
      letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
      Algebra.adjoin A ({-(Polynomial.X : B)} : Set B) = ⊤) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let B := Polynomial (MvPolynomial (Fin n) ℤ)
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    Module.Free A B := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let B := Polynomial (MvPolynomial (Fin n) ℤ)
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  have hNormalized_injective : Function.Injective (algebraMap A B) := by
    -- The normalized source action is `rename Fin.revPerm`, then the injective
    -- elementary-symmetric map, then the algebra equivalence `finSuccEquiv`.
    have hcomp :
        Function.Injective
          ((((elementary_symmetric_ring_hom (n + 1)).comp (rename Fin.revPerm)).toRingHom) :
            A → A) := by
      exact (elementary_symmetric_ring_hom_injective (n + 1)).comp
        (MvPolynomial.rename_injective (R := ℤ) Fin.revPerm (Equiv.injective Fin.revPerm))
    intro a b hab
    dsimp [freeMonic_succ_normalizedAlgebra, A, B] at hab
    exact hcomp ((MvPolynomial.finSuccEquiv ℤ n).injective hab)
  letI : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hNormalized_injective
  -- Route correction: once `-(Polynomial.X)` generates the normalized successor algebra, the
  -- commutative-ring power-basis package gives freeness directly, so no extra injectivity bridge
  -- is needed here.
  let pb : PowerBasis A B :=
    PowerBasis.ofAdjoinEqTop' (x := -(Polynomial.X : B))
      (freeMonic_succ_isIntegral_neg_X n) hTop
  -- A power basis is, in particular, a module basis.
  exact Module.Free.of_basis pb.basis

/-- Helper for Example 10.136.8: the normalized successor root relation can be rewritten in the
`aeval` form needed to map out of the one-root extension `AdjoinRoot (freeMonic)`. -/
theorem freeMonic_succ_aeval_neg_X_eq_zero (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let B := Polynomial (MvPolynomial (Fin n) ℤ)
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    Polynomial.aeval (-(Polynomial.X : B)) (Polynomial.freeMonic ℤ (n + 1)) = 0 := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let B := Polynomial (MvPolynomial (Fin n) ℤ)
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  -- Expand `aeval` into evaluation after mapping coefficients through the normalized algebra map.
  have hEval :
      (Polynomial.map (algebraMap A B) (Polynomial.freeMonic ℤ (n + 1))).eval
        (-(Polynomial.X : B)) = 0 := by
    simpa only [freeMonic_succ_normalizedAlgebra, A, B, RingHom.comp_assoc, Polynomial.map_map] using
      freeMonic_succ_eval_neg_X_eq_zero n
  -- Replace the mapped-polynomial evaluation by the corresponding `aeval`.
  rw [Polynomial.eval_map_algebraMap] at hEval
  exact hEval

/-- Helper for Example 10.136.8: the normalized successor target receives the canonical map from
the one-root extension `AdjoinRoot (freeMonic)` by sending the adjoined root to `-(X)`. -/
noncomputable def freeMonic_succ_adjoinRoot_to_normalized (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let B := Polynomial (MvPolynomial (Fin n) ℤ)
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    AdjoinRoot (Polynomial.freeMonic ℤ (n + 1)) →ₐ[A] B :=
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let B := Polynomial (MvPolynomial (Fin n) ℤ)
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  AdjoinRoot.liftAlgHom (Polynomial.freeMonic ℤ (n + 1)) (Algebra.ofId A B)
    (-(Polynomial.X : B)) (freeMonic_succ_aeval_neg_X_eq_zero n)

/-- Helper for Example 10.136.8: the previous map equips the normalized successor target with its
intermediate `AdjoinRoot (freeMonic)`-algebra structure for the one-root tower. -/
@[reducible]
noncomputable def freeMonic_succ_adjoinRootAlgebra (n : ℕ) :
    Algebra (AdjoinRoot (Polynomial.freeMonic ℤ (n + 1)))
      (Polynomial (MvPolynomial (Fin n) ℤ)) :=
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let B := Polynomial (MvPolynomial (Fin n) ℤ)
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  (freeMonic_succ_adjoinRoot_to_normalized n).toAlgebra

/-- Helper for Example 10.136.8: the `finSuccEquiv` normalization intertwines the reversed
successor algebra map with the transported normalized one. -/
theorem freeMonic_succ_normalized_target_commutes (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    letI : Algebra A (MvPolynomial (Fin (n + 1)) ℤ) :=
      (((elementary_symmetric_ring_hom (n + 1)).comp (rename Fin.revPerm)).toAlgebra)
    letI : Algebra A (Polynomial (MvPolynomial (Fin n) ℤ)) := freeMonic_succ_normalizedAlgebra n
    ∀ a : A,
      MvPolynomial.finSuccEquiv ℤ n (algebraMap A (MvPolynomial (Fin (n + 1)) ℤ) a) =
        algebraMap A (Polynomial (MvPolynomial (Fin n) ℤ)) a := by
  dsimp [freeMonic_succ_normalizedAlgebra]
  intro a
  rfl

/-- Helper for Example 10.136.8: `MvPolynomial.finSuccEquiv` already carries the reversed
successor target to the normalized one as an algebra equivalence over the source ring. -/
noncomputable def freeMonic_succ_normalized_target_algEquiv (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    letI : Algebra A (MvPolynomial (Fin (n + 1)) ℤ) :=
      (((elementary_symmetric_ring_hom (n + 1)).comp (rename Fin.revPerm)).toAlgebra)
    letI : Algebra A (Polynomial (MvPolynomial (Fin n) ℤ)) := freeMonic_succ_normalizedAlgebra n
    MvPolynomial (Fin (n + 1)) ℤ ≃ₐ[A] Polynomial (MvPolynomial (Fin n) ℤ) :=
  let A := MvPolynomial (Fin (n + 1)) ℤ
  letI : Algebra A (MvPolynomial (Fin (n + 1)) ℤ) :=
    (((elementary_symmetric_ring_hom (n + 1)).comp (rename Fin.revPerm)).toAlgebra)
  letI : Algebra A (Polynomial (MvPolynomial (Fin n) ℤ)) := freeMonic_succ_normalizedAlgebra n
  -- The underlying ring equivalence is `finSuccEquiv`, and the algebra compatibility is
  -- definitionally the normalization used to define `freeMonic_succ_normalizedAlgebra`.
  { (MvPolynomial.finSuccEquiv ℤ n) with
    commutes' := freeMonic_succ_normalized_target_commutes n }

/-- Helper for Example 10.136.8: after adjoining the distinguished root of
`Polynomial.freeMonic ℤ (n + 1)`, the remaining degree-`n` quotient polynomial is the canonical
successor-stage coefficient package. -/
noncomputable def freeMonic_succ_remainder_quotient (n : ℕ) :
    Polynomial (AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))) :=
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  ((Polynomial.freeMonic ℤ (n + 1)).map (algebraMap A A1)) /ₘ (Polynomial.X - Polynomial.C β)

/-- Helper for Example 10.136.8: the quotient polynomial obtained by dividing out the distinguished
linear root factor reconstructs the mapped successor free monic polynomial. -/
theorem freeMonic_succ_remainder_quotient_mul (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    (Polynomial.X - Polynomial.C β) * freeMonic_succ_remainder_quotient n =
      (Polynomial.freeMonic ℤ (n + 1)).map (algebraMap A A1) := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  -- The adjoined class `β` is, by construction, a root of the mapped free monic polynomial, so
  -- the linear factor `(X - C β)` divides it exactly once in the canonical quotient.
  simpa [freeMonic_succ_remainder_quotient, A, A1, β] using
    (Polynomial.mul_divByMonic_eq_iff_isRoot.2
      (AdjoinRoot.isRoot_root (Polynomial.freeMonic ℤ (n + 1))))

/-- Helper for Example 10.136.8: the canonical quotient polynomial over the one-root stage is
still monic of degree `n`, so `mapEquivMonic` recovers its coefficient map without recursion. -/
noncomputable def freeMonic_succ_remainder_monicDegreeEq (n : ℕ) :
    Polynomial.MonicDegreeEq (AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))) n := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let p : Polynomial A1 := (Polynomial.freeMonic ℤ (n + 1)).map (algebraMap A A1)
  haveI : Nontrivial A1 := AdjoinRoot.nontrivial (Polynomial.freeMonic ℤ (n + 1)) (by
    rw [Polynomial.degree_freeMonic]
    exact_mod_cast Nat.succ_ne_zero n)
  have hpMonic : p.Monic := by
    -- Mapping the universal free monic polynomial preserves monicity.
    simpa [A, A1, p] using (Polynomial.monic_freeMonic ℤ (n + 1)).map (algebraMap A A1)
  have hAinj : Function.Injective (algebraMap A A1) := by
    -- The coefficient ring injects into the one-root extension because `freeMonic` has
    -- nonzero degree.
    dsimp [A, A1]
    exact AdjoinRoot.of.injective_of_degree_ne_zero (f := Polynomial.freeMonic ℤ (n + 1)) (by
      rw [Polynomial.degree_freeMonic]
      exact_mod_cast Nat.succ_ne_zero n)
  have hpDegree : p.degree = n + 1 := by
    -- Injectivity of the coefficient map keeps the mapped successor degree unchanged.
    simpa [A, A1, p, Polynomial.degree_freeMonic] using
      (Polynomial.degree_map_eq_of_injective hAinj (Polynomial.freeMonic ℤ (n + 1)))
  have hpNatDegree : p.natDegree = n + 1 := by
    exact Polynomial.natDegree_eq_of_degree_eq_some hpDegree
  have hdegree :
      (Polynomial.X - Polynomial.C β : Polynomial A1).degree ≤ p.degree := by
    -- The linear factor has degree `1`, which is bounded by the mapped successor degree.
    rw [Polynomial.degree_eq_natDegree hpMonic.ne_zero,
      Polynomial.degree_eq_natDegree (Polynomial.X_sub_C_ne_zero β), hpNatDegree,
      Polynomial.natDegree_X_sub_C]
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hlead :
      (freeMonic_succ_remainder_quotient n).leadingCoeff = p.leadingCoeff := by
    -- Division by a monic linear factor preserves the leading coefficient.
    simpa [freeMonic_succ_remainder_quotient, A, A1, β, p] using
      (Polynomial.leadingCoeff_divByMonic_of_monic
        (p := p) (q := Polynomial.X - Polynomial.C β) (Polynomial.monic_X_sub_C β) hdegree)
  have hmonic :
      (freeMonic_succ_remainder_quotient n).Monic := by
    rw [Polynomial.Monic.def, hlead, hpMonic.leadingCoeff]
  have hnatDegree : (freeMonic_succ_remainder_quotient n).natDegree = n := by
    -- The quotient drops the degree by exactly `1`.
    rw [freeMonic_succ_remainder_quotient, Polynomial.natDegree_divByMonic p
      (Polynomial.monic_X_sub_C β), hpNatDegree, Polynomial.natDegree_X_sub_C]
    simp
  exact Polynomial.MonicDegreeEq.mk (freeMonic_succ_remainder_quotient n) hmonic hnatDegree

/-- Helper for Example 10.136.8: `mapEquivMonic` packages the canonical quotient polynomial as the
corresponding coefficient algebra map from the predecessor universal coefficient ring. -/
noncomputable def freeMonic_succ_remainder_coeff_algHom (n : ℕ) :
    MvPolynomial (Fin n) ℤ →ₐ[ℤ] AdjoinRoot (Polynomial.freeMonic ℤ (n + 1)) :=
  (MvPolynomial.mapEquivMonic ℤ (AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))) n).symm
    (freeMonic_succ_remainder_monicDegreeEq n)

/-- Helper for Example 10.136.8: the coefficient map recovered from `mapEquivMonic` reproduces the
canonical quotient polynomial exactly. -/
theorem freeMonic_succ_remainder_coeff_algHom_spec (n : ℕ) :
    (Polynomial.freeMonic ℤ n).map (freeMonic_succ_remainder_coeff_algHom n).toRingHom =
      freeMonic_succ_remainder_quotient n := by
  -- This is exactly the `apply_symm_apply` identity of the representability equivalence.
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  have h :
      (MvPolynomial.mapEquivMonic ℤ A1 n) (freeMonic_succ_remainder_coeff_algHom n) =
        freeMonic_succ_remainder_monicDegreeEq n := by
    simp [A1, freeMonic_succ_remainder_coeff_algHom]
  simpa [MvPolynomial.mapEquivMonic, freeMonic_succ_remainder_monicDegreeEq] using
    congrArg Subtype.val h

/-- Helper for Example 10.136.8: the concrete normalized remainder polynomial has degree `n`,
so it provides the normalized target point of the representable `MonicDegreeEq` family. -/
theorem freeMonic_succ_remainder_natDegree (n : ℕ) :
    (freeMonic_succ_remainder n).natDegree = n := by
  cases n with
  | zero =>
      simp [freeMonic_succ_remainder]
  | succ n =>
      -- The normalized remainder is a product of `n + 1` monic linear factors.
      rw [freeMonic_succ_remainder, Polynomial.natDegree_prod_of_monic]
      · simp
      · intro i hi
        exact Polynomial.monic_X_add_C (Polynomial.C (MvPolynomial.X i))

/-- Helper for Example 10.136.8: package the normalized remainder polynomial as the corresponding
degree-`n` monic polynomial in the normalized successor target. -/
noncomputable def freeMonic_succ_remainder_monicDegreeEq_normalized (n : ℕ) :
    Polynomial.MonicDegreeEq (Polynomial (MvPolynomial (Fin n) ℤ)) n :=
  Polynomial.MonicDegreeEq.mk (freeMonic_succ_remainder n)
    (freeMonic_succ_remainder_monic n) (freeMonic_succ_remainder_natDegree n)

/-- Helper for Example 10.136.8: after sending the adjoined root to `-X`, the canonical quotient
polynomial over `AdjoinRoot (freeMonic)` becomes the concrete normalized remainder polynomial. -/
theorem freeMonic_succ_remainder_quotient_map_to_normalized (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let B := Polynomial (MvPolynomial (Fin n) ℤ)
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    Polynomial.map (freeMonic_succ_adjoinRoot_to_normalized n).toRingHom
      (freeMonic_succ_remainder_quotient n) =
        freeMonic_succ_remainder n := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial (MvPolynomial (Fin n) ℤ)
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let φ : A1 →+* B := (freeMonic_succ_adjoinRoot_to_normalized n).toRingHom
  -- The coefficient map factors through `A → A1 → B`, and the adjoined root maps to `-X`.
  have hcomp : RingHom.comp φ (algebraMap A A1) = algebraMap A B := by
    apply RingHom.ext
    intro a
    exact (freeMonic_succ_adjoinRoot_to_normalized n).commutes a
  have hroot : φ β = -(Polynomial.X : B) := by
    simpa [A, A1, B, β, φ, freeMonic_succ_adjoinRoot_to_normalized] using
      AdjoinRoot.liftAlgHom_root
        (p := Polynomial.freeMonic ℤ (n + 1))
        (i := Algebra.ofId A B)
        (x := -(Polynomial.X : B))
        (h := freeMonic_succ_aeval_neg_X_eq_zero n)
  -- Map the quotient description across the canonical `AdjoinRoot → B` algebra map and then
  -- cancel the distinguished monic linear factor on the left.
  calc
    Polynomial.map φ (freeMonic_succ_remainder_quotient n)
        = (Polynomial.map φ
            ((Polynomial.freeMonic ℤ (n + 1)).map (algebraMap A A1))) /ₘ
            (Polynomial.map φ (Polynomial.X - Polynomial.C β)) := by
          simp [freeMonic_succ_remainder_quotient, A, A1, β, φ, Polynomial.map_divByMonic,
            Polynomial.monic_X_sub_C]
    _ = ((((Polynomial.X : Polynomial B) + Polynomial.C (Polynomial.X : B)) *
          freeMonic_succ_remainder n) /ₘ
          ((Polynomial.X : Polynomial B) + Polynomial.C (Polynomial.X : B))) := by
          -- The mapped numerator is the normalized successor factorization itself.
          have hfactor :
              Polynomial.map φ ((Polynomial.freeMonic ℤ (n + 1)).map (algebraMap A A1)) =
                ((Polynomial.X : Polynomial B) + Polynomial.C (Polynomial.X : B)) *
                  freeMonic_succ_remainder n := by
            simpa [Polynomial.map_map, hcomp] using
              freeMonic_succ_factorization_under_finSuccEquiv n
          have hdivisor :
              Polynomial.map φ (Polynomial.X - Polynomial.C β) =
                (Polynomial.X : Polynomial (Polynomial (MvPolynomial (Fin n) ℤ))) +
                  Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin n) ℤ)) := by
            calc
              Polynomial.map φ
                  ((Polynomial.X :
                      Polynomial (AdjoinRoot (Polynomial.freeMonic ℤ (n + 1)))) -
                    Polynomial.C β)
                  = (Polynomial.X : Polynomial B) - Polynomial.C (φ β) := by
                      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
              _ = (Polynomial.X : Polynomial B) + Polynomial.C (Polynomial.X : B) := by
                  rw [hroot]
                  simp
          rw [hfactor]
          rw [hdivisor]
    _ = freeMonic_succ_remainder n := by
          -- Division by the displayed monic linear factor cancels immediately.
          rw [Polynomial.mul_divByMonic_cancel_left]
          exact Polynomial.monic_X_add_C (Polynomial.X : B)

/-- Helper for Example 10.136.8: in the normalized successor target, the adjoined root acts as the
negated outer polynomial variable. -/
theorem freeMonic_succ_adjoinRoot_root_eq_neg_X (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial (MvPolynomial (Fin n) ℤ)
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
    algebraMap A1 B (AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) = -(Polynomial.X : B) := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial (MvPolynomial (Fin n) ℤ)
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  -- This is the defining computation rule of the `AdjoinRoot` lift used for the successor stage.
  change
    freeMonic_succ_adjoinRoot_to_normalized n
      (AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) = -(Polynomial.X : B)
  exact
    AdjoinRoot.liftAlgHom_root
      (p := Polynomial.freeMonic ℤ (n + 1))
      (i := Algebra.ofId A B)
      (x := -(Polynomial.X : B))
      (h := freeMonic_succ_aeval_neg_X_eq_zero n)

/-- Helper for Example 10.136.8: the predecessor coefficient action recovered from the quotient
polynomial agrees, after mapping to the normalized successor target, with the reversed
elementary-symmetric coefficient action followed by coefficient inclusion into the polynomial
ring. -/
theorem freeMonic_succ_remainder_coeff_action_eq_rev (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let B := Polynomial (MvPolynomial (Fin n) ℤ)
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    ((freeMonic_succ_adjoinRoot_to_normalized n).toRingHom.comp
        (freeMonic_succ_remainder_coeff_algHom n).toRingHom) =
      (((Polynomial.CAlgHom (R := ℤ) (A := MvPolynomial (Fin n) ℤ)).comp
        (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)))).toRingHom) := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let B := Polynomial A0
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  let hqAlg :
      A0 →ₐ[ℤ] B :=
    { (freeMonic_succ_adjoinRoot_to_normalized n).toRingHom.comp
        (freeMonic_succ_remainder_coeff_algHom n).toRingHom with
      commutes' := by
        intro z
        simp }
  let hrevAlg :
      A0 →ₐ[ℤ] B :=
    (Polynomial.CAlgHom (R := ℤ) (A := A0)).comp
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)))
  let hq :
      (MvPolynomial.mapEquivMonic ℤ B n)
          hqAlg =
        freeMonic_succ_remainder_monicDegreeEq_normalized n := by
    -- The representability equivalence records exactly the mapped quotient polynomial.
    apply Subtype.ext
    -- Expand the representability map and then rewrite via the quotient polynomial identity.
    calc
      (Polynomial.freeMonic ℤ n).map hqAlg.toRingHom
          = Polynomial.map (freeMonic_succ_adjoinRoot_to_normalized n).toRingHom
              ((Polynomial.freeMonic ℤ n).map
                (freeMonic_succ_remainder_coeff_algHom n).toRingHom) := by
              simp [hqAlg, Polynomial.map_map]
      _ = Polynomial.map (freeMonic_succ_adjoinRoot_to_normalized n).toRingHom
            (freeMonic_succ_remainder_quotient n) := by
            rw [freeMonic_succ_remainder_coeff_algHom_spec]
      _ = freeMonic_succ_remainder n := by
            rw [freeMonic_succ_remainder_quotient_map_to_normalized]
  let hrev :
      (MvPolynomial.mapEquivMonic ℤ B n)
          hrevAlg =
        freeMonic_succ_remainder_monicDegreeEq_normalized n := by
    -- Mapping the predecessor split factorization through `Polynomial.C` produces the same
    -- normalized remainder polynomial.
    apply Subtype.ext
    have hmap :=
      congrArg (Polynomial.map (Polynomial.C : A0 →+* B))
        (freeMonic_map_elementary_symmetric_ring_hom_rev n)
    simpa [A0, B, hrevAlg, freeMonic_succ_remainder, Polynomial.map_map,
      Polynomial.map_prod, Polynomial.map_add, Polynomial.map_C] using hmap
  simpa [A, A0, B, hqAlg, hrevAlg] using
    congrArg AlgHom.toRingHom ((MvPolynomial.mapEquivMonic ℤ B n).injective (hq.trans hrev.symm))

/-- Helper for Example 10.136.8: after restricting scalars along the predecessor reversed
coefficient action, `Polynomial.toFinsupp` remains linear for the induced polynomial action. -/
theorem freeMonic_succ_polynomial_toFinsupp_smul (A : Type*) [CommSemiring A]
    (alg : Algebra A A) :
    letI : Module A A := alg.toModule
    ∀ a : A, ∀ p : Polynomial A, Polynomial.toFinsupp (a • p) = a • Polynomial.toFinsupp p := by
  letI : Module A A := alg.toModule
  -- Compare both sides coefficientwise: the theorem-local scalar action multiplies each
  -- coefficient by the same source image of `a`.
  intro a p
  ext n
  simp [Polynomial.toFinsupp_apply]

/-- Helper for Example 10.136.8: the predecessor reversed algebra hypothesis already implies that
its polynomial extension is free over the same source ring. -/
theorem freeMonic_succ_predecessor_polynomial_free (n : ℕ)
    (hprev :
      letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
        (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
      Module.Free (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ)) :
    let A := MvPolynomial (Fin n) ℤ
    letI : Algebra A A := (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    Module.Free A (Polynomial A) := by
  let A := MvPolynomial (Fin n) ℤ
  let algRev : Algebra A A :=
    (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  letI : Algebra A A := algRev
  letI : Module A A := algRev.toModule
  have hprev' : Module.Free A A := by
    simpa [A, algRev] using hprev
  letI : Module.Free A A := hprev'
  letI : Module.Free A (ℕ →₀ A) := Module.Free.finsupp (ι := ℕ) (R := A) (M := A)
  let e : Polynomial A ≃ₗ[A] (ℕ →₀ A) :=
    { __ := (Polynomial.toFinsuppIso A).toAddEquiv
      map_smul' := freeMonic_succ_polynomial_toFinsupp_smul A algRev }
  -- Transport the free finitely-supported-function basis across the coefficientwise polynomial
  -- linear equivalence for the predecessor action.
  simpa [A, algRev] using
    (Module.Free.of_equiv' (P := ℕ →₀ A)
      (inferInstance : Module.Free A (ℕ →₀ A))
      e.symm)

/-- Helper for Example 10.136.8: once the adjoined root acts as the outer polynomial variable,
an `A₁`-linear map out of the normalized successor target is determined by its values on constant
coefficient polynomials. -/
theorem freeMonic_succ_coeff_inclusion_ext (n : ℕ)
    {Q : Type*} [AddCommMonoid Q]
    [Module (AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))) Q] :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
    ∀ (g₁ g₂ : B →ₗ[A1] Q),
      (∀ a : A0, g₁ (Polynomial.C a) = g₂ (Polynomial.C a)) → g₁ = g₂ := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  have haux :
      ∀ (g₁ g₂ : B →ₗ[A1] Q),
        (∀ a : A0, g₁ (Polynomial.C a) = g₂ (Polynomial.C a)) → g₁ = g₂ := by
    intro g₁ g₂ hC
    have hroot :
        algebraMap A1 B (AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) = -(Polynomial.X : B) := by
      -- The successor `AdjoinRoot` action sends the distinguished root to the normalized variable.
      simpa [A, A1, B] using freeMonic_succ_adjoinRoot_root_eq_neg_X n
    have hX :
        algebraMap A1 B (-AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) = (Polynomial.X : B) := by
      -- Negating the root rewrite turns the distinguished scalar into the outer polynomial variable.
      calc
        algebraMap A1 B (-AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) =
            -algebraMap A1 B (AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) := by
              simp
        _ = (Polynomial.X : B) := by
              rw [hroot]
              exact neg_neg (Polynomial.X : B)
    have hXpow :
        ∀ k : ℕ,
          algebraMap A1 B ((-AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) ^ k) =
            (Polynomial.X : B) ^ k := by
      intro k
      -- The displayed scalar acts by the same power of the normalized outer variable.
      rw [map_pow, hX]
    ext p
    -- Decompose into monomials so the root rewrite turns every term into an `A₁`-scalar multiple
    -- of a constant coefficient polynomial.
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simp [hp, hq]
    | monomial k a =>
        have hmonomial :
            Polynomial.monomial k a =
              ((-AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) ^ k : A1) •
                (Polynomial.C a : B) := by
          -- Rewrite the monomial as a power of `X`, then replace `X` by the adjoined scalar.
          calc
            Polynomial.monomial k a = (Polynomial.C a : B) * (Polynomial.X : B) ^ k := by
              rw [Polynomial.C_mul_X_pow_eq_monomial]
            _ = (Polynomial.C a : B) *
                algebraMap A1 B ((-AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) ^ k) := by
                  rw [hXpow k]
            _ = algebraMap A1 B ((-AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) ^ k) *
                (Polynomial.C a : B) := by
                  rw [mul_comm]
            _ = ((-AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) ^ k : A1) •
                (Polynomial.C a : B) := by
                  rw [Algebra.smul_def]
        calc
          g₁ (Polynomial.monomial k a) =
              g₁ (((-AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) ^ k : A1) •
                (Polynomial.C a : B)) := by
                  rw [hmonomial]
          _ = ((-AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) ^ k) • g₁ (Polynomial.C a) := by
                rw [g₁.map_smul]
          _ = ((-AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) ^ k) • g₂ (Polynomial.C a) := by
                rw [hC a]
          _ = g₂ (((-AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) ^ k : A1) •
                (Polynomial.C a : B)) := by
                  rw [g₂.map_smul]
          _ = g₂ (Polynomial.monomial k a) := by
                rw [hmonomial]
  simpa [A, A0, A1, B] using haux

/-- Helper for Example 10.136.8: an `A₀`-linear map out of the regular module `A₀` is determined
by the image of `1`. -/
theorem freeMonic_succ_linearMap_apply_eq_smul_one
    {A0 : Type*} [CommSemiring A0] {Q : Type*} [AddCommMonoid Q] [Module A0 Q]
    (g : A0 →ₗ[A0] Q) (a : A0) :
    g a = a • g 1 := by
  -- Rewrite `a` as `a • 1` and then use `A₀`-linearity once.
  calc
    g a = g (a • (1 : A0)) := by simp
    _ = a • g (1 : A0) := by rw [g.map_smul]

/-- Helper for Example 10.136.8: evaluating the normalized successor target at `X = -β`
sends the distinguished outer variable `-X` back to the adjoined root `β`. -/
theorem freeMonic_succ_eval₂RingHom_root (n : ℕ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
    ψRing (-(Polynomial.X : B)) = β := by
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  -- Evaluating the outer variable at `-β` turns `-X` back into `β`.
  simpa

/-- Helper for Example 10.136.8: evaluating the normalized successor target at `X = -β`
does recover the quotient-coefficient action after first restricting the successor coefficients
along the predecessor reversed elementary-symmetric map. -/
theorem freeMonic_succ_eval₂RingHom_comp_remainder_coeffs (n : ℕ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
    RingHom.comp (RingHom.comp ψRing (algebraMap A1 B))
        (freeMonic_succ_remainder_coeff_algHom n).toRingHom =
      RingHom.comp (freeMonic_succ_remainder_coeff_algHom n).toRingHom
        (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) := by
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  have hcoeff :
      RingHom.comp (algebraMap A1 B) (freeMonic_succ_remainder_coeff_algHom n).toRingHom =
        (((Polynomial.CAlgHom (R := ℤ) (A := A0)).comp
          (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)))).toRingHom) := by
    -- Rewrite the quotient-coefficient action in the normalized target by the predecessor
    -- reversed elementary-symmetric coefficients.
    simpa [A1, B] using freeMonic_succ_remainder_coeff_action_eq_rev n
  apply RingHom.ext
  intro x
  have hx := DFunLike.congr_fun hcoeff x
  -- Apply evaluation to the already-normalized constant-polynomial identity.
  calc
    ψRing ((algebraMap A1 B) ((freeMonic_succ_remainder_coeff_algHom n) x)) =
        ψRing (Polynomial.C
          ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) x)) := by
            exact congrArg ψRing hx
    _ = algebraMap A0 A1
          ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) x) := by
            simpa [A0, A1, B, β, ψRing] using
              freeMonic_succ_eval₂RingHom_C n
                ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) x)
    _ = (freeMonic_succ_remainder_coeff_algHom n)
          ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) x) := by
            rfl

/-- Helper for Example 10.136.8: the evaluation composite sends the universal successor free monic
polynomial to zero at the adjoined root `β`, which is the side condition needed for the corrected
`AdjoinRoot.lift` description. -/
theorem freeMonic_succ_eval₂RingHom_lift_relation (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
    (Polynomial.freeMonic ℤ (n + 1)).eval₂
        (RingHom.comp ψRing (algebraMap A B)) β = 0 := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  have hzero :
      (Polynomial.freeMonic ℤ (n + 1)).eval₂ (algebraMap A B) (-(Polynomial.X : B)) = 0 := by
    -- Reuse the normalized successor root relation before applying evaluation to `A₁`.
    simpa [Polynomial.aeval_def, A, B] using freeMonic_succ_aeval_neg_X_eq_zero n
  have hhom :
      ψRing ((Polynomial.freeMonic ℤ (n + 1)).eval₂ (algebraMap A B) (-(Polynomial.X : B))) =
        (Polynomial.freeMonic ℤ (n + 1)).eval₂
          (RingHom.comp ψRing (algebraMap A B)) (ψRing (-(Polynomial.X : B))) := by
    -- Push evaluation through the ring homomorphism `ψRing`.
    simpa using
      (Polynomial.hom_eval₂ (p := Polynomial.freeMonic ℤ (n + 1))
        (g := ψRing) (f := algebraMap A B) (x := -(Polynomial.X : B)))
  have hmapped :
      (Polynomial.freeMonic ℤ (n + 1)).eval₂
          (RingHom.comp ψRing (algebraMap A B)) (ψRing (-(Polynomial.X : B))) = 0 := by
    -- Apply `ψRing` to the already-known vanishing relation in the normalized target.
    rw [← hhom, hzero]
    simp
  -- Replace the evaluated outer variable by the previously computed root value `β`.
  simpa [A, A0, A1, B, β, ψRing] using hmapped

/-- Helper for Example 10.136.8: the composite `A₁ → Polynomial A₀ → A₁` is the canonical
`AdjoinRoot` endomorphism determined by its induced action on the successor source ring and the
fact that it fixes the adjoined root `β`. -/
theorem freeMonic_succ_eval₂RingHom_section (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
    RingHom.comp ψRing (algebraMap A1 B) =
      AdjoinRoot.lift (RingHom.comp ψRing (algebraMap A B)) β
        (freeMonic_succ_eval₂RingHom_lift_relation n) := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  have hβ :
      (Polynomial.freeMonic ℤ (n + 1)).eval₂
          (RingHom.comp ψRing (algebraMap A B)) β = 0 := by
    -- Freeze the side condition once so the `AdjoinRoot.lift` term stays readable.
    simpa [A, A0, A1, B, β, ψRing] using freeMonic_succ_eval₂RingHom_lift_relation n
  -- Route correction: the old claim that `ψRing` is literally a section was too strong. The
  -- corrected statement identifies the composite with the unique `AdjoinRoot` endomorphism that
  -- has the induced source action `ψRing.comp (algebraMap A B)` and still fixes the adjoined root.
  apply AdjoinRoot.ringHom_ext
  · -- Both ring maps restrict to the same action on the successor source ring `A`.
    apply RingHom.ext
    intro a
    have hcomm :
        (algebraMap A1 B) ((AdjoinRoot.of (Polynomial.freeMonic ℤ (n + 1))) a) =
          algebraMap A B a := by
      -- The successor `AdjoinRoot` algebra was defined by a lift extending the normalized
      -- source action, so it commutes with the source coefficients by construction.
      simpa [A, A1, B, AdjoinRoot.algebraMap_eq] using
        (freeMonic_succ_adjoinRoot_to_normalized n).commutes a
    calc
      (((RingHom.comp ψRing (algebraMap A1 B)).comp
          (AdjoinRoot.of (Polynomial.freeMonic ℤ (n + 1)))) a) =
          ψRing ((algebraMap A1 B) ((AdjoinRoot.of (Polynomial.freeMonic ℤ (n + 1))) a)) := by
            rfl
      _ = ψRing (algebraMap A B a) := by
            exact congrArg ψRing hcomm
      _ =
          (((AdjoinRoot.lift (RingHom.comp ψRing (algebraMap A B)) β hβ).comp
              (AdjoinRoot.of (Polynomial.freeMonic ℤ (n + 1)))) a) := by
            simp [AdjoinRoot.lift_comp_of]
  · -- Both ring maps send the adjoined root to `β`.
    calc
      (RingHom.comp ψRing (algebraMap A1 B))
          (AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) =
          ψRing (-(Polynomial.X : B)) := by
            simpa [RingHom.comp_apply, A, A1, B] using
              congrArg ψRing (freeMonic_succ_adjoinRoot_root_eq_neg_X n)
      _ = β := by
            simpa [A0, A1, B, β, ψRing] using freeMonic_succ_eval₂RingHom_root n
      _ = AdjoinRoot.lift (RingHom.comp ψRing (algebraMap A B)) β hβ
            (AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) := by
              simp

/-- Helper for Example 10.136.8: after evaluating the normalized successor target at `X = -β`,
the induced action on the full successor source ring is the canonical coefficient action
`A → A₁`. -/
theorem freeMonic_succ_eval₂RingHom_comp_source_eq (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  RingHom.comp ψRing (algebraMap A B) = algebraMap A A1 := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  let φ : A →ₐ[ℤ] A1 :=
    { RingHom.comp ψRing (algebraMap A B) with
      commutes' := by
        intro z
        simp [ψRing] }
  let ι : A →ₐ[ℤ] A1 := IsScalarTower.toAlgHom ℤ A A1
  -- Compare the two source maps through the representability of monic degree-`n + 1`
  -- polynomials by `MvPolynomial.mapEquivMonic`.
  change φ.toRingHom = ι.toRingHom
  refine congrArg AlgHom.toRingHom <|
    (MvPolynomial.mapEquivMonic ℤ A1 (n + 1)).injective ?_
  apply Subtype.ext
  have hfactor :
      (Polynomial.freeMonic ℤ (n + 1)).map (algebraMap A B) =
        (((Polynomial.X : Polynomial B) + Polynomial.C (Polynomial.X : B)) *
          freeMonic_succ_remainder n) := by
    -- Unfold the normalized successor action to the previously established one-factor split form.
    simpa [A, A0, B, freeMonic_succ_normalizedAlgebra, Polynomial.map_map] using
      freeMonic_succ_factorization_under_finSuccEquiv n
  have hcoeffAction :
      RingHom.comp (algebraMap A1 B) (freeMonic_succ_remainder_coeff_algHom n).toRingHom =
        (((Polynomial.CAlgHom (R := ℤ) (A := A0)).comp
          (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)))).toRingHom) := by
    -- Freeze the coefficient action on the normalized remainder in the exact theorem-local form.
    simpa [A, A0, A1, B, freeMonic_succ_adjoinRootAlgebra] using
      freeMonic_succ_remainder_coeff_action_eq_rev n
  have hremainder :
      freeMonic_succ_remainder n =
        (Polynomial.freeMonic ℤ n).map
          (((Polynomial.CAlgHom (R := ℤ) (A := A0)).comp
            (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)))).toRingHom) := by
    -- Rewrite the normalized remainder as the predecessor split polynomial with coefficients
    -- inserted as constants in `Polynomial A₀`.
    have hmap :=
      congrArg (Polynomial.map (Polynomial.C : A0 →+* B))
        (freeMonic_map_elementary_symmetric_ring_hom_rev n)
    simpa [A0, B, freeMonic_succ_remainder, Polynomial.map_map, Polynomial.map_prod,
      Polynomial.map_add, Polynomial.map_C] using hmap.symm
  calc
    (MvPolynomial.mapEquivMonic ℤ A1 (n + 1) φ).1
        = Polynomial.map ψRing ((Polynomial.freeMonic ℤ (n + 1)).map (algebraMap A B)) := by
            simp [MvPolynomial.mapEquivMonic, φ, Polynomial.map_map]
    _ = Polynomial.map ψRing
          ((((Polynomial.X : Polynomial B) + Polynomial.C (Polynomial.X : B)) *
            freeMonic_succ_remainder n)) := by
            rw [hfactor]
    _ = ((Polynomial.X - Polynomial.C β) *
          Polynomial.map ψRing (freeMonic_succ_remainder n)) := by
            -- Evaluating the distinguished coefficient variable at `-β` turns the first factor
            -- into the linear root factor `(X - C β)`.
            simp [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
              A0, A1, B, β, ψRing, sub_eq_add_neg]
    _ = ((Polynomial.X - Polynomial.C β) *
          ((Polynomial.freeMonic ℤ n).map
            (RingHom.comp (RingHom.comp ψRing (algebraMap A1 B))
              (freeMonic_succ_remainder_coeff_algHom n).toRingHom))) := by
            -- Rewrite the concrete remainder by the predecessor source map and then re-evaluate
            -- its coefficients through the quotient stage.
            rw [hremainder, Polynomial.map_map, ← hcoeffAction]
            rfl
    _ = ((Polynomial.X - Polynomial.C β) *
          (Polynomial.freeMonic ℤ n).map (freeMonic_succ_remainder_coeff_algHom n).toRingHom) := by
            -- Route correction: the earlier product-transport attempt would identify the quotient
            -- coefficients with the remaining roots, which is false for `n > 1`. The remaining
            -- source-faithful proof must instead compare successor coefficients via the
            -- `(X - C β)` recursion coming from the canonical quotient polynomial.
            sorry
    _ = (Polynomial.X - Polynomial.C β) * freeMonic_succ_remainder_quotient n := by
            rw [freeMonic_succ_remainder_coeff_algHom_spec]
    _ = (Polynomial.freeMonic ℤ (n + 1)).map (algebraMap A A1) := by
            simpa [A, A1, β] using freeMonic_succ_remainder_quotient_mul n
    _ = (MvPolynomial.mapEquivMonic ℤ A1 (n + 1) ι).1 := by
            rfl

/-- Helper for Example 10.136.8: once the induced source action is identified with the canonical
one on `A₁`, the corrected `AdjoinRoot.lift` from the evaluation composite is just the identity. -/
theorem freeMonic_succ_corrected_lift_eq_id (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
    AdjoinRoot.lift (RingHom.comp ψRing (algebraMap A B)) β
      (freeMonic_succ_eval₂RingHom_lift_relation n) = RingHom.id A1 := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  have hsource :
      RingHom.comp ψRing (algebraMap A B) = algebraMap A A1 := by
    -- Rewrite the source action to the canonical coefficient action on the one-root stage.
    simpa [A, A0, A1, B, β, ψRing] using freeMonic_succ_eval₂RingHom_comp_source_eq n
  -- After the source action is canonical, this is exactly the standard self-lift of `AdjoinRoot`.
  calc
    AdjoinRoot.lift (RingHom.comp ψRing (algebraMap A B)) β
        (freeMonic_succ_eval₂RingHom_lift_relation n) =
          AdjoinRoot.lift (algebraMap A A1) β
            (AdjoinRoot.isAdjoinRoot (Polynomial.freeMonic ℤ (n + 1))).aeval_root_self := by
              simp [hsource, A1, β]
    _ = RingHom.id A1 := by
          -- Identify the canonical self-lift directly by its action on coefficients and on the
          -- adjoined root.
          apply AdjoinRoot.ringHom_ext
          · calc
              (AdjoinRoot.lift (algebraMap A A1) β
                  (AdjoinRoot.isAdjoinRoot (Polynomial.freeMonic ℤ (n + 1))).aeval_root_self).comp
                  (AdjoinRoot.of (Polynomial.freeMonic ℤ (n + 1))) =
                  algebraMap A A1 := by
                    simpa using
                      (AdjoinRoot.lift_comp_of
                        (f := Polynomial.freeMonic ℤ (n + 1))
                        (i := algebraMap A A1)
                        (a := β)
                        (h := (AdjoinRoot.isAdjoinRoot
                          (Polynomial.freeMonic ℤ (n + 1))).aeval_root_self))
              _ = (RingHom.id A1).comp (AdjoinRoot.of (Polynomial.freeMonic ℤ (n + 1))) := by
                    rfl
          · calc
              AdjoinRoot.lift (algebraMap A A1) β
                  (AdjoinRoot.isAdjoinRoot (Polynomial.freeMonic ℤ (n + 1))).aeval_root_self
                  (AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) = β := by
                    simpa using
                      (AdjoinRoot.lift_root
                        (f := Polynomial.freeMonic ℤ (n + 1))
                        (i := algebraMap A A1)
                        (a := β)
                        (h := (AdjoinRoot.isAdjoinRoot
                          (Polynomial.freeMonic ℤ (n + 1))).aeval_root_self))
              _ = (RingHom.id A1) (AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) := by
                    rfl

/-- Helper for Example 10.136.8: evaluating at `X = -β` is literally a section of the successor
`AdjoinRoot` algebra map once the corrected lift is identified with the identity. -/
theorem freeMonic_succ_eval₂RingHom_is_section (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
    RingHom.comp ψRing (algebraMap A1 B) = RingHom.id A1 := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  -- Chain the corrected universal-property description with the identity-on-`A₁` lift.
  calc
    RingHom.comp ψRing (algebraMap A1 B) =
        AdjoinRoot.lift (RingHom.comp ψRing (algebraMap A B)) β
          (freeMonic_succ_eval₂RingHom_lift_relation n) := by
            simpa [A, A0, A1, B, β, ψRing] using freeMonic_succ_eval₂RingHom_section n
    _ = RingHom.id A1 := by
          simpa [A, A0, A1, B, β, ψRing] using freeMonic_succ_corrected_lift_eq_id n

/-- Helper for Example 10.136.8: evaluating a constant polynomial at `X = -β` just applies the
theorem-local predecessor coefficient map into the one-root stage. -/
theorem freeMonic_succ_eval₂RingHom_C (n : ℕ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
    ∀ a : A0, ψRing (Polynomial.C a) = algebraMap A0 A1 a := by
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  -- Constants are untouched by polynomial evaluation except for the coefficient map.
  intro a
  simp

/-- Helper for Example 10.136.8: `Polynomial.C` preserves addition for the theorem-local
coefficient-inclusion map. -/
theorem freeMonic_succ_coeff_inclusionLinear_map_add (n : ℕ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let B := Polynomial A0
    ∀ a b : A0, (Polynomial.C (a + b) : B) = Polynomial.C a + Polynomial.C b := by
  let A0 := MvPolynomial (Fin n) ℤ
  let B := Polynomial A0
  intro a b
  simpa using (Polynomial.C_add a b)

/-- Helper for Example 10.136.8: `Polynomial.C` is compatible with the theorem-local twisted
predecessor scalar action induced by the reversed elementary-symmetric map. -/
theorem freeMonic_succ_coeff_inclusionLinear_map_smul (n : ℕ)
    (a b : MvPolynomial (Fin n) ℤ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let B := Polynomial A0
    let revHom : A0 →+* A0 :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom)
    let coeffHom : A0 →+* B :=
      (((Polynomial.CAlgHom (R := ℤ) (A := A0)).comp
        (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)))).toRingHom)
    let algRev : Algebra A0 A0 := revHom.toAlgebra
    let coeffAlg : Algebra A0 B := coeffHom.toAlgebra
    letI : Algebra A0 A0 := algRev
    letI : Module A0 A0 := algRev.toModule
    letI : Algebra A0 B := coeffAlg
    letI : Module A0 B := coeffAlg.toModule
    (Polynomial.C (a • b) : B) = a • (Polynomial.C b : B) := by
  let A0 := MvPolynomial (Fin n) ℤ
  let B := Polynomial A0
  let revHom : A0 →+* A0 :=
    (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom)
  let coeffHom : A0 →+* B :=
    (((Polynomial.CAlgHom (R := ℤ) (A := A0)).comp
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)))).toRingHom)
  let algRev : Algebra A0 A0 := revHom.toAlgebra
  let coeffAlg : Algebra A0 B := coeffHom.toAlgebra
  letI : Algebra A0 A0 := algRev
  letI : Module A0 A0 := algRev.toModule
  letI : Algebra A0 B := coeffAlg
  letI : Module A0 B := coeffAlg.toModule
  have hcoeff :
      algebraMap A0 B a = Polynomial.C (revHom a) := by
    -- By definition the theorem-local coefficient action is constant inclusion after the twisted
    -- predecessor coefficient map.
    rfl
  -- Rewrite both scalar actions through their concrete coefficient-ring descriptions.
  calc
    (Polynomial.C (a • b) : B) = Polynomial.C (revHom a * b) := by
      -- The source scalar action is multiplication by the reversed coefficient image.
      change Polynomial.C ((algebraMap A0 A0 a) * b) = Polynomial.C (revHom a * b)
      rfl
    _ = Polynomial.C (revHom a) * Polynomial.C b := by
      rw [Polynomial.C_mul]
    _ = algebraMap A0 B a * Polynomial.C b := by
      rw [hcoeff]
    _ = a • (Polynomial.C b : B) := by
      rw [Algebra.smul_def, hcoeff]

/-- Helper for Example 10.136.8: once the normalized successor target is identified with the base
change of the predecessor splitting algebra over `AdjoinRoot (freeMonic)`, the successor free stage
over that one-root extension follows. -/
theorem freeMonic_succ_free_over_adjoinRoot (n : ℕ)
    (hprev :
      letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
        (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
      Module.Free (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ)) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial (MvPolynomial (Fin n) ℤ)
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
    Module.Free A1 B := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  let algRev : Algebra A0 A0 :=
    (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  letI : Algebra A0 A0 := algRev
  letI : Module A0 A0 := algRev.toModule
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  have hprev' : Module.Free A0 A0 := by
    -- Re-express the induction hypothesis in the predecessor coefficient-ring notation.
    simpa [A0, algRev] using hprev
  -- Route correction: the successor-step freeness is no longer blocked by the linear packaging
  -- of the twisted coefficient inclusion: `Polynomial.C` now has the correct theorem-local
  -- `A₀`-linearity. The remaining structural gap is to exhibit the actual `A₁`-base-change model.
  clear hprev'
  -- TODO: package the theorem-local constant inclusion `A₀ → B` as the base-change map
  -- `A₁ ⊗[A₀] A₀ → B`, then conclude by `IsBaseChange.free`.
  sorry

/-- Helper for Example 10.136.8: if two source algebra structures on the same target differ by a
domain ring equivalence, then finite generation and freeness transport across that equivalence. -/
theorem finite_free_of_domain_equiv
    {A₁ A₂ B : Type*} [CommSemiring A₁] [CommSemiring A₂] [CommSemiring B]
    (alg₁ : Algebra A₁ B) (alg₂ : Algebra A₂ B) (e : A₁ ≃+* A₂)
    (hcompat :
      RingHom.comp (@algebraMap A₂ B _ _ alg₂) e.toRingHom =
        @algebraMap A₁ B _ _ alg₁)
    (hfinite : @Module.Finite A₁ B _ _ alg₁.toModule)
    (hfree : @Module.Free A₁ B _ _ alg₁.toModule) :
    @Module.Finite A₂ B _ _ alg₂.toModule ∧ @Module.Free A₂ B _ _ alg₂.toModule := by
  letI : Algebra A₁ B := alg₁
  letI : Algebra A₂ B := alg₂
  letI : Module.Finite A₁ B := hfinite
  letI : Module.Free A₁ B := hfree
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.symm e.toRingHom e.symm.toRingHom
  -- Finite generation is invariant under compatible ring equivalences on source and target.
  have hfinite' : Module.Finite A₂ B := by
    have hcompat' :
        RingHom.comp (algebraMap A₂ B) e.toRingHom =
          RingHom.comp (RingEquiv.refl B) (algebraMap A₁ B) := by
      simpa using hcompat
    exact
      @Module.Finite.of_equiv_equiv A₁ B A₂ B _ _ _ _ alg₁ alg₂ e (RingEquiv.refl B) hcompat'
        hfinite
  -- The identity map on `B` becomes semilinear once the two source actions are matched by `e`.
  have hsemilinear : B ≃ₛₗ[e.toRingHom] B := by
    -- Both semilinear maps are literally the identity on the underlying additive group.
    refine LinearEquiv.ofLinear ?_ ?_ ?_ ?_
    · refine
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := ?_ }
      intro a b
      have happly := DFunLike.congr_fun hcompat a
      simpa [Algebra.smul_def, RingHom.comp_apply] using
        congrArg (fun x : B ↦ x * b) happly.symm
    · refine
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := ?_ }
      intro a b
      have happly := DFunLike.congr_fun hcompat (e.symm a)
      simpa [Algebra.smul_def, RingHom.comp_apply] using
        congrArg (fun x : B ↦ x * b) happly
    · ext b
      rfl
    · ext b
      rfl
  -- Freeness transports along semilinear equivalences.
  have hfree' : Module.Free A₂ B := Module.Free.of_equiv hsemilinear
  exact ⟨hfinite', hfree'⟩

/-- Helper for Example 10.136.8: every target root variable is integral over the reversed
elementary-symmetric coefficient ring because the universal monic polynomial splits as a product of
linear factors. -/
theorem isIntegral_X_of_elementary_symmetric_ring_hom_rev (n : ℕ) (i : Fin n) :
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    IsIntegral (MvPolynomial (Fin n) ℤ) (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) := by
  let A := MvPolynomial (Fin n) ℤ
  letI : Algebra A A := (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  let s : Multiset A := Finset.univ.val.map fun j : Fin n => -(MvPolynomial.X j : A)
  have hsplitMap :
      (Polynomial.freeMonic ℤ n).map
          (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) =
        (s.map fun x : A =>
          (Polynomial.X - Polynomial.C x : Polynomial (MvPolynomial (Fin n) ℤ))).prod := by
    -- Rewrite the source split polynomial in the `X - C r` normal form required by the
    -- standard root-to-integrality API.
    calc
      (Polynomial.freeMonic ℤ n).map
          (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom)
          =
            ∏ j : Fin n,
              ((Polynomial.X : Polynomial (MvPolynomial (Fin n) ℤ)) +
                Polynomial.C (MvPolynomial.X j : A)) := by
              exact freeMonic_map_elementary_symmetric_ring_hom_rev n
      _ = (s.map fun x : A =>
            (Polynomial.X - Polynomial.C x : Polynomial (MvPolynomial (Fin n) ℤ))).prod := by
            rw [Finset.prod_eq_multiset_prod]
            dsimp [s]
            rw [Multiset.map_map]
            refine congrArg Multiset.prod ?_
            refine Multiset.map_congr rfl ?_
            intro j hj
            change
              ((Polynomial.X : Polynomial (MvPolynomial (Fin n) ℤ)) +
                  Polynomial.C (MvPolynomial.X j : A)) =
                (Polynomial.X - Polynomial.C (-(MvPolynomial.X j : A)) :
                  Polynomial (MvPolynomial (Fin n) ℤ))
            rw [sub_eq_add_neg, Polynomial.C_neg, neg_neg]
  have hsplit :
      (Polynomial.freeMonic ℤ n).mapAlg A A =
        (s.map fun x : A =>
          (Polynomial.X - Polynomial.C x : Polynomial (MvPolynomial (Fin n) ℤ))).prod := by
    simpa [Polynomial.mapAlg_eq_map] using hsplitMap
  have hroot :
      Polynomial.aeval (-(MvPolynomial.X i : A)) (Polynomial.freeMonic ℤ n) = 0 := by
    -- The chosen variable is one of the displayed roots of the split universal polynomial.
    exact Polynomial.aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C
      (R := A) (A := A) (p := Polynomial.freeMonic ℤ n) (s := s)
      (x := -(MvPolynomial.X i : A)) (by simp [s]) hsplit
  have hintNeg' := 
    -- A root of a monic polynomial is integral over the coefficient ring.
    isIntegral_leadingCoeff_smul (R := A) (S := A)
      (p := Polynomial.freeMonic ℤ n) (x := -(MvPolynomial.X i : A)) hroot
  have hlead :
      (Polynomial.freeMonic ℤ n).leadingCoeff • (-(MvPolynomial.X i : A)) =
        -(MvPolynomial.X i : A) := by
    simp [Algebra.smul_def, Polynomial.monic_freeMonic]
  have hintNeg : IsIntegral A (-(MvPolynomial.X i : A)) := hlead ▸ hintNeg'
  -- Negating an integral element preserves integrality, so the variable itself is integral.
  exact IsIntegral.of_neg hintNeg

/-- Helper for Example 10.136.8: for the reversed algebra structure, adjoining the target root
variables already recovers the whole target polynomial ring. -/
  theorem adjoin_root_variables_eq_top_of_elementary_symmetric_ring_hom_rev (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    Algebra.adjoin (MvPolynomial (Fin n) ℤ)
      (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ)) = ⊤ := by
  let A := MvPolynomial (Fin n) ℤ
  letI : Algebra A A := (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  let S : Subalgebra A A := Algebra.adjoin A (Set.range (MvPolynomial.X : Fin n → A))
  refine top_unique ?_
  intro p hpTop
  clear hpTop
  -- The target ring is generated by integer coefficients and the root variables.
  induction p using MvPolynomial.induction_on with
  | C r =>
      simpa [S] using S.algebraMap_mem (MvPolynomial.C r : A)
  | add p q hp hq =>
      exact S.add_mem hp hq
  | mul_X p i hp =>
      exact S.mul_mem hp (Algebra.subset_adjoin (by exact ⟨i, rfl⟩))

/-- Helper for Example 10.136.8: finite generation follows because the target polynomial ring is
generated by finitely many integral root variables over the reversed coefficient ring. -/
theorem elementary_symmetric_ring_hom_rev_finite (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    Module.Finite (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) := by
  let A := MvPolynomial (Fin n) ℤ
  letI : Algebra A A := (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  let s : Set A := Set.range (MvPolynomial.X : Fin n → A)
  have hsIntegral : ∀ x ∈ s, IsIntegral A x := by
    -- Each generator lies among the explicit roots of the universal monic polynomial.
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact isIntegral_X_of_elementary_symmetric_ring_hom_rev n i
  have hfiniteAdjoin : Module.Finite A (Algebra.adjoin A s) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (hf := Set.toFinite s) hsIntegral
  have hsTop : Algebra.adjoin A s = ⊤ := by
    simpa [s] using adjoin_root_variables_eq_top_of_elementary_symmetric_ring_hom_rev n
  let e : Algebra.adjoin A s ≃ₐ[A] A := by
    -- `MvPolynomial` is generated by its variables, so the adjoin is the top subalgebra.
    exact hsTop ▸ (Subalgebra.topEquiv (R := A) (A := A))
  letI : Module.Finite A (Algebra.adjoin A s) := hfiniteAdjoin
  exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Example 10.136.8: in zero variables, the reversed elementary-symmetric map is the
identity ring endomorphism on `ℤ`. -/
theorem elementary_symmetric_ring_hom_rev_zero_eq_id :
    (((elementary_symmetric_ring_hom 0).comp (rename Fin.revPerm)).toRingHom) =
      RingHom.id (MvPolynomial (Fin 0) ℤ) := by
  apply RingHom.ext
  intro p
  -- Every polynomial in zero variables is constant, so it suffices to check constants.
  have hp : p = MvPolynomial.C (MvPolynomial.coeff 0 p) := MvPolynomial.eq_C_of_isEmpty p
  rw [hp]
  simp [elementary_symmetric_ring_hom]

/-- Helper for Example 10.136.8: after reversing the source coefficient variables, the
elementary-symmetric map is finite free. -/
theorem elementary_symmetric_ring_hom_rev_finite_free (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    Module.Finite (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) ∧
      Module.Free (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) := by
  induction n with
  | zero =>
      refine ⟨elementary_symmetric_ring_hom_rev_finite 0, ?_⟩
      let A := MvPolynomial (Fin 0) ℤ
      let algId : Algebra A A := (RingHom.id A).toAlgebra
      let algRev : Algebra A A :=
        (((elementary_symmetric_ring_hom 0).comp (rename Fin.revPerm)).toAlgebra)
      -- The zero-variable reversed source action is the identity action.
      have hcompat :
          RingHom.comp (@algebraMap A A _ _ algRev) (RingEquiv.refl A).toRingHom =
            @algebraMap A A _ _ algId := by
        simpa [algId, algRev] using elementary_symmetric_ring_hom_rev_zero_eq_id
      have hfiniteId : @Module.Finite A A _ _ algId.toModule := by
        letI : Algebra A A := algId
        simpa using (Module.Finite.self A)
      have hfreeId : @Module.Free A A _ _ algId.toModule := by
        letI : Algebra A A := algId
        simpa using (Module.Free.self (R := A))
      simpa [A, algRev] using
        (finite_free_of_domain_equiv algId algRev (RingEquiv.refl A) hcompat
          hfiniteId hfreeId).2
  | succ n ih =>
      refine ⟨elementary_symmetric_ring_hom_rev_finite (n + 1), ?_⟩
      let A := MvPolynomial (Fin (n + 1)) ℤ
      let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
      let B := Polynomial (MvPolynomial (Fin n) ℤ)
      letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
      letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
      have hA1 : Module.Free A A1 := by
        -- The first stage of the successor tower is the standard free one-root extension.
        simpa [A1] using (Polynomial.monic_freeMonic ℤ (n + 1)).free_adjoinRoot
      have hB : Module.Free A1 B := by
        -- The remaining successor-stage freeness is exactly the base-change comparison blocker.
        simpa [A, A1, B] using freeMonic_succ_free_over_adjoinRoot n ih.2
      have hNormalized : Module.Free A B := by
        -- Compose the one-root free stage with the remainder-stage free tower.
        letI : Module.Free A A1 := hA1
        letI : Module.Free A1 B := hB
        exact Module.Free.trans (R := A) (S := A1) (M := B)
      letI : Algebra A (MvPolynomial (Fin (n + 1)) ℤ) :=
        (((elementary_symmetric_ring_hom (n + 1)).comp (rename Fin.revPerm)).toAlgebra)
      -- Transport freeness back across the normalization equivalence `finSuccEquiv`.
      exact Module.Free.of_equiv (freeMonic_succ_normalized_target_algEquiv n).symm.toLinearEquiv

/-- Helper for Example 10.136.8: after restricting scalars along a theorem-local self-action on
`A`, `Polynomial.toFinsupp` still intertwines the induced coefficientwise scalar actions. -/
theorem polynomial_toFinsupp_smul_restrictScalars (A : Type*) [CommSemiring A]
    (alg : Algebra A A) :
    letI : Module A A := alg.toModule
    ∀ a : A, ∀ p : Polynomial A, Polynomial.toFinsupp (a • p) = a • Polynomial.toFinsupp p := by
  letI : Module A A := alg.toModule
  -- Compare both sides coefficientwise: both scalar actions multiply each coefficient by the
  -- theorem-local image of `a` in `A`.
  intro a p
  ext n
  simp [Polynomial.toFinsupp_apply]

/-- Helper for Example 10.136.8: once the predecessor target ring is free over the reversed
coefficient algebra, the coefficientwise polynomial extension remains free over that same source
algebra. -/
theorem polynomial_rev_free_of_rev_free (n : ℕ) :
    let A := MvPolynomial (Fin n) ℤ
    letI : Algebra A A :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    Module.Free A (Polynomial A) := by
  let A := MvPolynomial (Fin n) ℤ
  let algRev : Algebra A A :=
    (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  letI : Algebra A A := algRev
  letI : Module A A := algRev.toModule
  letI : Module.Free A A := (elementary_symmetric_ring_hom_rev_finite_free n).2
  letI : Module.Free A (ℕ →₀ A) := Module.Free.finsupp (ι := ℕ) (R := A) (M := A)
  let e : Polynomial A ≃ₗ[A] (ℕ →₀ A) :=
    { __ := (Polynomial.toFinsuppIso A).toAddEquiv
      map_smul' := polynomial_toFinsupp_smul_restrictScalars A algRev }
  -- Transport the free finitely-supported-function basis across the theorem-local linear
  -- equivalence from the new helper.
  simpa [algRev] using
    (Module.Free.of_equiv' (P := ℕ →₀ A)
      (inferInstance : Module.Free A (ℕ →₀ A))
      e.symm)

-- Proof sketch: identify `elementary_symmetric_ring_hom n` with the canonical fundamental-theorem
-- owner for symmetric polynomials and use the standard monomial basis to obtain finite generation
-- and freeness over `ℤ[a₁, \ldots, aₙ]`.
/-- Example 10.136.8: the elementary-symmetric map
`ℤ[a₁, \ldots, aₙ] → ℤ[α₁, \ldots, αₙ]` is finite free. -/
theorem elementary_symmetric_ring_hom_finite_free (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
      (elementary_symmetric_ring_hom n).toAlgebra
    Module.Finite (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) ∧
      Module.Free (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) := by
  let revAlg :
      Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
    (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  let alg :
      Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
    (elementary_symmetric_ring_hom n).toAlgebra
  let revEquiv :
      MvPolynomial (Fin n) ℤ ≃+* MvPolynomial (Fin n) ℤ :=
    (renameEquiv ℤ (Fin.revPerm : Equiv.Perm (Fin n))).toRingEquiv
  letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) := revAlg
  have hrev := elementary_symmetric_ring_hom_rev_finite_free n
  -- Route correction: once the reversed theorem is available, the public theorem is only transport
  -- back along the domain automorphism `rename Fin.rev`.
  have hcompat_ring :
      RingHom.comp (elementary_symmetric_ring_hom n).toRingHom revEquiv.toRingHom =
        (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) := by
    rfl
  have hcompat :
      RingHom.comp
          (@algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) _ _ alg)
          revEquiv.toRingHom =
        @algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) _ _ revAlg := by
    simpa [revAlg, alg] using hcompat_ring
  exact finite_free_of_domain_equiv revAlg alg revEquiv hcompat hrev.1 hrev.2

-- Proof sketch: the finite-free statement gives finite generation of the target polynomial ring as
-- a module over the source polynomial ring for the algebra structure induced by
-- `elementary_symmetric_ring_hom n`; this is exactly the ring-hom notion of finiteness.
/-- The elementary-symmetric map is finite. -/
theorem elementary_symmetric_ring_hom_finite (n : ℕ) :
    (elementary_symmetric_ring_hom n).Finite := by
  letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
    (elementary_symmetric_ring_hom n).toAlgebra
  -- The finite-free theorem already provides the module-finite half of the desired conclusion.
  simpa [RingHom.algebraMap_toAlgebra] using
    (RingHom.finite_algebraMap).mpr (elementary_symmetric_ring_hom_finite_free n).1

-- Proof sketch: every finite ring map is quasi-finite in mathlib, so this follows formally from
-- `elementary_symmetric_ring_hom_finite n`.
/-- The elementary-symmetric map is quasi-finite, equivalently its fibers are finite. -/
theorem elementary_symmetric_ring_hom_quasi_finite (n : ℕ) :
    (elementary_symmetric_ring_hom n).QuasiFinite := by
  -- Every finite ring map is quasi-finite.
  exact RingHom.QuasiFinite.of_finite (elementary_symmetric_ring_hom_finite n)

-- Proof sketch: a finite free module is flat, and because its rank is positive the induced map on
-- spectra is surjective; equivalently, the ring map is faithfully flat.
/-- The elementary-symmetric map is faithfully flat. -/
theorem elementary_symmetric_ring_hom_faithfully_flat (n : ℕ) :
    (elementary_symmetric_ring_hom n).FaithfullyFlat := by
  letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
    (elementary_symmetric_ring_hom n).toAlgebra
  letI : Module.Free (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
    (elementary_symmetric_ring_hom_finite_free n).2
  -- A nontrivial free module is faithfully flat, so the ring-hom statement is the algebra-map view.
  simpa [RingHom.algebraMap_toAlgebra] using
    (RingHom.faithfullyFlat_algebraMap_iff).mpr
      (inferInstance :
        Module.FaithfullyFlat (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ))
