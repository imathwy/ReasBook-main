import Mathlib

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

