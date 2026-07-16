import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.Index

noncomputable section

open LinearMap (BilinForm)
open scoped Pointwise TensorProduct

universe u v w

open LinearMap.BilinForm

local notation:max p " •ℤ " E => (Representation.primeIdeal p • (⊤ : Submodule ℤ E))

/- Exercise 15-15.2-6 (3): the nondegeneracy conclusion for a symmetric positive definite
integral bilinear form is already owned by
`LinearMap.BilinForm.nondegenerate_of_isSymm_of_posDef`; the exercise adds no separate invariant
wrapper theorem, since invariance plays no role in the canonical statement. -/
recall LinearMap.BilinForm.nondegenerate_of_isSymm_of_posDef

section ThompsonExercise

variable {G : Type u} [Group G]
variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section IntegralLatticeAmbient

variable [Module.Free ℤ E] [Module.Finite ℤ E]

-- Proof sketch: starting from any positive definite symmetric form on the integral module `E`,
-- average it over the finite group `G`.
/-- Exercise 15-15.2-6 (1): for a finite group action, there exists a symmetric `G`-invariant
positive definite integral bilinear form on `E`. -/
theorem exists_positive_definite_invariant_bilinForm
    [Finite G] (ρ : Representation ℤ G E) :
    ∃ B : BilinForm ℤ E, B.IsSymm ∧ B.IsInvariantUnder ρ ∧ B.toQuadraticMap.PosDef := by
  letI : Fintype G := Fintype.ofFinite G
  let b := Module.Free.chooseBasis ℤ E
  let ι := Module.Free.ChooseBasisIndex ℤ E
  letI : Finite ι := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  let Bstd : BilinForm ℤ E := Matrix.toBilin b (1 : Matrix ι ι ℤ)
  let B : BilinForm ℤ E := ∑ g : G, Bstd.comp (ρ g) (ρ g)
  refine ⟨B, ?_, ?_, ?_⟩
  · -- The averaged form stays symmetric because each summand is a pullback of a symmetric form.
    refine ⟨?_⟩
    intro x y
    simp [B, Bstd, Matrix.toBilin_apply, Matrix.one_apply, mul_comm]
  · -- Averaging over right multiplication makes the form `G`-invariant.
    rw [LinearMap.BilinForm.isInvariantUnder_iff]
    intro a x y
    simp only [B]
    simpa [map_mul] using
      (Equiv.sum_comp (Equiv.mulRight a) (fun g : G => Bstd (ρ g x) (ρ g y)))
  · -- The identity summand is already positive on nonzero vectors, so the whole sum is positive.
    intro x hx
    have hxrepr : b.repr x ≠ 0 := by
      intro hrepr
      apply hx
      exact b.repr.injective (by simpa using hrepr)
    obtain ⟨i, hi⟩ : ∃ i : ι, b.repr x i ≠ 0 := by
      by_contra h
      apply hxrepr
      ext j
      by_contra hj
      exact h ⟨j, hj⟩
    have hBstd_sum_pos : 0 < ∑ j : ι, (b.repr x j)^2 := by
      refine Finset.sum_pos' ?_ ?_
      · intro j hj
        exact sq_nonneg _
      · exact ⟨i, Finset.mem_univ i, by simpa using sq_pos_of_ne_zero hi⟩
    have hBstd_xx : 0 < Bstd x x := by
      simpa [Bstd, Matrix.toBilin_apply, Matrix.one_apply, pow_two] using hBstd_sum_pos
    have hB_term_nonneg :
        ∀ g ∈ (Finset.univ : Finset G), 0 ≤ Bstd (ρ g x) (ρ g x) := by
      intro g hg
      have hsum_nonneg : 0 ≤ ∑ j : ι, (b.repr (ρ g x) j)^2 := by
        refine Finset.sum_nonneg ?_
        intro j hj'
        exact sq_nonneg _
      simpa [Bstd, Matrix.toBilin_apply, Matrix.one_apply, pow_two] using hsum_nonneg
    calc
      0 < Bstd x x := hBstd_xx
      _ ≤ ∑ g : G, Bstd (ρ g x) (ρ g x) := by
        have hmem : (1 : G) ∈ (Finset.univ : Finset G) := Finset.mem_univ 1
        simpa [B, LinearMap.BilinForm.comp_apply] using
          Finset.single_le_sum hB_term_nonneg hmem
      _ = B x x := by
        simp [B, LinearMap.BilinForm.comp_apply]

-- Proof sketch: extend `B` to `ℚ ⊗[ℤ] E`, identify the integral dual lattice attached to a
-- nondegenerate invariant form, and then apply the stable-lattice homothety mechanism from
-- Exercise `15-15.2-5` to the original lattice and its dual lattice inside the scalar-extended
-- representation.
/-- Helper for Exercise 15-15.2-6: the raw tensor comparison map is already linear over the
localized coefficient ring on the exact tensor owner. -/
theorem localized_at_prime_tensor_to_fractionRing_tensor_raw_map_smul
    (p : ℕ) [Fact p.Prime] (a : Localization (Representation.primeIdeal p).primeCompl)
    (z : Localization (Representation.primeIdeal p).primeCompl ⊗[ℤ] E) :
    localized_at_prime_tensor_to_fractionRing_tensor_raw (E := E) p (a • z) =
      a • localized_at_prime_tensor_to_fractionRing_tensor_raw (E := E) p z := by
  -- Compare both sides on pure tensors and then extend by tensor-product linearity.
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul b x =>
      rw [TensorProduct.smul_tmul', localized_at_prime_tensor_to_fractionRing_tensor_raw_apply_tmul]
      rw [localized_at_prime_tensor_to_fractionRing_tensor_raw_apply_tmul]
      rw [show (a • b : Localization (Representation.primeIdeal p).primeCompl) = a * b by rfl]
      rw [map_mul]
      rw [show a •
          ((algebraMap (Localization (Representation.primeIdeal p).primeCompl) (FractionRing ℤ) b) •
            ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x)) =
          (algebraMap (Localization (Representation.primeIdeal p).primeCompl) (FractionRing ℤ) a) •
            (((algebraMap (Localization (Representation.primeIdeal p).primeCompl) (FractionRing ℤ) b) •
              ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x))) by rfl]
      rw [smul_smul]
  | add z w hz hw =>
      simp [map_add, hz, hw]

/-- Helper for Exercise 15-15.2-6: after identifying the localized module with
`ℤ_(p) ⊗[ℤ] E`, the remaining source-faithful step is to extend scalars on the localized
coefficient factor from `ℤ_(p)` to `ℚ`. -/
noncomputable def localized_at_prime_tensor_to_fractionRing_tensor
    (p : ℕ) [Fact p.Prime] :
    Localization (Representation.primeIdeal p).primeCompl ⊗[ℤ] E →ₗ[
      Localization (Representation.primeIdeal p).primeCompl] FractionRing ℤ ⊗[ℤ] E :=
  { toFun := localized_at_prime_tensor_to_fractionRing_tensor_raw (E := E) p
    map_add' := (localized_at_prime_tensor_to_fractionRing_tensor_raw (E := E) p).map_add
    map_smul' := localized_at_prime_tensor_to_fractionRing_tensor_raw_map_smul (E := E) p }

/-- Helper for Exercise 15-15.2-6: the tensor-leg map to the rational ambient sends a pure tensor
to the expected scalar multiple of `1 ⊗ x`. -/
theorem localized_at_prime_tensor_to_fractionRing_tensor_apply_tmul
    (p : ℕ) [Fact p.Prime] (a : Localization (Representation.primeIdeal p).primeCompl) (x : E) :
    localized_at_prime_tensor_to_fractionRing_tensor (E := E) p (a ⊗ₜ[ℤ] x) =
      (algebraMap (Localization (Representation.primeIdeal p).primeCompl) (FractionRing ℤ) a) •
        ((1 : FractionRing ℤ) ⊗ₜ[ℤ] x) := by
  -- The rebuilt exact-owner comparison map keeps the raw pure-tensor formula.
  simpa [localized_at_prime_tensor_to_fractionRing_tensor] using
    localized_at_prime_tensor_to_fractionRing_tensor_raw_apply_tmul (E := E) p a x

/-- Helper for Exercise 15-15.2-6: on tensor-product basis coordinates, the scalar-upgraded
prime-local tensor map simply applies the coefficient embedding `ℤ_(p) → ℚ` coordinatewise. -/
theorem localized_at_prime_tensor_to_fractionRing_tensor_injective
    (p : ℕ) [Fact p.Prime] :
    Function.Injective (localized_at_prime_tensor_to_fractionRing_tensor (E := E) p) := by
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex ℤ E) ℤ E := Module.Free.chooseBasis ℤ E
  have hcoord :
      ∀ (z : Localization (Representation.primeIdeal p).primeCompl ⊗[ℤ] E)
        (i : Module.Free.ChooseBasisIndex ℤ E),
        ((TensorProduct.equivFinsuppOfBasisRight b)
            (localized_at_prime_tensor_to_fractionRing_tensor (E := E) p z)) i =
          algebraMap (Localization (Representation.primeIdeal p).primeCompl) (FractionRing ℤ)
            (((TensorProduct.equivFinsuppOfBasisRight b) z) i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero =>
        simp
    | tmul a x =>
        -- On pure tensors, the coordinate description is just coefficientwise localization.
        calc
          ((TensorProduct.equivFinsuppOfBasisRight b)
              (localized_at_prime_tensor_to_fractionRing_tensor (E := E) p (a ⊗ₜ[ℤ] x))) i
              =
            ((TensorProduct.equivFinsuppOfBasisRight b)
              (((algebraMap (Localization (Representation.primeIdeal p).primeCompl)
                  (FractionRing ℤ) a) ⊗ₜ[ℤ] x))) i := by
                rfl
          _ =
            (((b.repr x) i : ℤ) •
              (algebraMap (Localization (Representation.primeIdeal p).primeCompl)
                (FractionRing ℤ) a)) := by
                  rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
          _ =
            algebraMap (Localization (Representation.primeIdeal p).primeCompl) (FractionRing ℤ)
              ((((b.repr x) i : ℤ) • a)) := by
                simp [map_mul, mul_comm]
          _ =
            algebraMap (Localization (Representation.primeIdeal p).primeCompl) (FractionRing ℤ)
              (((TensorProduct.equivFinsuppOfBasisRight b) (a ⊗ₜ[ℤ] x)) i) := by
                rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add z w hz hw =>
        -- The coordinate formula is additive, so the tensor-product induction closes the proof.
        simp [map_add, hz, hw]
  intro z w hzw
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  have hcoord0 :
      algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
        (((TensorProduct.equivFinsuppOfBasisRight b) z) i) =
      algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
        (((TensorProduct.equivFinsuppOfBasisRight b) w) i) := by
    have hcoord0' :=
      congrArg
        (fun t ↦ ((TensorProduct.equivFinsuppOfBasisRight b) t) i)
        hzw
    calc
      algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
          (((TensorProduct.equivFinsuppOfBasisRight b) z) i)
          =
        ((TensorProduct.equivFinsuppOfBasisRight b)
          (localized_at_prime_tensor_to_fractionRing_tensor (E := E) p z)) i := by
            symm
            exact hcoord z i
      _ =
        ((TensorProduct.equivFinsuppOfBasisRight b)
          (localized_at_prime_tensor_to_fractionRing_tensor (E := E) p w)) i :=
            hcoord0'
      _ =
        algebraMap (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)
          (((TensorProduct.equivFinsuppOfBasisRight b) w) i) := hcoord w i
  exact
    (IsFractionRing.injective
      (Localization.AtPrime (Representation.primeIdeal p)) (FractionRing ℤ)) hcoord0

/-- Helper for Exercise 15-15.2-6: on a subsingleton free `ℤ`-module, every integral bilinear
form is automatically self-dual in the determinant-one owner sense because every basis is empty. -/
theorem isSelfDualIntegralLattice_of_subsingleton
    [Subsingleton E] (B : BilinForm ℤ E) :
    B.IsSelfDualIntegralLattice := by
  intro n b
  -- A basis of a subsingleton finite free module has empty index type.
  have hcard : Fintype.card (Fin n) = 0 := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_zero_of_subsingleton]
  letI : IsEmpty (Fin n) := Fintype.card_eq_zero_iff.mp hcard
  -- The determinant of an empty Gram matrix is `1`.
  simpa using (Matrix.det_isEmpty (M := B.toMatrix b))

/-- Helper for Exercise 15-15.2-6: the common rational ambient is nontrivial because the
denominator-`1` inclusion of the integral lattice is injective. -/
theorem fractionRing_tensor_nontrivial [Nontrivial E] :
    Nontrivial (FractionRing ℤ ⊗[ℤ] E) := by
  -- The map `x ↦ 1 ⊗ x` separates distinct integral vectors inside the rational ambient.
  exact Function.Injective.nontrivial (include_in_fractionRing_tensor_injective (E := E))

end IntegralLatticeAmbient

end ThompsonExercise
