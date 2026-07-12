import Mathlib
import StacksProject_2024.Chap15.Lemma_15_89_9
import StacksProject_2024.Chap15.Lemma_15_91_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type u} [AddCommGroup M] [Module R M]
variable (f : R)

/-
Domain-style sampling:
- primary domain: commutative algebra of tensor base change along completion/localization, together
  with the canonical tensor-product/product comparison;
- sampled owner declarations:
  `principalPowerIdealImageQuotientMap`,
  `principalAdicCompletion_quotientMap_bijective`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`,
  `TensorProduct.prodRight`;
- best owner abstraction: the source-facing statement is nontriviality after base change to the
  product ring `R' × R_f`; its core support comes from the canonical quotient-map owner
  `principalPowerIdealImageQuotientMap` on the powers of `(f)`, the ideal-power-torsion
  base-change theorem from Lemma `15.89.9`, the principal completion specialization
  `principalAdicCompletion_quotientMap_bijective`, and the product tensor equivalence
  `TensorProduct.prodRight`;
- primitive data: the algebra map `R → R'`, the element `f`, the `R`-module `M`, and the
  quotient-map bijectivity hypothesis for `(f)^n`;
- derived API: the completion specialization and the decomposition of the tensor product with a
  product algebra into the corresponding product of tensor products;
- triage: the first theorem is `source-facing`, the completion specialization is a `bridge/view`,
  and the tensor-product/product equivalence is the `core/canonical` owner abstraction.
-/

-- Proof sketch: if `M ⊗[R] Localization.Away f` were trivial, then every element of `M` would be
-- killed by a power of `f`. Lemma `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`
-- then identifies `M ⊗[R] R'` with `M`, so the `R'`-summand stays nontrivial. Finally, tensoring
-- with the finite direct sum `R' ⊕ R_f` decomposes into the corresponding product of tensor
-- products.
/-- Helper for Lemma 15.91.2: if the tensor product with `R_f` is subsingleton, then the
canonical localization `M[f⁻¹]` is subsingleton as well. -/
lemma away_subsingleton_of_tensor_localization_subsingleton
    (hsub : Subsingleton (M ⊗[R] Localization.Away f)) :
    Subsingleton (LocalizedModule.Away f M) := by
  -- Transport the subsingleton statement across the canonical tensor/localization equivalence.
  let e : M ⊗[R] Localization.Away f ≃ₗ[R] LocalizedModule.Away f M :=
    (TensorProduct.comm R M (Localization.Away f)).trans
      ((LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm.restrictScalars R)
  constructor
  intro x y
  apply e.symm.injective
  exact @Subsingleton.elim _ hsub (e.symm x) (e.symm y)

/-- Helper for Lemma 15.91.2: if the localization away from `f` is subsingleton, then `M` is
torsion under powers of the principal ideal `(f)`. -/
lemma isIdealPowerTorsion_of_away_subsingleton
    (hsub : Subsingleton (LocalizedModule.Away f M)) :
    Module.IsIdealPowerTorsion (principalIdeal f) M := by
  -- Rewrite vanishing of the localization as the usual powers-of-`f` torsion condition.
  have htors : Module.IsTorsion' M (Submonoid.powers f) := by
    intro x
    obtain ⟨r, hr, hx⟩ :=
      (LocalizedModule.subsingleton_iff (S := Submonoid.powers f) (M := M)).mp hsub x
    exact ⟨⟨r, hr⟩, hx⟩
  exact (Module.isIdealPowerTorsion_principalIdeal_iff (M := M) f).2 htors

/-- Helper for Lemma 15.91.2: bijectivity of the canonical map `M → R' ⊗[R] M` forces the
right-ordered tensor product `M ⊗[R] R'` to be nontrivial when `M` is nontrivial. -/
lemma nontrivial_tensorProduct_right_of_bijective_mk
    [Nontrivial M]
    (hbij : Function.Bijective (TensorProduct.mk R R' M 1)) :
    Nontrivial (M ⊗[R] R') := by
  -- Pick two distinct elements of `M`, separate them after tensor base change, and swap factors.
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  have hxy_tensor : TensorProduct.mk R R' M 1 x ≠ TensorProduct.mk R R' M 1 y := by
    intro hEq
    exact hxy (hbij.1 hEq)
  have hxy_comm :
      (TensorProduct.comm R R' M) (TensorProduct.mk R R' M 1 x) ≠
        (TensorProduct.comm R R' M) (TensorProduct.mk R R' M 1 y) := by
    intro hEq
    exact hxy_tensor ((TensorProduct.comm R R' M).injective hEq)
  exact
    ⟨⟨(TensorProduct.comm R R' M) (TensorProduct.mk R R' M 1 x),
        (TensorProduct.comm R R' M) (TensorProduct.mk R R' M 1 y),
        hxy_comm⟩⟩

/-- Lemma 15.91.2: if the canonical maps `R / (f)^n → R' / (f)^n R'` are bijective for every
positive integer `n`, then tensoring any nontrivial `R`-module with `R' × R_f` remains
nontrivial. -/
@[stacks 0BNL]
theorem tensorProduct_prod_localizationAway_nontrivial_of_quotientMapBijective
    [Nontrivial M]
    (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Nontrivial (M ⊗[R] (R' × Localization.Away f)) := by
  classical
  let e := TensorProduct.prodRight R R M R' (Localization.Away f)
  -- Rewrite the target through the tensor/product decomposition and split on the localization
  -- branch.
  rcases subsingleton_or_nontrivial (M ⊗[R] Localization.Away f) with hAway | hAway
  · -- If the localization tensor factor vanishes, then `M` is `(f)`-power torsion.
    have htors :
        Module.IsIdealPowerTorsion (principalIdeal f) M :=
      isIdealPowerTorsion_of_away_subsingleton (R := R) (M := M) (f := f)
        (away_subsingleton_of_tensor_localization_subsingleton
          (R := R) (M := M) (f := f) hAway)
    have hquot' :
        ∀ n : ℕ+, Function.Bijective
          (Ideal.quotientMap
            (((principalIdeal f) ^ (n : ℕ)).map (algebraMap R R'))
            (algebraMap R R')
            Ideal.le_comap_map) := by
      -- Compare the principal-power quotient map with the generic quotient map through the
      -- canonical quotient equivalence on the target side.
      intro n
      let I : Ideal R := principalIdeal f
      let σ : R →+* R' := algebraMap R R'
      have hmap :
          Ideal.map σ (I ^ (n : ℕ)) = principalPowerIdeal (σ f) n := by
        simp [I, σ, principalPowerIdeal, principalIdeal, Ideal.map_pow, Ideal.map_span,
          Set.image_singleton]
      have htransport :
          principalPowerIdealImageQuotientMap σ f n =
            (Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
              (Ideal.quotientMap
                (Ideal.map σ (I ^ (n : ℕ)))
                σ
                Ideal.le_comap_map) := by
        apply Ideal.Quotient.ringHom_ext
        ext r
        dsimp [principalPowerIdealImageQuotientMap, principalPowerIdealQuotientMap]
        simpa [I, principalPowerIdeal, Ideal.quotientMap_mk] using
          (Ideal.quotientEquivAlgOfEq_mk (R₁ := R) (h := hmap) (x := σ r))
      have hcomp :
          Function.Bijective
            ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
              (Ideal.quotientMap
                (Ideal.map σ (I ^ (n : ℕ)))
                σ
                Ideal.le_comap_map)) := by
        have hcomp0 : Function.Bijective (principalPowerIdealImageQuotientMap σ f n) := by
          simpa [σ] using hquot n
        rw [htransport] at hcomp0
        exact hcomp0
      constructor
      · intro x y hxy
        have hxy0 :
            (Ideal.quotientMap
              (Ideal.map σ (I ^ (n : ℕ)))
              σ
              Ideal.le_comap_map) x =
              (Ideal.quotientMap
                (Ideal.map σ (I ^ (n : ℕ)))
                σ
                Ideal.le_comap_map) y := by
          simpa [I, σ] using hxy
        have hxy' :
            ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
              (Ideal.quotientMap
                (Ideal.map σ (I ^ (n : ℕ)))
                σ
                Ideal.le_comap_map)) x =
              ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
                (Ideal.quotientMap
                  (Ideal.map σ (I ^ (n : ℕ)))
                  σ
                  Ideal.le_comap_map)) y := by
          exact congrArg (Ideal.quotientEquivAlgOfEq R hmap) hxy0
        exact hcomp.1 hxy'
      · intro z
        obtain ⟨x, hx⟩ :=
          hcomp.2 ((Ideal.quotientEquivAlgOfEq R hmap) z)
        refine ⟨x, ?_⟩
        have hx' := hx
        have hx0 :
            (Ideal.quotientMap
              (Ideal.map σ (I ^ (n : ℕ)))
              σ
              Ideal.le_comap_map) x = z :=
          (Ideal.quotientEquivAlgOfEq R hmap).injective hx'
        simpa [I, σ] using hx0
    have hleft_bijective :
        Function.Bijective (TensorProduct.mk R R' M 1) :=
      tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
        (I := principalIdeal f) (R' := R') (M := M) htors hquot'
    have hleft :
        Nontrivial (M ⊗[R] R') :=
      nontrivial_tensorProduct_right_of_bijective_mk
        (R := R) (R' := R') (M := M) hleft_bijective
    -- The left tensor factor already gives two distinct points in the product decomposition.
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (M ⊗[R] R')
    have hpair :
        e.symm (x, (0 : M ⊗[R] Localization.Away f)) ≠
          e.symm (y, (0 : M ⊗[R] Localization.Away f)) := by
      intro hEq
      have hEq' :
          (x, (0 : M ⊗[R] Localization.Away f)) =
            (y, (0 : M ⊗[R] Localization.Away f)) :=
        e.symm.injective hEq
      exact hxy (congrArg Prod.fst hEq')
    exact
      ⟨⟨e.symm (x, (0 : M ⊗[R] Localization.Away f)),
          e.symm (y, (0 : M ⊗[R] Localization.Away f)),
          hpair⟩⟩
  · -- If the localization tensor factor is already nontrivial, it directly makes the product
    -- decomposition nontrivial.
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (M ⊗[R] Localization.Away f)
    have hpair :
        e.symm ((0 : M ⊗[R] R'), x) ≠
          e.symm ((0 : M ⊗[R] R'), y) := by
      intro hEq
      have hEq' :
          ((0 : M ⊗[R] R'), x) = ((0 : M ⊗[R] R'), y) :=
        e.symm.injective hEq
      exact hxy (congrArg Prod.snd hEq')
    exact
      ⟨⟨e.symm ((0 : M ⊗[R] R'), x),
          e.symm ((0 : M ⊗[R] R'), y),
          hpair⟩⟩

-- Proof sketch: apply
-- `tensorProduct_prod_localizationAway_nontrivial_of_quotientMapBijective` with
-- `R' = principalAdicCompletion f`, and use
-- `principalAdicCompletion_quotientMap_bijective` to verify the quotient-map hypothesis in the
-- principal-image form used above.
/-- The `(f)`-adic completion and the localization away from `f` jointly detect nontrivial
`R`-modules. -/
theorem tensorProduct_completion_prod_localizationAway_nontrivial
    [Nontrivial M] :
    Nontrivial
      (M ⊗[R] (principalAdicCompletion f × Localization.Away f)) := by
  -- Specialize the previous theorem to the principal adic completion and use the completion
  -- quotient comparison from Lemma `15.91.1`.
  simpa using
    (tensorProduct_prod_localizationAway_nontrivial_of_quotientMapBijective
      (R := R) (R' := principalAdicCompletion f) (M := M) f
      (fun n ↦ principalAdicCompletion_quotientMap_bijective (R := R) f n))

end
