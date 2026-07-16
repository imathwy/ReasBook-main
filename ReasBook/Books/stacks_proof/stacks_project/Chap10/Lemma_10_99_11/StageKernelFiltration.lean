import stacks_proof.stacks_project.Chap10.Lemma_10_99_11.MappedIdealTensor

open CategoryTheory.Limits IsLocalRing
open scoped TensorProduct Pointwise

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/-- Helper for Lemma 10.99.11: inside the ideal `I`, multiplying by `I ^ n` cuts out the
submodule `I ^ (n + 1)`. -/
lemma ideal_pow_smul_top_eq_submoduleOf_pow_succ
    (I : Ideal R) (n : ℕ) :
    I ^ n • (⊤ : Submodule R I) = (I ^ (n + 1)).submoduleOf I := by
  -- Proof comment: pull the ambient ideal product `I ^ n * I = I ^ (n + 1)` back along the
  -- subtype map of `I`.
  have hsubmoduleOf :
      ((I ^ n) • I).submoduleOf I = I ^ n • (⊤ : Submodule R I) := by
    simpa [Submodule.range_subtype] using
      (Submodule.comap_smul'' (f := I.subtype) I.subtype_injective
        (p := I) (I := I ^ n) (by simpa [Submodule.range_subtype]))
  calc
    I ^ n • (⊤ : Submodule R I) = ((I ^ n) • I).submoduleOf I := by
      symm
      exact hsubmoduleOf
    _ = (I ^ n * I).submoduleOf I := by
      rw [Ideal.smul_eq_mul]
    _ = (I ^ (n + 1)).submoduleOf I := by
      rw [pow_succ]

/-- Helper for Lemma 10.99.11: quotienting an ideal by its intersection with `K` identifies with
its image inside `R ⧸ K`. -/
noncomputable def ideal_quotient_inf_equiv_map_quotient
    (K J : Ideal R) :
    (J ⧸ (J ⊓ K).submoduleOf J) ≃ₗ[R]
      (((Ideal.map (Ideal.Quotient.mk K) J : Ideal (R ⧸ K)) :
        Submodule (R ⧸ K) (R ⧸ K)).restrictScalars R) := by
  let q : J →ₗ[R] (R ⧸ K) :=
    { toFun := fun x ↦ Ideal.Quotient.mk K x.1
      map_add' := fun x y ↦ rfl
      map_smul' := fun a x ↦ rfl }
  have hker : LinearMap.ker q = (J ⊓ K).submoduleOf J := by
    -- Proof comment: an element of `J` dies in `R ⧸ K` exactly when it already lies in `K`.
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      change (x : R) ∈ J ⊓ K
      exact ⟨x.2, Ideal.Quotient.eq_zero_iff_mem.mp hx⟩
    · intro hx
      change (x : R) ∈ J ⊓ K at hx
      rw [LinearMap.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx.2
  have hrange :
      LinearMap.range q =
        (((Ideal.map (Ideal.Quotient.mk K) J : Ideal (R ⧸ K)) :
          Submodule (R ⧸ K) (R ⧸ K)).restrictScalars R) := by
    -- Proof comment: the range consists exactly of quotient classes represented by elements of `J`.
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Ideal.mem_map_of_mem (Ideal.Quotient.mk K) x.2
    · intro hy
      rcases
          (Ideal.mem_map_iff_of_surjective
            (f := Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective).1 hy with
        ⟨x, hxJ, rfl⟩
      exact ⟨⟨x, hxJ⟩, rfl⟩
  -- Proof comment: now apply the first isomorphism theorem to the restricted quotient map.
  exact
    (Submodule.quotEquivOfEq (LinearMap.ker q) ((J ⊓ K).submoduleOf J) hker).symm.trans
      (q.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

/-- Helper for Lemma 10.99.11: the left quotient `I / I ^ (n + 1)` is the image ideal of `I`
inside `R ⧸ I ^ (n + 1)`. -/
noncomputable def ideal_quotient_equiv_mapped_power_stage
    (I : Ideal R) (n : ℕ) :
    (I ⧸ (I ^ (n + 1)).submoduleOf I) ≃ₗ[R]
      (((Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I :
          Ideal (R ⧸ I ^ (n + 1))) :
        Submodule (R ⧸ I ^ (n + 1)) (R ⧸ I ^ (n + 1))).restrictScalars R) := by
  -- Proof comment: because `I ^ (n + 1) ≤ I`, the quotient map `I → R ⧸ I ^ (n + 1)` has kernel
  -- exactly `I ^ (n + 1)` and range equal to the mapped ideal.
  have hpow : I ^ (n + 1) ≤ I := by
    exact Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hsub :
      ((I ⊓ I ^ (n + 1)).submoduleOf I) = (I ^ (n + 1)).submoduleOf I := by
    ext x
    change (x : R) ∈ I ⊓ I ^ (n + 1) ↔ (x : R) ∈ I ^ (n + 1)
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨x.2, hx⟩
  -- Proof comment: first rewrite the denominator submodule, then apply the first-isomorphism
  -- comparison to the quotient map `I → R ⧸ I ^ (n + 1)`.
  exact
    (Submodule.quotEquivOfEq _ _ hsub).symm.trans
      (ideal_quotient_inf_equiv_map_quotient (R := R) (K := I ^ (n + 1)) (J := I))

/-- Helper for Lemma 10.99.11: tensoring the left quotient `I / I ^ (n + 1)` with `M` can be
rewritten so the left tensor factor is the mapped ideal inside `R ⧸ I ^ (n + 1)`. -/
noncomputable def ideal_quotient_tensor_mapped_power_stage
    (I : Ideal R) (n : ℕ) :
    (I ⧸ (I ^ (n + 1)).submoduleOf I) ⊗[R] M ≃ₗ[R]
      ((((Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I :
            Ideal (R ⧸ I ^ (n + 1))) :
          Submodule (R ⧸ I ^ (n + 1)) (R ⧸ I ^ (n + 1))).restrictScalars R) ⊗[R] M) :=
  -- Proof comment: only the left tensor factor changes; the module factor `M` is untouched.
  TensorProduct.congr
    (ideal_quotient_equiv_mapped_power_stage (R := R) I n)
    (LinearEquiv.refl R M)

omit [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.11: after the left tensor factor has been rewritten as the mapped ideal
in `R / I^(n + 1)`, the remaining right tensor factor is the standard quotient/base-change owner
`M / I^(n + 1) M`. -/
noncomputable def mapped_power_stage_right_tensor_linearEquiv
    (I : Ideal R) (n : ℕ) :
    ((((Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I : Ideal (R ⧸ I ^ (n + 1))) :
          Submodule (R ⧸ I ^ (n + 1)) (R ⧸ I ^ (n + 1))).restrictScalars R) ⊗[R] M) ≃ₗ[R ⧸ I ^ (n + 1)]
      (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I ⊗[R ⧸ I ^ (n + 1)]
        (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))) := by
  let A : Type u := R ⧸ I ^ (n + 1)
  let J : Ideal A := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I
  let eN : A ⊗[R] M ≃ₗ[A] M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) :=
    LinearEquiv.extendScalarsOfSurjective (R := R) (S := A)
      Ideal.Quotient.mk_surjective (TensorProduct.quotTensorEquivQuotSMul M (I ^ (n + 1)))
  -- Proof comment: separate the missing owner transport into the standard base-change comparison
  -- `J ⊗[R] M ≃ J ⊗[A] (A ⊗[R] M)` and the quotient-module comparison
  -- `A ⊗[R] M ≃ M / I^(n + 1) M`.
  exact
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R A A
        (((J : Submodule A A).restrictScalars R)) M).symm).trans
      (TensorProduct.congr (LinearEquiv.refl A (J : Submodule A A)) eN)

omit [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.11: the full source-to-stage owner is the composite of the left
quotient normalization and the right-factor quotient/base-change comparison. -/
noncomputable def ideal_quotient_tensor_stage_linearEquiv
    (I : Ideal R) (n : ℕ) :
    (I ⧸ (I ^ (n + 1)).submoduleOf I) ⊗[R] M ≃ₗ[R]
      (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I ⊗[R ⧸ I ^ (n + 1)]
        (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))) :=
  (ideal_quotient_tensor_mapped_power_stage (R := R) (M := M) I n).trans
    ((mapped_power_stage_right_tensor_linearEquiv (R := R) (M := M) I n).restrictScalars R)

omit [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.11: the inverse of the full source-to-stage owner sends a stage pure
tensor back to the corresponding source pure tensor. -/
@[simp] theorem ideal_quotient_tensor_stage_linearEquiv_symm_tmul_mk
    (I : Ideal R) (n : ℕ) (a : I) (m : M) :
    (ideal_quotient_tensor_stage_linearEquiv (R := R) (M := M) I n).symm
        ((ideal_quotient_equiv_mapped_power_stage (R := R) I n (Submodule.Quotient.mk a)) ⊗ₜ[R ⧸
          I ^ (n + 1)] (Submodule.Quotient.mk m)) =
      (Submodule.Quotient.mk a) ⊗ₜ[R] m := by
  let A : Type u := R ⧸ I ^ (n + 1)
  let J : Ideal A := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I
  let eN : A ⊗[R] M ≃ₗ[A] M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) :=
    LinearEquiv.extendScalarsOfSurjective (R := R) (S := A)
      Ideal.Quotient.mk_surjective (TensorProduct.quotTensorEquivQuotSMul M (I ^ (n + 1)))
  let e₁ :
      ((((J : Submodule A A).restrictScalars R) ⊗[R] M)) ≃ₗ[A] J ⊗[A] (A ⊗[R] M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A
      (((J : Submodule A A).restrictScalars R)) M).symm
  let e₂ :
      J ⊗[A] (A ⊗[R] M) ≃ₗ[A]
        J ⊗[A] (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) :=
    TensorProduct.congr (LinearEquiv.refl A (J : Submodule A A)) eN
  change
    (ideal_quotient_tensor_mapped_power_stage (R := R) (M := M) I n).symm
        (((e₁.trans e₂).symm
          ((ideal_quotient_equiv_mapped_power_stage (R := R) I n (Submodule.Quotient.mk a)) ⊗ₜ[A]
            (Submodule.Quotient.mk m)))) =
      (Submodule.Quotient.mk a) ⊗ₜ[R] m
  rw [LinearEquiv.symm_trans_apply]
  have hq :
      eN.symm (Submodule.Quotient.mk m : M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) =
        ((1 : A) ⊗ₜ[R] m) := by
    apply eN.injective
    -- Proof comment: the quotient/base-change comparison is normalized by the standard
    -- `quotTensorEquivQuotSMul_mk_one_tmul` formula.
    rw [LinearEquiv.apply_symm_apply]
    convert (TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (M := M) (I := I ^ (n + 1)) m).symm
  -- Proof comment: first compute the right-factor transport on generators through the quotient
  -- owner `A ⊗[R] M ≃ M / I^(n + 1) M`.
  have hright :
      e₁.symm
          (e₂.symm
            ((ideal_quotient_equiv_mapped_power_stage (R := R) I n (Submodule.Quotient.mk a)) ⊗ₜ[A]
              (Submodule.Quotient.mk m))) =
        (ideal_quotient_equiv_mapped_power_stage (R := R) I n (Submodule.Quotient.mk a)) ⊗ₜ[R] m := by
    rw [TensorProduct.congr_symm_tmul]
    rw [hq]
    -- Proof comment: cancel the redundant base-change tensor and simplify the trivial scalar `1`.
    change
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A
        (((J : Submodule A A).restrictScalars R)) M)
          (((ideal_quotient_equiv_mapped_power_stage (R := R) I n (Submodule.Quotient.mk a)) ⊗ₜ[A]
            ((1 : A) ⊗ₜ[R] m))) =
        (ideal_quotient_equiv_mapped_power_stage (R := R) I n (Submodule.Quotient.mk a)) ⊗ₜ[R] m
    simpa using
      (TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul
        (R := R) (A := A) (B := A)
        (m := ideal_quotient_equiv_mapped_power_stage (R := R) I n (Submodule.Quotient.mk a))
        (n := m) (a := (1 : A)))
  -- Proof comment: the remaining left-factor transport is exactly the inverse of
  -- `ideal_quotient_equiv_mapped_power_stage`.
  calc
    (ideal_quotient_tensor_mapped_power_stage (R := R) (M := M) I n).symm
        (e₁.symm
          (e₂.symm
            ((ideal_quotient_equiv_mapped_power_stage (R := R) I n (Submodule.Quotient.mk a)) ⊗ₜ[A]
              (Submodule.Quotient.mk m)))) =
      (ideal_quotient_tensor_mapped_power_stage (R := R) (M := M) I n).symm
        ((ideal_quotient_equiv_mapped_power_stage (R := R) I n (Submodule.Quotient.mk a)) ⊗ₜ[R] m) := by
          rw [hright]
    _ = (Submodule.Quotient.mk a) ⊗ₜ[R] m := by
          simpa [ideal_quotient_tensor_mapped_power_stage] using
            (TensorProduct.congr_symm_tmul
              (ideal_quotient_equiv_mapped_power_stage (R := R) I n) (LinearEquiv.refl R M)
              (ideal_quotient_equiv_mapped_power_stage (R := R) I n (Submodule.Quotient.mk a)) m)

/-- Helper for Lemma 10.99.11: the source-to-stage owner sends a source pure tensor to the
corresponding stage pure tensor. -/
@[simp] theorem ideal_quotient_tensor_stage_linearEquiv_tmul_mk
    (I : Ideal R) (n : ℕ) (a : I) (m : M) :
    ideal_quotient_tensor_stage_linearEquiv (R := R) (M := M) I n
        ((Submodule.Quotient.mk a) ⊗ₜ[R] m) =
      (ideal_quotient_equiv_mapped_power_stage (R := R) I n (Submodule.Quotient.mk a)) ⊗ₜ[R ⧸
        I ^ (n + 1)] (Submodule.Quotient.mk m) := by
  -- Proof comment: the previously proved inverse-on-generators formula determines the forward map
  -- on generators by applying the inverse equivalence.
  apply (ideal_quotient_tensor_stage_linearEquiv (R := R) (M := M) I n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (ideal_quotient_tensor_stage_linearEquiv_symm_tmul_mk (R := R) (M := M) I n a m).symm

omit [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.11: the scalar-action map of `I` on `M / I^(n+1) M` kills
`I^(n+1) ⊆ I`, so it descends to `I / I^(n+1)`. -/
lemma ideal_quotient_scalar_action_ker_le
    (I : Ideal R) (n : ℕ) :
    (I ^ (n + 1)).submoduleOf I ≤
      LinearMap.ker
        ((LinearMap.compRight R (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
          ((LinearMap.lsmul R M).comp I.subtype)) := by
  intro a ha
  ext m
  -- Proof comment: an element of `I^(n+1)` acts trivially on the quotient by `I^(n+1) M`.
  exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul ha (by simp))

omit [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.11: the quotient `I / I^(n+1)` acts on `M / I^(n+1) M`. -/
noncomputable def ideal_quotient_scalar_action
    (I : Ideal R) (n : ℕ) :
    (I ⧸ (I ^ (n + 1)).submoduleOf I) →ₗ[R]
      (M →ₗ[R] M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) :=
  Submodule.liftQ
    ((I ^ (n + 1)).submoduleOf I)
    ((LinearMap.compRight R (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
      ((LinearMap.lsmul R M).comp I.subtype))
    (ideal_quotient_scalar_action_ker_le (R := R) (M := M) I n)

omit [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.11: the quotient-side source multiplication map
`(I / I^(n+1)) ⊗ M → M / I^(n+1) M`. -/
noncomputable def ideal_quotient_tensor_to_module_quotient
    (I : Ideal R) (n : ℕ) :
    (I ⧸ (I ^ (n + 1)).submoduleOf I) ⊗[R] M →ₗ[R]
      M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) :=
  TensorProduct.lift (ideal_quotient_scalar_action (R := R) (M := M) I n)

omit [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.11: on pure tensors, the quotient-side source multiplication map sends
`(a mod I^(n+1)) ⊗ m` to the class of `a • m`. -/
@[simp] theorem ideal_quotient_tensor_to_module_quotient_tmul_mk
    (I : Ideal R) (n : ℕ) (a : I) (m : M) :
    ideal_quotient_tensor_to_module_quotient (R := R) (M := M) I n
        ((Submodule.Quotient.mk a) ⊗ₜ[R] m) =
      Submodule.Quotient.mk ((a : R) • m) :=
  by
    simp [ideal_quotient_tensor_to_module_quotient, ideal_quotient_scalar_action]

omit [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.11: the stage multiplication map is the quotient of the source
multiplication map under the normalized stage owner. -/
lemma stage_tensor_multiplication_comp_ideal_quotient_tensor_stage_linearEquiv
    (I : Ideal R) (n : ℕ) :
    (TensorProduct.lift
      ((LinearMap.lsmul (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
        (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I).subtype)).restrictScalars R ∘ₗ
        (ideal_quotient_tensor_stage_linearEquiv (R := R) (M := M) I n).toLinearMap =
      ideal_quotient_tensor_to_module_quotient (R := R) (M := M) I n := by
  -- Proof comment: both composites send the source generator `(a mod I^(n+1)) ⊗ m` to the class
  -- of `a • m` in `M / I^(n+1) M`.
  apply TensorProduct.ext'
  intro q m
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective ((I ^ (n + 1)).submoduleOf I) q
  have hstage :=
    (show
      ideal_quotient_tensor_stage_linearEquiv (R := R) (M := M) I n
          (((I ^ (n + 1)).submoduleOf I).mkQ a ⊗ₜ[R] m) =
        (ideal_quotient_equiv_mapped_power_stage (R := R) I n (((I ^ (n + 1)).submoduleOf I).mkQ a)) ⊗ₜ[R ⧸
          I ^ (n + 1)] (Submodule.Quotient.mk m) by
      simpa using
        ideal_quotient_tensor_stage_linearEquiv_tmul_mk (R := R) (M := M) I n a m)
  -- Proof comment: after rewriting the source generator through the normalized owner, both sides
  -- are literally the class of `(a : R) • m`.
  calc
    (TensorProduct.lift
      ((LinearMap.lsmul (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
        (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I).subtype)).restrictScalars R
        (ideal_quotient_tensor_stage_linearEquiv (R := R) (M := M) I n
          ((((I ^ (n + 1)).submoduleOf I).mkQ a) ⊗ₜ[R] m)) =
      (TensorProduct.lift
        ((LinearMap.lsmul (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
          (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I).subtype)).restrictScalars R
          ((ideal_quotient_equiv_mapped_power_stage (R := R) I n (((I ^ (n + 1)).submoduleOf I).mkQ a)) ⊗ₜ[R ⧸
            I ^ (n + 1)] (Submodule.Quotient.mk m)) := by
            exact congrArg
              ((TensorProduct.lift
                ((LinearMap.lsmul (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
                  (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I).subtype)).restrictScalars R)
              hstage
    _ = ideal_quotient_tensor_to_module_quotient (R := R) (M := M) I n
          ((((I ^ (n + 1)).submoduleOf I).mkQ a) ⊗ₜ[R] m) := by
            rfl

omit [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.11: quotienting `I ⊗ M` by tensors coming from `I^(n+1)` turns the
source multiplication map into the quotient-side source multiplication map after taking classes in
the source quotient. -/
lemma ideal_quotient_tensor_to_module_quotient_comp_quotientTensorEquiv_symm_mkQ
    (I : Ideal R) (n : ℕ) :
    ideal_quotient_tensor_to_module_quotient (R := R) (M := M) I n ∘ₗ
        (TensorProduct.quotientTensorEquiv M ((I ^ (n + 1)).submoduleOf I)).symm.toLinearMap ∘ₗ
        Submodule.mkQ
          (LinearMap.range
            (TensorProduct.map ((I ^ (n + 1)).submoduleOf I).subtype
              (LinearMap.id : M →ₗ[R] M))) =
      (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ ∘ₗ
        TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) := by
  -- Proof comment: the quotient owner on `I ⊗ M` is built so that the class of `a ⊗ m` records
  -- exactly the class of `a • m` in `M / I^(n+1) M`.
  apply TensorProduct.ext'
  intro a m
  have hsymm :
      (TensorProduct.quotientTensorEquiv M ((I ^ (n + 1)).submoduleOf I)).symm
          (Submodule.Quotient.mk (a ⊗ₜ[R] m)) =
        (Submodule.Quotient.mk a) ⊗ₜ[R] m := by
    simpa using
      (TensorProduct.quotientTensorEquiv_symm_apply_mk_tmul
        (R := R) (N := M) ((I ^ (n + 1)).submoduleOf I) a m)
  have happly :=
    congrArg (ideal_quotient_tensor_to_module_quotient (R := R) (M := M) I n) hsymm
  simpa [LinearMap.comp_apply, Submodule.mkQ_apply] using happly

omit [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.11: the stage multiplication map over `R / I^(n + 1)` is injective
because the quotient module `M / I^(n + 1) M` is flat over that quotient ring. -/
lemma stage_tensor_multiplication_injective_of_flat_quotient
    (I : Ideal R) (hflat : FlatQuotientsByIdealPowers M I) (n : ℕ) :
    Function.Injective
      (TensorProduct.lift
        ((LinearMap.lsmul (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
          (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I).subtype)) := by
  -- Proof comment: at the quotient stage, the textbook flatness hypothesis is exactly the
  -- injectivity criterion for the canonical ideal-tensor multiplication map.
  exact
    source_tensor_to_module_injective_of_flat
      (A := R ⧸ I ^ (n + 1))
      (I := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I)
      (N := M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))
      (hflat (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))

omit [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.11: if a submodule of an ideal lies in `J I`, then tensoring that
inclusion with `M` lands in `J (I ⊗ M)`. -/
lemma range_subtype_rTensor_le_smul_top
    (I : Ideal R) (N : Submodule R I) (J : Ideal R)
    (hN : N ≤ J • (⊤ : Submodule R I)) :
    LinearMap.range (N.subtype.rTensor M) ≤ J • (⊤ : Submodule R (I ⊗[R] M)) := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  -- Proof comment: tensor induction reduces the statement to pure tensors whose left factor
  -- already lies in `J I`.
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · simp
  · intro n m
    change ((n : I) ⊗ₜ[R] m : I ⊗[R] M) ∈ J • (⊤ : Submodule R (I ⊗[R] M))
    have hn : (n : I) ∈ J • (⊤ : Submodule R I) := hN n.2
    -- Proof comment: expand the left factor inside `J • ⊤` and push the generators through the
    -- tensor product.
    refine Submodule.smul_induction_on hn ?_ ?_
    · intro r hr z hz
      simpa [TensorProduct.smul_tmul'] using
        (Submodule.smul_mem_smul hr
          (show z ⊗ₜ[R] m ∈ (⊤ : Submodule R (I ⊗[R] M)) by simp))
    · intro z w hz hw
      simpa [TensorProduct.add_tmul] using add_mem hz hw
  · intro y z hy hz
    simpa [LinearMap.map_add] using add_mem hy hz

omit [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module S M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.11: the source kernel `K = ker(I ⊗[R] M → M)` lies in
`I^n (I ⊗[R] M)` for every `n`. -/
lemma tensor_kernel_le_pow_smul_top_stage
    (I : Ideal R) (hflat : FlatQuotientsByIdealPowers M I) (n : ℕ) :
    LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)) ≤
      I ^ n • (⊤ : Submodule R (I ⊗[R] M)) := by
  let den : Submodule R I := (I ^ (n + 1)).submoduleOf I
  let denTensor :
      Submodule R (I ⊗[R] M) :=
    LinearMap.range
      (TensorProduct.map den.subtype (LinearMap.id : M →ₗ[R] M))
  let μ : I ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  let eQ :
      (I ⧸ den) ⊗[R] M ≃ₗ[R]
        (I ⊗[R] M) ⧸ denTensor :=
    TensorProduct.quotientTensorEquiv M den
  intro x hx
  have hxμ : μ x = 0 := by
    exact LinearMap.mem_ker.mp hx
  have hstage_zero :
      eQ.symm (Submodule.mkQ denTensor x) = 0 := by
    -- Proof comment: the class of `x` in the quotient stage is killed by the quotient-side source
    -- multiplication map, so the stage injectivity forces that class to vanish.
    apply (ideal_quotient_tensor_stage_linearEquiv (R := R) (M := M) I n).injective
    apply stage_tensor_multiplication_injective_of_flat_quotient (R := R) (M := M) I hflat n
    have hquot_zero :
        ideal_quotient_tensor_to_module_quotient (R := R) (M := M) I n
            (eQ.symm (Submodule.mkQ denTensor x)) = 0 := by
      have hcomp :=
        ideal_quotient_tensor_to_module_quotient_comp_quotientTensorEquiv_symm_mkQ
          (R := R) (M := M) I n
      simpa [eQ, denTensor, μ, LinearMap.comp_apply, hxμ] using
        congrArg (fun f ↦ f x) hcomp
    have hstage_comp :=
      stage_tensor_multiplication_comp_ideal_quotient_tensor_stage_linearEquiv
        (R := R) (M := M) I n
    have hstage_map_zero :
        (TensorProduct.lift
          ((LinearMap.lsmul (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
            (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I).subtype)).restrictScalars R
            ((ideal_quotient_tensor_stage_linearEquiv (R := R) (M := M) I n)
              (eQ.symm (Submodule.mkQ denTensor x))) = 0 := by
      calc
        (TensorProduct.lift
          ((LinearMap.lsmul (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
            (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I).subtype)).restrictScalars R
            ((ideal_quotient_tensor_stage_linearEquiv (R := R) (M := M) I n)
              (eQ.symm (Submodule.mkQ denTensor x))) =
            ideal_quotient_tensor_to_module_quotient (R := R) (M := M) I n
              (eQ.symm (Submodule.mkQ denTensor x)) := by
                simpa [LinearMap.comp_apply] using
                  congrArg
                    (fun f ↦ f (eQ.symm (Submodule.mkQ denTensor x)))
                    hstage_comp
        _ = 0 := hquot_zero
    simpa using hstage_map_zero
  have hclass_zero : Submodule.mkQ denTensor x = 0 := by
    simpa using congrArg eQ hstage_zero
  have hxrange : x ∈ denTensor := by
    exact (Submodule.Quotient.mk_eq_zero _).1 hclass_zero
  have hden :
      den ≤ I ^ n • (⊤ : Submodule R I) := by
    simpa [den] using
      (le_of_eq (ideal_pow_smul_top_eq_submoduleOf_pow_succ (R := R) I n).symm)
  have hrange :
      denTensor ≤ I ^ n • (⊤ : Submodule R (I ⊗[R] M)) := by
    simpa [denTensor] using
      range_subtype_rTensor_le_smul_top (R := R) (M := M) I den (I ^ n) hden
  exact hrange hxrange

/-- Helper for Lemma 10.99.11: the source multiplication map `I ⊗[R] M → M`, viewed as an
`S`-linear map via the scalar action on the right tensor factor. -/
noncomputable def source_tensor_to_module
    (I : Ideal R) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    I ⊗[R] M →ₗ[S] M := by
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  let eComm : I ⊗[R] M ≃ₗ[S] M ⊗[R] I :=
    (TensorProduct.comm R I M).toAddEquiv.linearEquiv S
  -- Proof comment: commute the two tensor factors and then contract the ideal factor by the
  -- canonical left tensor map followed by the base-change `rid` equivalence.
  exact
    (TensorProduct.AlgebraTensorModule.rid R S M).toLinearMap.comp
      ((TensorProduct.AlgebraTensorModule.lTensor S M I.subtype).comp eComm.toLinearMap)

/-- Helper for Lemma 10.99.11: restricting the `S`-linear source multiplication map back to `R`
recovers the original source multiplication map `I ⊗[R] M → M`. -/
lemma source_tensor_to_module_restrictScalars
    (I : Ideal R) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    (source_tensor_to_module (R := R) (S := S) (M := M) I).restrictScalars R =
      TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) := by
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  -- Proof comment: both maps send a source pure tensor `a ⊗ m` to the scalar action `(a : R) • m`.
  apply TensorProduct.ext'
  intro a m
  simp [source_tensor_to_module, TensorProduct.AlgebraTensorModule.rid_tmul]

/-- Helper for Lemma 10.99.11: the textbook source kernel
`ker(I ⊗[R] M → M)` satisfies the mapped-ideal power filtration as an `S`-submodule. -/
lemma source_tensor_kernel_le_mapped_power_smul_top
    (I : Ideal R) (hflat : FlatQuotientsByIdealPowers M I) (n : ℕ) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    LinearMap.ker (source_tensor_to_module (R := R) (S := S) (M := M) I) ≤
      (Ideal.map (algebraMap R S) I) ^ n • (⊤ : Submodule S (I ⊗[R] M)) := by
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  let μS : I ⊗[R] M →ₗ[S] M :=
    source_tensor_to_module (R := R) (S := S) (M := M) I
  have hkerR :
      LinearMap.ker (μS.restrictScalars R) ≤ I ^ n • (⊤ : Submodule R (I ⊗[R] M)) := by
    -- Proof comment: after forgetting the target-ring scalars, this is exactly the already proved
    -- source-stage filtration `K ⊆ I^n (I ⊗[R] M)`.
    simpa [μS, source_tensor_to_module_restrictScalars (R := R) (S := S) (M := M) I] using
      tensor_kernel_le_pow_smul_top_stage (R := R) (M := M) I hflat n
  have hpow :
      ((Ideal.map (algebraMap R S) I) ^ n • (⊤ : Submodule S (I ⊗[R] M))).restrictScalars R =
        I ^ n • (⊤ : Submodule R (I ⊗[R] M)) := by
    -- Proof comment: the `R`-power stage is the restriction of scalars of the mapped ideal power
    -- stage on the `S`-module `I ⊗[R] M`.
    simpa [Ideal.map_pow] using
      (Ideal.smul_restrictScalars
        (R := R) (S := S) (M := I ⊗[R] M) (I := I ^ n)
        (N := (⊤ : Submodule S (I ⊗[R] M))))
  have hker_restrict :
      LinearMap.ker (μS.restrictScalars R) = (LinearMap.ker μS).restrictScalars R := by
    simpa using LinearMap.ker_restrictScalars (R := R) μS
  -- Proof comment: rewrite both the kernel and the target stage through restriction of scalars and
  -- then forget back to the ambient `S`-submodule statement.
  rw [hker_restrict] at hkerR
  exact fun x hx ↦ by
    change x ∈ ((Ideal.map (algebraMap R S) I) ^ n • (⊤ : Submodule S (I ⊗[R] M))).restrictScalars R
    rw [hpow]
    exact hkerR hx

/-- Helper for Lemma 10.99.11: after localizing at a prime `q` containing `IS`, the localized
source kernel `ker(I ⊗[R] M → M)` vanishes. -/
lemma localized_source_tensor_kernel_eq_bot_at_prime
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflat : FlatQuotientsByIdealPowers M I) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    (LinearMap.ker (source_tensor_to_module (R := R) (S := S) (M := M) I)).localized
        q.asIdeal.primeCompl = ⊥ := by
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  let K : Submodule S (I ⊗[R] M) :=
    LinearMap.ker (source_tensor_to_module (R := R) (S := S) (M := M) I)
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let Sq := Localization.AtPrime q.asIdeal
  letI : Module.Finite S (I ⊗[R] M) := by
    let _ : Module.Finite R I := Module.Finite.of_fg I.fg_of_isNoetherianRing
    let _ : Module.Finite S (S ⊗[R] I) := by infer_instance
    let _ : Module.Finite S ((S ⊗[R] I) ⊗[S] M) := by infer_instance
    let eComm :
        (I ⊗[R] M) ≃ₗ[S] (M ⊗[R] I) :=
      (TensorProduct.comm R I M).toAddEquiv.linearEquiv S
    let e :
        ((S ⊗[R] I) ⊗[S] M) ≃ₗ[S] (I ⊗[R] M) :=
      (TensorProduct.comm S M (S ⊗[R] I)).symm.trans <|
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M I).trans
          eComm.symm
    simpa using (Module.Finite.equiv e : Module.Finite S (I ⊗[R] M))
  letI : Module.Finite Sq (LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M)) := inferInstance
  have hpow :
      ∀ n : ℕ, K ≤ J ^ n • (⊤ : Submodule S (I ⊗[R] M)) := by
    intro n
    simpa [K, J] using
      source_tensor_kernel_le_mapped_power_smul_top
        (R := R) (S := S) (M := M) I hflat n
  have hmap :
      Ideal.map (algebraMap S Sq) J ≤ Ideal.jacobson (⊥ : Ideal Sq) := by
    calc
      Ideal.map (algebraMap S Sq) J ≤ Ideal.map (algebraMap S Sq) q.asIdeal :=
        Ideal.map_mono hq
      _ = IsLocalRing.maximalIdeal Sq := by
        simpa [Sq] using Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal)
      _ ≤ Ideal.jacobson (⊥ : Ideal Sq) :=
        IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal Sq)
  have hlocal :
      (⨅ n : ℕ, (Ideal.map (algebraMap S Sq) J) ^ n • ⊤ :
        Submodule Sq (LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson
      (I := Ideal.map (algebraMap S Sq) J)
      (M := LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M))
      hmap
  have hle :
      K.localized q.asIdeal.primeCompl ≤
        (⨅ n : ℕ, (Ideal.map (algebraMap S Sq) J) ^ n • ⊤ :
          Submodule Sq (LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M))) := by
    refine le_iInf fun n ↦ ?_
    change
      K.localized' Sq q.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M)) ≤
        (Ideal.map (algebraMap S Sq) J) ^ n •
          (⊤ : Submodule Sq (LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M)))
    refine le_trans
      ((Submodule.localized'gi Sq q.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M))).gc.monotone_l
        (hpow n)) ?_
    rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Ideal.map_pow, Submodule.localized'_top]
  rw [hlocal] at hle
  simpa [K] using hle

/-- Helper for Lemma 10.99.11: after localizing at a prime `q` containing `IS`, the localized
source multiplication map `I ⊗[R] M → M` becomes injective. -/
lemma localized_source_multiplication_injective_at_prime
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflat : FlatQuotientsByIdealPowers M I) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    Function.Injective
      (LocalizedModule.map q.asIdeal.primeCompl
        (source_tensor_to_module (R := R) (S := S) (M := M) I)) := by
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  let μ :
      I ⊗[R] M →ₗ[S] M :=
    source_tensor_to_module (R := R) (S := S) (M := M) I
  have hker_bot :
      (LinearMap.ker μ).localized q.asIdeal.primeCompl = ⊥ := by
    -- Proof comment: this is exactly the localized source-kernel vanishing proved above.
    simpa [μ] using
      localized_source_tensor_kernel_eq_bot_at_prime
        (R := R) (S := S) (M := M) I q hq hflat
  have hsub :
      Subsingleton (LocalizedModule q.asIdeal.primeCompl (LinearMap.ker μ)) := by
    -- Proof comment: convert the localized kernel equality `K_q = 0` into a subsingleton owner.
    let _ : Subsingleton ↥((LinearMap.ker μ).localized q.asIdeal.primeCompl) :=
      (Submodule.subsingleton_iff_eq_bot).2 hker_bot
    exact (LinearMap.ker μ).localizedEquiv q.asIdeal.primeCompl |>.symm.injective.subsingleton
  -- Proof comment: Lemma `10.79.2` turns localized kernel vanishing into injectivity of the
  -- localized source map.
  exact
    (localized_map_injective_iff_subsingleton_ker μ q.asIdeal.primeCompl).2 hsub

end
