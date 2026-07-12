import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

open scoped TensorProduct

/- Domain triage: this proposition is about the tensor-product comparison map from a tensor with
an arbitrary product to the product of the tensors.
- `source-facing`: the TFAE identifying finite generation of `M` with surjectivity of those
  comparison maps.
- `core/canonical`: the owner maps `TensorProduct.piRightHom` and `TensorProduct.piScalarRightHom`
  from mathlib.
- `bridge/view`: the constant-family and scalar-family clauses are just specializations of those
  owner maps, not separate primitive data.
Primitive data are only the semiring, the module, and the chosen family `Q`. -/

-- Proof sketch: `(1) → (2)` is proved by choosing a surjection from a finite free module onto `M`
-- and comparing the induced commutative square with `TensorProduct.piRight` for the finite free
-- source. The implications `(2) → (3) → (4)` are obtained by specialization. For `(4) → (1)`,
-- apply surjectivity for the index set `M` to the diagonal element `fun x ↦ x : M → M`; a
-- preimage is a finite sum of pure tensors, whose left tensor factors then generate `M`.
/-- Helper for Proposition 10.89.2: a tensor with a finite free module on the left is identified
with a finite tuple by commuting the tensor factors and then applying `piScalarRight`. -/
def fin_free_tensor_equiv (n : ℕ) (X : Type*) [AddCommMonoid X] [Module R X] :
    ((Fin n → R) ⊗[R] X) ≃ₗ[R] Fin n → X :=
  TensorProduct.comm R (Fin n → R) X ≪≫ₗ TensorProduct.piScalarRight R R X (Fin n)

/-- Helper for Proposition 10.89.2: after identifying finite free tensors with tuples,
`TensorProduct.piRightHom` evaluates those tuples coordinatewise. -/
lemma piRightHom_fin_free_tensor_equiv {n : ℕ} {A : Type w} {Q : A → Type x}
    [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)]
    (t : ((Fin n → R) ⊗[R] (∀ a, Q a))) :
    (fun a ↦ fin_free_tensor_equiv (R := R) n (Q a)
        ((TensorProduct.piRightHom R R (Fin n → R) Q t) a)) =
      fun a i ↦ fin_free_tensor_equiv (R := R) n (∀ a, Q a) t i a := by
  -- Reduce the comparison to pure tensors, where both sides compute directly.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a i
    simp [fin_free_tensor_equiv]
  · intro f q
    ext a i
    simp [fin_free_tensor_equiv, TensorProduct.piRightHom_tmul]
  · intro t₁ t₂ ht₁ ht₂
    ext a i
    simp only [map_add, Pi.add_apply]
    rw [congr_fun (congr_fun ht₁ a) i, congr_fun (congr_fun ht₂ a) i]

/-- Helper for Proposition 10.89.2: for a finite free left tensor factor,
`TensorProduct.piRightHom` is surjective. -/
lemma piRightHom_surjective_fin_free (n : ℕ) (A : Type w) (Q : A → Type x)
    [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)] :
    Function.Surjective (TensorProduct.piRightHom R R (Fin n → R) Q) := by
  intro y
  -- Pull the target family back to a tuple of functions on `Fin n`.
  let z : Fin n → ∀ a, Q a := fun i a ↦ fin_free_tensor_equiv (R := R) n (Q a) (y a) i
  refine ⟨(fin_free_tensor_equiv (R := R) n (∀ a, Q a)).symm z, ?_⟩
  ext a
  apply (fin_free_tensor_equiv (R := R) n (Q a)).injective
  -- The comparison lemma identifies the image with the chosen coordinatewise preimage.
  simpa [z] using congr_fun
    (piRightHom_fin_free_tensor_equiv (R := R) (Q := Q)
      ((fin_free_tensor_equiv (R := R) n (∀ a, Q a)).symm z)) a

/-- Helper for Proposition 10.89.2: tensoring a surjection with a product commutes with the
canonical comparison map to the product of the tensor factors. -/
lemma piRightHom_rTensor_apply {n : ℕ} {A : Type w} {Q : A → Type x}
    [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)]
    (f : (Fin n → R) →ₗ[R] M) (t : ((Fin n → R) ⊗[R] (∀ a, Q a))) :
    TensorProduct.piRightHom R R M Q (f.rTensor (∀ a, Q a) t) =
      fun a ↦ f.rTensor (Q a) ((TensorProduct.piRightHom R R (Fin n → R) Q t) a) := by
  -- Check the square on pure tensors and extend by tensor induction.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a
    simp
  · intro x q
    ext a
    simp [TensorProduct.piRightHom_tmul]
  · intro t₁ t₂ ht₁ ht₂
    ext a
    simp [ht₁, ht₂]

/-- Helper for Proposition 10.89.2: if a surjective family-valued element lies in the image of
`TensorProduct.piScalarRightHom`, then the left tensor factors of a finite decomposition generate
`M`. -/
lemma module_finite_of_piScalarRightHom_eq_surjective {A : Type w} {d : A → M}
    (hd : Function.Surjective d) {t : M ⊗[R] (A → R)}
    (ht : TensorProduct.piScalarRightHom R R M A t = d) :
    Module.Finite R M := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finsupp_left t
  let generators : Finset M := S.support
  have hx_mem_span : ∀ x : M, x ∈ Submodule.span R (↑generators : Set M) := by
    intro x
    obtain ⟨a, rfl⟩ := hd x
    -- Evaluate the diagonal identity at `x` to obtain an explicit finite linear combination.
    have hx : d a = generators.sum fun m ↦ S m a • m := by
      calc
        d a = (TensorProduct.piScalarRightHom R R M A t) a := by simpa [ht]
        _ = (TensorProduct.piScalarRightHom R R M A (S.sum fun m n ↦ m ⊗ₜ[R] n)) a := by rw [hS]
        _ = generators.sum fun m ↦ S m a • m := by
              simpa [generators, Finsupp.sum]
    refine (Submodule.mem_span_finset).2 ?_
    refine ⟨fun m ↦ S m a, ?_, ?_⟩
    · intro m hm
      by_contra hm_support
      have hzero : S m = 0 := by
        by_contra hne
        exact hm_support (Finsupp.mem_support_iff.mpr hne)
      exact hm (by simp [hzero])
    · simpa using hx.symm
  have htop : ⊤ ≤ Submodule.span R (↑generators : Set M) := by
    intro x hx
    exact hx_mem_span x
  have hspan_top : Submodule.span R (↑generators : Set M) = ⊤ := top_le_iff.mp htop
  letI : Module.Finite R (Submodule.span R (↑generators : Set M)) :=
    Module.Finite.span_of_finite R (Set.toFinite _)
  have hfinite_span : Module.Finite R (Submodule.span R (↑generators : Set M)) := inferInstance
  have hfinite_top : Module.Finite R (⊤ : Submodule R M) := by
    exact hspan_top ▸ hfinite_span
  letI : Module.Finite R (⊤ : Submodule R M) := hfinite_top
  -- Replace `M` by the span of the extracted finite generating set.
  exact Module.Finite.equiv (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M)

/-- Helper for Proposition 10.89.2: replacing the constant family `ULift R` by `R` on the tensor
source is a linear equivalence. -/
def pi_ulift_scalar_domain_equiv (A : Type (max v w)) :
    (M ⊗[R] (A → ULift.{max u x} R)) ≃ₗ[R] (M ⊗[R] (A → R)) :=
  TensorProduct.congr (LinearEquiv.refl R M)
    (LinearEquiv.piCongrRight fun _ ↦ ULift.moduleEquiv)

/-- Helper for Proposition 10.89.2: replacing the constant family `ULift R` by `R` on the target
product is a linear equivalence. -/
def pi_ulift_scalar_codomain_equiv (A : Type (max v w)) :
    (A → M ⊗[R] ULift.{max u x} R) ≃ₗ[R] (A → M) :=
  LinearEquiv.piCongrRight fun _ ↦
    TensorProduct.congr (LinearEquiv.refl R M) ULift.moduleEquiv ≪≫ₗ TensorProduct.rid R M

/-- Helper for Proposition 10.89.2: after transporting the constant family `ULift R` back to `R`,
the canonical map `TensorProduct.piRightHom` becomes `TensorProduct.piScalarRightHom`. -/
lemma piScalarRightHom_eq_piRightHom_ulift (A : Type (max v w))
    (t : M ⊗[R] (A → ULift.{max u x} R)) :
    TensorProduct.piScalarRightHom R R M A ((pi_ulift_scalar_domain_equiv (R := R) (M := M) A) t) =
      pi_ulift_scalar_codomain_equiv (R := R) (M := M) A
        (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) t) := by
  -- Both sides are linear in `t`, so it suffices to compute on pure tensors.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a
    simp [pi_ulift_scalar_domain_equiv, pi_ulift_scalar_codomain_equiv]
  · intro m f
    ext a
    simp [pi_ulift_scalar_domain_equiv, pi_ulift_scalar_codomain_equiv,
      TensorProduct.piRightHom_tmul, TensorProduct.piScalarRightHom_tmul]
  · intro t₁ t₂ ht₁ ht₂
    ext a
    simp [ht₁, ht₂]

/-- Proposition 10.89.2: for an `R`-module `M`, the following are equivalent: `M` is finitely
generated; for every family `(Q α)`, the canonical map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is surjective; for every `R`-module `Q` and every set
`A`, the canonical map `M ⊗[R] (A → Q) → A → (M ⊗[R] Q)` is surjective; and for every set `A`,
the canonical map `M ⊗[R] (A → R) → A → M` is surjective. -/
@[stacks 059J]
theorem module_finite_tfae_tensorProduct_pi_surjective :
    List.TFAE
      [ Module.Finite R M,
        ∀ (A : Type (max v w)) (Q : A → Type (max u x))
            [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)],
          Function.Surjective (TensorProduct.piRightHom R R M Q),
        ∀ (A : Type (max v w)) (Q : Type (max u x)) [AddCommMonoid Q] [Module R Q],
          Function.Surjective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)),
        ∀ (A : Type (max v w)),
          Function.Surjective (TensorProduct.piScalarRightHom R R M A) ] := by
  -- Follow the textbook route `(1) → (2) → (3) → (4) → (1)`.
  tfae_have 1 → 2 := by
    intro hM
    letI : Module.Finite R M := hM
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    intro A Q _ _ y
    -- Pull back each coordinate along the finite free presentation of `M`.
    obtain ⟨y₀, hy₀⟩ := Function.Surjective.piMap
      (fun a ↦ LinearMap.rTensor_surjective (Q a) hf) y
    obtain ⟨t, ht⟩ := piRightHom_surjective_fin_free (R := R) n A Q y₀
    refine ⟨f.rTensor (∀ a, Q a) t, ?_⟩
    ext a
    -- The commutative square transfers the finite-free surjectivity to `M`.
    calc
      TensorProduct.piRightHom R R M Q (f.rTensor (∀ a, Q a) t) a
          = f.rTensor (Q a) ((TensorProduct.piRightHom R R (Fin n → R) Q t) a) := by
              simpa using congr_fun
                (piRightHom_rTensor_apply (R := R) (M := M) (Q := Q) f t) a
      _ = f.rTensor (Q a) (y₀ a) := by rw [ht]
      _ = y a := by simpa using congr_fun hy₀ a
  tfae_have 2 → 3 := by
    intro h A Q _ _
    -- This is the constant-family specialization of clause `(2)`.
    simpa using h A (fun _ : A ↦ Q)
  tfae_have 3 → 4 := by
    intro h A
    -- Specialize clause `(3)` to `ULift R` and transport back along the canonical equivalences.
    let y' := (pi_ulift_scalar_codomain_equiv (R := R) (M := M) A).symm
    intro y
    obtain ⟨t, ht⟩ := h A (ULift.{max u x} R) (y' y)
    refine ⟨(pi_ulift_scalar_domain_equiv (R := R) (M := M) A) t, ?_⟩
    calc
      TensorProduct.piScalarRightHom R R M A
          ((pi_ulift_scalar_domain_equiv (R := R) (M := M) A) t)
          = pi_ulift_scalar_codomain_equiv (R := R) (M := M) A
              (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) t) := by
                  simpa using piScalarRightHom_eq_piRightHom_ulift (R := R) (M := M) A t
      _ = pi_ulift_scalar_codomain_equiv (R := R) (M := M) A (y' y) := by rw [ht]
      _ = y := by simp [y']
  tfae_have 4 → 1 := by
    intro h
    -- Use a preimage of the diagonal element indexed by `ULift M` to extract generators.
    obtain ⟨t, ht⟩ := h (ULift.{max v w} M) ULift.down
    exact module_finite_of_piScalarRightHom_eq_surjective
      (R := R) (M := M) (A := ULift.{max v w} M)
      (d := ULift.down) (fun x ↦ ⟨⟨x⟩, rfl⟩) ht
  tfae_finish

end
