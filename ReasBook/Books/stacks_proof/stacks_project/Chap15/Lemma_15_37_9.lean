import Mathlib
import Mathlib.RingTheory.TensorProduct.Quotient
import stacks_proof.stacks_project.Chap15.Definition_15_37_3
import stacks_proof.stacks_project.Chap15.Lemma_15_37_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace RingHom

section

open Algebra.TensorProduct

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

section TopologicalHelpers

variable {A : Type*}
variable [CommRing A] [TopologicalSpace S] [IsTopologicalRing S]
variable [TopologicalSpace A] [IsTopologicalRing A]

/-- Helper for Lemma 15.37.9: if an open ideal of the source lies in the kernel of a ring
homomorphism, then the map is continuous. This is the final continuity step for the descended
lift once a power of `𝔫` is shown to vanish. -/
private theorem continuous_of_open_ideal_le_ker_aux
    (φ : S →+* A) (I : Ideal S)
    (hIopen : IsOpen (I : Set S)) (hIker : I ≤ RingHom.ker φ) :
    Continuous φ := by
  -- Check continuity at `0`; the open kernel ideal is a neighborhood mapping entirely to `0`.
  apply continuous_of_continuousAt_zero φ
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro U hU
  refine Filter.mem_of_superset (hIopen.mem_nhds I.zero_mem) ?_
  intro x hx
  have hxker : φ x = 0 := RingHom.mem_ker.mp (hIker hx)
  simpa [hxker] using mem_of_mem_nhds hU

end TopologicalHelpers

section Helpers

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Helper for Lemma 15.37.9: the split `R`-linear retraction on `R' ⊗[R] A` obtained by applying
`σ` on the `R'`-factor and then collapsing `R ⊗[R] A` with `TensorProduct.lid`. -/
private noncomputable def tensor_split_retraction
    (σ : R' →ₗ[R] R) : R' ⊗[R] A →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap.comp
    (TensorProduct.map σ (LinearMap.id : A →ₗ[R] A))

/-- Helper for Lemma 15.37.9: the tensor split retraction is a left inverse to the canonical
`includeRight : A → R' ⊗[R] A`. -/
private theorem tensor_split_retraction_apply_includeRight
    (σ : R' →ₗ[R] R)
    (hσ : Function.LeftInverse σ (Algebra.linearMap R R'))
    (a : A) :
    tensor_split_retraction (R := R) (R' := R') (A := A) σ
      ((includeRight : A →ₐ[R] R' ⊗[R] A) a) = a := by
  -- First rewrite `includeRight a` as `1 ⊗ₜ a`; the split identity gives `σ 1 = 1`,
  -- so `TensorProduct.lid` collapses the remaining simple tensor to `a`.
  have hσ1 : σ 1 = 1 := by
    simpa using hσ 1
  simp [tensor_split_retraction, hσ1]

/-- Helper for Lemma 15.37.9: packaged as a linear-map identity, the split retraction really
retracts `includeRight`. -/
private theorem tensor_split_retraction_comp_includeRight
    (σ : R' →ₗ[R] R)
    (hσ : Function.LeftInverse σ (Algebra.linearMap R R')) :
    tensor_split_retraction (R := R) (R' := R') (A := A) σ ∘ₗ
        (includeRight : A →ₐ[R] R' ⊗[R] A).toLinearMap =
      LinearMap.id := by
  -- Extensionality reduces the linear-map identity to the pointwise computation above.
  ext a
  simpa using tensor_split_retraction_apply_includeRight
    (R := R) (R' := R') (A := A) σ hσ a

/-- Helper for Lemma 15.37.9: on the `R'`-branch, the split retraction records the projected
scalar `σ r'` in `A`. -/
private theorem tensor_split_retraction_apply_includeLeft
    (σ : R' →ₗ[R] R)
    (r' : R') :
    tensor_split_retraction (R := R) (R' := R') (A := A) σ
      ((includeLeft : R' →ₐ[R] R' ⊗[R] A) r') =
      algebraMap R A (σ r') := by
  -- Rewrite `includeLeft r'` as `r' ⊗ₜ 1`; after applying `σ ⊗ id`, `TensorProduct.lid`
  -- turns the resulting simple tensor into the corresponding scalar in `A`.
  simpa [Algebra.smul_def] using
    (show tensor_split_retraction (R := R) (R' := R') (A := A) σ
        ((includeLeft : R' →ₐ[R] R' ⊗[R] A) r') = σ r' • (1 : A) by
      simp [tensor_split_retraction])

/-- Helper for Lemma 15.37.9: projecting after left multiplication by the `A`-summand
`includeRight a` is the same as multiplying by `a` after projecting. -/
private theorem tensor_split_retraction_includeRight_mul
    (σ : R' →ₗ[R] R)
    (a : A) (x : R' ⊗[R] A) :
    tensor_split_retraction (R := R) (R' := R') (A := A) σ
        (((includeRight : A →ₐ[R] R' ⊗[R] A) a) * x) =
      a * tensor_split_retraction (R := R) (R' := R') (A := A) σ x := by
  -- Reduce to pure tensors, where the tensor-product multiplication is explicit.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r' b
    -- On `r' ⊗ₜ b`, both sides simplify to the same scalar multiple of `a * b`.
    simp [tensor_split_retraction, Algebra.smul_def, mul_assoc, mul_comm]
  · intro x y hx hy
    -- The retraction is linear, so the multiplicative compatibility is additive in the second
    -- variable.
    calc
      tensor_split_retraction (R := R) (R' := R') (A := A) σ
          (((includeRight : A →ₐ[R] R' ⊗[R] A) a) * (x + y))
          = tensor_split_retraction (R := R) (R' := R') (A := A) σ
              (((includeRight : A →ₐ[R] R' ⊗[R] A) a) * x) +
            tensor_split_retraction (R := R) (R' := R') (A := A) σ
              (((includeRight : A →ₐ[R] R' ⊗[R] A) a) * y) := by
              simp [mul_add, map_add]
      _ = a * tensor_split_retraction (R := R) (R' := R') (A := A) σ x +
            a * tensor_split_retraction (R := R) (R' := R') (A := A) σ y := by
              rw [hx, hy]
      _ = a * (tensor_split_retraction (R := R) (R' := R') (A := A) σ x +
            tensor_split_retraction (R := R) (R' := R') (A := A) σ y) := by
              rw [left_distrib]
      _ = a * tensor_split_retraction (R := R) (R' := R') (A := A) σ (x + y) := by
              rw [map_add]

/-- Helper for Lemma 15.37.9: projecting after right multiplication by the `A`-summand
`includeRight a` is the same as multiplying by `a` after projecting. -/
private theorem tensor_split_retraction_mul_includeRight
    (σ : R' →ₗ[R] R)
    (x : R' ⊗[R] A) (a : A) :
    tensor_split_retraction (R := R) (R' := R') (A := A) σ
        (x * ((includeRight : A →ₐ[R] R' ⊗[R] A) a)) =
      tensor_split_retraction (R := R) (R' := R') (A := A) σ x * a := by
  -- Reduce to pure tensors, where the tensor-product multiplication is explicit.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r' b
    -- On `r' ⊗ₜ b`, both sides simplify to the same scalar multiple of `b * a`.
    simp [tensor_split_retraction, Algebra.smul_def, mul_assoc, mul_comm]
  · intro x y hx hy
    -- The retraction is linear, so the multiplicative compatibility is additive in the first
    -- variable.
    calc
      tensor_split_retraction (R := R) (R' := R') (A := A) σ
          ((x + y) * ((includeRight : A →ₐ[R] R' ⊗[R] A) a))
          = tensor_split_retraction (R := R) (R' := R') (A := A) σ
              (x * ((includeRight : A →ₐ[R] R' ⊗[R] A) a)) +
            tensor_split_retraction (R := R) (R' := R') (A := A) σ
              (y * ((includeRight : A →ₐ[R] R' ⊗[R] A) a)) := by
              simp [add_mul, map_add]
      _ = tensor_split_retraction (R := R) (R' := R') (A := A) σ x * a +
            tensor_split_retraction (R := R) (R' := R') (A := A) σ y * a := by
              rw [hx, hy]
      _ = (tensor_split_retraction (R := R) (R' := R') (A := A) σ x +
            tensor_split_retraction (R := R) (R' := R') (A := A) σ y) * a := by
              rw [right_distrib]
      _ = tensor_split_retraction (R := R) (R' := R') (A := A) σ (x + y) * a := by
              rw [map_add]

/-- Helper for Lemma 15.37.9: the tensor product with `A ⧸ J` is canonically the quotient of
`R' ⊗[R] A` by the extended ideal `Jₜ`. -/
private noncomputable def tensor_quotient_baseChange_equiv
    (J : Ideal A) :
    R' ⊗[R] (A ⧸ J) ≃+* (R' ⊗[R] A) ⧸
      Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) (S := R') (T := A) (A := R') J).toRingEquiv

/-- Helper for Lemma 15.37.9: the quotient/tensor comparison sends a pure tensor with a quotient
representative to the corresponding quotient class in the tensor product. -/
private theorem tensor_quotient_baseChange_equiv_tmul_mk
    (J : Ideal A) (r' : R') (a : A) :
    tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J
      (r' ⊗ₜ[R] Ideal.Quotient.mk J a) =
    Ideal.Quotient.mk
      (Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J)
      (r' ⊗ₜ[R] a) := by
  -- This is the canonical pure-tensor computation for `tensorQuotientEquiv`.
  rfl

/-- Helper for Lemma 15.37.9: the inverse quotient/tensor comparison recovers the pure tensor with
the quotient representative. -/
private theorem tensor_quotient_baseChange_equiv_symm_mk
    (J : Ideal A) (r' : R') (a : A) :
    (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).symm
      (Ideal.Quotient.mk
        (Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J)
        (r' ⊗ₜ[R] a)) =
    r' ⊗ₜ[R] Ideal.Quotient.mk J a := by
  -- The inverse equivalence is the tensor of the quotient map on the `A`-factor.
  rfl

/-- Helper for Lemma 15.37.9: the descended `includeRight` map on `A ⧸ J` is obtained by first
forming the tensor-side `includeRight` and then using the quotient/tensor comparison. -/
private noncomputable def tensor_includeRight_quotient
    (J : Ideal A) :
    A ⧸ J →+* (R' ⊗[R] A) ⧸
      Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J :=
  (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).toRingHom.comp
    (includeRight : A ⧸ J →ₐ[R] R' ⊗[R] (A ⧸ J)).toRingHom

/-- Helper for Lemma 15.37.9: on representatives, the descended `includeRight` map is the obvious
quotient of the tensor-side `includeRight`. -/
private theorem tensor_includeRight_quotient_mk
    (J : Ideal A) (a : A) :
    tensor_includeRight_quotient (R := R) (R' := R') (A := A) J (Ideal.Quotient.mk J a) =
      Ideal.Quotient.mk
        (Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J)
        ((includeRight : A →ₐ[R] R' ⊗[R] A) a) := by
  -- The branch formula is the pure-tensor rewrite specialized to `1 ⊗ₜ a`.
  simpa [tensor_includeRight_quotient] using
    tensor_quotient_baseChange_equiv_tmul_mk
      (R := R) (R' := R') (A := A) J (1 : R') a

/-- Helper for Lemma 15.37.9: after quotienting by the extended ideal, the inverse comparison
equivalence is exactly `TensorProduct.map (id) (Ideal.Quotient.mk J)`. -/
private theorem tensor_quotient_baseChange_equiv_symm_comp_quotient_mk
    (J : Ideal A) :
    ((tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).symm.toRingHom).comp
        (Ideal.Quotient.mk
          (Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J)) =
      (Algebra.TensorProduct.map (AlgHom.id R' R') (Ideal.Quotient.mkₐ R J)).toRingHom := by
  -- The two tensor-side quotient maps agree on both canonical branches.
  apply Algebra.TensorProduct.ringHom_ext
  · ext r'
    simpa using
      tensor_quotient_baseChange_equiv_symm_mk
        (R := R) (R' := R') (A := A) J r' (1 : A)
  · ext a
    simpa using
      tensor_quotient_baseChange_equiv_symm_mk
        (R := R) (R' := R') (A := A) J (1 : R') a

/-- Helper for Lemma 15.37.9: the split tensor retraction commutes with quotienting on the
`A`-factor. This is the projection step used after descending the lifted tensor square. -/
private theorem tensor_split_retraction_quotient_map_comm
    (J : Ideal A) (σ : R' →ₗ[R] R) (x : R' ⊗[R] A) :
    tensor_split_retraction (R := R) (R' := R') (A := A ⧸ J) σ
        ((Algebra.TensorProduct.map (AlgHom.id R' R') (Ideal.Quotient.mkₐ R J)) x) =
      Ideal.Quotient.mk J
        (tensor_split_retraction (R := R) (R' := R') (A := A) σ x) := by
  -- Reduce to pure tensors; there the two routes are the same scalar computation followed by the
  -- quotient map.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r' a
    simp [tensor_split_retraction, Algebra.smul_def, mul_comm]
  · intro x y hx hy
    -- Both constructions are additive in the tensor variable, so the inductive hypothesis
    -- propagates across sums.
    calc
      tensor_split_retraction (R := R) (R' := R') (A := A ⧸ J) σ
          ((Algebra.TensorProduct.map (AlgHom.id R' R') (Ideal.Quotient.mkₐ R J)) (x + y)) =
        tensor_split_retraction (R := R) (R' := R') (A := A ⧸ J) σ
          ((Algebra.TensorProduct.map (AlgHom.id R' R') (Ideal.Quotient.mkₐ R J)) x) +
        tensor_split_retraction (R := R) (R' := R') (A := A ⧸ J) σ
          ((Algebra.TensorProduct.map (AlgHom.id R' R') (Ideal.Quotient.mkₐ R J)) y) := by
            simp [map_add]
      _ = Ideal.Quotient.mk J
            (tensor_split_retraction (R := R) (R' := R') (A := A) σ x) +
          Ideal.Quotient.mk J
            (tensor_split_retraction (R := R) (R' := R') (A := A) σ y) := by
            rw [hx, hy]
      _ = Ideal.Quotient.mk J
            (tensor_split_retraction (R := R) (R' := R') (A := A) σ (x + y)) := by
            simp [map_add]

/-- Helper for Lemma 15.37.9: the base-changed quotient map `ψₜ` agrees with the quotient of the
canonical left inclusion `R' → R' ⊗[R] A`. -/
private theorem quotient_tensor_baseChange_comp_includeLeft
    (J : Ideal A) (ψ : S →ₐ[R] A ⧸ J) :
    let Jₜ := Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J
    let ψₜ : R' ⊗[R] S →+* (R' ⊗[R] A) ⧸ Jₜ :=
      (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R' R') ψ).toRingHom
    (Ideal.Quotient.mk Jₜ).comp (includeLeftRingHom : R' →+* R' ⊗[R] A) =
      ψₜ.comp (includeLeftRingHom : R' →+* R' ⊗[R] S) := by
  -- On an element `r' : R'`, both sides are the quotient class of `r' ⊗ₜ 1`.
  ext r'
  -- Rewrite both branches as pure tensors and then evaluate the quotient/tensor comparison on
  -- `r' ⊗ₜ 1`.
  change
    Ideal.Quotient.mk
        (Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J)
        (r' ⊗ₜ[R] (1 : A)) =
      tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J
        (r' ⊗ₜ[R] ψ 1)
  rw [map_one]
  simpa using
    tensor_quotient_baseChange_equiv_tmul_mk
      (R := R) (R' := R') (A := A) J r' (1 : A)

/-- Helper for Lemma 15.37.9: on the `includeRight` branch, the tensor-side quotient map is the
descended `includeRight` map applied to `ψ`. -/
private theorem quotient_tensor_baseChange_apply_includeRight
    (J : Ideal A) (ψ : S →ₐ[R] A ⧸ J) (s : S) :
    let Jₜ := Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J
    let ψₜ : R' ⊗[R] S →+* (R' ⊗[R] A) ⧸ Jₜ :=
      (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R' R') ψ).toRingHom
    ψₜ ((includeRight : S →ₐ[R] R' ⊗[R] S) s) =
      tensor_includeRight_quotient (R := R) (R' := R') (A := A) J (ψ s) := by
  -- Both sides evaluate to the quotient class of `1 ⊗ₜ ψ s`.
  change
    tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J
      (1 ⊗ₜ[R] ψ s) =
      ((tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).toRingHom.comp
        (includeRight : A ⧸ J →ₐ[R] R' ⊗[R] (A ⧸ J)).toRingHom) (ψ s)
  rfl

/-- Helper for Lemma 15.37.9: the tensor-side map induced by `ψ` agrees with `ψ` on the
canonical `includeRight` branch. This is the branch identity used in the continuity descent. -/
private theorem tensor_map_comp_includeRight
    (J : Ideal A) (ψ : S →ₐ[R] A ⧸ J) :
    ((Algebra.TensorProduct.map (AlgHom.id R' R') ψ).toRingHom).comp
        ((includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom) =
      ((includeRight : A ⧸ J →ₐ[R] R' ⊗[R] (A ⧸ J)).toRingHom).comp ψ.toRingHom := by
  -- Both sides send `s` to the pure tensor `1 ⊗ₜ ψ s`.
  ext s
  rfl

/-- Helper for Lemma 15.37.9: if `ψ` kills a power of `𝔫`, then the tensor-side map kills the
same power of the extended ideal on `R' ⊗[R] S`. This is the kernel containment needed for the
continuity of the base-changed quotient map. -/
private theorem tensor_extended_pow_le_ker
    (J : Ideal A) (ψ : S →ₐ[R] A ⧸ J) (𝔫 : Ideal S) (n : ℕ)
    (hker : 𝔫 ^ n ≤ RingHom.ker ψ.toRingHom) :
    let K : Ideal (R' ⊗[R] S) :=
      Ideal.map ((includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom) 𝔫
    let Tψ : R' ⊗[R] S →+* R' ⊗[R] (A ⧸ J) :=
      (Algebra.TensorProduct.map (AlgHom.id R' R') ψ).toRingHom
    K ^ n ≤ RingHom.ker Tψ := by
  -- Rewrite the extended power as the image of `𝔫 ^ n`, then check the `includeRight` branch
  -- elementwise using `tensor_map_comp_includeRight`.
  dsimp
  rw [← Ideal.map_pow]
  refine Ideal.map_le_iff_le_comap.mpr ?_
  intro s hs
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have hsψ : ψ s = 0 := RingHom.mem_ker.mp (hker hs)
  have hbranch := congrArg
    (fun f : S →+* R' ⊗[R] (A ⧸ J) => f s)
    (tensor_map_comp_includeRight (R := R) (S := S) (R' := R') (A := A) J ψ)
  simpa [hsψ] using hbranch

/-- Helper for Lemma 15.37.9: once a tensor-side lift has the correct quotient, projecting its
`includeRight` branch through the split retraction recovers the original quotient map `ψ`. -/
private theorem projected_includeRight_quotient_eq
    (J : Ideal A) (ψ : S →ₐ[R] A ⧸ J)
    (σ : R' →ₗ[R] R)
    (hσ : Function.LeftInverse σ (Algebra.linearMap R R'))
    (Φ : R' ⊗[R] S →+* R' ⊗[R] A)
    (hΦquot :
      let Jₜ := Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J
      let ψₜ : R' ⊗[R] S →+* (R' ⊗[R] A) ⧸ Jₜ :=
        (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).toRingHom.comp
          (Algebra.TensorProduct.map (AlgHom.id R' R') ψ).toRingHom
      (Ideal.Quotient.mk Jₜ).comp Φ = ψₜ)
    (s : S) :
    Ideal.Quotient.mk J
      ((tensor_split_retraction (R := R) (R' := R') (A := A) σ)
        (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s))) = ψ s := by
  let Jₜ : Ideal (R' ⊗[R] A) :=
    Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J
  let ψₜ : R' ⊗[R] S →+* (R' ⊗[R] A) ⧸ Jₜ :=
    (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R' R') ψ).toRingHom
  have hquot : (Ideal.Quotient.mk Jₜ).comp Φ = ψₜ := by
    simpa [Jₜ, ψₜ] using hΦquot
  -- Evaluate the lifted quotient identity on `includeRight s` and transport it back to the tensor
  -- product with `A ⧸ J`.
  have htensor :
      (Algebra.TensorProduct.map (AlgHom.id R' R') (Ideal.Quotient.mkₐ R J))
          (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s)) =
        (includeRight : A ⧸ J →ₐ[R] R' ⊗[R] (A ⧸ J)) (ψ s) := by
    have hstep := congrArg (fun f => f ((includeRight : S →ₐ[R] R' ⊗[R] S) s)) hquot
    have hstep' :
        Ideal.Quotient.mk Jₜ (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s)) =
          tensor_includeRight_quotient (R := R) (R' := R') (A := A) J (ψ s) := by
      simpa [Jₜ, ψₜ] using hstep
    have htransport := congrArg
      ((tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).symm) hstep'
    -- Rewrite the left-hand side through the inverse quotient/tensor comparison and note that the
    -- right-hand side is definitionally `includeRight (ψ s)`.
    calc
      (Algebra.TensorProduct.map (AlgHom.id R' R') (Ideal.Quotient.mkₐ R J))
          (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s)) =
        (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).symm
          (Ideal.Quotient.mk Jₜ (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s))) := by
            symm
            have hsymm_comp :
                ((tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).symm.toRingHom).comp
                    (Ideal.Quotient.mk Jₜ) =
                  (Algebra.TensorProduct.map (AlgHom.id R' R') (Ideal.Quotient.mkₐ R J)).toRingHom := by
              simpa [Jₜ] using
                tensor_quotient_baseChange_equiv_symm_comp_quotient_mk
                  (R := R) (R' := R') (A := A) J
            simpa using congrArg
              (fun f : R' ⊗[R] A →+* R' ⊗[R] (A ⧸ J) =>
                f (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s)))
              hsymm_comp
      _ =
        (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).symm
          (tensor_includeRight_quotient (R := R) (R' := R') (A := A) J (ψ s)) := htransport
      _ = (includeRight : A ⧸ J →ₐ[R] R' ⊗[R] (A ⧸ J)) (ψ s) := by
            simpa [tensor_includeRight_quotient] using
              (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).symm_apply_apply
                ((includeRight : A ⧸ J →ₐ[R] R' ⊗[R] (A ⧸ J)) (ψ s))
  -- Apply the split retraction on `A ⧸ J` to descend from the tensor product back to the quotient.
  have hprojected := congrArg
    (tensor_split_retraction (R := R) (R' := R') (A := A ⧸ J) σ) htensor
  calc
    Ideal.Quotient.mk J
        ((tensor_split_retraction (R := R) (R' := R') (A := A) σ)
          (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s))) =
      tensor_split_retraction (R := R) (R' := R') (A := A ⧸ J) σ
        ((Algebra.TensorProduct.map (AlgHom.id R' R') (Ideal.Quotient.mkₐ R J))
          (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s))) := by
            symm
            simpa using tensor_split_retraction_quotient_map_comm
              (R := R) (R' := R') (A := A) J σ
              (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s))
    _ =
      tensor_split_retraction (R := R) (R' := R') (A := A ⧸ J) σ
        ((includeRight : A ⧸ J →ₐ[R] R' ⊗[R] (A ⧸ J)) (ψ s)) := hprojected
    _ = ψ s := by
          simpa using tensor_split_retraction_apply_includeRight
            (R := R) (R' := R') (A := A ⧸ J) σ hσ (ψ s)

/-- Helper for Lemma 15.37.9: after projecting a lifted `includeRight` branch back to `A`, the
remaining error lies both in the extended ideal and in the kernel of the split retraction. This is
the source-faithful decomposition used in the final multiplicativity check. -/
private theorem lifted_includeRight_error_mem_extended_ideal_and_ker
    (J : Ideal A) (ψ : S →ₐ[R] A ⧸ J)
    (σ : R' →ₗ[R] R)
    (hσ : Function.LeftInverse σ (Algebra.linearMap R R'))
    (Φ : R' ⊗[R] S →+* R' ⊗[R] A)
    (hΦquot :
      let Jₜ := Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J
      let ψₜ : R' ⊗[R] S →+* (R' ⊗[R] A) ⧸ Jₜ :=
        (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).toRingHom.comp
          (Algebra.TensorProduct.map (AlgHom.id R' R') ψ).toRingHom
      (Ideal.Quotient.mk Jₜ).comp Φ = ψₜ)
    (s : S) :
    let Jₜ := Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J
    let πA := tensor_split_retraction (R := R) (R' := R') (A := A) σ
    let φs := πA (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s))
    let δs := Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s) -
      (includeRight : A →ₐ[R] R' ⊗[R] A) φs
    δs ∈ Jₜ ∧ δs ∈ LinearMap.ker πA := by
  let Jₜ : Ideal (R' ⊗[R] A) :=
    Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J
  let πA : R' ⊗[R] A →ₗ[R] A :=
    tensor_split_retraction (R := R) (R' := R') (A := A) σ
  let φs : A :=
    πA (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s))
  let δs : R' ⊗[R] A :=
    Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s) -
      (includeRight : A →ₐ[R] R' ⊗[R] A) φs
  have hφquot : Ideal.Quotient.mk J φs = ψ s := by
    -- The projected `includeRight` branch already computes the quotient map `ψ`.
    simpa [Jₜ, πA, φs] using
      projected_includeRight_quotient_eq
        (R := R) (S := S) (R' := R') (A := A) J ψ σ hσ Φ hΦquot s
  have hxquot :
      Ideal.Quotient.mk Jₜ (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s)) =
        tensor_includeRight_quotient (R := R) (R' := R') (A := A) J (ψ s) := by
    -- Evaluate the lifted quotient identity on the canonical `includeRight` branch.
    have hstep := congrArg
      (fun f : R' ⊗[R] S →+* (R' ⊗[R] A) ⧸ Jₜ =>
        f ((includeRight : S →ₐ[R] R' ⊗[R] S) s))
      (by simpa [Jₜ] using hΦquot)
    simpa [Jₜ] using hstep
  have hincquot :
      Ideal.Quotient.mk Jₜ ((includeRight : A →ₐ[R] R' ⊗[R] A) φs) =
        tensor_includeRight_quotient (R := R) (R' := R') (A := A) J (Ideal.Quotient.mk J φs) := by
    -- The descended `includeRight` map is the quotient of the tensor-side `includeRight`.
    simpa [Jₜ] using
      tensor_includeRight_quotient_mk (R := R) (R' := R') (A := A) J φs
  have hδ_mem : δs ∈ Jₜ := by
    -- The two representatives have the same quotient class, so their difference lies in `Jₜ`.
    apply (Ideal.Quotient.eq_zero_iff_mem (I := Jₜ)).mp
    have hsame :
        Ideal.Quotient.mk Jₜ (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s)) =
          Ideal.Quotient.mk Jₜ ((includeRight : A →ₐ[R] R' ⊗[R] A) φs) := by
      calc
        Ideal.Quotient.mk Jₜ (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s)) =
            tensor_includeRight_quotient (R := R) (R' := R') (A := A) J (ψ s) := hxquot
        _ =
            tensor_includeRight_quotient (R := R) (R' := R') (A := A) J
              (Ideal.Quotient.mk J φs) := by
              rw [hφquot]
        _ = Ideal.Quotient.mk Jₜ ((includeRight : A →ₐ[R] R' ⊗[R] A) φs) := hincquot.symm
    change
      Ideal.Quotient.mk Jₜ
          (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s) -
            (includeRight : A →ₐ[R] R' ⊗[R] A) φs) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hsame
  have hδ_ker : δs ∈ LinearMap.ker πA := by
    -- By construction, the projected part of `δs` cancels exactly.
    rw [LinearMap.mem_ker]
    dsimp [δs, φs, πA]
    rw [map_sub]
    have hproj :
        tensor_split_retraction (R := R) (R' := R') (A := A) σ
            ((includeRight : A →ₐ[R] R' ⊗[R] A)
              ((tensor_split_retraction (R := R) (R' := R') (A := A) σ)
                (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s)))) =
          tensor_split_retraction (R := R) (R' := R') (A := A) σ
            (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s)) := by
      simpa using
        tensor_split_retraction_apply_includeRight
          (R := R) (R' := R') (A := A) σ hσ
          ((tensor_split_retraction (R := R) (R' := R') (A := A) σ)
            (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s)))
    exact sub_eq_zero.mpr hproj.symm
  simpa [Jₜ, πA, φs, δs] using And.intro hδ_mem hδ_ker

end Helpers

/- Domain-style sampling for Lemma 15.37.9:
- primary domain: descent of adic topological formal smoothness along a split base change in
  commutative algebra.
- inspected owner declarations:
  * `RingHom.FormallySmoothTopologically`, the core topological lifting owner from Definition
    `15.37.1`;
  * `RingHom.formally_smooth_for_adic`, the chapter owner bridge for the discrete-source adic
    specialization from Definition `15.37.3`;
  * `RingHom.formally_smooth_for_adic_baseChange`, the forward base-change theorem from
    Lemma `15.37.8`;
  * `RingHom.formallySmoothTopologically_adicSource_iff_discreteSource`, the source-topology bridge
    from Lemma `15.37.2`.
- best owner abstraction: the source-facing theorem in this file should use the chapter adic owner
  `RingHom.formally_smooth_for_adic`; the lower-level owner
  `RingHom.FormallySmoothTopologically` is the core/canonical implementation layer.
- primitive data: the ideal `𝔫 : Ideal S`, the split `R`-linear retraction of `R → R'`, and
  formal smoothness for the base-changed map with respect to the extended ideal.
- derived API: descent of formal smoothness for the original map `R → S`.

Source/core/bridge triage:
- `source-facing`: formal smoothness of `R → S` for the `𝔫`-adic topology.
- `core/canonical`: `RingHom.FormallySmoothTopologically`.
- `bridge/view`: `RingHom.formally_smooth_for_adic`. -/

-- Proof sketch: given a square-zero lifting problem for `R → S`, base change it along `R → R'`
-- to a lifting problem for `R' → R' ⊗[R] S`. The assumed topological formal smoothness over `R'`
-- gives a lift after base change. Choose an `R`-linear retraction `R' → R`, use it to split
-- `A ⊗[R] R'` as `A ⊕ (A ⊗[R] C)`, and then project the lifted map back to the summand `A`,
-- exactly as in the Stacks Project argument.
set_option maxHeartbeats 800000 in
section
/-- Lemma 15.37.9: if `R` is an `R`-linear direct summand of `R'` and the canonical base-change map
`R' → R' ⊗[R] S` is formally smooth for the adic topology defined by the extended ideal
`𝔫 (R' ⊗[R] S)`, then `R → S` is formally smooth for the `𝔫`-adic topology. -/
@[stacks 07EH]
theorem formally_smooth_for_adic_of_split_baseChange
    (𝔫 : Ideal S)
    (hsplit : ∃ σ : R' →ₗ[R] R, Function.LeftInverse σ (Algebra.linearMap R R'))
    (hf : formally_smooth_for_adic
      (includeLeftRingHom : R' →+* R' ⊗[R] S) (Ideal.map includeRight.toRingHom 𝔫)) :
    formally_smooth_for_adic (algebraMap R S) 𝔫 := by
  rw [RingHom.formally_smooth_for_adic_iff]
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := ⟨rfl⟩
  letI : TopologicalSpace S := Ideal.adicTopology 𝔫
  refine
    { toContinuous := continuous_of_discreteTopology
      lift_condition := ?_ }
  intro A _ _ _ J _ hJ ψ hψ g hg hcomm
  letI : Algebra R A := g.toAlgebra
  letI : Algebra R (A ⧸ J) := ((Ideal.Quotient.mk J).comp g).toAlgebra
  let ψAlg : S →ₐ[R] A ⧸ J :=
    { toRingHom := ψ
      commutes' := fun r ↦ by
        change ψ (algebraMap R S r) = Ideal.Quotient.mk J (g r)
        exact (DFunLike.congr_fun hcomm r).symm }
  rcases hsplit with ⟨σ, hσ⟩
  let K : Ideal (R' ⊗[R] S) :=
    Ideal.map ((includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom) 𝔫
  let Jₜ : Ideal (R' ⊗[R] A) :=
    Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J
  let ψₜ : R' ⊗[R] S →+* (R' ⊗[R] A) ⧸ Jₜ :=
    (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R' R') ψAlg).toRingHom
  letI : TopologicalSpace R' := ⊥
  letI : DiscreteTopology R' := ⟨rfl⟩
  letI : TopologicalSpace (R' ⊗[R] S) := Ideal.adicTopology K
  have hfTop :
      (includeLeftRingHom : R' →+* R' ⊗[R] S).FormallySmoothTopologically := by
    have hfK :
        formally_smooth_for_adic
          (includeLeftRingHom : R' →+* R' ⊗[R] S) K := by
      simpa [K] using hf
    exact
      (RingHom.formally_smooth_for_adic_iff
        (includeLeftRingHom : R' →+* R' ⊗[R] S) K).mp hfK
  letI : TopologicalSpace (R' ⊗[R] A) := ⊥
  letI : DiscreteTopology (R' ⊗[R] A) := ⟨rfl⟩
  let qTop : TopologicalSpace ((R' ⊗[R] A) ⧸ Jₜ) := ⊥
  letI : TopologicalSpace ((R' ⊗[R] A) ⧸ Jₜ) := qTop
  let qDisc : DiscreteTopology ((R' ⊗[R] A) ⧸ Jₜ) := ⟨rfl⟩
  letI : DiscreteTopology ((R' ⊗[R] A) ⧸ Jₜ) := qDisc
  have hJₜ : Jₜ ^ 2 = ⊥ := by
    dsimp [Jₜ]
    rw [← Ideal.map_pow, hJ]
    simp
  have h𝔫adic : IsAdic 𝔫 := rfl
  rcases RingHom.pow_le_ker_of_continuous_to_discrete_quotient 𝔫 h𝔫adic ψ hψ with
    ⟨n, hn⟩
  have hKkerT :
      K ^ n ≤ RingHom.ker
        ((Algebra.TensorProduct.map (AlgHom.id R' R') ψAlg).toRingHom) := by
    simpa [K] using
      tensor_extended_pow_le_ker
        (R := R) (S := S) (R' := R') (A := A) J ψAlg 𝔫 n hn
  have hKker : K ^ n ≤ RingHom.ker ψₜ := by
    intro x hx
    rw [RingHom.mem_ker]
    have hx0 :
        ((Algebra.TensorProduct.map (AlgHom.id R' R') ψAlg).toRingHom) x = 0 := by
      exact RingHom.mem_ker.mp (hKkerT hx)
    change
      (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J)
          (((Algebra.TensorProduct.map (AlgHom.id R' R') ψAlg).toRingHom) x) = 0
    have hx0' : (Algebra.TensorProduct.map (AlgHom.id R' R') ψAlg) x = 0 := hx0
    exact congrArg
      (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J) hx0'
  have hKopen : IsOpen (((K ^ n : Ideal (R' ⊗[R] S)) : Set (R' ⊗[R] S))) := by
    have hKadic : IsAdic K := rfl
    exact (isAdic_iff.mp hKadic).1 n
  have hψₜcont : Continuous ψₜ :=
    continuous_of_open_ideal_le_ker_aux ψₜ (K ^ n) hKopen hKker
  have hcommₜ :
      (Ideal.Quotient.mk Jₜ).comp (includeLeftRingHom : R' →+* R' ⊗[R] A) =
        ψₜ.comp (includeLeftRingHom : R' →+* R' ⊗[R] S) := by
    simpa [Jₜ, ψₜ] using
      quotient_tensor_baseChange_comp_includeLeft
        (R := R) (S := S) (R' := R') (A := A) J ψAlg
  obtain ⟨Φ, hΦcont, hΦquot, hΦleft⟩ :=
    @RingHom.FormallySmoothTopologically.exists_lift
      R' (R' ⊗[R] S) _ _ inferInstance _ _ inferInstance
      (includeLeftRingHom : R' →+* R' ⊗[R] S) hfTop
      (R' ⊗[R] A) _ _ inferInstance Jₜ qDisc
      hJₜ ψₜ hψₜcont
      (includeLeftRingHom : R' →+* R' ⊗[R] A) continuous_of_discreteTopology hcommₜ
  have hΦquot' :
      let Jₜ := Ideal.map ((includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom) J
      let ψₜ : R' ⊗[R] S →+* (R' ⊗[R] A) ⧸ Jₜ :=
        (tensor_quotient_baseChange_equiv (R := R) (R' := R') (A := A) J).toRingHom.comp
          (Algebra.TensorProduct.map (AlgHom.id R' R') ψAlg).toRingHom
      (Ideal.Quotient.mk Jₜ).comp Φ = ψₜ := by
    simpa [Jₜ, ψₜ] using hΦquot
  have hincludeRightCont :
      Continuous ((includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom) := by
    refine
      (RingHom.continuous_adic_iff_exists_pow_map_le
        ((includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom) 𝔫 K).2 ?_
    refine ⟨1, ?_⟩
    simpa [K]
  let πA : R' ⊗[R] A →ₗ[R] A :=
    tensor_split_retraction (R := R) (R' := R') (A := A) σ
  let φFun : S → A := fun s ↦ πA (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s))
  have hφquot : ∀ s : S, Ideal.Quotient.mk J (φFun s) = ψ s := by
    intro s
    simpa [φFun, πA] using
      projected_includeRight_quotient_eq
        (R := R) (S := S) (R' := R') (A := A) J ψAlg σ hσ Φ hΦquot' s
  have hφcomp_apply : ∀ r : R, φFun (algebraMap R S r) = g r := by
    intro r
    calc
      φFun (algebraMap R S r)
          = πA (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) (algebraMap R S r))) := rfl
      _ = πA (Φ ((includeLeft : R' →ₐ[R] R' ⊗[R] S) (algebraMap R R' r))) := by
            simp
      _ = πA ((includeLeft : R' →ₐ[R] R' ⊗[R] A) (algebraMap R R' r)) := by
            exact congrArg πA (DFunLike.congr_fun hΦleft (algebraMap R R' r))
      _ = algebraMap R A (σ (algebraMap R R' r)) := by
            simpa [πA] using
              tensor_split_retraction_apply_includeLeft
                (R := R) (R' := R') (A := A) σ (algebraMap R R' r)
      _ = algebraMap R A r := by
            simpa using congrArg (algebraMap R A) (hσ r)
      _ = g r := rfl
  have hφ_zero : φFun 0 = 0 := by
    simpa using hφcomp_apply (0 : R)
  have hφ_one : φFun 1 = 1 := by
    simpa using hφcomp_apply (1 : R)
  have hφ_add (s t : S) : φFun (s + t) = φFun s + φFun t := by
    calc
      φFun (s + t)
          = πA (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) (s + t))) := rfl
      _ = πA (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s) +
            Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) t)) := by
            rw [map_add, map_add]
      _ = πA (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s)) +
            πA (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) t)) := by
            rw [map_add]
      _ = φFun s + φFun t := rfl
  have hφ_mul (s t : S) : φFun (s * t) = φFun s * φFun t := by
      let xs : R' ⊗[R] A := Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s)
      let xt : R' ⊗[R] A := Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) t)
      let φs : A := φFun s
      let φt : A := φFun t
      let δs : R' ⊗[R] A := xs - (includeRight : A →ₐ[R] R' ⊗[R] A) φs
      let δt : R' ⊗[R] A := xt - (includeRight : A →ₐ[R] R' ⊗[R] A) φt
      let mainTerm : R' ⊗[R] A :=
        ((includeRight : A →ₐ[R] R' ⊗[R] A) φs) *
          ((includeRight : A →ₐ[R] R' ⊗[R] A) φt)
      let crossRightTerm : R' ⊗[R] A :=
        δs * ((includeRight : A →ₐ[R] R' ⊗[R] A) φt)
      let crossLeftTerm : R' ⊗[R] A :=
        ((includeRight : A →ₐ[R] R' ⊗[R] A) φs) * δt
      let errorTerm : R' ⊗[R] A := δs * δt
      have hδs :
          δs ∈ Jₜ ∧ δs ∈ LinearMap.ker πA := by
        simpa [Jₜ, πA, φFun, xs, φs, δs] using
          lifted_includeRight_error_mem_extended_ideal_and_ker
            (R := R) (S := S) (R' := R') (A := A) J ψAlg σ hσ Φ hΦquot' s
      have hδt :
          δt ∈ Jₜ ∧ δt ∈ LinearMap.ker πA := by
        simpa [Jₜ, πA, φFun, xt, φt, δt] using
          lifted_includeRight_error_mem_extended_ideal_and_ker
            (R := R) (S := S) (R' := R') (A := A) J ψAlg σ hσ Φ hΦquot' t
      have hxs : xs = (includeRight : A →ₐ[R] R' ⊗[R] A) φs + δs := by
        dsimp [δs]
        abel
      have hxt : xt = (includeRight : A →ₐ[R] R' ⊗[R] A) φt + δt := by
        dsimp [δt]
        abel
      have hπδs : πA δs = 0 := LinearMap.mem_ker.mp hδs.2
      have hπδt : πA δt = 0 := LinearMap.mem_ker.mp hδt.2
      have hδsδt_zero : δs * δt = 0 := by
        have hmul_mem : δs * δt ∈ Jₜ * Jₜ := Ideal.mul_mem_mul hδs.1 hδt.1
        have hmul_mem' : δs * δt ∈ Jₜ ^ 2 := by
          simpa [pow_two] using hmul_mem
        have hbot_mem : δs * δt ∈ (⊥ : Ideal (R' ⊗[R] A)) := by
          simpa [hJₜ] using hmul_mem'
        simpa using hbot_mem
      have hmain :
          πA (((includeRight : A →ₐ[R] R' ⊗[R] A) φs) *
            ((includeRight : A →ₐ[R] R' ⊗[R] A) φt)) =
            φs * φt := by
        calc
          πA (((includeRight : A →ₐ[R] R' ⊗[R] A) φs) *
              ((includeRight : A →ₐ[R] R' ⊗[R] A) φt))
              = πA ((includeRight : A →ₐ[R] R' ⊗[R] A) (φs * φt)) := by
                  exact congrArg πA
                    ((includeRight : A →ₐ[R] R' ⊗[R] A).map_mul φs φt).symm
          _ = φs * φt := by
                simpa [πA] using
                  tensor_split_retraction_apply_includeRight
                    (R := R) (R' := R') (A := A) σ hσ (φs * φt)
      have hcross_left :
          πA (((includeRight : A →ₐ[R] R' ⊗[R] A) φs) * δt) = 0 := by
        calc
          πA (((includeRight : A →ₐ[R] R' ⊗[R] A) φs) * δt)
              = φs * πA δt := by
                  simpa [πA] using
                    tensor_split_retraction_includeRight_mul
                      (R := R) (R' := R') (A := A) σ φs δt
          _ = 0 := by simp [hπδt]
      have hcross_right :
          πA (δs * ((includeRight : A →ₐ[R] R' ⊗[R] A) φt)) = 0 := by
        calc
          πA (δs * ((includeRight : A →ₐ[R] R' ⊗[R] A) φt))
              = πA δs * φt := by
                  simpa [πA] using
                    tensor_split_retraction_mul_includeRight
                    (R := R) (R' := R') (A := A) σ δs φt
          _ = 0 := by simp [hπδs]
      have hπδsδt_zero : πA (δs * δt) = 0 := by
        simpa [hδsδt_zero] using (πA.map_zero : πA 0 = 0)
      have hmainTerm : πA mainTerm = φs * φt := by
        simpa [mainTerm] using hmain
      have hcrossRightTerm : πA crossRightTerm = 0 := by
        simpa [crossRightTerm] using hcross_right
      have hcrossLeftTerm : πA crossLeftTerm = 0 := by
        simpa [crossLeftTerm] using hcross_left
      have herrorTerm : πA errorTerm = 0 := by
        change πA (δs * δt) = 0
        exact hπδsδt_zero
      have hmul_expand :
          xs * xt = (mainTerm + crossRightTerm) + (crossLeftTerm + errorTerm) := by
        calc
          xs * xt =
              ((((includeRight : A →ₐ[R] R' ⊗[R] A) φs) + δs) *
                (((includeRight : A →ₐ[R] R' ⊗[R] A) φt) + δt)) := by
                rw [hxs, hxt]
          _ =
              ((((includeRight : A →ₐ[R] R' ⊗[R] A) φs) + δs) *
                  ((includeRight : A →ₐ[R] R' ⊗[R] A) φt)) +
                ((((includeRight : A →ₐ[R] R' ⊗[R] A) φs) + δs) * δt) := by
                rw [mul_add]
          _ =
              ((((includeRight : A →ₐ[R] R' ⊗[R] A) φs) *
                  ((includeRight : A →ₐ[R] R' ⊗[R] A) φt)) +
                (δs * ((includeRight : A →ₐ[R] R' ⊗[R] A) φt))) +
                ((((includeRight : A →ₐ[R] R' ⊗[R] A) φs) * δt) + δs * δt) := by
                rw [add_mul, add_mul]
          _ = (mainTerm + crossRightTerm) + (crossLeftTerm + errorTerm) := by
                rfl
      have hmul_goal : πA (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) (s * t))) = φs * φt := by
        calc
        πA (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) (s * t)))
            = πA (Φ (((includeRight : S →ₐ[R] R' ⊗[R] S) s) *
                ((includeRight : S →ₐ[R] R' ⊗[R] S) t))) := by
                rw [map_mul]
        _ = πA
              (Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) s) *
                Φ ((includeRight : S →ₐ[R] R' ⊗[R] S) t)) := by
              rw [Φ.map_mul]
        _ = πA (xs * xt) := by
              rfl
        _ = πA ((mainTerm + crossRightTerm) + (crossLeftTerm + errorTerm)) := by
              exact congrArg πA hmul_expand
        _ = (πA mainTerm + πA crossRightTerm) + (πA crossLeftTerm + πA errorTerm) := by
              rw [map_add, map_add, map_add]
        _ = (φs * φt + 0) + (0 + 0) := by
              rw [hmainTerm, hcrossRightTerm, hcrossLeftTerm, herrorTerm]
        _ = φs * φt := by
              simp
      simpa [φFun, φs, φt] using hmul_goal
  let φ : S →+* A :=
    { toFun := φFun
      map_zero' := hφ_zero
      map_one' := hφ_one
      map_add' := hφ_add
      map_mul' := hφ_mul }
  have hπAcont : Continuous πA := continuous_of_discreteTopology
  have hφcont : Continuous φ := hπAcont.comp (hΦcont.comp hincludeRightCont)
  have hφquot_hom : (Ideal.Quotient.mk J).comp φ = ψ := by
    ext s
    change Ideal.Quotient.mk J (φ s) = ψ s
    exact hφquot s
  have hφcomp : φ.comp (algebraMap R S) = g := by
    ext r
    change φ ((algebraMap R S) r) = g r
    exact hφcomp_apply r
  exact ⟨φ, hφcont, hφquot_hom, hφcomp⟩

end

end

end RingHom
