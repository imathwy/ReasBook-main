import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_119_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_119_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open CategoryTheory
open LinearEquiv
open LinearMap
open scoped TensorProduct
open scoped DeterminantLine

universe u v w

variable {R : Type u} [CommRing R]
variable {M' : Type v} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
  [Module.Projective R M']
variable {M'' : Type w} [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
  [Module.Projective R M'']

/-
Domain-style sampling for Lemma 15.119.5:
- primary domain: determinant lines of finite projective modules and the canonical comparison maps
  attached to short exact sequences, specialized to the split rows for a direct sum;
- sampled owner declarations:
  * `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso`,
  * `determinantTensorIsoOfShortExact`,
  * `determinantTensorIsoOfShortExact_naturality`,
  * `determinantLineMap`,
  * `LinearMap.projectiveDet`;
- best owner abstraction:
  `core/canonical`: `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso`, with the
    presented-row bridge `determinantTensorIsoOfShortExact`;
  `bridge/view`: the symmetry square for the split exact rows
    `0 → M' → M' × M'' → M'' → 0` and `0 → M'' → M'' × M' → M' → 0`;
- primitive data: the finite projective modules `M'` and `M''`;
- derived API: the determinant comparison maps for the two split rows, the determinant-line map of
  `LinearEquiv.prodComm`, the canonical determinant scalar
  `tensorSwitchSign R M' M'' = det(-id_{M' ⊗[R] M''})`, and the tensor symmetry twisted by that
  scalar action.

This file therefore stays at the bridge layer and reuses the determinant-line owners already
introduced in `15.119.2` and `15.119.3`, rather than introducing any parallel split-row wrapper.
-/

section TensorSwitchSign

variable (R) (M') (M'')

/-- The canonical sign scalar `ε = det(-id_{M' ⊗[R] M''}) ∈ R` from the determinant owner
`LinearMap.projectiveDet`. -/
noncomputable def tensorSwitchSign : R :=
  LinearMap.projectiveDet
    (-LinearMap.id : (M' ⊗[R] M'') →ₗ[R] M' ⊗[R] M'')

end TensorSwitchSign

/-- Helper for Lemma 15.119.5: the determinant comparison map for the split row
`0 → M' → M' × M'' → M'' → 0` is given by wedging with the obvious lift along `snd`. -/
theorem split_determinant_tensor_iso_inl_snd_apply
    (x' : det(M')) (x'' : det(M'')) :
    (determinantTensorIsoOfShortExact
        (inl R M' M'')
        (snd R M' M'')
        inl_injective
        snd_surjective
        Function.Exact.inl_snd
        (x' ⊗ₜ[R] x'') : ExteriorAlgebra R (M' × M'')) =
      ExteriorAlgebra.map (inl R M' M'') (x' : ExteriorAlgebra R M') *
        ExteriorAlgebra.map (inr R M' M'') (x'' : ExteriorAlgebra R M'') := by
  -- Use the canonical split lift of `x''` through `snd`.
  simpa using
    (determinantTensorIsoOfShortExact_spec
      (inl R M' M'')
      (snd R M' M'')
      inl_injective
      snd_surjective
      Function.Exact.inl_snd
      x'
      x''
      (ExteriorAlgebra.map (inr R M' M'') (x'' : ExteriorAlgebra R M''))
      (by
        rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
        simp))

/-- Helper for Lemma 15.119.5: the determinant comparison map for the split row
`0 → M'' → M' × M'' → M' → 0` is given by wedging with the obvious lift along `fst`. -/
theorem split_determinant_tensor_iso_inr_fst_apply
    (x'' : det(M'')) (x' : det(M')) :
    (determinantTensorIsoOfShortExact
        (inr R M' M'')
        (fst R M' M'')
        inr_injective
        fst_surjective
        Function.Exact.inr_fst
        (x'' ⊗ₜ[R] x') : ExteriorAlgebra R (M' × M'')) =
      ExteriorAlgebra.map (inr R M' M'') (x'' : ExteriorAlgebra R M'') *
        ExteriorAlgebra.map (inl R M' M'') (x' : ExteriorAlgebra R M') := by
  -- Use the canonical split lift of `x'` through `fst`.
  simpa using
    (determinantTensorIsoOfShortExact_spec
      (inr R M' M'')
      (fst R M' M'')
      inr_injective
      fst_surjective
      Function.Exact.inr_fst
      x''
      x'
      (ExteriorAlgebra.map (inl R M' M'') (x' : ExteriorAlgebra R M'))
      (by
        rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
        simp))

/-- Helper for Lemma 15.119.5: at the owner `.toLinearMap` interface used by the square proof,
the split row `0 → M' → M' × M'' → M'' → 0` still evaluates on a pure tensor by wedging the
obvious lifts along `inl` and `inr`. -/
theorem determinantTensorIsoOfShortExact_toLinearMap_tmul_inl_snd
    (x' : det(M')) (x'' : det(M'')) :
    ((determinantTensorIsoOfShortExact
        (inl R M' M'')
        (snd R M' M'')
        inl_injective
        snd_surjective
        Function.Exact.inl_snd).toLinearMap
        (x' ⊗ₜ[R] x'') : ExteriorAlgebra R (M' × M'')) =
      ExteriorAlgebra.map (inl R M' M'') (x' : ExteriorAlgebra R M') *
        ExteriorAlgebra.map (inr R M' M'') (x'' : ExteriorAlgebra R M'') := by
  -- Proof comment: this is exactly the split wedge formula from
  -- `split_determinant_tensor_iso_inl_snd_apply`, restated at the `.toLinearMap` interface.
  simpa using split_determinant_tensor_iso_inl_snd_apply
    (R := R) (M' := M') (M'' := M'') x' x''

/-- Helper for Lemma 15.119.5: at the owner `.toLinearMap` interface used by the square proof,
the split row `0 → M'' → M' × M'' → M' → 0` still evaluates on a pure tensor by wedging the
obvious lifts along `inr` and `inl`. -/
theorem determinantTensorIsoOfShortExact_toLinearMap_tmul_inr_fst
    (x'' : det(M'')) (x' : det(M')) :
    ((determinantTensorIsoOfShortExact
        (inr R M' M'')
        (fst R M' M'')
        inr_injective
        fst_surjective
        Function.Exact.inr_fst).toLinearMap
        (x'' ⊗ₜ[R] x') : ExteriorAlgebra R (M' × M'')) =
      ExteriorAlgebra.map (inr R M' M'') (x'' : ExteriorAlgebra R M'') *
        ExteriorAlgebra.map (inl R M' M'') (x' : ExteriorAlgebra R M') := by
  -- Proof comment: this is the same owner-level normalization for the swapped split row.
  simpa using split_determinant_tensor_iso_inr_fst_apply
    (R := R) (M' := M') (M'' := M'') x'' x'

/-- Helper for Lemma 15.119.5: on a finite free module, any split finite free presentation
computes the ordinary determinant of an endomorphism. -/
theorem splitFreePresentation_det_lift_eq_det_of_free
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [Module.Free R M]
    (p : SplitFreePresentation (R := R) (M := M))
    (f : M →ₗ[R] M) :
    LinearMap.det (p.lift f) = LinearMap.det f := by
  let a : M →ₗ[R] Fin p.rank → R := p.iota
  let b : (Fin p.rank → R) →ₗ[R] M := (f - 1) ∘ₗ p.pi
  have hlift : p.lift f = 1 + a ∘ₗ b := by
    -- Proof comment: rewrite the split lift in the standard `1 + ab` form used by
    -- Lemma `15.119.6` on free modules.
    ext x i
    simp [SplitFreePresentation.lift, a, b, LinearMap.comp_apply, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm]
  have hback : 1 + b ∘ₗ a = f := by
    -- Proof comment: the splitting relation `pi ∘ iota = id` collapses the projective correction
    -- term, so the opposite composite is exactly `f`.
    ext x
    simp [a, b, LinearMap.comp_assoc, LinearMap.comp_apply, p.pi_comp_iota, sub_eq_add_neg,
      add_assoc]
  calc
    LinearMap.det (p.lift f) = LinearMap.det (1 + a ∘ₗ b) := by rw [hlift]
    _ = LinearMap.det (1 + b ∘ₗ a) :=
      LinearMap.linearMap_det_id_add_a_comp_b_eq_det_id_add_b_comp_a
        (R := R) (M := M) (N := Fin p.rank → R) a b
    _ = LinearMap.det f := by rw [hback]

/-- Helper for Lemma 15.119.5: on a finite free module, `projectiveDet` agrees with the ordinary
determinant. -/
theorem projectiveDet_eq_det_of_free
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [Module.Free R M]
    (f : M →ₗ[R] M) :
    LinearMap.projectiveDet f = LinearMap.det f := by
  let p : SplitFreePresentation (R := R) (M := M) :=
    LinearMap.splitFreePresentation (R := R) (M := M)
  -- Proof comment: `projectiveDet` is defined using the chosen split lift, and the previous lemma
  -- shows that every split presentation computes the usual determinant in the free case.
  simpa [LinearMap.projectiveDet, p] using
    (splitFreePresentation_det_lift_eq_det_of_free (R := R) (p := p) f)

/-- Helper for Lemma 15.119.5: the explicit free tensor-model endomorphism whose determinant
computes the switch sign. -/
noncomputable abbrev tensor_split_model_endomorphism :=
  let p' : SplitFreePresentation (R := R) (M := M') :=
    LinearMap.splitFreePresentation (R := R) (M := M')
  let p'' : SplitFreePresentation (R := R) (M := M'') :=
    LinearMap.splitFreePresentation (R := R) (M := M'')
  let a : (M' ⊗[R] M'') →ₗ[R]
      ((Fin p'.rank → R) ⊗[R] (Fin p''.rank → R)) :=
    TensorProduct.map p'.iota p''.iota
  let b : ((Fin p'.rank → R) ⊗[R] (Fin p''.rank → R)) →ₗ[R]
      (M' ⊗[R] M'') :=
    (- (2 : R)) • TensorProduct.map p'.pi p''.pi
  1 + a ∘ₗ b

/-- Helper for Lemma 15.119.5: the scalar `tensorSwitchSign` is the determinant of the concrete
split-free tensor model obtained from the chosen split presentations of `M'` and `M''`. -/
theorem tensorSwitchSign_eq_det_tensor_split_model :
    tensorSwitchSign R M' M'' =
      LinearMap.det (tensor_split_model_endomorphism (R := R) (M' := M') (M'' := M'')) := by
  let p' : SplitFreePresentation (R := R) (M := M') :=
    LinearMap.splitFreePresentation (R := R) (M := M')
  let p'' : SplitFreePresentation (R := R) (M := M'') :=
    LinearMap.splitFreePresentation (R := R) (M := M'')
  let a : (M' ⊗[R] M'') →ₗ[R]
      ((Fin p'.rank → R) ⊗[R] (Fin p''.rank → R)) :=
    TensorProduct.map p'.iota p''.iota
  let b : ((Fin p'.rank → R) ⊗[R] (Fin p''.rank → R)) →ₗ[R]
      (M' ⊗[R] M'') :=
    (- (2 : R)) • TensorProduct.map p'.pi p''.pi
  have hneg : 1 + b ∘ₗ a = (-LinearMap.id : (M' ⊗[R] M'') →ₗ[R] M' ⊗[R] M'') := by
    -- Proof comment: on pure tensors, `b ∘ a` is `-2` times the identity because both split
    -- presentations retract along `pi ∘ iota = id`.
    ext x y
    have hpi' : p'.pi (p'.iota x) = x := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun f : M' →ₗ[R] M' ↦ f x) p'.pi_comp_iota
    have hpi'' : p''.pi (p''.iota y) = y := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun f : M'' →ₗ[R] M'' ↦ f y) p''.pi_comp_iota
    calc
      ((1 + b ∘ₗ a) (x ⊗ₜ[R] y))
          = (1 : R) • (x ⊗ₜ[R] y) +
              (- (2 : R)) • (p'.pi (p'.iota x) ⊗ₜ[R] p''.pi (p''.iota y)) := by
              simp [a, b, LinearMap.comp_apply, TensorProduct.map_tmul]
      _ = (1 : R) • (x ⊗ₜ[R] y) + (- (2 : R)) • (x ⊗ₜ[R] y) := by
            rw [hpi', hpi'']
      _ = ((1 : R) + (- (2 : R))) • (x ⊗ₜ[R] y) := by
            rw [← add_smul]
      _ = (-1 : R) • (x ⊗ₜ[R] y) := by
            norm_num
      _ = (-LinearMap.id : (M' ⊗[R] M'') →ₗ[R] M' ⊗[R] M'') (x ⊗ₜ[R] y) := by
            simp
  have hdet :
      LinearMap.projectiveDet (1 + a ∘ₗ b) =
        LinearMap.projectiveDet (1 + b ∘ₗ a) :=
    LinearMap.det_id_add_a_comp_b_eq_det_id_add_b_comp_a
      (R := R) (M := M' ⊗[R] M'')
      (N := (Fin p'.rank → R) ⊗[R] (Fin p''.rank → R)) a b
  -- Proof comment: compare `-id` on the projective tensor product with the explicit free tensor
  -- ambient via Lemma `15.119.6`, then collapse the free-side projective determinant to `det`.
  calc
    tensorSwitchSign R M' M'' =
        LinearMap.projectiveDet (-LinearMap.id :
          (M' ⊗[R] M'') →ₗ[R] M' ⊗[R] M'') := by
      rfl
    _ = LinearMap.projectiveDet (1 + b ∘ₗ a) := by rw [hneg.symm]
    _ = LinearMap.projectiveDet (1 + a ∘ₗ b) := hdet.symm
    _ = LinearMap.det (1 + a ∘ₗ b) :=
      projectiveDet_eq_det_of_free
        (R := R)
        (M := (Fin p'.rank → R) ⊗[R] (Fin p''.rank → R))
        (1 + a ∘ₗ b)
    _ = LinearMap.det (tensor_split_model_endomorphism (R := R) (M' := M') (M'' := M'')) := by
      rfl

/-- Helper for Lemma 15.119.5: the split-row wedge product already lands in the determinant line
of `M' × M''`. -/
theorem split_block_product_mem_det_prod
    (x' : det(M')) (x'' : det(M'')) :
    ExteriorAlgebra.map (inl R M' M'') x'.1 *
        ExteriorAlgebra.map (inr R M' M'') x''.1 ∈ det(M' × M'') := by
  -- Proof comment: rewrite the product as the split determinant comparison map; its codomain is
  -- definitionally the determinant line of `M' × M''`.
  rw [← split_determinant_tensor_iso_inl_snd_apply (R := R) (M' := M') (M'' := M'') x' x'']
  exact
    (determinantTensorIsoOfShortExact
      (inl R M' M'')
      (snd R M' M'')
      inl_injective
      snd_surjective
      Function.Exact.inl_snd
      (x' ⊗ₜ[R] x'')).2

/-- Helper for Lemma 15.119.5: the swapped split-row wedge product also lands in the determinant
line of `M' × M''`. -/
theorem swapped_split_block_product_mem_det_prod
    (x' : det(M')) (x'' : det(M'')) :
    ExteriorAlgebra.map (inr R M' M'') x''.1 *
        ExteriorAlgebra.map (inl R M' M'') x'.1 ∈ det(M' × M'') := by
  -- Proof comment: the same normalization applies to the swapped split row.
  rw [← split_determinant_tensor_iso_inr_fst_apply (R := R) (M' := M') (M'' := M'') x'' x']
  exact
    (determinantTensorIsoOfShortExact
      (inr R M' M'')
      (fst R M' M'')
      inr_injective
      fst_surjective
      Function.Exact.inr_fst
      (x'' ⊗ₜ[R] x')).2

/-- Helper for Lemma 15.119.5: on the same split-free tensor model used to compute
`tensorSwitchSign`, swapping the two determinant blocks contributes the determinant of the model
endomorphism. -/
theorem split_free_block_swap_sign_with_det_scalar
    (x' : det(M')) (x'' : det(M'')) :
    ExteriorAlgebra.map (inl R M' M'') x'.1 *
        ExteriorAlgebra.map (inr R M' M'') x''.1 =
      LinearMap.det (tensor_split_model_endomorphism (R := R) (M' := M') (M'' := M'')) •
        (ExteriorAlgebra.map (inr R M' M'') x''.1 *
          ExteriorAlgebra.map (inl R M' M'') x'.1) := by
  -- TODO: both sides already lie in the same determinant line `det(M' × M'')` by
  -- `split_block_product_mem_det_prod` and `swapped_split_block_product_mem_det_prod`. The
  -- remaining blocker is the source-faithful local free-basis computation inside that line,
  -- identifying the swap scalar with
  -- `LinearMap.det (tensor_split_model_endomorphism ...) = det(-id_{M' ⊗[R] M''})`.
  sorry

/-- Helper for Lemma 15.119.5: swapping the two determinant blocks inside the same exterior
algebra contributes the canonical sign scalar `det(-id_{M' ⊗[R] M''})`. -/
theorem determinant_block_swap_eq_tensorSwitchSign_smul
    (x' : det(M')) (x'' : det(M'')) :
    ExteriorAlgebra.map (inl R M' M'') x'.1 *
        ExteriorAlgebra.map (inr R M' M'') x''.1 =
      (tensorSwitchSign R M' M'') •
        (ExteriorAlgebra.map (inr R M' M'') x''.1 *
          ExteriorAlgebra.map (inl R M' M'') x'.1) := by
  -- Route correction: the previous route tried to identify `projectiveDet (-id)` with a global
  -- determinant-line endomorphism first. The new route computes `tensorSwitchSign` as the
  -- determinant of one explicit split-free tensor model, so only the free Koszul-sign
  -- calculation remains.
  rw [tensorSwitchSign_eq_det_tensor_split_model (R := R) (M' := M') (M'' := M'')]
  simpa using split_free_block_swap_sign_with_det_scalar
    (R := R) (M' := M') (M'' := M'') x' x''

/-- Helper for Lemma 15.119.5: on a pure tensor in `det(M') ⊗ det(M'')`, the two routes around
the same-product square agree after rewriting both determinant comparison maps to their split
wedge formulas and applying the block-swap sign identity. -/
theorem determinant_tensor_iso_same_product_swap_on_tmul
    (x' : det(M')) (x'' : det(M'')) :
    ((determinantTensorIsoOfShortExact
        (inl R M' M'')
        (snd R M' M'')
        inl_injective
        snd_surjective
        Function.Exact.inl_snd).toLinearMap
        (x' ⊗ₜ[R] x'') : ExteriorAlgebra R (M' × M'')) =
      ((determinantTensorIsoOfShortExact
          (inr R M' M'')
          (fst R M' M'')
          inr_injective
          fst_surjective
          Function.Exact.inr_fst).toLinearMap
          (((TensorProduct.comm R (det(M')) (det(M''))).toLinearMap.comp
            (Module.toModuleEnd R (det(M') ⊗[R] det(M'')) (tensorSwitchSign R M' M'')))
            (x' ⊗ₜ[R] x'')) : ExteriorAlgebra R (M' × M'')) := by
  -- Proof comment: normalize the left determinant map, apply the source-faithful block-swap sign
  -- computation, then rewrite the right route as the determinant map on the signed swapped tensor.
  calc
    ((determinantTensorIsoOfShortExact
        (inl R M' M'')
        (snd R M' M'')
        inl_injective
        snd_surjective
        Function.Exact.inl_snd).toLinearMap
        (x' ⊗ₜ[R] x'') : ExteriorAlgebra R (M' × M'')) =
      ExteriorAlgebra.map (inl R M' M'') (x' : ExteriorAlgebra R M') *
        ExteriorAlgebra.map (inr R M' M'') (x'' : ExteriorAlgebra R M'') := by
      simpa using determinantTensorIsoOfShortExact_toLinearMap_tmul_inl_snd
        (R := R) (M' := M') (M'' := M'') x' x''
    _ = (tensorSwitchSign R M' M'') •
        (ExteriorAlgebra.map (inr R M' M'') (x'' : ExteriorAlgebra R M'') *
          ExteriorAlgebra.map (inl R M' M'') (x' : ExteriorAlgebra R M')) := by
      simpa using determinant_block_swap_eq_tensorSwitchSign_smul
        (R := R) (M' := M') (M'' := M'') x' x''
    _ = (tensorSwitchSign R M' M'') •
        (((determinantTensorIsoOfShortExact
            (inr R M' M'')
            (fst R M' M'')
            inr_injective
            fst_surjective
            Function.Exact.inr_fst).toLinearMap
            (x'' ⊗ₜ[R] x')) : ExteriorAlgebra R (M' × M'')) := by
      simpa using congrArg
        (fun z : ExteriorAlgebra R (M' × M'') ↦ (tensorSwitchSign R M' M'') • z)
        (determinantTensorIsoOfShortExact_toLinearMap_tmul_inr_fst
          (R := R) (M' := M') (M'' := M'') x'' x').symm
    _ = ((determinantTensorIsoOfShortExact
          (inr R M' M'')
          (fst R M' M'')
          inr_injective
          fst_surjective
          Function.Exact.inr_fst).toLinearMap
          ((tensorSwitchSign R M' M'') • (x'' ⊗ₜ[R] x')) :
          ExteriorAlgebra R (M' × M'')) := by
      rw [LinearMap.map_smul]
      rfl
    _ = ((determinantTensorIsoOfShortExact
          (inr R M' M'')
          (fst R M' M'')
          inr_injective
          fst_surjective
          Function.Exact.inr_fst).toLinearMap
          (((TensorProduct.comm R (det(M')) (det(M''))).toLinearMap.comp
            (Module.toModuleEnd R (det(M') ⊗[R] det(M'')) (tensorSwitchSign R M' M'')))
            (x' ⊗ₜ[R] x'')) :
          ExteriorAlgebra R (M' × M'')) := by
      simp [LinearMap.comp_apply, TensorProduct.comm_tmul]

/-- Helper for Lemma 15.119.5: inside the fixed product `M' × M''`, the two split determinant
comparison maps differ only by the signed tensor switch. -/
theorem same_product_square_composite_on_tmul
    (x' : det(M')) (x'' : det(M'')) :
    ((((LinearEquiv.refl R (det(M' × M''))).toLinearMap).comp
        ((determinantTensorIsoOfShortExact
          (inl R M' M'')
          (snd R M' M'')
          inl_injective
          snd_surjective
          Function.Exact.inl_snd).toLinearMap))
        (x' ⊗ₜ[R] x'') : ExteriorAlgebra R (M' × M'')) =
      ((((determinantTensorIsoOfShortExact
          (inr R M' M'')
          (fst R M' M'')
          inr_injective
          fst_surjective
          Function.Exact.inr_fst).toLinearMap).comp
          (((TensorProduct.comm R (det(M')) (det(M''))).toLinearMap).comp
            (Module.toModuleEnd R (det(M') ⊗[R] det(M'')) (tensorSwitchSign R M' M''))))
        (x' ⊗ₜ[R] x'') : ExteriorAlgebra R (M' × M'')) := by
  -- Proof comment: restate the pure-tensor comparison at the exact composite shape used by the
  -- `CommSq` proof so later tensor induction sees only ordinary linear-map composition.
  simpa [LinearMap.comp_apply] using
    determinant_tensor_iso_same_product_swap_on_tmul
      (R := R) (M' := M') (M'' := M'') x' x''

/-- Helper for Lemma 15.119.5: inside the fixed product `M' × M''`, the two split determinant
comparison maps differ only by the signed tensor switch. -/
theorem determinant_tensor_iso_same_product_swap_commutes :
    CommSq
      (ModuleCat.ofHom <|
        (determinantTensorIsoOfShortExact
          (inl R M' M'')
          (snd R M' M'')
          inl_injective
          snd_surjective
          Function.Exact.inl_snd).toLinearMap)
      (ModuleCat.ofHom <|
        (TensorProduct.comm R (det(M')) (det(M''))).toLinearMap.comp
          (Module.toModuleEnd R (det(M') ⊗[R] det(M'')) (tensorSwitchSign R M' M'')))
      (ModuleCat.ofHom <| (LinearEquiv.refl R (det(M' × M''))).toLinearMap)
      (ModuleCat.ofHom <|
        (determinantTensorIsoOfShortExact
          (inr R M' M'')
          (fst R M' M'')
          inr_injective
          fst_surjective
          Function.Exact.inr_fst).toLinearMap) := by
  -- Proof comment: the square is already normalized on pure tensors, and `TensorProduct.ext`
  -- upgrades that normalization to equality of the underlying linear maps.
  refine CommSq.mk ?_
  ext x' x''
  simpa [LinearMap.comp_apply] using
    same_product_square_composite_on_tmul
      (R := R) (M' := M') (M'' := M'') x' x''

/-- Helper for Lemma 15.119.5: on a pure tensor in `det(M'') ⊗ det(M')`, transporting the split
row across `prodComm` agrees with the split determinant comparison map for the swapped product. -/
theorem split_row_prodComm_naturality_on_tmul
    (x'' : det(M'')) (x' : det(M')) :
    (((determinantLineMap (prodComm R M' M'')).toLinearMap).comp
      ((determinantTensorIsoOfShortExact
          (inr R M' M'')
          (fst R M' M'')
          inr_injective
          fst_surjective
          Function.Exact.inr_fst).toLinearMap)
        (x'' ⊗ₜ[R] x') : ExteriorAlgebra R (M'' × M')) =
      ((determinantTensorIsoOfShortExact
          (inl R M'' M')
          (snd R M'' M')
          inl_injective
          snd_surjective
          Function.Exact.inl_snd).toLinearMap
        (x'' ⊗ₜ[R] x') : ExteriorAlgebra R (M'' × M')) := by
  have h_inr :
      (prodComm R M' M'').toLinearMap.comp (inr R M' M'') = inl R M'' M' := by
    -- Proof comment: `prodComm` sends the right summand of `M' × M''` to the left summand of
    -- `M'' × M'`.
    ext x <;> rfl
  have h_inl :
      (prodComm R M' M'').toLinearMap.comp (inl R M' M'') = inr R M'' M' := by
    -- Proof comment: `prodComm` sends the left summand of `M' × M''` to the right summand of
    -- `M'' × M'`.
    ext x <;> rfl
  -- Proof comment: rewrite the left route by functoriality of `ExteriorAlgebra.map`, then the
  -- result is exactly the split wedge formula for the swapped product.
  change
    (ExteriorAlgebra.map (prodComm R M' M'').toLinearMap
        (((determinantTensorIsoOfShortExact
            (inr R M' M'')
            (fst R M' M'')
            inr_injective
            fst_surjective
            Function.Exact.inr_fst).toLinearMap
            (x'' ⊗ₜ[R] x')) : ExteriorAlgebra R (M' × M'')) :
        ExteriorAlgebra R (M'' × M')) =
      ((determinantTensorIsoOfShortExact
          (inl R M'' M')
          (snd R M'' M')
          inl_injective
          snd_surjective
          Function.Exact.inl_snd).toLinearMap
        (x'' ⊗ₜ[R] x') : ExteriorAlgebra R (M'' × M'))
  rw [determinantTensorIsoOfShortExact_toLinearMap_tmul_inr_fst]
  rw [map_mul]
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  rw [h_inr, h_inl]
  rw [determinantTensorIsoOfShortExact_toLinearMap_tmul_inl_snd
    (R := R) (M' := M'') (M'' := M') x'' x']

/-- Helper for Lemma 15.119.5: the naturality square from Lemma `15.119.3` for the split row
`0 → M'' → M' × M'' → M' → 0` and the product-swap equivalence. -/
theorem prodComm_square_composite_on_tmul
    (x'' : det(M'')) (x' : det(M')) :
    ((((determinantLineMap (prodComm R M' M'')).toLinearMap).comp
        ((determinantTensorIsoOfShortExact
          (inr R M' M'')
          (fst R M' M'')
          inr_injective
          fst_surjective
          Function.Exact.inr_fst).toLinearMap))
        (x'' ⊗ₜ[R] x') : ExteriorAlgebra R (M'' × M')) =
      ((((determinantTensorIsoOfShortExact
          (inl R M'' M')
          (snd R M'' M')
          inl_injective
          snd_surjective
          Function.Exact.inl_snd).toLinearMap).comp
          ((LinearEquiv.refl R (det(M'') ⊗[R] det(M'))).toLinearMap))
        (x'' ⊗ₜ[R] x') : ExteriorAlgebra R (M'' × M')) := by
  -- Proof comment: freeze the naturality comparison in the same explicit composite normal form
  -- needed by the final square proof.
  simpa [LinearMap.comp_apply] using
    split_row_prodComm_naturality_on_tmul
      (R := R) (M' := M') (M'' := M'') x'' x'

/-- Helper for Lemma 15.119.5: the naturality square from Lemma `15.119.3` for the split row
`0 → M'' → M' × M'' → M' → 0` and the product-swap equivalence. -/
theorem split_row_prodComm_naturality :
    CommSq
      (ModuleCat.ofHom <|
        (determinantTensorIsoOfShortExact
          (inr R M' M'')
          (fst R M' M'')
          inr_injective
          fst_surjective
          Function.Exact.inr_fst).toLinearMap)
      (ModuleCat.ofHom <| (LinearEquiv.refl R (det(M'') ⊗[R] det(M'))).toLinearMap)
      (ModuleCat.ofHom <| (determinantLineMap (prodComm R M' M'')).toLinearMap)
      (ModuleCat.ofHom <|
        (determinantTensorIsoOfShortExact
          (inl R M'' M')
          (snd R M'' M')
          inl_injective
          snd_surjective
          Function.Exact.inl_snd).toLinearMap) := by
  -- Proof comment: the naturality square is already explicit on pure tensors, so the
  -- tensor-product extensionality principle packages it into the owner `CommSq`.
  refine CommSq.mk ?_
  ext x'' x'
  simpa [LinearMap.comp_apply] using
    prodComm_square_composite_on_tmul
      (R := R) (M' := M') (M'' := M'') x'' x'

/-- Lemma 15.119.5: for the split short exact sequences
`0 → M' → M' × M'' → M'' → 0` and `0 → M'' → M'' × M' → M' → 0`, the determinant-line
comparison maps from Lemma `15.119.2` are intertwined by switching the summands, up to the sign
scalar `tensorSwitchSign R M' M'' = det(-id_{M' ⊗[R] M''})` by which `-1` acts on the determinant
line of `M' ⊗[R] M''`. -/
theorem determinant_tensor_iso_switch_summands_commutes
    : CommSq
        (ModuleCat.ofHom <|
          (determinantTensorIsoOfShortExact
            (inl R M' M'')
            (snd R M' M'')
            inl_injective
            snd_surjective
            Function.Exact.inl_snd).toLinearMap)
        (ModuleCat.ofHom <|
          (TensorProduct.comm R (det(M')) (det(M''))).toLinearMap.comp
            (Module.toModuleEnd R (det(M') ⊗[R] det(M'')) (tensorSwitchSign R M' M'')))
        (ModuleCat.ofHom <| (determinantLineMap (prodComm R M' M'')).toLinearMap)
        (ModuleCat.ofHom <|
          (determinantTensorIsoOfShortExact
            (inl R M'' M')
            (snd R M'' M')
            inl_injective
            snd_surjective
            Function.Exact.inl_snd).toLinearMap) := by
  -- Compose the same-product sign square with the product-swap transport square.
  simpa using
    CategoryTheory.CommSq.vert_comp
      (determinant_tensor_iso_same_product_swap_commutes
        (R := R) (M' := M') (M'' := M''))
      (split_row_prodComm_naturality (R := R) (M' := M') (M'' := M''))
