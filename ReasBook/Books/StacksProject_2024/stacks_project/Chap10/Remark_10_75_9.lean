import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_75_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

universe u

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

set_option quotPrecheck false in
notation "Tor₁[" R "](" M ", " N ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R N))

/- Domain triage:
- primary domain: the low-degree `Tor₁`/tensor exact sequence for a short exact sequence of
  `R`-modules, specialized to `0 → I → R → R ⧸ I → 0`;
- sampled owner declarations of the same kind:
  `CategoryTheory.Tor`,
  `ModuleCat.torTensorSixTermSequence_exact`,
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`,
  `LinearMap.lid_comp_rTensor`;
- best owner abstraction: the core/canonical owners are `CategoryTheory.Tor (ModuleCat R) 1` for
  the homological term, surfaced below as `Tor₁[R](M, N)`, and the canonical tensor multiplication
  map
  `TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)`;
- primitive data: the ring `R`, the `R`-module `M`, and the ideal `I`;
- derived API: the comparison equivalence identifying the specific `Tor₁` term with the kernel of
  the canonical map.

Source/core/bridge triage:
- `source-facing`: the Stacks remark identifying `Tor₁^R(M, R/I)` with the kernel of
  `I ⊗[R] M → M`;
- `core/canonical`: `CategoryTheory.Tor`, `ModuleCat.torTensorSixTermSequence_exact`,
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`, and `LinearMap.lid_comp_rTensor`;
- `bridge/view`: the comparison equivalence below. This should be exposed directly as the canonical
  object, not wrapped in `Nonempty`.
-/

-- Proof sketch: apply the six-term exact sequence for `0 → I → R → R/I → 0`; after identifying
-- `R ⊗[R] M` with `M` via `TensorProduct.lid`, exactness identifies `Tor₁^R(M, R/I)` with the
-- kernel of the canonical multiplication map `I ⊗[R] M → M`.
/-- Remark 10.75.9: for an ideal `I`, the proof of Lemma 10.75.8 identifies
`Tor₁^R(M, R/I)` with the kernel of the canonical map `I ⊗[R] M → M`. -/
noncomputable def tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (I : Ideal R) :
    Tor₁[R](M, R ⧸ I) ≃ₗ[R]
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)) := by
  let μ : I ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  change Tor₁[R](M, R ⧸ I) ≃ₗ[R] LinearMap.ker μ
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk I.subtype I.mkQ (by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem.2 x.2)
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa using (LinearMap.exact_subtype_mkQ I)
    · exact (ModuleCat.mono_iff_injective _).2 I.injective_subtype
    · exact (ModuleCat.epi_iff_surjective _).2 I.mkQ_surjective
  let T := ModuleCat.torTensorSixTermSequence (ModuleCat.of R M) hS
  have hT : T.Exact := ModuleCat.torTensorSixTermSequence_exact (ModuleCat.of R M) hS
  have hTorR :
      IsZero (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R R)) := by
    simpa using
      CategoryTheory.isZero_Tor_succ_of_projective
        (ModuleCat R) (ModuleCat.of R M) (ModuleCat.of R R) 0
  have hmap12 : T.map' 1 2 = 0 := hTorR.eq_of_src _ _
  have hmono23 : Mono (T.map' 2 3) := by
    have : Mono (T.sc hT.toIsComplex 1).g := (hT.exact 1).mono_g (by simpa using hmap12)
    simpa using this
  have hExact23 : Function.Exact (T.map' 2 3).hom (T.map' 3 4).hom := by
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (T.sc hT.toIsComplex 2)).1
        (hT.exact 2)
  have hmap34' : T.map' 3 4 = MonoidalCategoryStruct.whiskerLeft (ModuleCat.of R M) S.f := by
    dsimp [T]
    unfold ModuleCat.torTensorSixTermSequence ComposableArrows.mk₅ ComposableArrows.mk₄
    rfl
  have hmap34 : (T.map' 3 4).hom = I.subtype.lTensor M := by
    rw [hmap34']
    change ModuleCat.Hom.hom
        (MonoidalCategoryStruct.whiskerLeft (ModuleCat.of R M) (ModuleCat.ofHom I.subtype)) =
      I.subtype.lTensor M
    rw [ModuleCat.hom_whiskerLeft]
    rfl
  have hμ :
      μ.comp (TensorProduct.comm R M I).toLinearMap =
        (TensorProduct.rid R M).toLinearMap.comp (T.map' 3 4).hom := by
    have hcommLid :
        (TensorProduct.lid R M).toLinearMap.comp (TensorProduct.comm R M R).toLinearMap =
          (TensorProduct.rid R M).toLinearMap := by
      exact congrArg LinearEquiv.toLinearMap TensorProduct.comm_trans_lid
    dsimp [μ]
    rw [← LinearMap.lid_comp_rTensor]
    change
      (TensorProduct.lid R M).toLinearMap.comp
          ((I.subtype.rTensor M).comp (TensorProduct.comm R M I).toLinearMap) =
        (TensorProduct.rid R M).toLinearMap.comp (T.map' 3 4).hom
    rw [LinearMap.rTensor_comp_comm]
    change
      (TensorProduct.lid R M).toLinearMap.comp
          ((TensorProduct.comm R M R).toLinearMap.comp (I.subtype.lTensor M)) =
        (TensorProduct.rid R M).toLinearMap.comp (T.map' 3 4).hom
    rw [hmap34, ← LinearMap.comp_assoc, hcommLid]
    rfl
  have hμ_exact :
      Function.Exact
        ((TensorProduct.comm R M I).toLinearMap.comp (T.map' 2 3).hom)
        μ := by
    let e₁ : ↑(T.obj ⟨2, by decide⟩) ≃ₗ[R] ↑(T.obj ⟨2, by decide⟩) := LinearEquiv.refl R _
    let e₂ : ↑(T.obj ⟨3, by decide⟩) ≃ₗ[R] I ⊗[R] M := by
      change M ⊗[R] I ≃ₗ[R] I ⊗[R] M
      exact TensorProduct.comm R M I
    let e₃ : ↑(T.obj ⟨4, by decide⟩) ≃ₗ[R] M := by
      change M ⊗[R] R ≃ₗ[R] M
      exact TensorProduct.rid R M
    have h12 :
        ((TensorProduct.comm R M I).toLinearMap.comp (T.map' 2 3).hom) ∘ₗ e₁.toLinearMap =
          e₂.toLinearMap ∘ₗ (T.map' 2 3).hom := by
      ext x
      rfl
    have h23 :
        μ ∘ₗ e₂.toLinearMap =
          e₃.toLinearMap ∘ₗ (T.map' 3 4).hom := by
      simpa [LinearMap.comp_assoc] using hμ
    exact (Function.Exact.iff_of_ladder_linearEquiv h12 h23).2 hExact23
  have hμ_injective :
      Function.Injective ((TensorProduct.comm R M I).toLinearMap.comp (T.map' 2 3).hom) :=
    (TensorProduct.comm R M I).injective.comp ((ModuleCat.mono_iff_injective _).1 hmono23)
  let hker :
      IsLimit
        (KernelFork.ofι
          (ModuleCat.ofHom ((TensorProduct.comm R M I).toLinearMap.comp (T.map' 2 3).hom))
          (ModuleCat.hom_ext hμ_exact.linearMap_comp_eq_zero)) :=
    ModuleCat.isLimitKernelFork
      (ModuleCat.ofHom ((TensorProduct.comm R M I).toLinearMap.comp (T.map' 2 3).hom))
      (ModuleCat.ofHom μ)
      hμ_exact hμ_injective
  exact
    (((limit.isoLimitCone ⟨_, hker⟩).symm ≪≫
      ModuleCat.kernelIsoKer (ModuleCat.ofHom μ)).toLinearEquiv)

end
