import StacksProject_2024.Chap10.Lemma_10_163_1.RegularSequenceDepthDrop

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open RingTheory Sequence Ideal IsLocalRing
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct Pointwise

universe u v w x uA uP

section

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N] [Module.Flat R N]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] N

/-- Helper for Lemma 10.163.1: quotienting the tensor product by a target element agrees with
tensoring the source module against the target quotient. -/
noncomputable def tensor_quotient_by_target_element
    {M' : Type w} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    {N' : Type x} [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] (f : S) :
    QuotSMulTop f (N' ⊗[R] M') ≃ₗ[S] QuotSMulTop f N' ⊗[R] M' := by
  let e₀ :
      ((S ⊗[R] M') ⊗[S] N') ≃ₗ[S] (N' ⊗[R] M') :=
    (TensorProduct.comm S (S ⊗[R] M') N').trans <|
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N' M'
  let e₁ :
      QuotSMulTop f (N' ⊗[R] M') ≃ₗ[S]
        QuotSMulTop f ((S ⊗[R] M') ⊗[S] N') :=
    QuotSMulTop.congr f e₀.symm
  let e₂ :
      QuotSMulTop f ((S ⊗[R] M') ⊗[S] N') ≃ₗ[S]
        QuotSMulTop f (N' ⊗[S] (S ⊗[R] M')) :=
    QuotSMulTop.congr f (TensorProduct.comm S (S ⊗[R] M') N')
  let e₃ :
      QuotSMulTop f (N' ⊗[S] (S ⊗[R] M')) ≃ₗ[S]
        QuotSMulTop f N' ⊗[S] (S ⊗[R] M') :=
    (QuotSMulTop.quotSMulTopTensorEquivQuotSMulTop
      (r := f) (M' := N') (M := S ⊗[R] M')).symm
  let e₄ :
      QuotSMulTop f N' ⊗[S] (S ⊗[R] M') ≃ₗ[S]
        QuotSMulTop f N' ⊗[R] M' :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (QuotSMulTop f N') M'
  -- Proof comment: commute the tensor factors until the quotientable `N'` sits on the left,
  -- push the quotient through that factor, and then cancel the auxiliary base change again.
  exact e₁.trans (e₂.trans (e₃.trans e₄))

/-- Helper for Lemma 10.163.1: if `f` is regular on `N` and `N / fN` stays flat over `R`, then
`f` is also regular on `N ⊗[R] M`. -/
lemma target_regular_on_tensor
    {M' : Type w} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    {N' : Type x} [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] {f : S}
    (hreg : IsSMulRegular N' f) (hflat : Module.Flat R (QuotSMulTop f N')) :
    IsSMulRegular (N' ⊗[R] M') f := by
  let u : N' →ₗ[R] N' := (LinearMap.lsmul S N' f).restrictScalars R
  have hu : Function.Injective u := by
    -- Proof comment: forgetting from `S`-linearity to `R`-linearity does not change the
    -- underlying multiplication map, so regularity of `f` on `N'` is exactly injectivity of `u`.
    intro x y hxy
    apply hreg
    simpa [u] using hxy
  have hrange :
      LinearMap.range (LinearMap.lsmul S N' f) = f • (⊤ : Submodule S N') := by
    -- Proof comment: the image of multiplication by `f` is definitionally the pointwise
    -- `f`-multiple of the top submodule.
    ext n
    constructor
    · rintro ⟨m, rfl⟩
      exact Submodule.smul_mem_pointwise_smul m f (⊤ : Submodule S N') trivial
    · intro hn
      rcases (Submodule.mem_smul_pointwise_iff_exists n f (⊤ : Submodule S N')).1 hn with
        ⟨m, -, hm⟩
      exact ⟨m, by simpa [LinearMap.lsmul_apply] using hm⟩
  have hflat_range : Module.Flat R (N' ⧸ LinearMap.range u) := by
    -- Proof comment: identify the range of the restricted multiplication map with `fN'`, then
    -- rewrite the assumed flat quotient `QuotSMulTop f N'`.
    have hflat_smul :
        Module.Flat R (N' ⧸ (f • (⊤ : Submodule S N')).restrictScalars R) := by
      simpa [QuotSMulTop] using hflat
    rw [LinearMap.range_restrictScalars, hrange]
    exact hflat_smul
  have hu_tensor : Function.Injective (u.lTensor M') :=
    LinearMap.lTensor_injective_of_exact_of_flat
      (Submodule.mkQ (LinearMap.range u))
      (Submodule.mkQ_surjective _)
      u
      hu
      (LinearMap.exact_map_mkQ_range u)
      M'
  have hu_rTensor : Function.Injective (u.rTensor M') := by
    -- Proof comment: the left- and right-tensor injectivity criteria are equivalent.
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    exact hu_tensor
  have hu_rTensor_eq :
      u.rTensor M' = (LinearMap.lsmul S (N' ⊗[R] M') f).restrictScalars R := by
    -- Proof comment: both `R`-linear endomorphisms send a pure tensor `n ⊗ m` to
    -- `(f • n) ⊗ m`, so extensionality on pure tensors identifies them.
    ext n m
    simp [u, TensorProduct.smul_tmul']
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro z hz
  apply hu_rTensor
  -- Proof comment: rewrite the tensorized multiplication map as scalar multiplication by `f` on
  -- `N' ⊗[R] M'`, then feed the assumed vanishing into injectivity.
  simpa [hu_rTensor_eq] using hz

/-- Helper for Lemma 10.163.1: quotienting the target module by a closed-fiber regular element
lowers the closed-fiber depth by one. -/
lemma closed_fiber_depth_after_target_quotient
    {N' : Type x} [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] [Module.Flat R N'] {f : S}
    (hf : f ∈ maximalIdeal S)
    (hreg : IsSMulRegular (ClosedFiber ⊗[S] N') (algebraMap S ClosedFiber f)) :
    moduleDepth ClosedFiber (ClosedFiber ⊗[S] QuotSMulTop f N') =
      moduleDepth ClosedFiber (ClosedFiber ⊗[S] N') - 1 := by
  letI : IsLocalHom (algebraMap S ClosedFiber) :=
    IsLocalHom.of_surjective (algebraMap S ClosedFiber)
      (closedFiber_algebraMap_surjective (R := R) (S := S))
  have hf_closed : algebraMap S ClosedFiber f ∈ maximalIdeal ClosedFiber := by
    refine (IsLocalRing.mem_maximalIdeal _).2 <| mem_nonunits_iff.mpr ?_
    have hf_nonunit : ¬ IsUnit f :=
      mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal f).1 hf)
    intro hf_unit
    exact hf_nonunit <| IsLocalHom.map_nonunit (f := algebraMap S ClosedFiber) f hf_unit
  let e :
      QuotSMulTop (algebraMap S ClosedFiber f) (ClosedFiber ⊗[S] N') ≃ₗ[ClosedFiber]
        ClosedFiber ⊗[S] QuotSMulTop f N' :=
    QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop
      (R := S) (r := f) (M := N') ClosedFiber
  have hdrop :
      moduleDepth ClosedFiber
          (QuotSMulTop (algebraMap S ClosedFiber f) (ClosedFiber ⊗[S] N')) =
        moduleDepth ClosedFiber (ClosedFiber ⊗[S] N') - 1 := by
    -- Proof comment: the split-universe depth-drop theorem now applies directly over the closed
    -- fiber ring, because the lifted target element is regular on the closed-fiber module.
    exact
      moduleDepth_quotSMulTop_eq_sub_one_univ
        (A := ClosedFiber) (P := ClosedFiber ⊗[S] N') hreg hf_closed
  -- Proof comment: transport the quotient-depth drop across the canonical tensor/quotient
  -- comparison for the base change `S → ClosedFiber`.
  simpa [moduleDepth_eq_of_linearEquiv (A := ClosedFiber) (e := e)] using hdrop


end
