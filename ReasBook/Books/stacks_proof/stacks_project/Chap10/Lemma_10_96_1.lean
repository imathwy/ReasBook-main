import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_82_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {K M N : Type v} [AddCommGroup K] [Module R K]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

-- Domain-style sampling:
-- * primary domain: adic-completion exactness and the tensor comparison with completion.
-- * sampled owner declarations:
--   `AdicCompletion.map_exact`,
--   `AdicCompletion.map_injective`,
--   `AdicCompletion.map_surjective`,
--   `AdicCompletion.ofTensorProduct_surjective_of_finite`.
-- * best owner abstractions:
--   `ShortComplex (ModuleCat (AdicCompletion I R))` built from `AdicCompletion.map I f`,
--   and the completion-linear comparison map `AdicCompletion.ofTensorProduct I M`.
-- * primitive data: these completion-linear maps themselves.
-- * bridge/view data: `restrictScalars R` and `TensorProduct.comm` only translate the owner maps
--   to source-order presentations and should not remain the main public surface.

-- Proof sketch: the hypothesis is exactly surjectivity of the induced map on the quotients
-- `M / IM → N / IN`. Factor the composite `M → N → N / IN` through `M / IM`, deduce the
-- surjectivity of `mkQ ∘ φ`, and then apply
-- `AdicCompletion.map_surjective_of_mkQ_comp_surjective`.
/-- Lemma 10.96.1 (1): if the induced map `M / IM → N / IN` is surjective, then the induced map on
`I`-adic completions `M^∧ → N^∧` is surjective. -/
@[stacks 0315]
theorem completionMap_surjective_of_reduceModIdeal_surjective
    (φ : M →ₗ[R] N) (hφ : Function.Surjective (φ.reduceModIdeal I)) :
    Function.Surjective (AdicCompletion.map I φ) := by
  apply AdicCompletion.map_surjective_of_mkQ_comp_surjective
  intro y
  obtain ⟨x, hx⟩ := hφ y
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • ⊤ : Submodule R M) x
  exact ⟨m, by simpa [LinearMap.reduceModIdeal_apply] using hx⟩

/- Lemma 10.96.1 (2): a surjective map of `R`-modules induces a surjective map on `I`-adic
completions. This is exactly the canonical theorem `AdicCompletion.map_surjective`. -/
recall AdicCompletion.map_surjective

/-- Helper for Lemma 10.96.1: quotienting by an ideal agrees with `reduceModIdeal` after
restricting scalars back to `R`. -/
lemma quotientMapByIdeal_eq_reduceModIdeal_restrictScalars
    {P Q : Type v} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (J : Ideal R) (φ : P →ₗ[R] Q) :
    φ.quotientMapByIdeal J = (φ.reduceModIdeal J).restrictScalars R := by
  -- Both maps are determined by what they do to quotient representatives.
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R P)) x
  rfl

/-- Helper for Lemma 10.96.1: quotient reduction commutes with the tensor-quotient comparison. -/
lemma quotientMapByIdeal_lTensor_naturality
    {P Q : Type v} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (J : Ideal R) (φ : P →ₗ[R] Q) :
    φ.quotientMapByIdeal J ∘ₗ TensorProduct.quotTensorEquivQuotSMul P J =
      TensorProduct.quotTensorEquivQuotSMul Q J ∘ₗ φ.lTensor (R ⧸ J) := by
  -- Check the ladder on pure tensors and extend by tensor-product extensionality.
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

/-- Helper for Lemma 10.96.1: injectivity transfers across a commutative ladder of linear
equivalences. -/
lemma injective_of_ladder_linearEquiv
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    {φ : A →ₗ[R] B} {ψ : A' →ₗ[R] B'} {e₁ : A ≃ₗ[R] A'} {e₂ : B ≃ₗ[R] B'}
    (h : ψ ∘ₗ e₁ = e₂ ∘ₗ φ) (hφ : Function.Injective φ) :
    Function.Injective ψ := by
  -- Pull equality back through the equivalences and use injectivity of the known map.
  intro x y hxy
  apply e₁.symm.injective
  apply hφ
  apply e₂.injective
  calc
    e₂ (φ (e₁.symm x)) = ψ x := by
      simpa using (LinearMap.congr_fun h (e₁.symm x)).symm
    _ = ψ y := hxy
    _ = e₂ (φ (e₁.symm y)) := by
      simpa using LinearMap.congr_fun h (e₁.symm y)

/-- Helper for Lemma 10.96.1: flatness of the cokernel makes the quotient map induced by the left
term injective modulo any ideal. -/
lemma quotientMapByIdeal_injective_of_exact_of_flat
    {P Q T : Type v}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T] [Module.Flat R T]
    (J : Ideal R) (φ : P →ₗ[R] Q) (ψ : Q →ₗ[R] T)
    (hφ : Function.Injective φ) (hψ : Function.Surjective ψ) (hExact : Function.Exact φ ψ) :
    Function.Injective (φ.quotientMapByIdeal J) := by
  -- Tensor exactness with `R / J` gives injectivity on the tensor side.
  have hTensorInj : Function.Injective (φ.lTensor (R ⧸ J)) := by
    simpa [LinearMap.lTensor_inj_iff_rTensor_inj] using
      LinearMap.lTensor_injective_of_exact_of_flat ψ hψ φ hφ hExact (R ⧸ J)
  -- The quotient-tensor equivalence transports that injectivity back to quotient modules.
  exact injective_of_ladder_linearEquiv (R := R)
    (quotientMapByIdeal_lTensor_naturality (R := R) J φ) hTensorInj

/-- Helper for Lemma 10.96.1: exactness survives reduction modulo an ideal when the right map is
surjective. -/
lemma quotientMapByIdeal_exact_of_exact_surjective
    {P Q T : Type v}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T]
    (J : Ideal R) (φ : P →ₗ[R] Q) (ψ : Q →ₗ[R] T)
    (hExact : Function.Exact φ ψ) (hψ : Function.Surjective ψ) :
    Function.Exact (φ.quotientMapByIdeal J) (ψ.quotientMapByIdeal J) := by
  -- Descend exactness through the quotient API and identify the image condition by surjectivity.
  refine
    (Function.Exact.exact_mapQ_iff (f := φ) (g := ψ) hExact
      (Submodule.smul_top_le_comap_smul_top J φ)
      (Submodule.smul_top_le_comap_smul_top J ψ)).2 ?_
  simpa [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hψ]

/-- Helper for Lemma 10.96.1: if every quotient map induced by `φ` is injective, then the map on
`I`-adic completions is injective. -/
lemma completionMap_injective_of_stagewise_injective
    (φ : K →ₗ[R] M)
    (hstageInj :
      ∀ n : ℕ, Function.Injective (((φ.reduceModIdeal (I ^ n)).restrictScalars R))) :
    Function.Injective (AdicCompletion.map I φ) := by
  -- Equality in the completion is detected on every quotient stage.
  intro x y hxy
  ext n
  apply hstageInj n
  simpa [AdicCompletion.map_val_apply] using congrArg (fun z ↦ z.val n) hxy

/-- Helper for Lemma 10.96.1: stagewise exactness and injectivity on the quotient inverse system
lift to exactness on the completed maps. -/
lemma completionMap_exact_of_stagewise_exact
    {φ : K →ₗ[R] M} {ψ : M →ₗ[R] N}
    (hcomp : ψ ∘ₗ φ = 0)
    (hstageExact :
      ∀ n : ℕ,
        Function.Exact (((φ.reduceModIdeal (I ^ n)).restrictScalars R))
          (((ψ.reduceModIdeal (I ^ n)).restrictScalars R)))
    (hstageInj :
      ∀ n : ℕ, Function.Injective (((φ.reduceModIdeal (I ^ n)).restrictScalars R))) :
    Function.Exact (AdicCompletion.map I φ) (AdicCompletion.map I ψ) := by
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
  · -- The completed maps compose to zero because the original maps do.
    rw [AdicCompletion.map_comp, hcomp, AdicCompletion.map_zero]
  · -- Construct a compatible family of stagewise preimages inside the completion.
    intro y hy
    have hyZero : AdicCompletion.map I ψ y = 0 := by
      simpa [LinearMap.mem_ker] using hy
    let x :
        ∀ n : ℕ,
          { z : K ⧸ (I ^ n • (⊤ : Submodule R K)) //
              ((φ.reduceModIdeal (I ^ n)).restrictScalars R) z = y.val n } :=
      fun n ↦ by
        have hyStage :
            ((ψ.reduceModIdeal (I ^ n)).restrictScalars R) (y.val n) = 0 := by
          simpa [AdicCompletion.map_val_apply] using congrArg (fun z ↦ z.val n) hyZero
        classical
        have hyRange :
            y.val n ∈ Set.range (((φ.reduceModIdeal (I ^ n)).restrictScalars R)) :=
          (hstageExact n (y.val n)).mp hyStage
        exact ⟨Classical.choose hyRange, Classical.choose_spec hyRange⟩
    refine ⟨⟨fun n ↦ (x n).1, ?_⟩, ?_⟩
    · -- Injectivity of the reduced left maps forces the chosen preimages to be compatible.
      intro m n hmn
      apply hstageInj m
      calc
        ((φ.reduceModIdeal (I ^ m)).restrictScalars R)
            (AdicCompletion.transitionMap I K hmn (x n).1)
          = AdicCompletion.transitionMap I M hmn
              (((φ.reduceModIdeal (I ^ n)).restrictScalars R) (x n).1) := by
              simpa [LinearMap.comp_apply] using
                LinearMap.congr_fun
                  (AdicCompletion.transitionMap_comp_reduceModIdeal
                    (I := I) (f := φ) hmn)
                  (x n).1 |>.symm
        _ = AdicCompletion.transitionMap I M hmn (y.val n) := by
              rw [(x n).2]
        _ = y.val m := by
              simpa using y.property hmn
        _ = ((φ.reduceModIdeal (I ^ m)).restrictScalars R) (x m).1 := by
              rw [(x m).2]
    · -- Stagewise equality gives equality in the completion.
      ext n
      simpa [AdicCompletion.map_val_apply] using (x n).2

-- Proof sketch: for every `n`, flatness of `N` makes the reduced sequence
-- `0 → K / I^n K → M / I^n M → N / I^n N → 0` short exact by tensoring with `R / I^n`. The
-- transition maps on the left system are surjective, so Lemma `10.87.1` applies to these inverse
-- systems and yields short exactness after passing to the inverse limit, i.e. after completion.
/-- Lemma 10.96.1 (3): if `0 → K → M → N → 0` is a short exact sequence of `R`-modules and `N` is
flat, then the induced sequence `0 → K^∧ → M^∧ → N^∧ → 0` is short exact. -/
@[stacks 0315]
theorem completionShortComplex_shortExact_of_flat_cokernel
    {f : K →ₗ[R] M} {g : M →ₗ[R] N}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    [Module.Flat R N] :
    (ShortComplex.moduleCatMk
      (AdicCompletion.map I f)
      (AdicCompletion.map I g)
      (by
        rw [AdicCompletion.map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero])).ShortExact :=
    by
  -- Work stagewise on the inverse system `X / I^n X`: flatness makes the left maps injective
  -- modulo every `I^n`, and exactness survives the quotient. The compatible-family model of
  -- `AdicCompletion` then lets us assemble a preimage in the completion directly.
  have hzero : AdicCompletion.map I g ∘ₗ AdicCompletion.map I f = 0 := by
    rw [AdicCompletion.map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
  let S : ShortComplex (ModuleCat (AdicCompletion I R)) :=
    ShortComplex.moduleCatMk (AdicCompletion.map I f) (AdicCompletion.map I g) hzero
  have hstageInj :
      ∀ n : ℕ, Function.Injective (((f.reduceModIdeal (I ^ n)).restrictScalars R)) := by
    intro n
    have hquot :
        Function.Injective (f.quotientMapByIdeal (I ^ n)) :=
      quotientMapByIdeal_injective_of_exact_of_flat (R := R) (J := I ^ n) f g hf hg hfg
    simpa [quotientMapByIdeal_eq_reduceModIdeal_restrictScalars (R := R) (J := I ^ n) f] using hquot
  have hstageExact :
      ∀ n : ℕ,
        Function.Exact (((f.reduceModIdeal (I ^ n)).restrictScalars R))
          (((g.reduceModIdeal (I ^ n)).restrictScalars R)) := by
    intro n
    have hquot :
        Function.Exact (f.quotientMapByIdeal (I ^ n)) (g.quotientMapByIdeal (I ^ n)) :=
      quotientMapByIdeal_exact_of_exact_surjective (R := R) (J := I ^ n) f g hfg hg
    simpa [quotientMapByIdeal_eq_reduceModIdeal_restrictScalars (R := R) (J := I ^ n) f,
      quotientMapByIdeal_eq_reduceModIdeal_restrictScalars (R := R) (J := I ^ n) g] using hquot
  have hExactCompletion : Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) :=
    completionMap_exact_of_stagewise_exact (I := I) hfg.linearMap_comp_eq_zero hstageExact hstageInj
  have hInjCompletion : Function.Injective (AdicCompletion.map I f) :=
    completionMap_injective_of_stagewise_injective (I := I) f hstageInj
  have hSurjCompletion : Function.Surjective (AdicCompletion.map I g) :=
    AdicCompletion.map_surjective I hg
  simpa [S] using ModuleCat.shortComplex_shortExact S
    hExactCompletion hInjCompletion hSurjCompletion

-- Proof sketch: choose a finite free surjection onto `M`, use the canonical theorem
-- `AdicCompletion.map_surjective` to obtain a surjection on completions, and compare this
-- completed free module with the tensor product
-- `M ⊗[R] AdicCompletion I R`. This is the standard argument packaged in
-- `AdicCompletion.ofTensorProduct_surjective_of_finite`.
/-
Lemma 10.96.1 (4): the canonical completion-linear comparison map
`AdicCompletion I R ⊗[R] M → M^∧` is surjective for finite `M`. This is exactly the owner theorem
`AdicCompletion.ofTensorProduct_surjective_of_finite`.
-/
recall AdicCompletion.ofTensorProduct_surjective_of_finite

/-- Companion bridge: the same surjectivity result written with the source-order tensor product
`M ⊗[R] R^∧`, obtained from `AdicCompletion.ofTensorProduct I M` via `TensorProduct.comm`. -/
theorem tensorCompletionToCompletion_surjective_of_finite [Module.Finite R M] :
    Function.Surjective
      ((((AdicCompletion.ofTensorProduct I M).restrictScalars R).comp
        (TensorProduct.comm R M (AdicCompletion I R)).toLinearMap) :
        TensorProduct R M (AdicCompletion I R) →ₗ[R] AdicCompletion I M) := by
  intro y
  obtain ⟨x, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  refine ⟨(TensorProduct.comm R M (AdicCompletion I R)).symm x, by simp⟩

end
