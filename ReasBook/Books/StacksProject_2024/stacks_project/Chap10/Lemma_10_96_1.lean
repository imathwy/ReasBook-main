import Mathlib
import Mathlib.Tactic.Recall

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

-- Proof sketch: for every `n`, flatness of `N` makes the reduced sequence
-- `0 → K / I^n K → M / I^n M → N / I^n N → 0` short exact by tensoring with `R / I^n`. The
-- transition maps on the left system are surjective, so Lemma `10.87.1` applies to these inverse
-- systems and yields short exactness after passing to the inverse limit, i.e. after completion.
/-- Lemma 10.96.1 (3): if `0 → K → M → N → 0` is a short exact sequence of `R`-modules and `N` is
flat, then the induced sequence `0 → K^∧ → M^∧ → N^∧ → 0` is short exact. -/
theorem completionShortComplex_shortExact_of_flat_cokernel
    {f : K →ₗ[R] M} {g : M →ₗ[R] N}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    [Module.Flat R N] :
    (ShortComplex.moduleCatMk
      (AdicCompletion.map I f)
      (AdicCompletion.map I g)
      (by
        rw [AdicCompletion.map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero])).ShortExact :=
  sorry

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
