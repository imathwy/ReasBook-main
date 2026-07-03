import Mathlib
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_96_1 (from Chap10) -/
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

/-! ### Definition_10_96_2 (from Chap10) -/
universe u v

section

variable (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/- Definition 10.96.2: an `R`-module `M` is `I`-adically complete if it satisfies the canonical
mathlib predicate `IsAdicComplete I M`; for `M = R`, this is the textbook notion that `R` is
`I`-adically complete as a ring. -/
recall IsAdicComplete

/- Companion recall: `AdicCompletion.of_bijective_iff` identifies `I`-adic completeness with the
statement that the canonical map `M → AdicCompletion I M`, i.e. to the inverse limit of the
quotients `M / I^n M`, is bijective. -/
recall AdicCompletion.of_bijective_iff

end

/-! ### Lemma_10_96_3 (from Chap10) -/
noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/- Lemma 10.96.3 (1): for a finitely generated ideal `I`, the `I`-adic completion `AdicCompletion I M`
is `I`-adically complete. -/
recall AdicCompletion.isAdicComplete

/- Lemma 10.96.3 (2): for every positive integer `n`, the kernel of the canonical map
`AdicCompletion I M → M ⧸ (I ^ n • ⊤)` is exactly `I ^ n` times the completed module. -/
recall AdicCompletion.pow_smul_top_eq_ker_eval

/- Companion bridge: the canonical map `AdicCompletion.ofPowSMul` from the completion of `I ^ n M`
into the completion of `M` has image equal to the kernel of the evaluation map. -/
recall AdicCompletion.restrictScalars_range_ofPowSMul_eq_ker_eval

end

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

/-- Helper for Lemma 10.96.3: after restricting scalars to `R`, the kernel of the algebra-valued
evaluation map agrees with the kernel of the underlying linear evaluation map. -/
lemma ker_evalₐ_restrictScalars_eq_ker_eval (n : ℕ) :
    (((RingHom.ker (AdicCompletion.evalₐ I n) : Ideal (AdicCompletion I R)) :
        Submodule (AdicCompletion I R) (AdicCompletion I R)).restrictScalars R) =
      (AdicCompletion.eval I R n).ker := by
  have hle₁ : (I ^ n : Ideal R) ≤ I ^ n • (⊤ : Submodule R R) := by
    simpa [Ideal.smul_eq_mul] using le_of_eq (Ideal.mul_top (I ^ n)).symm
  have hle₂ : I ^ n • (⊤ : Submodule R R) ≤ (I ^ n : Ideal R) := by
    simpa [Ideal.smul_eq_mul] using le_of_eq (Ideal.mul_top (I ^ n))
  -- Compare kernel membership by transporting vanishing across the canonical quotient factors.
  ext x
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx
    simpa [hx] using (AdicCompletion.factor_evalₐ_eq_eval (I := I) (n := n) x hle₁).symm
  · intro hx
    simpa [hx] using (AdicCompletion.factor_eval_eq_evalₐ (I := I) (n := n) x hle₂).symm

-- Proof sketch: compare the ring-theoretic map `AdicCompletion.evalₐ I n` with the module map
-- `AdicCompletion.eval I R n`, then translate the kernel description from the module theorem into
-- an equality of ideals in `AdicCompletion I R`.
/-- For every `n : ℕ`, the ideal generated by `I ^ n` in the completed ring is the kernel of the
canonical map `AdicCompletion I R → R ⧸ I ^ n`. -/
theorem completionIdeal_pow_eq_ker_evalₐ (hI : I.FG) (n : ℕ) :
    Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) =
      RingHom.ker (AdicCompletion.evalₐ I n) := by
  -- Restrict scalars so the goal matches the module-side kernel statement from the completion API.
  apply Submodule.restrictScalars_injective R (AdicCompletion I R) (AdicCompletion I R)
  -- The left-hand ideal map becomes `I ^ n • ⊤`, which is exactly the source-proof image term.
  calc
    (((Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) : Ideal (AdicCompletion I R)) :
        Submodule (AdicCompletion I R) (AdicCompletion I R)).restrictScalars R) =
        I ^ n • (⊤ : Submodule R (AdicCompletion I R)) := by
          simpa [Ideal.smul_top_eq_map]
    _ = (AdicCompletion.eval I R n).ker := by
      -- Finite generation gives the kernel description on the completed module.
      simpa using (AdicCompletion.pow_smul_top_eq_ker_eval (I := I) (M := R) (n := n) hI)
    _ =
        (((RingHom.ker (AdicCompletion.evalₐ I n) : Ideal (AdicCompletion I R)) :
          Submodule (AdicCompletion I R) (AdicCompletion I R)).restrictScalars R) := by
      -- The algebra-valued and linear evaluation maps have the same kernel after restricting scalars.
      symm
      exact ker_evalₐ_restrictScalars_eq_ker_eval (I := I) n

end

/-! ### Lemma_10_96_4 (from Chap10) -/
open CategoryTheory
open AdicCompletion

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M N Q : Type v}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]

/-- A module annihilated by a power of `I` is `I`-adically complete. -/
-- Proof sketch: if `I ^ c • Q = 0`, then the inverse system `Q / I^n Q` is eventually constant with
-- value `Q`, so the canonical map `Q → AdicCompletion I Q` is bijective. Conclude using
-- `AdicCompletion.of_bijective_iff`.
theorem isAdicComplete_of_pow_smul_top_eq_bot (c : ℕ)
    (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) : IsAdicComplete I Q := by
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · -- At the cutoff stage `c`, congruence modulo `I ^ c Q` is actual equality.
    refine ⟨fun x hx ↦ ?_⟩
    have hx0 : x ∈ I ^ c • (⊤ : Submodule R Q) := by
      simpa [SModEq] using hx c
    simpa [hc] using hx0
  · -- After stage `c`, the Cauchy sequence is literally constant, so `f c` is the limit.
    refine ⟨fun f hf ↦ ?_⟩
    refine ⟨f c, ?_⟩
    intro n
    by_cases hnc : n ≤ c
    · exact hf hnc
    · have hcn : c ≤ n := Nat.le_of_not_ge hnc
      have hEq : f c = f n := by
        have hq :
            Submodule.Quotient.mk (p := (I ^ c • (⊤ : Submodule R Q))) (f c) =
              Submodule.Quotient.mk (p := (I ^ c • (⊤ : Submodule R Q))) (f n) := by
          simpa using hf hcn
        have hmod : f c - f n ∈ I ^ c • (⊤ : Submodule R Q) := by
          rwa [Submodule.Quotient.eq] at hq
        have hbot : f c - f n ∈ (⊥ : Submodule R Q) := by
          simpa [hc] using hmod
        exact sub_eq_zero.mp (by simpa using hbot)
      simpa [hEq]

/-- Helper for Lemma 10.96.4: once `I ^ c` kills `Q`, every higher power of `I` kills `Q` as well. -/
theorem pow_smul_top_eq_bot_of_ge (c n : ℕ)
    (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) (hcn : c ≤ n) :
    I ^ n • (⊤ : Submodule R Q) = ⊥ := by
  apply le_antisymm ?_ bot_le
  exact le_trans
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right hcn))
    (by simpa [hc])

/-- Helper for Lemma 10.96.4: every element of `I ^ c N` lies in the range of `f` because its image
in the cokernel is zero. -/
theorem pow_smul_top_le_range_of_pow_smul_top_eq_bot
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q} (hfg : Function.Exact f g)
    {c : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) :
    I ^ c • (⊤ : Submodule R N) ≤ LinearMap.range f := by
  intro y hy
  have hmap :
      Submodule.map g (I ^ c • (⊤ : Submodule R N)) ≤ I ^ c • (⊤ : Submodule R Q) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact smul_mono_right _ le_top
  have hy0 : g y = 0 := by
    have hymem : g y ∈ I ^ c • (⊤ : Submodule R Q) := hmap (Submodule.mem_map_of_mem hy)
    simpa [hc] using hymem
  rcases (hfg y).mp hy0 with ⟨x, rfl⟩
  exact ⟨x, rfl⟩

/-- Helper for Lemma 10.96.4: after shifting by the annihilator exponent, `I ^ n N` is contained
in the image of `I ^ (n - c) M`. -/
theorem pow_smul_top_le_map_pow_tsub_of_pow_smul_top_eq_bot
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q} (hfg : Function.Exact f g)
    {c n : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) (hcn : c ≤ n) :
    I ^ n • (⊤ : Submodule R N) ≤ Submodule.map f (I ^ (n - c) • (⊤ : Submodule R M)) := by
  calc
    I ^ n • (⊤ : Submodule R N)
      = I ^ ((n - c) + c) • (⊤ : Submodule R N) := by
          rw [Nat.sub_add_cancel hcn]
    _ = (I ^ (n - c) * I ^ c) • (⊤ : Submodule R N) := by
          rw [pow_add]
    _ = I ^ (n - c) • (I ^ c • (⊤ : Submodule R N)) := by
          simpa using (Submodule.mul_smul (I ^ (n - c)) (I ^ c) (⊤ : Submodule R N))
    _ ≤ I ^ (n - c) • LinearMap.range f := by
          exact smul_mono_right _
            (pow_smul_top_le_range_of_pow_smul_top_eq_bot (I := I) hfg hc)
    _ = Submodule.map f (I ^ (n - c) • (⊤ : Submodule R M)) := by
          rw [Submodule.map_smul'', Submodule.map_top]

/-- Helper for Lemma 10.96.4: if `f x` lies in `I ^ n N`, then `x` already lies in
`I ^ (n - c) M`. -/
theorem mem_pow_tsub_smul_top_of_mem_comap_pow_smul_top
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q} (hf : Function.Injective f) (hfg : Function.Exact f g)
    {c n : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) (hcn : c ≤ n)
    {x : M} (hx : x ∈ Submodule.comap f (I ^ n • (⊤ : Submodule R N))) :
    x ∈ I ^ (n - c) • (⊤ : Submodule R M) := by
  have hmem :
      f x ∈ Submodule.map f (I ^ (n - c) • (⊤ : Submodule R M)) :=
    pow_smul_top_le_map_pow_tsub_of_pow_smul_top_eq_bot (I := I) hfg hc hcn hx
  rcases hmem with ⟨y, hy, hyx⟩
  have hxy : x = y := hf hyx.symm
  simpa [hxy] using hy

/-- Helper for Lemma 10.96.4: the filtered submodule
`Submodule.comap f (I ^ n • ⊤)` sits between `I ^ n M` and `I ^ (n - c) M`. -/
theorem pow_smul_comap_stage_sandwich
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q} (hf : Function.Injective f) (hfg : Function.Exact f g)
    {c n : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) (hcn : c ≤ n) :
    I ^ n • (⊤ : Submodule R M) ≤ Submodule.comap f (I ^ n • (⊤ : Submodule R N)) ∧
      Submodule.comap f (I ^ n • (⊤ : Submodule R N)) ≤ I ^ (n - c) • (⊤ : Submodule R M) := by
  constructor
  · -- The image of `I ^ n M` is visibly contained in `I ^ n N`.
    intro x hx
    change f x ∈ I ^ n • (⊤ : Submodule R N)
    have hmap : f x ∈ Submodule.map f (I ^ n • (⊤ : Submodule R M)) :=
      Submodule.mem_map_of_mem hx
    have hrange : f x ∈ I ^ n • LinearMap.range f := by
      simpa [Submodule.map_smul'', Submodule.map_top] using hmap
    exact (smul_mono_right _ (show LinearMap.range f ≤ (⊤ : Submodule R N) by exact le_top)) hrange
  · -- The annihilator cutoff moves the preimage of `I ^ n N` down to `I ^ (n - c) M`.
    intro x hx
    exact mem_pow_tsub_smul_top_of_mem_comap_pow_smul_top (I := I) hf hfg hc hcn hx

namespace AdicCompletion

/-- The map from the `I`-adic completion of `N` to an `I`-adically complete target `Q` induced by
`g : N →ₗ[R] Q`. -/
noncomputable abbrev mapToComplete (g : N →ₗ[R] Q) [IsAdicComplete I Q] :
    AdicCompletion I N →ₗ[R] Q :=
  ((ofLinearEquiv I Q).symm : AdicCompletion I Q →ₗ[R] Q).comp ((map I g).restrictScalars R)

@[simp]
theorem mapToComplete_of (g : N →ₗ[R] Q) [IsAdicComplete I Q] (x : N) :
    mapToComplete I g (of I N x) = g x := by
  apply (ofLinearEquiv I Q).injective
  rw [mapToComplete, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_of]
  simp

@[simp]
theorem mapToComplete_comp_of (g : N →ₗ[R] Q) [IsAdicComplete I Q] :
    (mapToComplete I g).comp (of I N) = g := by
  ext x
  exact mapToComplete_of I g x

theorem mapToComplete_comp_eq_zero {f : M →ₗ[R] N} {g : N →ₗ[R] Q} [IsAdicComplete I Q]
    (hfg : Function.Exact f g) :
    (mapToComplete I g).comp ((map I f).restrictScalars R) = 0 := by
  apply DFunLike.ext
  intro x
  apply (ofLinearEquiv I Q).injective
  simp [mapToComplete, map_comp_apply, hfg.linearMap_comp_eq_zero]

end AdicCompletion

/-- The map from `N^∧` to a quotient module `Q` annihilated by a power of `I`, obtained from the
canonical identification `Q^∧ ≃ Q`. -/
noncomputable abbrev completionMapToPowSmulTopEqBot (g : N →ₗ[R] Q) {c : ℕ}
    (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) : AdicCompletion I N →ₗ[R] Q :=
  let _ : IsAdicComplete I Q :=
    isAdicComplete_of_pow_smul_top_eq_bot I c hc
  AdicCompletion.mapToComplete I g

theorem completionMapToPowSmulTopEqBot_comp_eq_zero
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q} (hfg : Function.Exact f g)
    {c : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) :
    (completionMapToPowSmulTopEqBot I g hc).comp ((AdicCompletion.map I f).restrictScalars R) =
      0 := by
  let _ : IsAdicComplete I Q :=
    isAdicComplete_of_pow_smul_top_eq_bot I c hc
  -- After identifying `Q^∧` with `Q`, this is the standard vanishing of the composite.
  simpa [completionMapToPowSmulTopEqBot] using
    AdicCompletion.mapToComplete_comp_eq_zero (I := I) hfg

/-- Helper for Lemma 10.96.4: the completed left map is injective once the cokernel is annihilated
by `I ^ c`. -/
theorem completion_map_injective_of_pow_smul_top_eq_bot
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q}
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    {c : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) :
    Function.Injective (AdicCompletion.map I f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  ext n
  rcases Submodule.Quotient.mk_surjective (I ^ (n + c) • (⊤ : Submodule R M)) (x.val (n + c))
    with ⟨a, hxa⟩
  have hstage :
      f.reduceModIdeal (I ^ (n + c))
          (Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R M))) a) = 0 := by
    simpa [hxa, AdicCompletion.map_val_apply] using congrArg (fun z ↦ z.val (n + c)) hx
  have hfa : f a ∈ I ^ (n + c) • (⊤ : Submodule R N) := by
    simpa [LinearMap.reduceModIdeal_apply] using hstage
  have ha_mem :
      a ∈ I ^ ((n + c) - c) • (⊤ : Submodule R M) :=
    mem_pow_tsub_smul_top_of_mem_comap_pow_smul_top (I := I) hf hfg hc (Nat.le_add_left c n)
      hfa
  have hq :
      (Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R M))) a :
          M ⧸ I ^ (n + c) • (⊤ : Submodule R M)) ∈
        I ^ n • (⊤ : Submodule R (M ⧸ I ^ (n + c) • (⊤ : Submodule R M))) := by
    have ha_mem' : a ∈ I ^ n • (⊤ : Submodule R M) := by
      simpa [Nat.add_comm] using ha_mem
    have hmap :
        (Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R M))) a :
            M ⧸ I ^ (n + c) • (⊤ : Submodule R M)) ∈
          Submodule.map
            (Submodule.mkQ (I ^ (n + c) • (⊤ : Submodule R M)))
            (I ^ n • (⊤ : Submodule R M)) := by
      exact Submodule.mem_map_of_mem ha_mem'
    simpa [Submodule.map_smul'', Submodule.map_top] using hmap
  have hq' : x.val (n + c) ∈
      I ^ n • (⊤ : Submodule R (M ⧸ I ^ (n + c) • (⊤ : Submodule R M))) := by
    simpa [hxa] using hq
  exact (AdicCompletion.val_apply_mem_smul_top_iff (I := I) (x := x)
    (m_ge := Nat.le_add_right n c)).mp hq'

/-- Helper for Lemma 10.96.4: the completed map to `Q` is surjective because completion preserves
surjectivity and `Q` is already complete. -/
theorem completionMapToPowSmulTopEqBot_surjective
    {g : N →ₗ[R] Q} (hg : Function.Surjective g)
    {c : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) :
    Function.Surjective (completionMapToPowSmulTopEqBot I g hc) := by
  let _ : IsAdicComplete I Q :=
    isAdicComplete_of_pow_smul_top_eq_bot I c hc
  exact ((AdicCompletion.ofLinearEquiv I Q).symm.surjective).comp
    (AdicCompletion.map_surjective I hg)

-- Proof sketch: choose `c` with `I ^ c • Q = 0`, identify `Q / I^n Q` with `Q` for `n ≥ c`, and
-- rewrite the left quotients using `M ∩ I^n N`. Apply Lemma `10.87.1` to the inverse system of
-- short exact sequences `0 → M / (M ∩ I^n N) → N / I^n N → Q → 0`, then transport the right term
-- along the identification `Q^ ≃ Q`.
/-- Helper for Lemma 10.96.4: if a completed element maps to zero in `Q`, then each shifted
coordinate has a preimage in `M`. -/
theorem exists_stage_preimage_of_completion_kernel
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q} (hfg : Function.Exact f g)
    {c n : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥)
    {y : AdicCompletion I N} (hy : completionMapToPowSmulTopEqBot I g hc y = 0) :
    ∃ x : M,
      Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R N))) (f x) = y.val (n + c) := by
  let _ : IsAdicComplete I Q :=
    isAdicComplete_of_pow_smul_top_eq_bot I c hc
  -- Passing back through the completion equivalence turns the vanishing in `Q` into a vanishing in
  -- the completed cokernel.
  have hy' : AdicCompletion.map I g y = 0 := by
    exact (AdicCompletion.ofLinearEquiv I Q).symm.injective <| by
      simpa [completionMapToPowSmulTopEqBot, AdicCompletion.mapToComplete] using hy
  -- Choose a representative of the shifted coordinate and prove that its image in `Q` is zero.
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective
    (I ^ (n + c) • (⊤ : Submodule R N)) (y.val (n + c))
  have hstage :
      g.reduceModIdeal (I ^ (n + c)) (y.val (n + c)) = 0 := by
    simpa [AdicCompletion.map_val_apply] using congrArg (fun z ↦ z.val (n + c)) hy'
  have hgb_mem : g b ∈ I ^ (n + c) • (⊤ : Submodule R Q) := by
    have hstage' :
        g.reduceModIdeal (I ^ (n + c))
            (Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R N))) b) = 0 := by
      rw [← hb] at hstage
      exact hstage
    have hquot :
        Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R Q))) (g b) = 0 := by
      simpa [LinearMap.reduceModIdeal_apply] using hstage'
    have hquot' :
        Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R Q))) (g b) =
          Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R Q))) (0 : Q) := by
      simpa using hquot
    have hmem : g b - 0 ∈ I ^ (n + c) • (⊤ : Submodule R Q) := by
      rwa [Submodule.Quotient.eq] at hquot'
    simpa using hmem
  have hkill :
      I ^ (n + c) • (⊤ : Submodule R Q) = ⊥ :=
    pow_smul_top_eq_bot_of_ge (I := I) c (n + c) hc (Nat.le_add_left c n)
  have hgb : g b = 0 := by
    have hbot : g b ∈ (⊥ : Submodule R Q) := by
      simpa [hkill] using hgb_mem
    simpa using hbot
  -- Exactness of `M → N → Q` now lifts the representative back to `M`.
  rcases (hfg b).mp hgb with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [ha] using hb

/-- Helper for Lemma 10.96.4: shifted stagewise preimages of a kernel element form an
`I`-adic Cauchy sequence in `M`. -/
theorem stage_preimages_smodEq
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q} (hf : Function.Injective f) (hfg : Function.Exact f g)
    {c : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥)
    {y : AdicCompletion I N} {a : ℕ → M}
    (ha : ∀ n,
      Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R N))) (f (a n)) = y.val (n + c)) :
    ∀ n, a n ≡ a (n + 1) [SMOD (I ^ n • (⊤ : Submodule R M))] := by
  intro n
  -- Compare two consecutive lifts after pushing the later one down to the earlier quotient stage.
  have ha_succ :
      Submodule.Quotient.mk (p := (I ^ (n + c + 1) • (⊤ : Submodule R N))) (f (a (n + 1))) =
        y.val (n + c + 1) := by
    convert ha (n + 1) using 2
    · simp [Nat.add_assoc, Nat.add_comm]
    · simp [Nat.add_assoc, Nat.add_comm]
    · omega
  have hsucc :
      Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R N))) (f (a (n + 1))) =
        y.val (n + c) := by
    calc
      Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R N))) (f (a (n + 1)))
        = AdicCompletion.transitionMap I N (Nat.le_succ (n + c))
            (Submodule.Quotient.mk
              (p := (I ^ (n + c + 1) • (⊤ : Submodule R N))) (f (a (n + 1)))) := by
              simpa [AdicCompletion.transitionMap] using
                (Submodule.factor_mk
                  (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + c))))
                  (f (a (n + 1))))
      _ = AdicCompletion.transitionMap I N (Nat.le_succ (n + c)) (y.val (n + c + 1)) := by
            rw [ha_succ]
      _ = y.val (n + c) := by
            simpa using y.property (Nat.le_succ (n + c))
  have hdiff :
      f (a (n + 1) - a n) ∈ I ^ (n + c) • (⊤ : Submodule R N) := by
    have hquot :
        Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R N))) (f (a (n + 1))) =
          Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R N))) (f (a n)) := by
      rw [ha n]
      exact hsucc
    have hdiff' : f (a (n + 1)) - f (a n) ∈ I ^ (n + c) • (⊤ : Submodule R N) := by
      rwa [Submodule.Quotient.eq] at hquot
    simpa [map_sub] using hdiff'
  -- The filtration sandwich `f⁻¹(I^(n+c) N) ⊆ I^n M` is exactly the source proof's control step.
  have hcomap :
      a (n + 1) - a n ∈ Submodule.comap f (I ^ (n + c) • (⊤ : Submodule R N)) := hdiff
  have hmem :
      a (n + 1) - a n ∈ I ^ n • (⊤ : Submodule R M) := by
    have hsandwich :
        Submodule.comap f (I ^ (n + c) • (⊤ : Submodule R N)) ≤
          I ^ ((n + c) - c) • (⊤ : Submodule R M) :=
      (pow_smul_comap_stage_sandwich (I := I) hf hfg hc (Nat.le_add_left c n)).2
    have hmem' :
        a (n + 1) - a n ∈ I ^ ((n + c) - c) • (⊤ : Submodule R M) := hsandwich hcomap
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmem'
  have hneg :
      a n - a (n + 1) ∈ I ^ n • (⊤ : Submodule R M) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Submodule.neg_mem _ hmem)
  rw [SModEq, Submodule.Quotient.eq]
  exact hneg

/-- Helper for Lemma 10.96.4: the completed map `M^∧ → N^∧ → Q` is exact when a power of `I`
annihilates `Q`. -/
theorem completion_map_exact_of_pow_smul_top_eq_bot
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q}
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    {c : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) :
    Function.Exact ((AdicCompletion.map I f).restrictScalars R)
      (completionMapToPowSmulTopEqBot I g hc) := by
  refine LinearMap.exact_of_comp_of_mem_range
    (completionMapToPowSmulTopEqBot_comp_eq_zero (I := I) hfg hc) ?_
  intro y hy
  -- Lift each shifted coordinate of `y` to `M`, then use the filtration sandwich to make those
  -- lifts compatible.
  choose a ha using fun n ↦
    exists_stage_preimage_of_completion_kernel (I := I) hfg hc (n := n) hy
  let x : AdicCompletion I M :=
    AdicCompletion.mk I M (AdicCompletion.AdicCauchySequence.mk I M a
      (stage_preimages_smodEq (I := I) hf hfg hc ha))
  refine ⟨x, ?_⟩
  -- Projecting the lifted family to every quotient stage recovers the original completed element.
  ext n
  calc
    (((AdicCompletion.map I f).restrictScalars R) x).val n
      = Submodule.Quotient.mk (p := (I ^ n • (⊤ : Submodule R N))) (f (a n)) := by
          simp [x]
    _ = AdicCompletion.transitionMap I N (Nat.le_add_right n c)
          (Submodule.Quotient.mk (p := (I ^ (n + c) • (⊤ : Submodule R N))) (f (a n))) := by
          symm
          simpa [AdicCompletion.transitionMap] using
            (Submodule.factor_mk
              (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n c)))
              (f (a n)))
    _ = AdicCompletion.transitionMap I N (Nat.le_add_right n c) (y.val (n + c)) := by
          rw [ha n]
    _ = y.val n := by
          simpa using y.property (Nat.le_add_right n c)

/-- Lemma 10.96.4: if `0 → M → N → Q → 0` is exact and a power of `I` annihilates `Q`, then
completion yields a short exact sequence `0 → M^ → N^ → Q → 0`. -/
theorem completion_shortExact_of_pow_smul_top_eq_bot
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {c : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) :
    (ShortComplex.moduleCatMk
      ((AdicCompletion.map I f).restrictScalars R)
      (completionMapToPowSmulTopEqBot I g hc)
      (completionMapToPowSmulTopEqBot_comp_eq_zero I hfg hc)).ShortExact := by
  -- Route correction: the cutoff lemmas above now realize the source proof's filtration step
  -- `I^n M ⊆ M ∩ I^n N ⊆ I^(n-c) M`; here we use that control directly on shifted coordinates of a
  -- kernel element in `N^∧` to build its preimage in `M^∧`.
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · exact completion_map_exact_of_pow_smul_top_eq_bot (I := I) hf hfg hc
  · simpa using completion_map_injective_of_pow_smul_top_eq_bot (I := I) hf hfg hc
  · exact completionMapToPowSmulTopEqBot_surjective (I := I) hg hc

end
