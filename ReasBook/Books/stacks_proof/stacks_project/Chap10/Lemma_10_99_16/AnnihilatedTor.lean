import stacks_proof.stacks_project.Chap10.Lemma_10_99_16.SourceTorExact

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Pointwise
open scoped TensorProduct

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]


/-- Helper for Lemma 10.99.16: regularity of `f` on `M` forces the quotient-first owner
`Tor₁^A(A / (f), M)` to vanish. -/
lemma tor_one_quotient_first_by_regular_element_vanishes
    (f : A) (hfA : IsRegular f) (hfM : IsSMulRegular M f) :
    IsZero ((((Tor (ModuleCat A) 1).obj
      (ModuleCat.of A (A ⧸ Ideal.span ({f} : Set A)))).obj (ModuleCat.of A M))) := by
  let _ := hfM
  let S : ShortComplex (ModuleCat A) := ModuleCat.smulShortComplex (ModuleCat.of A A) f
  have hS : S.ShortExact := by
    -- Proof comment: regularity of `f` on `A` makes the principal multiplication row
    -- `0 → A --(·f)→ A → A/(f) → 0` short exact.
    simpa [S] using
      (IsSMulRegular.smulShortComplex_shortExact
        (M := ModuleCat.of A A) (r := f) hfA.isSMulRegular)
  obtain ⟨δ, hFive⟩ :=
    public_owner_tor_one_tensor_exact_of_shortExact (A := A) (M := M) (S := S) hS
  let β :
      ((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj S.X₂) ⟶
        ((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj S.X₃) :=
    (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.g))
  let u :
      ((tensorRight (ModuleCat.of A M)).obj S.X₁) ⟶
        ((tensorRight (ModuleCat.of A M)).obj S.X₂) :=
    (((tensorRight (ModuleCat.of A M)).map S.f))
  have hTorA :
      IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A A)).obj (ModuleCat.of A M))) := by
    let eA := (tor_left_owner_iso (A := A) (M := M) 1).app (ModuleCat.of A A)
    -- Proof comment: transport the source-owner unit vanishing back to the public quotient-first
    -- owner through `tor_left_owner_iso`.
    exact IsZero.of_iso (source_owner_tor_one_unit_isZero (A := A) (M := M)) eA
  have hβ_zero : β = 0 := by
    -- Proof comment: the source of the middle Tor arrow is already zero.
    simpa [β, S] using hTorA.eq_of_src β 0
  have hExactTor :
      Function.Exact β.hom δ.hom := by
    -- Proof comment: read the `(Tor₁, Tor₁, tensor)` exactness window at the middle Tor term.
    simpa [β, S, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.f))
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.g))
          δ
          (((tensorRight (ModuleCat.of A M)).map S.f))
          (((tensorRight (ModuleCat.of A M)).map S.g))).sc hFive.toIsComplex 1)).1
        (hFive.exact 1)
  have hExactTensor :
      Function.Exact δ.hom u.hom := by
    -- Proof comment: the same five-term row is exact at the connecting morphism into tensor.
    simpa [u, S, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.f))
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.g))
          δ
          (((tensorRight (ModuleCat.of A M)).map S.f))
          (((tensorRight (ModuleCat.of A M)).map S.g))).sc hFive.toIsComplex 2)).1
        (hFive.exact 2)
  have hTensor_injective : Function.Injective u.hom := by
    -- Proof comment: tensoring the injective multiplication-by-`f` map on `M` with the flat
    -- module `A` preserves injectivity, and this is exactly the endpoint map `u`.
    simpa [u, S, ModuleCat.hom_whiskerRight] using
      (IsSMulRegular.lTensor (R := A) (M := A) (M' := M) hfM :
        IsSMulRegular (A ⊗[A] M) f)
  have hδ_zero : δ = 0 := by
    -- Proof comment: exactness at the connecting morphism together with injectivity of the next
    -- tensor map forces the connecting morphism itself to vanish.
    ext x
    apply hTensor_injective
    have hcomp := LinearMap.congr_fun hExactTensor.linearMap_comp_eq_zero x
    simpa [LinearMap.comp_apply] using hcomp
  have hMid :
      IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A (QuotSMulTop f A))).obj
        (ModuleCat.of A M))) := by
    -- Proof comment: exactness at the middle Tor term with zero adjacent arrows kills the
    -- quotient-first Tor owner for `QuotSMulTop f A`.
    simpa [β, S] using isZero_of_exact_zero_zero hExactTor hβ_zero hδ_zero
  let eQuot :
      QuotSMulTop f A ≃ₗ[A] A ⧸ Ideal.span ({f} : Set A) :=
    (QuotSMulTop.equivTensorQuot (R := A) f A).trans
      (TensorProduct.lid A (A ⧸ Ideal.span ({f} : Set A)))
  -- Proof comment: transport from the quotient-by-submodule presentation `A / fA` to the
  -- canonical ideal-quotient presentation used in the statement.
  exact IsZero.of_iso hMid
    ((((Tor (ModuleCat A) 1).mapIso eQuot.toModuleIso).app (ModuleCat.of A M)).symm)


/-- Helper for Lemma 10.99.16: every module already defined over `A / (f)` is annihilated by
`(f)` after restricting scalars back to `A`. -/
lemma span_singleton_le_annihilator_of_quotient_module
    (f : A) {N : Type u} [AddCommGroup N]
    [Module (A ⧸ Ideal.span ({f} : Set A)) N] [Module A N]
    [IsScalarTower A (A ⧸ Ideal.span ({f} : Set A)) N] :
    Ideal.span ({f} : Set A) ≤ Module.annihilator A N := by
  have hbot :
      Ideal.span ({f} : Set A) • (⊤ : Submodule A N) = ⊥ := by
    -- Proof comment: modules over `A / (f)` are killed by the whole principal ideal.
    simpa using
      ideal_smul_top_eq_bot_of_quotient_module
        (R := A) (I := Ideal.span ({f} : Set A)) (N := N)
  simpa [Submodule.annihilator_top] using
    ((Submodule.le_annihilator_iff (R := A) (M := N)).2 hbot)

/-- Helper for Lemma 10.99.16: on the free module `ι →₀ A`, multiplication by `f` has image
exactly `(f) • ⊤`. -/
lemma range_finsupp_lsmul_eq_span_singleton_smul_top
    (f : A) (ι : Type u) :
    LinearMap.range (LinearMap.lsmul A (ι →₀ A) f) =
      Ideal.span ({f} : Set A) • (⊤ : Submodule A (ι →₀ A)) := by
  let F : Type u := ι →₀ A
  let μ : F →ₗ[A] F := LinearMap.lsmul A F f
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, rfl⟩
    -- Proof comment: every value in the image is visibly an `(f)`-multiple.
    exact Submodule.smul_mem_smul (Ideal.subset_span (by simp)) (by simp)
  · intro hx
    -- Proof comment: expand membership in `(f) • ⊤` termwise and pull out one explicit factor of
    -- `f` from each generator.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      rcases (Ideal.mem_span_singleton').1 hr with ⟨a, rfl⟩
      refine ⟨a • y, ?_⟩
      simp [μ, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    · intro y z hy hz
      rcases hy with ⟨y', rfl⟩
      rcases hz with ⟨z', rfl⟩
      refine ⟨y' + z', ?_⟩
      simp [μ, smul_add]

/-- Helper for Lemma 10.99.16: coefficientwise reduction modulo `(f)` gives the exact row
`(ι →₀ A) --(·f)→ (ι →₀ A) → (ι →₀ A/(f))`. -/
lemma finsupp_principal_quotient_exact
    (f : A) (ι : Type u) :
    Function.Exact (LinearMap.lsmul A (ι →₀ A) f)
      (finsupp_quotientMapLinear (R := A) (I := Ideal.span ({f} : Set A)) ι) := by
  -- Proof comment: identify the kernel of coefficientwise reduction with `(f) • ⊤`, then rewrite
  -- that ideal-smul submodule as the image of multiplication by `f`.
  exact (LinearMap.exact_iff).2 <|
    (finsupp_quotientMap_ker_eq_ideal_smul_top
      (R := A) (I := Ideal.span ({f} : Set A)) (ι := ι)).trans <|
      (range_finsupp_lsmul_eq_span_singleton_smul_top (A := A) f ι).symm

/-- Helper for Lemma 10.99.16: free `A / (f)`-modules have vanishing quotient-first `Tor₂` with
`M`. This is the free base case in the source proof's degree-`2` bootstrap. -/
lemma tor_two_free_quotient_module_vanishes
    (f : A) (hfA : IsRegular f) (ι : Type u) :
    IsZero ((((Tor (ModuleCat A) 2).obj
      (ModuleCat.of A (ι →₀ (A ⧸ Ideal.span ({f} : Set A))))).obj (ModuleCat.of A M))) := by
  let F : Type u := ι →₀ A
  let Fbar : Type u := ι →₀ (A ⧸ Ideal.span ({f} : Set A))
  let μ : F →ₗ[A] F := LinearMap.lsmul A F f
  let q : F →ₗ[A] Fbar :=
    finsupp_quotientMapLinear (R := A) (I := Ideal.span ({f} : Set A)) ι
  have hExact : Function.Exact μ q := by
    -- Proof comment: this is the direct free `(f)`-quotient row from the source proof.
    simpa [F, Fbar, μ, q] using finsupp_principal_quotient_exact (A := A) f ι
  have hμ_injective : Function.Injective μ := by
    -- Proof comment: regularity of `f` on `A` propagates coefficientwise to the free module.
    intro x y hxy
    ext i
    exact hfA.left (by simpa [μ] using congrArg (fun z : F => z i) hxy)
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk μ q (Function.Exact.linearMap_comp_eq_zero hExact)
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [S] using hExact
    · exact (ModuleCat.mono_iff_injective _).2 hμ_injective
    · exact (ModuleCat.epi_iff_surjective _).2 <| by
        simpa [q] using
          finsupp_quotientMap_surjective (R := A) (I := Ideal.span ({f} : Set A)) ι
  let _ : Projective (ModuleCat.of A F) :=
    ModuleCat.projective_of_free (M := ModuleCat.of A F) (Finsupp.basisSingleOne)
  have hTor₂F :
      IsZero ((((Tor (ModuleCat A) 2).obj (ModuleCat.of A F)).obj
        (ModuleCat.of A M))) := by
    -- Proof comment: free modules are projective, so higher Tor vanishes in degree `2`.
    simpa [F] using tor_succ_isZero_of_projective_left (A := A) (M := M) (P := F) 1
  have hTor₁F :
      IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A F)).obj
        (ModuleCat.of A M))) := by
    -- Proof comment: the same projective argument kills degree `1`.
    simpa [F] using tor_succ_isZero_of_projective_left (A := A) (M := M) (P := F) 0
  obtain ⟨δ, hFive⟩ :=
    tor_two_tor_one_five_term_exact_of_shortExact (A := A) (M := M) (S := S) hS
  let β :
      ((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).obj S.X₂) ⟶
        ((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).obj S.X₃) :=
    (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map S.g))
  have hβ_zero : β = 0 := by
    -- Proof comment: the source of the middle degree-`2` arrow is already zero.
    simpa [β, S] using hTor₂F.eq_of_src β 0
  have hδ_zero : δ = 0 := by
    -- Proof comment: the target `Tor₁(F, M)` also vanishes for the same projective reason.
    simpa [S] using hTor₁F.eq_of_tgt δ 0
  have hExactMid :
      Function.Exact β.hom δ.hom := by
    -- Proof comment: read exactness at the middle `Tor₂(Fbar, M)` term from the quotient-first
    -- `(2,1)` exact row.
    simpa [β, S, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map S.f))
          (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map S.g))
          δ
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.f))
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.g))).sc
            hFive.toIsComplex 1)).1
        (hFive.exact 1)
  -- Proof comment: exactness with zero outer arrows forces the middle `Tor₂` object to vanish.
  simpa [β, S] using isZero_of_exact_zero_zero hExactMid hβ_zero hδ_zero


end
