import stacks_proof.stacks_project.Chap10.Lemma_10_96_5.PositiveStageLimits

universe u

noncomputable section

open AdicCompletion
open CategoryTheory
open CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

local notation "ModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat R
local notation "moduleInvLim" => (lim : ModuleInverseSystem ⥤ ModuleCat R)

/-- Helper for Lemma 10.96.5: the inverse-limit functor on `R`-module inverse systems, with the
module universe frozen explicitly so later `ShortComplex.map` applications elaborate stably. -/
private abbrev moduleInverseLimitFunctor : ModuleInverseSystem ⥤ ModuleCat R :=
  lim

/-- Helper for Lemma 10.96.5: the completion coordinates of `(AdicCompletion I M)^∧` form the
compatible family needed to retract completeness back to `AdicCompletion I M`. -/
private theorem positive_stage_completion_eval_family_compat
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I (AdicCompletion I M) hmn ∘ₗ
        AdicCompletion.eval I (AdicCompletion I M) n =
      AdicCompletion.eval I (AdicCompletion I M) m := by
  -- This is exactly the compatibility relation defining adic completion coordinates.
  ext x
  simpa using
    (AdicCompletion.transitionMap_comp_eval_apply
      (I := I) (M := AdicCompletion I M) (hmn := hmn) (x := x))

/-- Helper for Lemma 10.96.5: if `M^∧` is complete, then its adic completion retracts onto
`M^∧` by the universal property of completeness. -/
private noncomputable abbrev positive_stage_completion_retraction
    (hcomplete : IsAdicComplete I (AdicCompletion I M)) :
    AdicCompletion I (AdicCompletion I M) →ₗ[R] AdicCompletion I M :=
  letI : IsAdicComplete I (AdicCompletion I M) := hcomplete
  IsAdicComplete.lift I
    (fun n ↦ AdicCompletion.eval I (AdicCompletion I M) n)
    (fun {_ _} hmn ↦ positive_stage_completion_eval_family_compat
      (R := R) (I := I) (M := M) hmn)

/-- Helper for Lemma 10.96.5: the completeness retraction realizes the expected quotient map at
every stage. -/
private theorem positive_stage_completion_retraction_mkQ
    (hcomplete : IsAdicComplete I (AdicCompletion I M)) (n : ℕ) :
    Submodule.mkQ (I ^ n • (⊤ : Submodule R (AdicCompletion I M))) ∘ₗ
        positive_stage_completion_retraction (R := R) (I := I) (M := M) hcomplete =
      AdicCompletion.eval I (AdicCompletion I M) n := by
  letI : IsAdicComplete I (AdicCompletion I M) := hcomplete
  -- This is the defining stagewise property of `IsAdicComplete.lift`.
  simpa [positive_stage_completion_retraction] using
    (IsAdicComplete.mkQ_comp_lift
      (I := I)
      (M := AdicCompletion I (AdicCompletion I M))
      (N := AdicCompletion I M)
      (f := fun n ↦ AdicCompletion.eval I (AdicCompletion I M) n)
      (h := fun {m n} hmn ↦ positive_stage_completion_eval_family_compat
        (R := R) (I := I) (M := M) hmn)
      n)

/-- Helper for Lemma 10.96.5: after applying the stage-`n` evaluation to `M^∧`, the completeness
retraction is exactly the quotient-stage map out of `(M^∧)^∧`. -/
private theorem positive_stage_completion_retraction_eval
    (hcomplete : IsAdicComplete I (AdicCompletion I M)) (n : ℕ+) :
    (AdicCompletion.eval I M (n : ℕ)).comp
        (positive_stage_completion_retraction (R := R) (I := I) (M := M) hcomplete) =
      (ker_eval_quotient_stageMap (I := I) (M := M) n).comp
        (AdicCompletion.eval I (AdicCompletion I M) (n : ℕ)) := by
  -- Evaluate both sides on a point and rewrite the inner quotient map using the lift formula.
  apply LinearMap.ext
  intro x
  have hmkQ :
      Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)))
          ((positive_stage_completion_retraction
              (R := R) (I := I) (M := M) hcomplete) x) =
        AdicCompletion.eval I (AdicCompletion I M) (n : ℕ) x := by
    exact LinearMap.congr_fun
      (positive_stage_completion_retraction_mkQ
        (R := R) (I := I) (M := M) hcomplete (n : ℕ)) x
  change
    AdicCompletion.eval I M (n : ℕ)
        ((positive_stage_completion_retraction
            (R := R) (I := I) (M := M) hcomplete) x) =
      (ker_eval_quotient_stageMap (I := I) (M := M) n)
        (AdicCompletion.eval I (AdicCompletion I M) (n : ℕ) x)
  rw [← hmkQ]
  rfl

/-- Helper for Lemma 10.96.5: completeness makes the retraction a left inverse to the canonical
map `M^∧ → (M^∧)^∧`, hence injective. -/
private theorem positive_stage_completion_retraction_comp_of
    (hcomplete : IsAdicComplete I (AdicCompletion I M)) :
    (AdicCompletion.of I (AdicCompletion I M)).comp
        (positive_stage_completion_retraction (R := R) (I := I) (M := M) hcomplete) =
      LinearMap.id := by
  -- Evaluate on every quotient stage of `(M^∧)^∧` and use the lift formula above.
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  have hmkQ :=
    LinearMap.congr_fun
      (positive_stage_completion_retraction_mkQ
        (R := R) (I := I) (M := M) hcomplete n) x
  simpa [LinearMap.comp_apply, AdicCompletion.eval_of] using hmkQ

/-- Helper for Lemma 10.96.5: the completeness retraction from `(M^∧)^∧` to `M^∧` is injective. -/
private theorem positive_stage_completion_retraction_injective
    (hcomplete : IsAdicComplete I (AdicCompletion I M)) :
    Function.Injective
      (positive_stage_completion_retraction (R := R) (I := I) (M := M) hcomplete) := by
  have hleft :
      Function.LeftInverse
        (AdicCompletion.of I (AdicCompletion I M))
        (positive_stage_completion_retraction (R := R) (I := I) (M := M) hcomplete) := by
    intro x
    exact LinearMap.congr_fun
      (positive_stage_completion_retraction_comp_of
        (R := R) (I := I) (M := M) hcomplete) x
  exact hleft.injective

/-- Helper for Lemma 10.96.5: after identifying the positive-stage inverse limits with the two
adic completions, the inverse-limit right map is the completeness retraction from `(M^∧)^∧`
back to `M^∧`. -/
lemma positive_stage_limMap_stageMap_eq_completion_retraction
    (hcomplete : IsAdicComplete I (AdicCompletion I M)) :
    limMap (positive_stage_stageMap (R := R) (I := I) (M := M)) =
      (positive_stage_completion_system_limit_iso (R := R) (I := I) (M := M)).hom ≫
        ModuleCat.ofHom
          (positive_stage_completion_retraction (R := R) (I := I) (M := M) hcomplete) ≫
        (positive_stage_module_system_limit_iso (R := R) (I := I) (M := M)).inv := by
  -- Compare both sides after every stage projection of the target inverse limit.
  apply limit.hom_ext
  intro i
  apply ModuleCat.hom_ext
  ext x
  have hleft' :
      limMap (positive_stage_stageMap (R := R) (I := I) (M := M)) ≫
          limit.π (positive_stage_module_system (R := R) (I := I) (M := M)) i =
        limit.π (positive_stage_completion_system (R := R) (I := I) (M := M)) i ≫
          (positive_stage_stageMap (R := R) (I := I) (M := M)).app i := by
    exact limMap_π (α := positive_stage_stageMap (R := R) (I := I) (M := M)) (j := i)
  have hleftMap := congrArg ModuleCat.Hom.hom hleft'
  have hleft :
      (limit.π (positive_stage_module_system (R := R) (I := I) (M := M)) i).hom
          ((limMap (positive_stage_stageMap (R := R) (I := I) (M := M))).hom x) =
        ((positive_stage_stageMap (R := R) (I := I) (M := M)).app i).hom
          ((limit.π (positive_stage_completion_system (R := R) (I := I) (M := M)) i).hom x) := by
    exact congrArg (fun f ↦ f x) hleftMap
  have hmodule :
      AdicCompletion.eval I M ((stagePNat i : ℕ))
          (((positive_stage_module_system_limit_iso
              (R := R) (I := I) (M := M)).hom)
            ((limMap (positive_stage_stageMap (R := R) (I := I) (M := M))).hom x)) =
        (limit.π (positive_stage_module_system (R := R) (I := I) (M := M)) i).hom
          ((limMap (positive_stage_stageMap (R := R) (I := I) (M := M))).hom x) := by
    simpa [Category.assoc, stagePNat] using
      congrArg (fun g ↦ g ((limMap
        (positive_stage_stageMap (R := R) (I := I) (M := M))).hom x))
        (positive_stage_module_system_limit_iso_hom_π
          (R := R) (I := I) (M := M) i)
  have hcompletion :
      AdicCompletion.eval I (AdicCompletion I M) ((stagePNat i : ℕ))
          (((positive_stage_completion_system_limit_iso
              (R := R) (I := I) (M := M)).hom) x) =
        (limit.π (positive_stage_completion_system (R := R) (I := I) (M := M)) i).hom x := by
    simpa [Category.assoc, stagePNat] using
      congrArg (fun g ↦ g x)
        (positive_stage_completion_system_limit_iso_hom_π
          (R := R) (I := I) (M := M) i)
  let n : ℕ+ := stagePNat i
  calc
    (limit.π (positive_stage_module_system (R := R) (I := I) (M := M)) i).hom
        ((limMap (positive_stage_stageMap (R := R) (I := I) (M := M))).hom x)
      = ((positive_stage_stageMap (R := R) (I := I) (M := M)).app i).hom
          ((limit.π (positive_stage_completion_system (R := R) (I := I) (M := M)) i).hom x) := hleft
    _ = (ker_eval_quotient_stageMap (I := I) (M := M) n)
          (AdicCompletion.eval I (AdicCompletion I M) ((stagePNat i : ℕ))
            (((positive_stage_completion_system_limit_iso
                (R := R) (I := I) (M := M)).hom) x)) := by
            rw [← hcompletion]
            rfl
    _ = AdicCompletion.eval I M ((stagePNat i : ℕ))
          ((positive_stage_completion_retraction
              (R := R) (I := I) (M := M) hcomplete)
            (((positive_stage_completion_system_limit_iso
                (R := R) (I := I) (M := M)).hom) x)) := by
            simpa using
              congrArg (fun f ↦ f (((positive_stage_completion_system_limit_iso
                (R := R) (I := I) (M := M)).hom) x))
                (positive_stage_completion_retraction_eval
                  (R := R) (I := I) (M := M) hcomplete n).symm
    _ = (limit.π (positive_stage_module_system (R := R) (I := I) (M := M)) i).hom
          (((positive_stage_module_system_limit_iso
              (R := R) (I := I) (M := M)).inv).hom
            ((positive_stage_completion_retraction
              (R := R) (I := I) (M := M) hcomplete)
              (((positive_stage_completion_system_limit_iso
                  (R := R) (I := I) (M := M)).hom) x))) := by
            let y :=
              (positive_stage_completion_retraction
                (R := R) (I := I) (M := M) hcomplete)
                (((positive_stage_completion_system_limit_iso
                    (R := R) (I := I) (M := M)).hom) x)
            have hproj :
                (limit.π (positive_stage_module_system (R := R) (I := I) (M := M)) i).hom
                    (((positive_stage_module_system_limit_iso
                        (R := R) (I := I) (M := M)).inv).hom y) =
                  AdicCompletion.eval I M ((stagePNat i : ℕ)) y := by
              exact LinearMap.congr_fun
                (congrArg ModuleCat.Hom.hom
                  (positive_stage_module_system_limit_iso_inv_π
                    (R := R) (I := I) (M := M) i))
                y
            exact hproj.symm

/-- Helper for Lemma 10.96.5: the inverse-limit short exact sequence for the positive-stage
systems supplies the concrete exactness and monomorphism data used in the completeness argument. -/
private theorem positive_stage_limit_exact_and_mono :
    Function.Exact
        ((limMap (positive_stage_left_ι (R := R) (I := I) (M := M))).hom)
        ((limMap (positive_stage_stageMap (R := R) (I := I) (M := M))).hom) ∧
      Mono (limMap (positive_stage_left_ι (R := R) (I := I) (M := M))) := by
  have hLimitShortExact :
      ((positive_stage_shortComplex (R := R) (I := I) (M := M)).map
        moduleInverseLimitFunctor).ShortExact := by
    -- Apply Lemma `10.87.1` to the positive-stage short complex built above.
    simpa [moduleInverseLimitFunctor] using
      moduleInverseLimit_shortExact_of_isMittagLeffler_left
        (R := R)
        (S := positive_stage_shortComplex (R := R) (I := I) (M := M))
        (hS := positive_stage_quotient_system_shortExact (R := R) (I := I) (M := M))
        (hML := positive_stage_left_system_isMittagLeffler (R := R) (I := I) (M := M))
  refine ⟨?_, ?_⟩
  · -- Project the exactness of the inverse-limit row to the concrete limit maps used later.
    simpa [positive_stage_shortComplex, moduleInverseLimitFunctor] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        ((positive_stage_shortComplex (R := R) (I := I) (M := M)).map
          moduleInverseLimitFunctor)).1 hLimitShortExact.exact
  · -- Project the monomorphism of the left inverse-limit map from the same short exact row.
    simpa [positive_stage_shortComplex, moduleInverseLimitFunctor] using hLimitShortExact.mono_f

/-- Helper for Lemma 10.96.5: if `AdicCompletion I M` is complete, then the inverse limit of the
positive-stage kernel quotients `K_n / I ^ n M^∧` is zero. -/
lemma positive_stage_left_limit_isZero_of_complete
    (hcomplete : IsAdicComplete I (AdicCompletion I M)) :
    IsZero (limit (positive_stage_left_system (R := R) (I := I) (M := M))) := by
  have hLimitData := positive_stage_limit_exact_and_mono (R := R) (I := I) (M := M)
  have hExact :
      Function.Exact
        ((limMap (positive_stage_left_ι (R := R) (I := I) (M := M))).hom)
        ((limMap (positive_stage_stageMap (R := R) (I := I) (M := M))).hom) := by
    -- This is the exactness component of the positive-stage inverse-limit sequence.
    exact hLimitData.1
  have hRightInj :
      Function.Injective
        ((limMap (positive_stage_stageMap (R := R) (I := I) (M := M))).hom) := by
    have hCompInj :
        Function.Injective
          (((positive_stage_completion_system_limit_iso
                (R := R) (I := I) (M := M)).hom ≫
              ModuleCat.ofHom
                (positive_stage_completion_retraction
                  (R := R) (I := I) (M := M) hcomplete) ≫
              (positive_stage_module_system_limit_iso
                (R := R) (I := I) (M := M)).inv).hom) := by
      -- The comparison is a composite of injective maps: two isomorphisms and the complete
      -- retraction from `(M^∧)^∧` to `M^∧`.
      exact
        (ConcreteCategory.bijective_of_isIso
          ((positive_stage_module_system_limit_iso
            (R := R) (I := I) (M := M)).inv)).1.comp
          ((positive_stage_completion_retraction_injective
            (R := R) (I := I) (M := M) hcomplete).comp
            (ConcreteCategory.bijective_of_isIso
              ((positive_stage_completion_system_limit_iso
                (R := R) (I := I) (M := M)).hom)).1)
    simpa [positive_stage_limMap_stageMap_eq_completion_retraction
      (R := R) (I := I) (M := M) hcomplete, Category.assoc] using hCompInj
  have hf_zero : limMap (positive_stage_left_ι (R := R) (I := I) (M := M)) = 0 := by
    -- Exactness forces the image of the left map into the kernel of the injective right map.
    apply ModuleCat.hom_ext
    ext x
    apply hRightInj
    simpa using
      LinearMap.congr_fun (Function.Exact.linearMap_comp_eq_zero hExact) x
  letI : Mono (limMap (positive_stage_left_ι (R := R) (I := I) (M := M))) := by
    -- This is the monomorphism component of the positive-stage inverse-limit sequence.
    exact hLimitData.2
  -- A monomorphism that is also zero can only start from the zero object.
  exact IsZero.of_mono_eq_zero
    (limMap (positive_stage_left_ι (R := R) (I := I) (M := M))) hf_zero


end
