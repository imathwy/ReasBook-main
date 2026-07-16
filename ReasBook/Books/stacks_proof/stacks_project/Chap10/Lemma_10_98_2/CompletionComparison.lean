import stacks_proof.stacks_project.Chap10.Lemma_10_98_2.QuotientKernelSystem

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

local notation "ModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat A
local notation "moduleInvLim" => (lim : ModuleInverseSystem ⥤ ModuleCat A)

/-- Helper for Lemma 10.98.2: extend a cone on the positive-stage quotient system of `limit M_`
by the trivial zeroth quotient. -/
noncomputable def limit_projection_quotient_family
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (s : Cone (limit_projection_quotient_system I M_)) (n : ℕ) :
    s.pt →ₗ[A]
      ((limit M_ : ModuleCat A) ⧸
        I ^ n • (⊤ : Submodule A (limit M_ : ModuleCat A))) :=
  if hn : 0 < n then
    (s.π.app (OrderDual.toDual ⟨n, hn⟩)).hom
  else
    0

/-- Helper for Lemma 10.98.2: the extended family from a positive-stage cone satisfies the full
compatibility relations defining the adic completion of `limit M_`. -/
theorem limit_projection_quotient_family_compat
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (s : Cone (limit_projection_quotient_system I M_))
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I (limit M_ : ModuleCat A) hmn ∘ₗ
        limit_projection_quotient_family I M_ s n =
      limit_projection_quotient_family I M_ s m := by
  by_cases hm : 0 < m
  · have hn : 0 < n := lt_of_lt_of_le hm hmn
    -- At positive stages this is exactly the cone compatibility.
    simpa [limit_projection_quotient_family, hm, hn, limit_projection_quotient_system,
      limit_projection_positive_stage_map, stagePNat] using
      congrArg ModuleCat.Hom.hom
        (s.w
          (homOfLE
            (show OrderDual.toDual ⟨n, hn⟩ ≤ OrderDual.toDual ⟨m, hm⟩ from hmn)))
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst hm0
    -- The zeroth quotient is the quotient by `⊤`, hence subsingleton.
    ext x
    have hs :
        Subsingleton
          (((limit M_ : ModuleCat A) ⧸
            I ^ 0 • (⊤ : Submodule A (limit M_ : ModuleCat A)))) := by
      simpa using
        (show Subsingleton
          (((limit M_ : ModuleCat A) ⧸
            (⊤ : Submodule A (limit M_ : ModuleCat A)))) from inferInstance)
    exact @Subsingleton.elim _ hs _ _

/-- Helper for Lemma 10.98.2: on a positive stage, the extended family is the given cone leg. -/
theorem limit_projection_quotient_family_pnat
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (s : Cone (limit_projection_quotient_system I M_)) (n : ℕ+) :
    limit_projection_quotient_family I M_ s (n : ℕ) =
      (s.π.app (OrderDual.toDual n)).hom := by
  -- Positive indices use the cone component directly.
  cases n with
  | mk n hn =>
      cases n with
      | zero =>
          cases Nat.lt_asymm hn hn
      | succ n =>
          rfl

/-- Helper for Lemma 10.98.2: the completion evaluation maps define a cone on the positive-stage
quotient system. -/
theorem limit_projection_quotient_completion_cone_naturality
    (I : Ideal A) (M_ : ModuleInverseSystem)
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    ((Functor.const (OrderDual ℕ+) ).obj
        (ModuleCat.of A (AdicCompletion I (limit M_ : ModuleCat A)))).map f ≫
      ModuleCat.ofHom
        (AdicCompletion.eval I (limit M_ : ModuleCat A) ((stagePNat j : ℕ))) =
      ModuleCat.ofHom
          (AdicCompletion.eval I (limit M_ : ModuleCat A) ((stagePNat i : ℕ))) ≫
        (limit_projection_quotient_system I M_).map f := by
  -- The completion coordinates already satisfy the quotient-transition compatibility.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa [limit_projection_quotient_system, limit_projection_positive_stage_map] using
    (AdicCompletion.transitionMap_comp_eval_apply
      (I := I) (M := (limit M_ : ModuleCat A))
      (hmn := show ((stagePNat j : ℕ+) : ℕ) ≤ ((stagePNat i : ℕ+) : ℕ) from
        (show stagePNat j ≤ stagePNat i from leOfHom f))
      (x := x))

/-- Helper for Lemma 10.98.2: the evaluation maps from the completion of `limit M_` to the
positive quotients form the comparison cone. -/
noncomputable abbrev limit_projection_quotient_completion_cone
    (I : Ideal A) (M_ : ModuleInverseSystem) :
    Cone (limit_projection_quotient_system I M_) :=
  { pt := ModuleCat.of A (AdicCompletion I (limit M_ : ModuleCat A))
    π :=
      { app := fun i ↦
          ModuleCat.ofHom
            (AdicCompletion.eval I (limit M_ : ModuleCat A) ((stagePNat i : ℕ)))
        naturality := fun {_ _} f ↦
          limit_projection_quotient_completion_cone_naturality I M_ f } }

/-- Helper for Lemma 10.98.2: maps into the adic completion are determined by all positive-stage
evaluations. -/
theorem limit_projection_quotient_completion_hom_ext
    (I : Ideal A) (M_ : ModuleInverseSystem)
    {X : ModuleCat A}
    {f g : X ⟶ (limit_projection_quotient_completion_cone I M_).pt}
    (hfg :
      ∀ n : ℕ+,
        f ≫ (limit_projection_quotient_completion_cone I M_).π.app (OrderDual.toDual n) =
          g ≫ (limit_projection_quotient_completion_cone I M_).π.app (OrderDual.toDual n)) :
    f = g := by
  -- Positive coordinates are given by the hypothesis, and stage `0` is subsingleton.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  cases n with
  | zero =>
      have hs :
          Subsingleton
            (((limit M_ : ModuleCat A) ⧸
              I ^ 0 • (⊤ : Submodule A (limit M_ : ModuleCat A)))) := by
        simpa using
          (show Subsingleton
            (((limit M_ : ModuleCat A) ⧸
              (⊤ : Submodule A (limit M_ : ModuleCat A)))) from inferInstance)
      exact @Subsingleton.elim _ hs _ _
  | succ n =>
      let i : ℕ+ := ⟨n + 1, Nat.succ_pos _⟩
      have hxy := congrArg ModuleCat.Hom.hom (hfg i)
      have hxyx := congrArg (fun k ↦ k x) hxy
      simpa [limit_projection_quotient_completion_cone, i] using hxyx

/-- Helper for Lemma 10.98.2: the universal lift from a cone on the positive-stage quotient system
to the completion cone is the completion lift of the extended compatible family. -/
noncomputable abbrev limit_projection_quotient_completion_lift
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (s : Cone (limit_projection_quotient_system I M_)) :
    s.pt ⟶ ModuleCat.of A (AdicCompletion I (limit M_ : ModuleCat A)) :=
  show s.pt ⟶ ModuleCat.of A (AdicCompletion I (limit M_ : ModuleCat A)) from
    ModuleCat.ofHom
      (AdicCompletion.lift I
        (limit_projection_quotient_family I M_ s)
        (limit_projection_quotient_family_compat I M_ s))

/-- Helper for Lemma 10.98.2: the universal lift to the completion cone has the expected stagewise
formula. -/
theorem limit_projection_quotient_completion_lift_fac
    (I : Ideal A) (M_ : ModuleInverseSystem) :
    ∀ (s : Cone (limit_projection_quotient_system I M_)) (i : OrderDual ℕ+),
      limit_projection_quotient_completion_lift I M_ s ≫
          (limit_projection_quotient_completion_cone I M_).π.app i =
        s.π.app i := by
  intro s i
  -- Evaluate the lifted compatible family at the positive stage `stagePNat i`.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa [limit_projection_quotient_completion_lift, limit_projection_quotient_completion_cone,
    limit_projection_quotient_family_pnat] using
    (AdicCompletion.eval_lift_apply I
      (limit_projection_quotient_family I M_ s)
      (limit_projection_quotient_family_compat I M_ s)
      ((stagePNat i : ℕ)) x)

/-- Helper for Lemma 10.98.2: the completion lift is uniquely determined by its positive-stage
evaluations. -/
theorem limit_projection_quotient_completion_lift_uniq
    (I : Ideal A) (M_ : ModuleInverseSystem) :
    ∀ (s : Cone (limit_projection_quotient_system I M_))
      (m : s.pt ⟶ (limit_projection_quotient_completion_cone I M_).pt),
      (∀ i, m ≫ (limit_projection_quotient_completion_cone I M_).π.app i = s.π.app i) →
        m = limit_projection_quotient_completion_lift I M_ s := by
  intro s m hm
  -- Positive-stage evaluations determine maps into the completion.
  refine limit_projection_quotient_completion_hom_ext (I := I) (M_ := M_)
      (f := m) (g := limit_projection_quotient_completion_lift I M_ s) ?_
  intro n
  have hmEval :
      m ≫ ModuleCat.ofHom (AdicCompletion.eval I (limit M_ : ModuleCat A) (n : ℕ)) =
        s.π.app (OrderDual.toDual n) := by
    simpa [limit_projection_quotient_completion_cone] using hm (OrderDual.toDual n)
  have hliftEval :
      limit_projection_quotient_completion_lift I M_ s ≫
          ModuleCat.ofHom (AdicCompletion.eval I (limit M_ : ModuleCat A) (n : ℕ)) =
        s.π.app (OrderDual.toDual n) := by
    simpa [limit_projection_quotient_completion_cone] using
      limit_projection_quotient_completion_lift_fac I M_ s (OrderDual.toDual n)
  exact hmEval.trans hliftEval.symm

/-- Helper for Lemma 10.98.2: the comparison cone from the completion of `limit M_` is limiting. -/
noncomputable def limit_projection_quotient_completion_isLimit
    (I : Ideal A) (M_ : ModuleInverseSystem) :
    IsLimit (limit_projection_quotient_completion_cone I M_) where
  lift := limit_projection_quotient_completion_lift I M_
  fac := limit_projection_quotient_completion_lift_fac I M_
  uniq := limit_projection_quotient_completion_lift_uniq I M_

/-- Helper for Lemma 10.98.2: the positive-stage quotient system of `limit M_` has inverse limit
the adic completion of `limit M_`. -/
noncomputable abbrev limit_projection_quotient_limitCone
    (I : Ideal A) (M_ : ModuleInverseSystem) :
    LimitCone (limit_projection_quotient_system I M_) :=
  { cone := limit_projection_quotient_completion_cone I M_
    isLimit := limit_projection_quotient_completion_isLimit I M_ }

/-- Helper for Lemma 10.98.2: the positive-stage quotient system attached to `limit M_` is
canonically identified with the adic completion of `limit M_`. -/
noncomputable abbrev limit_projection_quotient_limit_iso
    (I : Ideal A) (M_ : ModuleInverseSystem) :
    limit (limit_projection_quotient_system I M_) ≅
      ModuleCat.of A (AdicCompletion I (limit M_ : ModuleCat A)) :=
  show limit (limit_projection_quotient_system I M_) ≅
      ModuleCat.of A (AdicCompletion I (limit M_ : ModuleCat A)) from
    limit.isoLimitCone (limit_projection_quotient_limitCone I M_)

/-- Helper for Lemma 10.98.2: the inverse of the quotient-system limit identification evaluates to
the canonical completion quotient map at each positive stage. -/
theorem limit_projection_quotient_limit_iso_inv_π
    (I : Ideal A) (M_ : ModuleInverseSystem) (i : OrderDual ℕ+) :
    (limit_projection_quotient_limit_iso I M_).inv ≫
        limit.π (limit_projection_quotient_system I M_) i =
      ModuleCat.ofHom
        (AdicCompletion.eval I (limit M_ : ModuleCat A) ((stagePNat i : ℕ))) := by
  -- This is the projection formula for the canonical `limit.isoLimitCone`.
  simpa [limit_projection_quotient_limit_iso] using
    limit.isoLimitCone_inv_π (limit_projection_quotient_limitCone I M_) i

/-- Helper for Lemma 10.98.2: the forward quotient-system limit identification has the expected
positive-stage projection formula. -/
theorem limit_projection_quotient_limit_iso_hom_π
    (I : Ideal A) (M_ : ModuleInverseSystem) (i : OrderDual ℕ+) :
    (limit_projection_quotient_limit_iso I M_).hom ≫
        ModuleCat.ofHom
          (AdicCompletion.eval I (limit M_ : ModuleCat A) ((stagePNat i : ℕ))) =
      limit.π (limit_projection_quotient_system I M_) i := by
  -- This is the companion projection formula for `limit.isoLimitCone`.
  simpa [limit_projection_quotient_limit_iso] using
    limit.isoLimitCone_hom_π (limit_projection_quotient_limitCone I M_) i

/-- Helper for Lemma 10.98.2: the limit map on the quotient system is exactly the completion-to-
inverse-limit comparison after identifying the middle limit with the adic completion. -/
theorem quotient_limit_map_eq_completion_to_inverse_limit
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hStage :
      ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥) :
    limMap (limit_projection_stageMap I M_ hStage) =
      (limit_projection_quotient_limit_iso I M_).hom ≫
        completion_to_inverse_limit_hom I M_ hStage := by
  -- Compare both sides after every stage projection of the target inverse limit.
  apply limit.hom_ext
  intro i
  apply ModuleCat.hom_ext
  ext x
  have hleft' :
      limMap (limit_projection_stageMap I M_ hStage) ≫ limit.π M_ i =
        limit.π (limit_projection_quotient_system I M_) i ≫
          (limit_projection_stageMap I M_ hStage).app i := by
    exact limMap_π (α := limit_projection_stageMap I M_ hStage) (j := i)
  have hleftMap := congrArg ModuleCat.Hom.hom hleft'
  have hleft :
      (limit.π M_ i).hom ((limMap (limit_projection_stageMap I M_ hStage)).hom x) =
        ((limit_projection_stageMap I M_ hStage).app i).hom
          ((limit.π (limit_projection_quotient_system I M_) i).hom x) := by
    exact congrArg (fun f ↦ f x) hleftMap
  have hx :
      AdicCompletion.eval I (limit M_ : ModuleCat A) ((stagePNat i : ℕ))
          (((limit_projection_quotient_limit_iso I M_).hom x)) =
        (limit.π (limit_projection_quotient_system I M_) i).hom x := by
    simpa [Category.assoc, stagePNat] using
      congrArg (fun g ↦ g x) (limit_projection_quotient_limit_iso_hom_π I M_ i)
  let n : ℕ+ := stagePNat i
  -- Both stagewise formulas reduce to the same descended quotient map.
  calc
    (limit.π M_ i).hom ((limMap (limit_projection_stageMap I M_ hStage)).hom x)
        = ((limit_projection_stageMap I M_ hStage).app i).hom
            ((limit.π (limit_projection_quotient_system I M_) i).hom x) := hleft
    _ = ((limit_projection_stageMap I M_ hStage).app i).hom
          (AdicCompletion.eval I (limit M_ : ModuleCat A) ((stagePNat i : ℕ))
            (((limit_projection_quotient_limit_iso I M_).hom x))) := by
              rw [← hx]
    _ = (limit.π M_ i).hom
          ((completion_to_inverse_limit_hom I M_ hStage).hom
            (((limit_projection_quotient_limit_iso I M_).hom x))) := by
              simpa [limit_projection_stageMap, stagePNat, n] using
                (completion_to_inverse_limit_π_apply I M_ hStage n
                  (((limit_projection_quotient_limit_iso I M_).hom x))).symm

/-- Helper for Lemma 10.98.2: if `limit M_` is `I`-adically complete, then the completion-to-
inverse-limit comparison is bijective. -/
theorem completion_to_inverse_limit_bijective_of_complete
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hStage :
      ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥)
    (hcomplete : IsAdicComplete I (limit M_ : ModuleCat A)) :
    Function.Bijective (completion_to_inverse_limit I M_ hStage) := by
  let L := (limit M_ : ModuleCat A)
  have hleft :
      Function.LeftInverse (completion_to_inverse_limit I M_ hStage) (AdicCompletion.of I L) := by
    intro x
    -- Forget the categorical splitting to obtain the pointwise left inverse.
    simpa [completion_to_inverse_limit, LinearMap.comp_apply] using
      congrArg (fun g ↦ g x) (completion_to_inverse_limit_leftInverse_linear I M_ hStage)
  have hof :
      Function.Bijective (AdicCompletion.of I L) := by
    simpa [L] using (AdicCompletion.of_bijective_iff (I := I) (M := L)).2 hcomplete
  have hright :
      Function.RightInverse (completion_to_inverse_limit I M_ hStage) (AdicCompletion.of I L) :=
    hleft.rightInverse_of_surjective hof.surjective
  exact ⟨hright.injective, hleft.surjective⟩

/-- Helper for Lemma 10.98.2: the stage-annihilation witness is proposition-valued, so any two
proofs are equal. -/
theorem stage_annihilation_witness_eq
    {I : Ideal A} {M_ : ModuleInverseSystem}
    {h₁ h₂ :
      ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥} :
    h₁ = h₂ := by
  -- This is the proof-irrelevance step needed when the short-exact bridge is eventually
  -- transported across the functor-universe mismatch.
  exact Subsingleton.elim _ _

/-- Helper for Lemma 10.98.2: a typed adapter for the source-proof short complex, packaged with
the exact `ShortComplex ModuleInverseSystem` type expected by the inverse-limit bridge. -/
abbrev limit_projection_quotient_shortComplex_input
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    ShortComplex ModuleInverseSystem :=
  limit_projection_quotient_shortComplex I M_
    (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer)

/-- Helper for Lemma 10.98.2: the adapter short complex is short exact stagewise, exactly as in the
source-proof kernel short exact rows. -/
theorem limit_projection_quotient_shortComplex_input_shortExact
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    (limit_projection_quotient_shortComplex_input I M_ hSurj hKer).ShortExact := by
  -- The adapter is definitionally the stagewise short exact sequence already proved above.
  simpa [limit_projection_quotient_shortComplex_input] using
    limit_projection_quotient_shortComplex_shortExact I M_ hSurj hKer

/-- Helper for Lemma 10.98.2: the left term of the adapter short complex is Mittag-Leffler. -/
theorem limit_projection_kernel_system_isMittagLeffler_input
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    (((limit_projection_quotient_shortComplex_input I M_ hSurj hKer).X₁) ⋙
      forget (ModuleCat A)).IsMittagLeffler := by
  -- The adapter’s left object is definitionally the kernel inverse system from the source proof.
  simpa [limit_projection_quotient_shortComplex_input] using
    limit_projection_kernel_system_isMittagLeffler_of_successive_ideal_power_quotients
      I M_ hSurj hKer

/-- Helper for Lemma 10.98.2: the left map of the frozen source-proof short complex is exactly
the kernel inclusion morphism of inverse systems. -/
theorem limit_projection_quotient_shortComplex_input_f_eq
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    (limit_projection_quotient_shortComplex_input I M_ hSurj hKer).f =
      limit_projection_kernel_ι I M_
        (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer) := by
  -- Unfold the adapter once: its left map is definitionally the kernel inclusion.
  rfl

/-- Helper for Lemma 10.98.2: the right map of the frozen source-proof short complex is exactly
the descended stage-map morphism of inverse systems. -/
theorem limit_projection_quotient_shortComplex_input_g_eq
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    (limit_projection_quotient_shortComplex_input I M_ hSurj hKer).g =
      limit_projection_stageMap I M_
        (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer) := by
  -- Unfold the adapter once: its right map is definitionally the descended stage-map system.
  rfl

/-- Helper for Lemma 10.98.2: the forgetful functor from `A`-modules to abelian groups used in
the local replay of Lemma `10.87.1`. -/
abbrev limit_projection_forgetToAbelianGroup : ModuleCat A ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat A) AddCommGrpCat.{u}

/-- Helper for Lemma 10.98.2: the ambient category of abelian-group inverse systems over `ℕ+`. -/
abbrev limit_projection_AbelianGroupInverseSystem : Type (u + 1) :=
  OrderDual ℕ+ ⥤ AddCommGrpCat.{u}

/-- Helper for Lemma 10.98.2: the inverse-limit functor on abelian-group inverse systems. -/
abbrev limit_projection_abelianInvLim :
    limit_projection_AbelianGroupInverseSystem ⥤ AddCommGrpCat.{u} where
  obj F := limit F
  map α := limMap α
  map_id F := by
    -- This is the standard `lim` functor identity law specialized to the forgotten system.
    apply limit.hom_ext
    intro j
    simp
  map_comp α β := by
    -- The comparison is checked coordinatewise on each stage projection.
    apply limit.hom_ext
    intro j
    simp [Category.assoc]

/-- Helper for Lemma 10.98.2: whiskering by the forgetful functor turns module inverse systems
into abelian-group inverse systems. -/
abbrev limit_projection_forgetInverseSystemFunctor :
    ModuleInverseSystem ⥤ limit_projection_AbelianGroupInverseSystem where
  obj F := F ⋙ limit_projection_forgetToAbelianGroup
  map α := Functor.whiskerRight α limit_projection_forgetToAbelianGroup
  map_id F := by
    -- Whiskering the identity natural transformation is again the identity.
    rfl
  map_comp α β := by
    -- Whiskering preserves composition definitionally.
    rfl

/-- Helper for Lemma 10.98.2: the inverse-limit functor on the exact source category used by the
frozen short complex. -/
abbrev limit_projection_moduleInvLim : ModuleInverseSystem ⥤ ModuleCat A where
  obj F := limit F
  map α := limMap α
  map_id F := by
    -- This is the standard `lim` functor identity law on module inverse systems.
    apply limit.hom_ext
    intro j
    simp
  map_comp α β := by
    -- The comparison is checked coordinatewise on the universal projections.
    apply limit.hom_ext
    intro j
    simp [Category.assoc]

/-- Helper for Lemma 10.98.2: the universe-stable inverse-limit functor still preserves zero
morphisms, so it can be used with `ShortComplex.map`. -/
instance limit_projection_moduleInvLim_preservesZeroMorphisms :
    (limit_projection_moduleInvLim (A := A)).PreservesZeroMorphisms where
  map_zero X Y := by
    -- A morphism of inverse limits is zero once all its stagewise projections are zero.
    apply limit.hom_ext
    intro j
    simp [limit_projection_moduleInvLim]

/-- Helper for Lemma 10.98.2: the canonical comparison between forgetting after inverse limits and
taking inverse limits after forgetting commutes with every morphism of inverse systems. -/
theorem limit_projection_preservesLimitIso_hom_limMap_forget
    {X Y : ModuleInverseSystem} (α : X ⟶ Y) :
    (preservesLimitIso limit_projection_forgetToAbelianGroup X).hom ≫
        limMap (Functor.whiskerRight α limit_projection_forgetToAbelianGroup) =
      limit_projection_forgetToAbelianGroup.map (limMap α) ≫
        (preservesLimitIso limit_projection_forgetToAbelianGroup Y).hom := by
  -- Compare both sides after evaluating at each stage of the inverse system.
  apply limit.hom_ext
  intro i
  have hmid :
      (preservesLimitIso limit_projection_forgetToAbelianGroup X).hom ≫
          limMap (Functor.whiskerRight α limit_projection_forgetToAbelianGroup) ≫
            limit.π (Y ⋙ limit_projection_forgetToAbelianGroup) i =
        limit_projection_forgetToAbelianGroup.map (limMap α ≫ limit.π Y i) := by
    calc
      (preservesLimitIso limit_projection_forgetToAbelianGroup X).hom ≫
          limMap (Functor.whiskerRight α limit_projection_forgetToAbelianGroup) ≫
            limit.π (Y ⋙ limit_projection_forgetToAbelianGroup) i
        = (preservesLimitIso limit_projection_forgetToAbelianGroup X).hom ≫
            limit.π (X ⋙ limit_projection_forgetToAbelianGroup) i ≫
              (Functor.whiskerRight α limit_projection_forgetToAbelianGroup).app i := by
                simpa [Category.assoc] using
                  congrArg
                    (fun t ↦
                      (preservesLimitIso limit_projection_forgetToAbelianGroup X).hom ≫ t)
                    (limMap_π (Functor.whiskerRight α limit_projection_forgetToAbelianGroup) i)
      _ = limit_projection_forgetToAbelianGroup.map (limit.π X i) ≫
            (Functor.whiskerRight α limit_projection_forgetToAbelianGroup).app i := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ t ≫ (Functor.whiskerRight α limit_projection_forgetToAbelianGroup).app i)
                  (preservesLimitIso_hom_π
                    (G := limit_projection_forgetToAbelianGroup) (F := X) i)
      _ = limit_projection_forgetToAbelianGroup.map (limit.π X i) ≫
            limit_projection_forgetToAbelianGroup.map (α.app i) := by
              rfl
      _ = limit_projection_forgetToAbelianGroup.map (limit.π X i ≫ α.app i) := by
              rw [← limit_projection_forgetToAbelianGroup.map_comp]
      _ = limit_projection_forgetToAbelianGroup.map (limMap α ≫ limit.π Y i) := by
              rw [limMap_π]
  have hfinal :
      limit_projection_forgetToAbelianGroup.map (limMap α ≫ limit.π Y i) =
        (limit_projection_forgetToAbelianGroup.map (limMap α) ≫
            (preservesLimitIso limit_projection_forgetToAbelianGroup Y).hom) ≫
          limit.π (Y ⋙ limit_projection_forgetToAbelianGroup) i := by
    rw [limit_projection_forgetToAbelianGroup.map_comp]
    have hπY :
        limit_projection_forgetToAbelianGroup.map (limit.π Y i) =
          (preservesLimitIso limit_projection_forgetToAbelianGroup Y).hom ≫
            limit.π (Y ⋙ limit_projection_forgetToAbelianGroup) i := by
      simpa using
        (preservesLimitIso_hom_π
          (G := limit_projection_forgetToAbelianGroup) (F := Y) i).symm
    rw [hπY]
    simp [Category.assoc]
  exact hmid.trans hfinal

/-- Helper for Lemma 10.98.2: the local forgetful functor on inverse systems acts on morphisms by
whiskering with the module-to-abelian-group forgetful functor. -/
theorem limit_projection_forgetInverseSystemFunctor_map_eq
    {X Y : ModuleInverseSystem} (α : X ⟶ Y) :
    (limit_projection_forgetInverseSystemFunctor (A := A)).map α =
      Functor.whiskerRight α limit_projection_forgetToAbelianGroup := by
  rfl


end
