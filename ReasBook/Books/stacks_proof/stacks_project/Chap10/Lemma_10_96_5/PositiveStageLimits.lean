import stacks_proof.stacks_project.Chap10.Lemma_10_96_5.StageSystems

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

/-- Helper for Lemma 10.96.5: extend a cone on the positive-stage system `M / I ^ n M` by the
trivial zeroth stage. -/
private noncomputable def positive_stage_module_family
    (s : Cone (positive_stage_module_system (R := R) (I := I) (M := M))) (n : ℕ) :
    s.pt →ₗ[R] (M ⧸ I ^ n • (⊤ : Submodule R M)) :=
  if hn : 0 < n then
    (s.π.app (OrderDual.toDual ⟨n, hn⟩)).hom
  else
    0

/-- Helper for Lemma 10.96.5: the extended positive-stage module family satisfies the full
compatibility relations defining the adic completion of `M`. -/
private theorem positive_stage_module_family_compat
    (s : Cone (positive_stage_module_system (R := R) (I := I) (M := M)))
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I M hmn ∘ₗ
        positive_stage_module_family (R := R) (I := I) (M := M) s n =
      positive_stage_module_family (R := R) (I := I) (M := M) s m := by
  by_cases hm : 0 < m
  · have hn : 0 < n := lt_of_lt_of_le hm hmn
    -- Positive stages are exactly the cone-compatibility relations.
    simpa [positive_stage_module_family, hm, hn, positive_stage_module_system,
      positive_stage_module_map, stagePNat] using
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
          (M ⧸ I ^ 0 • (⊤ : Submodule R M)) := by
      simpa using
        (show Subsingleton (M ⧸ (⊤ : Submodule R M)) from inferInstance)
    exact @Subsingleton.elim _ hs _ _

/-- Helper for Lemma 10.96.5: on a positive stage, the extended module family is the original
cone leg. -/
private theorem positive_stage_module_family_pnat
    (s : Cone (positive_stage_module_system (R := R) (I := I) (M := M))) (n : ℕ+) :
    positive_stage_module_family (R := R) (I := I) (M := M) s (n : ℕ) =
      (s.π.app (OrderDual.toDual n)).hom := by
  cases n with
  | mk n hn =>
      cases n with
      | zero =>
          cases Nat.lt_asymm hn hn
      | succ n =>
          rfl

/-- Helper for Lemma 10.96.5: the evaluation maps on `AdicCompletion I M` define a cone on the
positive-stage inverse system `M / I ^ n M`. -/
private theorem positive_stage_module_completion_cone_naturality
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    ((Functor.const (OrderDual ℕ+)).obj (ModuleCat.of R (AdicCompletion I M))).map f ≫
      ModuleCat.ofHom (AdicCompletion.eval I M ((stagePNat j : ℕ))) =
        ModuleCat.ofHom (AdicCompletion.eval I M ((stagePNat i : ℕ))) ≫
          (positive_stage_module_system (R := R) (I := I) (M := M)).map f := by
  -- The adic completion coordinates already satisfy the transition compatibility.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa [positive_stage_module_system, positive_stage_module_map] using
    (AdicCompletion.transitionMap_comp_eval_apply
      (I := I) (M := M)
      (hmn := show ((stagePNat j : ℕ+) : ℕ) ≤ ((stagePNat i : ℕ+) : ℕ) from
        (show stagePNat j ≤ stagePNat i from leOfHom f))
      (x := x))

/-- Helper for Lemma 10.96.5: the completion of `M` maps to the positive-stage quotient system
via its evaluation maps. -/
private noncomputable abbrev positive_stage_module_completion_cone :
    Cone (positive_stage_module_system (R := R) (I := I) (M := M)) :=
  { pt := ModuleCat.of R (AdicCompletion I M)
    π :=
      { app := fun i ↦ ModuleCat.ofHom (AdicCompletion.eval I M ((stagePNat i : ℕ)))
        naturality := fun {_ _} f ↦
          positive_stage_module_completion_cone_naturality (R := R) (I := I) (M := M) f } }

/-- Helper for Lemma 10.96.5: maps into `AdicCompletion I M` are determined by all positive-stage
evaluation maps. -/
private theorem positive_stage_module_completion_hom_ext
    {X : ModuleCat R}
    {f g : X ⟶ (positive_stage_module_completion_cone (R := R) (I := I) (M := M)).pt}
    (hfg :
      ∀ n : ℕ+,
        f ≫ (positive_stage_module_completion_cone (R := R) (I := I) (M := M)).π.app
            (OrderDual.toDual n) =
          g ≫ (positive_stage_module_completion_cone (R := R) (I := I) (M := M)).π.app
            (OrderDual.toDual n)) :
    f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  cases n with
  | zero =>
      have hs : Subsingleton (M ⧸ I ^ 0 • (⊤ : Submodule R M)) := by
        simpa using (show Subsingleton (M ⧸ (⊤ : Submodule R M)) from inferInstance)
      exact @Subsingleton.elim _ hs _ _
  | succ n =>
      let i : ℕ+ := ⟨n + 1, Nat.succ_pos _⟩
      have hxy := congrArg ModuleCat.Hom.hom (hfg i)
      have hxyx := congrArg (fun k ↦ k x) hxy
      simpa [positive_stage_module_completion_cone, i] using hxyx

/-- Helper for Lemma 10.96.5: the universal lift from a cone on the positive-stage module system
to the completion of `M`. -/
private noncomputable abbrev positive_stage_module_completion_lift
    (s : Cone (positive_stage_module_system (R := R) (I := I) (M := M))) :
    s.pt ⟶ ModuleCat.of R (AdicCompletion I M) :=
  show s.pt ⟶ ModuleCat.of R (AdicCompletion I M) from
    ModuleCat.ofHom
      (AdicCompletion.lift I
        (positive_stage_module_family (R := R) (I := I) (M := M) s)
        (positive_stage_module_family_compat (R := R) (I := I) (M := M) s))

/-- Helper for Lemma 10.96.5: the universal lift to the completion of `M` has the expected
positive-stage formula. -/
private theorem positive_stage_module_completion_lift_fac :
    ∀ (s : Cone (positive_stage_module_system (R := R) (I := I) (M := M)))
      (i : OrderDual ℕ+),
      positive_stage_module_completion_lift (R := R) (I := I) (M := M) s ≫
          (positive_stage_module_completion_cone (R := R) (I := I) (M := M)).π.app i =
        s.π.app i := by
  intro s i
  -- Evaluating the lifted compatible family at a positive stage recovers the original cone leg.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa [positive_stage_module_completion_lift, positive_stage_module_completion_cone,
    positive_stage_module_family_pnat] using
    (AdicCompletion.eval_lift_apply I
      (positive_stage_module_family (R := R) (I := I) (M := M) s)
      (positive_stage_module_family_compat (R := R) (I := I) (M := M) s)
      ((stagePNat i : ℕ)) x)

/-- Helper for Lemma 10.96.5: the completion lift is uniquely determined by its positive-stage
evaluations. -/
private theorem positive_stage_module_completion_lift_uniq :
    ∀ (s : Cone (positive_stage_module_system (R := R) (I := I) (M := M)))
      (m : s.pt ⟶ (positive_stage_module_completion_cone (R := R) (I := I) (M := M)).pt),
      (∀ i,
          m ≫ (positive_stage_module_completion_cone (R := R) (I := I) (M := M)).π.app i =
            s.π.app i) →
        m = positive_stage_module_completion_lift (R := R) (I := I) (M := M) s := by
  intro s m hm
  refine positive_stage_module_completion_hom_ext (R := R) (I := I) (M := M)
      (f := m) (g := positive_stage_module_completion_lift (R := R) (I := I) (M := M) s) ?_
  intro n
  have hmEval :
      m ≫ ModuleCat.ofHom (AdicCompletion.eval I M (n : ℕ)) =
        s.π.app (OrderDual.toDual n) := by
    simpa [positive_stage_module_completion_cone] using hm (OrderDual.toDual n)
  have hliftEval :
      positive_stage_module_completion_lift (R := R) (I := I) (M := M) s ≫
          ModuleCat.ofHom (AdicCompletion.eval I M (n : ℕ)) =
        s.π.app (OrderDual.toDual n) := by
    simpa [positive_stage_module_completion_cone] using
      positive_stage_module_completion_lift_fac (R := R) (I := I) (M := M) s
        (OrderDual.toDual n)
  exact hmEval.trans hliftEval.symm

/-- Helper for Lemma 10.96.5: the evaluation cone from `AdicCompletion I M` is limiting for the
positive-stage system `M / I ^ n M`. -/
private noncomputable def positive_stage_module_completion_isLimit :
    IsLimit (positive_stage_module_completion_cone (R := R) (I := I) (M := M)) where
  lift := positive_stage_module_completion_lift (R := R) (I := I) (M := M)
  fac := positive_stage_module_completion_lift_fac (R := R) (I := I) (M := M)
  uniq := positive_stage_module_completion_lift_uniq (R := R) (I := I) (M := M)

/-- Helper for Lemma 10.96.5: the positive-stage system `M / I ^ n M` has inverse limit
`AdicCompletion I M`. -/
private noncomputable abbrev positive_stage_module_completion_limitCone :
    LimitCone (positive_stage_module_system (R := R) (I := I) (M := M)) :=
  { cone := positive_stage_module_completion_cone (R := R) (I := I) (M := M)
    isLimit := positive_stage_module_completion_isLimit (R := R) (I := I) (M := M) }

/-- Helper for Lemma 10.96.5: the positive-stage inverse limit `lim_n M / I ^ n M` is canonically
identified with `AdicCompletion I M`. -/
noncomputable abbrev positive_stage_module_system_limit_iso :
    limit (positive_stage_module_system (R := R) (I := I) (M := M)) ≅
      ModuleCat.of R (AdicCompletion I M) :=
  limit.isoLimitCone (positive_stage_module_completion_limitCone (R := R) (I := I) (M := M))

/-- Helper for Lemma 10.96.5: the inverse of the positive-stage module limit identification
evaluates to the canonical completion projection at each stage. -/
theorem positive_stage_module_system_limit_iso_inv_π (i : OrderDual ℕ+) :
    (positive_stage_module_system_limit_iso (R := R) (I := I) (M := M)).inv ≫
        limit.π (positive_stage_module_system (R := R) (I := I) (M := M)) i =
      ModuleCat.ofHom (AdicCompletion.eval I M ((stagePNat i : ℕ))) := by
  -- This is the projection formula for the canonical `limit.isoLimitCone`.
  simpa [positive_stage_module_system_limit_iso] using
    limit.isoLimitCone_inv_π
      (positive_stage_module_completion_limitCone (R := R) (I := I) (M := M)) i

/-- Helper for Lemma 10.96.5: the forward positive-stage module limit identification has the
expected stage projection formula. -/
theorem positive_stage_module_system_limit_iso_hom_π (i : OrderDual ℕ+) :
    (positive_stage_module_system_limit_iso (R := R) (I := I) (M := M)).hom ≫
        ModuleCat.ofHom (AdicCompletion.eval I M ((stagePNat i : ℕ))) =
      limit.π (positive_stage_module_system (R := R) (I := I) (M := M)) i := by
  -- This is the companion projection formula for `limit.isoLimitCone`.
  simpa [positive_stage_module_system_limit_iso] using
    limit.isoLimitCone_hom_π
      (positive_stage_module_completion_limitCone (R := R) (I := I) (M := M)) i

/-- Helper for Lemma 10.96.5: extend a cone on the positive-stage system
`M^∧ / I ^ n M^∧` by the trivial zeroth stage. -/
private noncomputable def positive_stage_completion_family
    (s : Cone (positive_stage_completion_system (R := R) (I := I) (M := M))) (n : ℕ) :
    s.pt →ₗ[R]
      (AdicCompletion I M ⧸ I ^ n • (⊤ : Submodule R (AdicCompletion I M))) :=
  if hn : 0 < n then
    (s.π.app (OrderDual.toDual ⟨n, hn⟩)).hom
  else
    0

/-- Helper for Lemma 10.96.5: the extended positive-stage completion family satisfies the full
compatibility relations defining the adic completion of `AdicCompletion I M`. -/
private theorem positive_stage_completion_family_compat
    (s : Cone (positive_stage_completion_system (R := R) (I := I) (M := M)))
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I (AdicCompletion I M) hmn ∘ₗ
        positive_stage_completion_family (R := R) (I := I) (M := M) s n =
      positive_stage_completion_family (R := R) (I := I) (M := M) s m := by
  by_cases hm : 0 < m
  · have hn : 0 < n := lt_of_lt_of_le hm hmn
    -- Positive stages are exactly the cone-compatibility relations.
    simpa [positive_stage_completion_family, hm, hn, positive_stage_completion_system,
      positive_stage_completion_map, stagePNat] using
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
          (AdicCompletion I M ⧸ I ^ 0 • (⊤ : Submodule R (AdicCompletion I M))) := by
      simpa using
        (show Subsingleton
          (AdicCompletion I M ⧸ (⊤ : Submodule R (AdicCompletion I M))) from inferInstance)
    exact @Subsingleton.elim _ hs _ _

/-- Helper for Lemma 10.96.5: on a positive stage, the extended completion family is the original
cone leg. -/
private theorem positive_stage_completion_family_pnat
    (s : Cone (positive_stage_completion_system (R := R) (I := I) (M := M))) (n : ℕ+) :
    positive_stage_completion_family (R := R) (I := I) (M := M) s (n : ℕ) =
      (s.π.app (OrderDual.toDual n)).hom := by
  cases n with
  | mk n hn =>
      cases n with
      | zero =>
          cases Nat.lt_asymm hn hn
      | succ n =>
          rfl

/-- Helper for Lemma 10.96.5: the evaluation maps on `(AdicCompletion I M)^∧` define a cone on
the positive-stage inverse system `M^∧ / I ^ n M^∧`. -/
private theorem positive_stage_completion_completion_cone_naturality
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    ((Functor.const (OrderDual ℕ+)).obj
        (ModuleCat.of R (AdicCompletion I (AdicCompletion I M)))).map f ≫
      ModuleCat.ofHom (AdicCompletion.eval I (AdicCompletion I M) ((stagePNat j : ℕ))) =
        ModuleCat.ofHom (AdicCompletion.eval I (AdicCompletion I M) ((stagePNat i : ℕ))) ≫
          (positive_stage_completion_system (R := R) (I := I) (M := M)).map f := by
  -- The completion-of-the-completion coordinates already satisfy the transition compatibility.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa [positive_stage_completion_system, positive_stage_completion_map] using
    (AdicCompletion.transitionMap_comp_eval_apply
      (I := I) (M := AdicCompletion I M)
      (hmn := show ((stagePNat j : ℕ+) : ℕ) ≤ ((stagePNat i : ℕ+) : ℕ) from
        (show stagePNat j ≤ stagePNat i from leOfHom f))
      (x := x))

/-- Helper for Lemma 10.96.5: the completion of `AdicCompletion I M` maps to the positive-stage
quotient system of `AdicCompletion I M` via its evaluation maps. -/
private noncomputable abbrev positive_stage_completion_completion_cone :
    Cone (positive_stage_completion_system (R := R) (I := I) (M := M)) :=
  { pt := ModuleCat.of R (AdicCompletion I (AdicCompletion I M))
    π :=
      { app := fun i ↦
          ModuleCat.ofHom (AdicCompletion.eval I (AdicCompletion I M) ((stagePNat i : ℕ)))
        naturality := fun {_ _} f ↦
          positive_stage_completion_completion_cone_naturality
            (R := R) (I := I) (M := M) f } }

/-- Helper for Lemma 10.96.5: maps into `(AdicCompletion I M)^∧` are determined by all
positive-stage evaluations. -/
private theorem positive_stage_completion_completion_hom_ext
    {X : ModuleCat R}
    {f g : X ⟶ (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)).pt}
    (hfg :
      ∀ n : ℕ+,
        f ≫ (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)).π.app
            (OrderDual.toDual n) =
          g ≫ (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)).π.app
            (OrderDual.toDual n)) :
    f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  cases n with
  | zero =>
      have hs :
          Subsingleton
            (AdicCompletion I M ⧸ I ^ 0 • (⊤ : Submodule R (AdicCompletion I M))) := by
        simpa using
          (show Subsingleton
            (AdicCompletion I M ⧸ (⊤ : Submodule R (AdicCompletion I M))) from inferInstance)
      exact @Subsingleton.elim _ hs _ _
  | succ n =>
      let i : ℕ+ := ⟨n + 1, Nat.succ_pos _⟩
      have hxy := congrArg ModuleCat.Hom.hom (hfg i)
      have hxyx := congrArg (fun k ↦ k x) hxy
      simpa [positive_stage_completion_completion_cone, i] using hxyx

/-- Helper for Lemma 10.96.5: the universal lift from a cone on the positive-stage completion
system to the completion of `AdicCompletion I M`. -/
private noncomputable abbrev positive_stage_completion_completion_lift
    (s : Cone (positive_stage_completion_system (R := R) (I := I) (M := M))) :
    s.pt ⟶ ModuleCat.of R (AdicCompletion I (AdicCompletion I M)) :=
  show s.pt ⟶ ModuleCat.of R (AdicCompletion I (AdicCompletion I M)) from
    ModuleCat.ofHom
      (AdicCompletion.lift I
        (positive_stage_completion_family (R := R) (I := I) (M := M) s)
        (positive_stage_completion_family_compat (R := R) (I := I) (M := M) s))

/-- Helper for Lemma 10.96.5: the universal lift to the completion of `AdicCompletion I M` has
the expected positive-stage formula. -/
private theorem positive_stage_completion_completion_lift_fac :
    ∀ (s : Cone (positive_stage_completion_system (R := R) (I := I) (M := M)))
      (i : OrderDual ℕ+),
      positive_stage_completion_completion_lift (R := R) (I := I) (M := M) s ≫
          (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)).π.app i =
        s.π.app i := by
  intro s i
  -- Evaluating the lifted compatible family at a positive stage recovers the original cone leg.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa [positive_stage_completion_completion_lift, positive_stage_completion_completion_cone,
    positive_stage_completion_family_pnat] using
    (AdicCompletion.eval_lift_apply I
      (positive_stage_completion_family (R := R) (I := I) (M := M) s)
      (positive_stage_completion_family_compat (R := R) (I := I) (M := M) s)
      ((stagePNat i : ℕ)) x)

/-- Helper for Lemma 10.96.5: the completion lift is uniquely determined by its positive-stage
evaluations. -/
private theorem positive_stage_completion_completion_lift_uniq :
    ∀ (s : Cone (positive_stage_completion_system (R := R) (I := I) (M := M)))
      (m : s.pt ⟶
        (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)).pt),
      (∀ i,
          m ≫ (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)).π.app i =
            s.π.app i) →
        m = positive_stage_completion_completion_lift (R := R) (I := I) (M := M) s := by
  intro s m hm
  refine positive_stage_completion_completion_hom_ext (R := R) (I := I) (M := M)
      (f := m)
      (g := positive_stage_completion_completion_lift (R := R) (I := I) (M := M) s) ?_
  intro n
  have hmEval :
      m ≫ ModuleCat.ofHom (AdicCompletion.eval I (AdicCompletion I M) (n : ℕ)) =
        s.π.app (OrderDual.toDual n) := by
    simpa [positive_stage_completion_completion_cone] using hm (OrderDual.toDual n)
  have hliftEval :
      positive_stage_completion_completion_lift (R := R) (I := I) (M := M) s ≫
          ModuleCat.ofHom (AdicCompletion.eval I (AdicCompletion I M) (n : ℕ)) =
        s.π.app (OrderDual.toDual n) := by
    simpa [positive_stage_completion_completion_cone] using
      positive_stage_completion_completion_lift_fac (R := R) (I := I) (M := M) s
        (OrderDual.toDual n)
  exact hmEval.trans hliftEval.symm

/-- Helper for Lemma 10.96.5: the evaluation cone from `(AdicCompletion I M)^∧` is limiting for
the positive-stage system `M^∧ / I ^ n M^∧`. -/
private noncomputable def positive_stage_completion_completion_isLimit :
    IsLimit (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)) where
  lift := positive_stage_completion_completion_lift (R := R) (I := I) (M := M)
  fac := positive_stage_completion_completion_lift_fac (R := R) (I := I) (M := M)
  uniq := positive_stage_completion_completion_lift_uniq (R := R) (I := I) (M := M)

/-- Helper for Lemma 10.96.5: the positive-stage system `M^∧ / I ^ n M^∧` has inverse limit
`(AdicCompletion I M)^∧`. -/
private noncomputable abbrev positive_stage_completion_completion_limitCone :
    LimitCone (positive_stage_completion_system (R := R) (I := I) (M := M)) :=
  { cone := positive_stage_completion_completion_cone (R := R) (I := I) (M := M)
    isLimit := positive_stage_completion_completion_isLimit (R := R) (I := I) (M := M) }

/-- Helper for Lemma 10.96.5: the positive-stage inverse limit `lim_n M^∧ / I ^ n M^∧` is
canonically identified with `(AdicCompletion I M)^∧`. -/
noncomputable abbrev positive_stage_completion_system_limit_iso :
    limit (positive_stage_completion_system (R := R) (I := I) (M := M)) ≅
      ModuleCat.of R (AdicCompletion I (AdicCompletion I M)) :=
  limit.isoLimitCone
    (positive_stage_completion_completion_limitCone (R := R) (I := I) (M := M))

/-- Helper for Lemma 10.96.5: the inverse of the positive-stage completion limit identification
evaluates to the canonical completion quotient map at each stage. -/
theorem positive_stage_completion_system_limit_iso_inv_π (i : OrderDual ℕ+) :
    (positive_stage_completion_system_limit_iso (R := R) (I := I) (M := M)).inv ≫
        limit.π (positive_stage_completion_system (R := R) (I := I) (M := M)) i =
      ModuleCat.ofHom (AdicCompletion.eval I (AdicCompletion I M) ((stagePNat i : ℕ))) := by
  -- This is the projection formula for the canonical `limit.isoLimitCone`.
  simpa [positive_stage_completion_system_limit_iso] using
    limit.isoLimitCone_inv_π
      (positive_stage_completion_completion_limitCone (R := R) (I := I) (M := M)) i

/-- Helper for Lemma 10.96.5: the forward positive-stage completion limit identification has the
expected stage projection formula. -/
theorem positive_stage_completion_system_limit_iso_hom_π (i : OrderDual ℕ+) :
    (positive_stage_completion_system_limit_iso (R := R) (I := I) (M := M)).hom ≫
        ModuleCat.ofHom (AdicCompletion.eval I (AdicCompletion I M) ((stagePNat i : ℕ))) =
      limit.π (positive_stage_completion_system (R := R) (I := I) (M := M)) i := by
  -- This is the companion projection formula for `limit.isoLimitCone`.
  simpa [positive_stage_completion_system_limit_iso] using
    limit.isoLimitCone_hom_π
      (positive_stage_completion_completion_limitCone (R := R) (I := I) (M := M)) i


end
