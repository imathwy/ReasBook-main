import stacks_proof.stacks_project.Chap10.Lemma_10_98_2.BasicMaps

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

local notation "ModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat A
local notation "moduleInvLim" => (lim : ModuleInverseSystem ⥤ ModuleCat A)

/-- Helper for Lemma 10.98.2: the successor quotient transition on
`(\varprojlim M_i) / I ^ n (\varprojlim M_i)`. -/
abbrev limit_projection_positive_stage_map
    (I : Ideal A) (M_ : ModuleInverseSystem) {i j : OrderDual ℕ+} (f : i ⟶ j) :
    ((limit M_ : ModuleCat A) ⧸
        I ^ ((stagePNat i : ℕ)) • (⊤ : Submodule A (limit M_ : ModuleCat A))) →ₗ[A]
      ((limit M_ : ModuleCat A) ⧸
        I ^ ((stagePNat j : ℕ)) • (⊤ : Submodule A (limit M_ : ModuleCat A))) :=
  AdicCompletion.transitionMap I (limit M_ : ModuleCat A)
    (show ((stagePNat j : ℕ+) : ℕ) ≤ ((stagePNat i : ℕ+) : ℕ) from
      (show stagePNat j ≤ stagePNat i from leOfHom f))

/-- Helper for Lemma 10.98.2: the kernel of the descended stage map is the image of the kernel of
the original projection inside the quotient stage. -/
theorem limit_projection_quotient_desc_ker
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hStage :
      ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+) :
    LinearMap.ker (limit_projection_quotient_desc I M_ hStage n) =
      Submodule.map
        (Submodule.mkQ
          (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A))))
        (LinearMap.ker (limitProjection M_ n)) := by
  -- `Submodule.ker_liftQ` is the source-proof identification
  -- `N_n / (N_n ∩ I ^ n M) = ker(M / I^n M → M_n)`.
  simpa [limit_projection_quotient_desc, limitProjection] using
    (Submodule.ker_liftQ
      (p := I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)))
      (f := (limit.π M_ (OrderDual.toDual n)).hom)
      (h := limit_projection_pow_smul_top_le_ker I M_ hStage n))

/-- Helper for Lemma 10.98.2: the descended stage maps commute with arbitrary quotient transition
maps on the inverse limit. -/
theorem limit_projection_positive_stage_map_comm
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hStage :
      ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥)
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    (M_.map f).hom ∘ₗ
        limit_projection_quotient_desc I M_ hStage (stagePNat i) =
      limit_projection_quotient_desc I M_ hStage (stagePNat j) ∘ₗ
        limit_projection_positive_stage_map I M_ f := by
  simpa [stagePNat, limit_projection_positive_stage_map] using
    limit_projection_quotient_desc_compat I M_ hStage f

/-- Helper for Lemma 10.98.2: an arbitrary quotient transition carries the higher-stage kernel
into the lower-stage kernel. -/
theorem limit_projection_positive_stage_map_mem_kernel
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hStage :
      ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥)
    {i j : OrderDual ℕ+} (f : i ⟶ j)
    {x :
      ((limit M_ : ModuleCat A) ⧸
        I ^ ((stagePNat i : ℕ)) • (⊤ : Submodule A (limit M_ : ModuleCat A)))}
    (hx : x ∈ LinearMap.ker (limit_projection_quotient_desc I M_ hStage (stagePNat i))) :
    limit_projection_positive_stage_map I M_ f x ∈
      LinearMap.ker (limit_projection_quotient_desc I M_ hStage (stagePNat j)) := by
  change limit_projection_quotient_desc I M_ hStage (stagePNat i) x = 0 at hx
  -- Evaluate the functorial comparison square on the chosen quotient class.
  have hcomm :=
    congrArg (fun g ↦ g x) (limit_projection_positive_stage_map_comm I M_ hStage f)
  change limit_projection_quotient_desc I M_ hStage (stagePNat j)
      (limit_projection_positive_stage_map I M_ f x) = 0
  calc
    limit_projection_quotient_desc I M_ hStage (stagePNat j)
        (limit_projection_positive_stage_map I M_ f x) =
      (M_.map f).hom
        (limit_projection_quotient_desc I M_ hStage (stagePNat i) x) := by
          simpa using hcomm.symm
    _ = 0 := by
          rw [hx]
          exact map_zero ((M_.map f).hom)

/-- Helper for Lemma 10.98.2: the restricted successor map on the quotient kernels
`N_{n + 1} / (N_{n + 1} ∩ I ^ (n + 1) M) → N_n / (N_n ∩ I ^ n M)`. -/
abbrev quotient_desc_kernel_transition
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hStage :
      ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+) :
    LinearMap.ker (limit_projection_quotient_desc I M_ hStage (n + 1)) →ₗ[A]
      LinearMap.ker (limit_projection_quotient_desc I M_ hStage n) :=
  ((limit_projection_positive_stage_map I M_
      (homOfLE
        (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n))).domRestrict
      (LinearMap.ker (limit_projection_quotient_desc I M_ hStage (n + 1)))).codRestrict
    (LinearMap.ker (limit_projection_quotient_desc I M_ hStage n))
    (fun x ↦
      limit_projection_positive_stage_map_mem_kernel I M_ hStage
        (homOfLE
          (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n)) x.2)

/-- Helper for Lemma 10.98.2: the source identity
`N_{n + 1} + I ^ n M = N_n` makes the successor transition on the quotient kernels surjective. -/
theorem quotient_desc_kernel_transition_surjective_of_successive_ideal_power_quotients
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
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    Function.Surjective
      (quotient_desc_kernel_transition I M_
        (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer) n) := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer
  intro y
  -- Rewrite the lower kernel as the quotient image of `N_n`, then split a representative
  -- through the source identity `N_{n + 1} + I ^ n M = N_n`.
  have hy_map :
      (y :
        ((limit M_ : ModuleCat A) ⧸
          I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)))) ∈
        Submodule.map
          (Submodule.mkQ
            (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A))))
          (LinearMap.ker (limitProjection M_ n)) := by
    rw [← limit_projection_quotient_desc_ker I M_ hStage n]
    exact y.2
  rcases hy_map with ⟨x, hxker, hy_eq⟩
  have hxsplit :
      x ∈ LinearMap.ker (limitProjection M_ (n + 1)) ⊔
        I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)) := by
    rw [limit_projection_ker_succ_sup_pow_smul_top_of_successive_ideal_power_quotients
      I M_ hSurj hKer n]
    exact hxker
  rcases Submodule.mem_sup.1 hxsplit with ⟨z, hz, w, hw, rfl⟩
  have hz_left :
      Submodule.Quotient.mk z ∈
        LinearMap.ker (limit_projection_quotient_desc I M_ hStage (n + 1)) := by
    rw [limit_projection_quotient_desc_ker I M_ hStage (n + 1)]
    exact ⟨z, hz, rfl⟩
  refine ⟨⟨Submodule.Quotient.mk z, hz_left⟩, ?_⟩
  apply Subtype.ext
  change limit_projection_positive_stage_map I M_
      (homOfLE
        (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n))
      (Submodule.Quotient.mk z) = y.1
  calc
    limit_projection_positive_stage_map I M_
        (homOfLE
          (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n))
        (Submodule.Quotient.mk z)
      = Submodule.Quotient.mk z := by
          rfl
    _ = Submodule.Quotient.mk (z + w) := by
          exact (Submodule.Quotient.eq
            (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)))).2 <| by
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using neg_mem hw
    _ = y.1 := hy_eq

/-- Helper for Lemma 10.98.2: the quotient system
`(\varprojlim M_i) / I^n (\varprojlim M_i)` viewed as an inverse system over `ℕ+`. -/
noncomputable abbrev limit_projection_quotient_system
    (I : Ideal A) (M_ : ModuleInverseSystem) : ModuleInverseSystem where
  obj i := ModuleCat.of A
    ((limit M_ : ModuleCat A) ⧸
      I ^ ((stagePNat i : ℕ)) • (⊤ : Submodule A (limit M_ : ModuleCat A)))
  map f := ModuleCat.ofHom (limit_projection_positive_stage_map I M_ f)
  map_id := by
    intro i
    -- The identity quotient transition fixes each representative.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    rfl
  map_comp := by
    intro i j k f g
    -- Quotient transition maps compose by keeping the same representative.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    rfl

/-- Helper for Lemma 10.98.2: the kernel system
`ker((\varprojlim M_i) / I^n (\varprojlim M_i) → M_n)` as an inverse system. -/
noncomputable abbrev limit_projection_kernel_system
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hStage :
      ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥) :
    ModuleInverseSystem where
  obj i := ModuleCat.of A
    (LinearMap.ker (limit_projection_quotient_desc I M_ hStage (stagePNat i)))
  map := by
    intro i j f
    exact ModuleCat.ofHom
      (((limit_projection_positive_stage_map I M_ f).domRestrict
          (LinearMap.ker (limit_projection_quotient_desc I M_ hStage (stagePNat i)))).codRestrict
        (LinearMap.ker (limit_projection_quotient_desc I M_ hStage (stagePNat j)))
        (fun x ↦ limit_projection_positive_stage_map_mem_kernel I M_ hStage f x.2))
  map_id := by
    intro i
    -- Restricting the identity quotient transition still gives the identity on the kernel.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change limit_projection_positive_stage_map I M_ (𝟙 i) x.1 = x.1
    refine Quotient.inductionOn' x.1 ?_
    intro x
    rfl
  map_comp := by
    intro i j k f g
    -- Restricting quotient transition maps to the kernels is compatible with composition.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change
      limit_projection_positive_stage_map I M_ (f ≫ g) x.1 =
        limit_projection_positive_stage_map I M_ g
          (limit_projection_positive_stage_map I M_ f x.1)
    refine Quotient.inductionOn' x.1 ?_
    intro x
    rfl

/-- Helper for Lemma 10.98.2: on the immediate predecessor morphism `(n + 1) ⟶ n`, the kernel
system map is exactly the restricted successor transition on quotient kernels. -/
theorem limit_projection_kernel_system_map_succ
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hStage :
      ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+) :
    ((limit_projection_kernel_system I M_ hStage).map
      (homOfLE
        (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n))).hom =
      quotient_desc_kernel_transition I M_ hStage n := by
  -- Both sides are definitionally the same restricted successor map.
  rfl

/-- Helper for Lemma 10.98.2: surjectivity of the successor kernel transitions propagates across
any finite positive-stage gap in the kernel inverse system. -/
theorem limit_projection_kernel_gap_map_surjective
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
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    ∀ k : ℕ,
      Function.Surjective
        (((limit_projection_kernel_system I M_
            (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer)).map
          (homOfLE
            (show OrderDual.toDual (stageShiftPNat n k) ≤ OrderDual.toDual n from by
              change (n : ℕ) ≤ ((stageShiftPNat n k : ℕ+) : ℕ)
              exact Nat.le_add_right _ _))).hom) := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer
  intro k
  induction k with
  | zero =>
      -- The zero-gap transition is the identity on the current kernel stage.
      have hzero :
          (homOfLE
            (show OrderDual.toDual (stageShiftPNat n 0) ≤ OrderDual.toDual n from by
              change (n : ℕ) ≤ ((stageShiftPNat n 0 : ℕ+) : ℕ)
              simp [stageShiftPNat])) =
            𝟙 (OrderDual.toDual n) := by
        exact Subsingleton.elim _ _
      have hId :
          (((limit_projection_kernel_system I M_ hStage).map
            (homOfLE
              (show OrderDual.toDual (stageShiftPNat n 0) ≤ OrderDual.toDual n from by
                change (n : ℕ) ≤ ((stageShiftPNat n 0 : ℕ+) : ℕ)
                simp [stageShiftPNat]))).hom) =
            (LinearMap.id :
              LinearMap.ker (limit_projection_quotient_desc I M_ hStage n) →ₗ[A]
                LinearMap.ker (limit_projection_quotient_desc I M_ hStage n)) := by
        rw [hzero]
        simpa [stageShiftPNat, limit_projection_positive_stage_map] using
          congrArg ModuleCat.Hom.hom
            ((limit_projection_kernel_system I M_ hStage).map_id (OrderDual.toDual n))
      rw [hId]
      exact Function.surjective_id
  | succ k ih =>
      -- Factor the gap-`k + 1` map into one successor step followed by the remaining gap.
      let step : OrderDual.toDual (stageShiftPNat n (k + 1)) ⟶
          OrderDual.toDual (stageShiftPNat n k) :=
        homOfLE
          (show OrderDual.toDual (stageShiftPNat n (k + 1)) ≤
              OrderDual.toDual (stageShiftPNat n k) from by
            change ((stageShiftPNat n k : ℕ+) : ℕ) ≤
              ((stageShiftPNat n (k + 1) : ℕ+) : ℕ)
            exact Nat.le_succ _)
      let tail : OrderDual.toDual (stageShiftPNat n k) ⟶ OrderDual.toDual n :=
        homOfLE
          (show OrderDual.toDual (stageShiftPNat n k) ≤ OrderDual.toDual n from by
            change (n : ℕ) ≤ ((stageShiftPNat n k : ℕ+) : ℕ)
            exact Nat.le_add_right _ _)
      have hstep :
          Function.Surjective
            (((limit_projection_kernel_system I M_ hStage).map step).hom) := by
        -- The first factor is exactly the successor transition proved surjective above.
        simpa [hStage, step, limit_projection_kernel_system_map_succ] using
          quotient_desc_kernel_transition_surjective_of_successive_ideal_power_quotients
            I M_ hSurj hKer (stageShiftPNat n k)
      have htail :
          Function.Surjective
            (((limit_projection_kernel_system I M_ hStage).map tail).hom) := by
        simpa [hStage, tail] using ih
      have hbig :
          (((limit_projection_kernel_system I M_ hStage).map
            (homOfLE
              (show OrderDual.toDual (stageShiftPNat n (k + 1)) ≤ OrderDual.toDual n from by
                change (n : ℕ) ≤ ((stageShiftPNat n (k + 1) : ℕ+) : ℕ)
                exact Nat.le_add_right _ _))).hom) =
            (((limit_projection_kernel_system I M_ hStage).map tail).hom).comp
              (((limit_projection_kernel_system I M_ hStage).map step).hom) := by
        have hmapcomp :
            (((limit_projection_kernel_system I M_ hStage).map (step ≫ tail)).hom) =
              (((limit_projection_kernel_system I M_ hStage).map tail).hom).comp
                (((limit_projection_kernel_system I M_ hStage).map step).hom) := by
          simpa using
            congrArg ModuleCat.Hom.hom
              ((limit_projection_kernel_system I M_ hStage).map_comp step tail)
        have hfactor :
            (homOfLE
              (show OrderDual.toDual (stageShiftPNat n (k + 1)) ≤ OrderDual.toDual n from by
                change (n : ℕ) ≤ ((stageShiftPNat n (k + 1) : ℕ+) : ℕ)
                exact Nat.le_add_right _ _)) =
              step ≫ tail := by
          exact Subsingleton.elim _ _
        simpa [hfactor] using hmapcomp
      rw [hbig]
      exact htail.comp hstep

/-- Helper for Lemma 10.98.2: every `homOfLE` transition in the kernel inverse system is
surjective. -/
theorem limit_projection_kernel_system_homOfLE_surjective
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
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1)))))
    {i j : ℕ+} (hij : i ≤ j) :
    Function.Surjective
      (((limit_projection_kernel_system I M_
          (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer)).map
        (homOfLE (show OrderDual.toDual j ≤ OrderDual.toDual i from hij))).hom) := by
  -- Rewrite the larger stage as a finite successor gap above the smaller stage.
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  have hj : j = stageShiftPNat i k := by
    exact Subtype.ext (by simpa [stageShiftPNat] using hk)
  subst hj
  -- The general `homOfLE` case is exactly the finite-gap case already proved.
  simpa using limit_projection_kernel_gap_map_surjective I M_ hSurj hKer i k

/-- Helper for Lemma 10.98.2: every morphism in the quotient-kernel inverse system is
surjective. -/
theorem limit_projection_kernel_system_map_surjective
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
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1)))))
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    Function.Surjective
      (((limit_projection_kernel_system I M_
          (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer)).map
        f).hom) := by
  -- In the thin category `OrderDual ℕ+`, every morphism is the canonical `homOfLE`.
  have hf :
      f =
        homOfLE
          (show i ≤ j from leOfHom f) := by
    exact Subsingleton.elim _ _
  -- The general morphism case reduces to the corresponding comparison map.
  simpa [hf] using
    limit_projection_kernel_system_homOfLE_surjective I M_ hSurj hKer
      (i := OrderDual.ofDual j) (j := OrderDual.ofDual i)
      (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)

/-- Helper for Lemma 10.98.2: the quotient-kernel inverse system is Mittag-Leffler once all of
its transition maps are known to be surjective. -/
theorem limit_projection_kernel_system_isMittagLeffler_of_successive_ideal_power_quotients
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
    ((limit_projection_kernel_system I M_
        (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer)) ⋙
      forget (ModuleCat A)).IsMittagLeffler := by
  -- The general criterion only asks for surjectivity on every transition map.
  exact Functor.isMittagLeffler_of_surjective
    (F := (limit_projection_kernel_system I M_
        (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer)) ⋙
      forget (ModuleCat A))
    (fun _ _ f ↦ by
      simpa using limit_projection_kernel_system_map_surjective I M_ hSurj hKer f)

/-- Helper for Lemma 10.98.2: the kernel inclusion
`ker((\varprojlim M_i) / I^n (\varprojlim M_i) → M_n) → (\varprojlim M_i) / I^n (\varprojlim M_i)`
as a morphism of inverse systems. -/
noncomputable abbrev limit_projection_kernel_ι
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hStage :
      ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥) :
    (limit_projection_kernel_system I M_ hStage) ⟶
      (limit_projection_quotient_system I M_) where
  app i := ModuleCat.ofHom
    (LinearMap.ker (limit_projection_quotient_desc I M_ hStage (stagePNat i))).subtype
  naturality := by
    intro i j f
    -- The kernel transition is defined by restricting the quotient transition.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- Helper for Lemma 10.98.2: the descended quotient-stage maps
`(\varprojlim M_i) / I^n (\varprojlim M_i) → M_n` as a morphism of inverse systems. -/
noncomputable abbrev limit_projection_stageMap
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hStage :
      ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥) :
    (limit_projection_quotient_system I M_) ⟶ M_ where
  app i := ModuleCat.ofHom
    (limit_projection_quotient_desc I M_ hStage (stagePNat i))
  naturality := by
    intro i j f
    -- Naturality is exactly the arbitrary-stage commutative square proved above.
    apply ModuleCat.hom_ext
    simpa using (limit_projection_positive_stage_map_comm I M_ hStage f).symm

/-- Helper for Lemma 10.98.2: the source-proof short complex of inverse systems
`0 → K_n → (\varprojlim M_i) / I^n (\varprojlim M_i) → M_n → 0`. -/
noncomputable abbrev limit_projection_quotient_shortComplex
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hStage :
      ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥) :
    ShortComplex ModuleInverseSystem :=
  ShortComplex.mk
    (limit_projection_kernel_ι I M_ hStage)
    (limit_projection_stageMap I M_ hStage)
    (by
      -- Stagewise, the descended quotient map vanishes on its kernel by definition.
      ext i x
      exact x.2)

/-- Helper for Lemma 10.98.2: the family of evaluation functors on module inverse systems is
jointly faithful, because a natural transformation is determined by its components. -/
lemma limit_projection_evaluation_jointlyFaithful :
    CategoryTheory.JointlyFaithful
      (fun i : OrderDual ℕ+ ↦
        (evaluation (OrderDual ℕ+) (ModuleCat A)).obj i) where
  map_injective := by
    intro X Y f g hfg
    -- Equality of natural transformations is pointwise equality on every stage.
    ext i x
    exact congrArg (fun h ↦ h.hom x) (hfg i)

/-- Helper for Lemma 10.98.2: the quotient-kernel short complex of inverse systems is short exact,
because each evaluation is the standard kernel short exact sequence of the descended stage map. -/
theorem limit_projection_quotient_shortComplex_shortExact
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
    (limit_projection_quotient_shortComplex I M_
      (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer)).ShortExact := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer
  let F : OrderDual ℕ+ → ModuleInverseSystem ⥤ ModuleCat A :=
    fun i ↦ (evaluation (OrderDual ℕ+) (ModuleCat A)).obj i
  let hJR :
      CategoryTheory.JointlyReflectIsomorphisms F :=
    CategoryTheory.JointlyFaithful.jointlyReflectsIsomorphisms
      (F := F) (limit_projection_evaluation_jointlyFaithful (A := A))
  -- Reflect short exactness from the stagewise kernel short exact sequences.
  refine (CategoryTheory.JointlyReflectIsomorphisms.shortExact_iff
      (F := F) hJR (limit_projection_quotient_shortComplex I M_ hStage)).2 ?_
  intro i
  have hsurj :
      Function.Surjective
        (limit_projection_quotient_desc I M_ hStage (OrderDual.ofDual i)) := by
    intro x
    rcases limit_projection_surjective_of_successive_ideal_power_quotients
        M_ hSurj (OrderDual.ofDual i) x with ⟨y, rfl⟩
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    simpa [hStage] using
      congrArg (fun g ↦ g y)
        (limit_projection_quotient_desc_comp_mkQ I M_ hStage (OrderDual.ofDual i))
  -- Evaluating the inverse-system short complex at stage `i` recovers the textbook kernel
  -- short exact sequence for the descended stage map.
  simpa [F, limit_projection_quotient_shortComplex, limit_projection_kernel_ι,
    limit_projection_stageMap, limit_projection_kernel_system, limit_projection_quotient_system,
    stagePNat] using
    (LinearMap.shortExact_shortComplexKer hsurj :
      (LinearMap.shortComplexKer
        (limit_projection_quotient_desc I M_ hStage (OrderDual.ofDual i))).ShortExact)


end
