import Mathlib
import stacks_project.Chap10.Lemma_10_87_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open AdicCompletion
open CategoryTheory
open CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "ModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat R
local notation "moduleInvLim" => (lim : ModuleInverseSystem ⥤ ModuleCat R)

/-- Helper for Lemma 10.96.5: the inverse-limit functor on `R`-module inverse systems, with the
module universe frozen explicitly so later `ShortComplex.map` applications elaborate stably. -/
private abbrev moduleInverseLimitFunctor : ModuleInverseSystem ⥤ ModuleCat R :=
  lim

-- Domain-style sampling:
-- * source-facing layer: a criterion for when the completion `AdicCompletion I M` is itself
--   `I`-adically complete, phrased by the kernels of the canonical quotient maps.
-- * core/canonical owner: `IsAdicComplete I (AdicCompletion I M)` together with the kernel
--   description `AdicCompletion.pow_smul_top_eq_ker_eval`.
-- * relevant sampled declarations:
--   `IsAdicComplete`,
--   `AdicCompletion.of_bijective_iff`,
--   `AdicCompletion.isAdicComplete`,
--   `AdicCompletion.pow_smul_top_eq_ker_eval`.
-- * primitive data: the owner object `AdicCompletion I M`; the submodules `ker (eval I M n)` are
--   derived from its canonical projections.
-- * bridge/view output: the textbook iff re-expressed directly in terms of the owner completion
--   object and its canonical evaluation maps.
--
-- Proof sketch: let `K_n = (AdicCompletion.eval I M n).ker`. The short exact sequences
-- `0 → K_n / I^n M^∧ → M^∧ / I^n M^∧ → M / I^n M → 0` form an inverse system with surjective
-- transition maps on the left. Applying Lemma `10.87.1` to these systems identifies the adic
-- completion of `M^∧` with `M^∧` precisely when each quotient `K_n / I^n M^∧` vanishes, i.e. when
-- `K_n = I^n M^∧` for every positive `n`.
/-- Helper for Lemma 10.96.5: the source-proof identity `K_{n + 1} + I ^ n M^∧ = K_n` for
`K_n = ker (AdicCompletion.eval I M n)`. -/
lemma ker_eval_succ_sup_pow_smul_top (n : ℕ+) :
    ((eval I M ((n : ℕ) + 1)).ker) ⊔
        I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)) =
      (eval I M (n : ℕ)).ker := by
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ (AdicCompletion.pow_smul_top_le_ker_eval (I := I) (M := M) (n := n))
    intro x hx
    -- Passing from stage `n + 1` to stage `n` sends a vanishing coordinate to a vanishing one.
    rw [LinearMap.mem_ker] at hx ⊢
    calc
      eval I M (n : ℕ) x =
          AdicCompletion.transitionMap I M (Nat.le_succ (n : ℕ))
            (eval I M ((n : ℕ) + 1) x) := by
              simpa using
                (AdicCompletion.transitionMap_comp_eval_apply (I := I) (M := M)
                  (hmn := Nat.le_succ (n : ℕ)) (x := x)).symm
      _ = 0 := by simp [hx]
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    -- The vanishing of the `n`th coordinate says the `n + 1`st coordinate lands in `I ^ n`.
    have hx_mem :
        eval I M ((n : ℕ) + 1) x ∈
          I ^ (n : ℕ) •
            (⊤ : Submodule R
              (M ⧸ I ^ ((n : ℕ) + 1) • (⊤ : Submodule R M))) := by
      simpa [AdicCompletion.eval_apply] using
        (AdicCompletion.val_apply_mem_smul_top_iff (I := I) (x := x)
          (m_ge := Nat.le_succ (n : ℕ))).2 hx
    -- Surjectivity of `eval` identifies the image of `I ^ n M^∧` with `I ^ n (M / I ^ (n + 1) M)`.
    have hmap :
        Submodule.map (eval I M ((n : ℕ) + 1))
          (I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M))) =
            I ^ (n : ℕ) •
              (⊤ : Submodule R
                (M ⧸ I ^ ((n : ℕ) + 1) • (⊤ : Submodule R M))) := by
      rw [Submodule.map_smul'', Submodule.map_top, AdicCompletion.range_eval]
    rcases (show eval I M ((n : ℕ) + 1) x ∈
        Submodule.map (eval I M ((n : ℕ) + 1))
          (I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M))) from by
            simpa [hmap] using hx_mem) with ⟨y, hy, hy_eq⟩
    -- Decompose `x` as a sum of a stage-`n + 1` kernel element and an `I ^ n` element.
    refine Submodule.mem_sup.2 ⟨x - y, ?_, y, hy, by abel⟩
    rw [LinearMap.mem_ker, map_sub, hy_eq, sub_eq_zero]

/-- Helper for Lemma 10.96.5: the quotient-stage map
`M^∧ / I ^ n M^∧ → M / I ^ n M` induced by the evaluation map at stage `n`. -/
abbrev ker_eval_quotient_stageMap (n : ℕ+) :
    (AdicCompletion I M ⧸ I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M))) →ₗ[R]
      M ⧸ (I ^ (n : ℕ) • (⊤ : Submodule R M)) :=
  Submodule.liftQ _ (AdicCompletion.eval I M (n : ℕ))
    (AdicCompletion.pow_smul_top_le_ker_eval (I := I) (M := M) (n := n))

/-- Helper for Lemma 10.96.5: the quotient-stage map is surjective because the underlying
evaluation map `M^∧ → M / I ^ n M` is surjective. -/
lemma ker_eval_quotient_stageMap_surjective (n : ℕ+) :
    Function.Surjective (ker_eval_quotient_stageMap (I := I) (M := M) n) := by
  intro x
  rcases AdicCompletion.eval_surjective (I := I) (M := M) (n := n) x with ⟨y, rfl⟩
  -- Lift a preimage of the stage-`n` quotient class to the quotient of the completion.
  refine ⟨Submodule.Quotient.mk y, rfl⟩

/-- Helper for Lemma 10.96.5: the kernel of the quotient-stage map is the image of the stage
kernel `K_n` inside `M^∧ / I ^ n M^∧`. -/
lemma ker_eval_quotient_stageMap_ker (n : ℕ+) :
    LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) n) =
      Submodule.map (Submodule.mkQ _)
        ((AdicCompletion.eval I M (n : ℕ)).ker) := by
  -- `Submodule.ker_liftQ` is exactly the stagewise kernel computation from the source proof.
  simpa [ker_eval_quotient_stageMap] using
    (Submodule.ker_liftQ
      (p := I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)))
      (f := AdicCompletion.eval I M (n : ℕ))
      (h := AdicCompletion.pow_smul_top_le_ker_eval (I := I) (M := M) (n := n)))

/-- Helper for Lemma 10.96.5: the textbook quotient sequence
`0 → K_n / I ^ n M^∧ → M^∧ / I ^ n M^∧ → M / I ^ n M → 0`
is realized as the kernel short complex of the quotient-stage map. -/
lemma ker_eval_quotient_stage_shortExact (n : ℕ+) :
    (LinearMap.shortComplexKer (ker_eval_quotient_stageMap (I := I) (M := M) n)).ShortExact := by
  -- Once the quotient-stage map is known to be surjective, the standard kernel short complex
  -- is short exact.
  exact LinearMap.shortExact_shortComplexKer
    (ker_eval_quotient_stageMap_surjective (I := I) (M := M) n)

/-- Helper for Lemma 10.96.5: the successor map on the completion quotients
`M^∧ / I ^ (n + 1) M^∧ → M^∧ / I ^ n M^∧`. -/
abbrev positive_stage_transition (n : ℕ+) :
    (AdicCompletion I M ⧸ I ^ ((n : ℕ) + 1) • (⊤ : Submodule R (AdicCompletion I M))) →ₗ[R]
      AdicCompletion I M ⧸ I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)) :=
  AdicCompletion.transitionMap I (AdicCompletion I M) (Nat.le_succ (n : ℕ))

/-- Helper for Lemma 10.96.5: the successor map on the module quotients
`M / I ^ (n + 1) M → M / I ^ n M`. -/
abbrev module_positive_stage_transition (n : ℕ+) :
    (M ⧸ I ^ ((n : ℕ) + 1) • (⊤ : Submodule R M)) →ₗ[R]
      M ⧸ I ^ (n : ℕ) • (⊤ : Submodule R M) :=
  AdicCompletion.transitionMap I M (Nat.le_succ (n : ℕ))

/-- Helper for Lemma 10.96.5: the stagewise quotient maps commute with the positive-stage
transition maps. This is the source-proof comparison square on successive quotients. -/
lemma positive_stage_transition_comm (n : ℕ+) :
    (module_positive_stage_transition (I := I) (M := M) n).comp
        (ker_eval_quotient_stageMap (I := I) (M := M) (n + 1)) =
      (ker_eval_quotient_stageMap (I := I) (M := M) n).comp
        (positive_stage_transition (I := I) (M := M) n) := by
  -- This is the standard compatibility of evaluation with the inverse-system transition maps.
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (I ^ ((n : ℕ) + 1) • (⊤ : Submodule R (AdicCompletion I M))) x
  change
    AdicCompletion.transitionMap I M (Nat.le_succ (n : ℕ))
        (AdicCompletion.eval I M ((n : ℕ) + 1) x) =
      AdicCompletion.eval I M (n : ℕ) x
  simpa [ker_eval_quotient_stageMap, module_positive_stage_transition, positive_stage_transition]
    using (AdicCompletion.transitionMap_comp_eval_apply
      (I := I) (M := M) (hmn := Nat.le_succ (n : ℕ)) (x := x))

/-- Helper for Lemma 10.96.5: the successor quotient transition sends the left kernel at stage
`n + 1` into the left kernel at stage `n`. -/
lemma positive_stage_transition_mem_kernel (n : ℕ+)
    {x : AdicCompletion I M ⧸ I ^ ((n : ℕ) + 1) • (⊤ : Submodule R (AdicCompletion I M))}
    (hx : x ∈ LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (n + 1))) :
    positive_stage_transition (I := I) (M := M) n x ∈
      LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) n) := by
  change ker_eval_quotient_stageMap (I := I) (M := M) (n + 1) x = 0 at hx
  -- Evaluate the commutative square on `x` and use that `x` already lies in the higher-stage
  -- kernel.
  have hcomm := congrArg (fun f =>
      f x) (positive_stage_transition_comm (I := I) (M := M) n)
  change ker_eval_quotient_stageMap (I := I) (M := M) n
      (positive_stage_transition (I := I) (M := M) n x) = 0
  calc
    ker_eval_quotient_stageMap (I := I) (M := M) n
        (positive_stage_transition (I := I) (M := M) n x)
      = module_positive_stage_transition (I := I) (M := M) n
          (ker_eval_quotient_stageMap (I := I) (M := M) (n + 1) x) := by
            simpa using hcomm.symm
    _ = module_positive_stage_transition (I := I) (M := M) n 0 := by
          rw [hx]
          rfl
    _ = 0 := by simp

/-- Helper for Lemma 10.96.5: the successor quotient transition restricted to the left kernels
`K_{n + 1} / I ^ (n + 1) M^∧ → K_n / I ^ n M^∧`. -/
abbrev positive_stage_left_transition (n : ℕ+) :
    LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (n + 1)) →ₗ[R]
      LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) n) :=
  ((positive_stage_transition (I := I) (M := M) n).domRestrict
      (LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (n + 1)))).codRestrict
    (LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) n))
    (fun x ↦ positive_stage_transition_mem_kernel (I := I) (M := M) n x.2)

/-- Helper for Lemma 10.96.5: the source identity
`K_{n + 1} + I ^ n M^∧ = K_n` makes the left-kernel transition surjective. -/
lemma positive_stage_left_transition_surjective (n : ℕ+) :
    Function.Surjective (positive_stage_left_transition (I := I) (M := M) n) := by
  intro y
  -- Rewrite the codomain kernel as the quotient image of `K_n`, then choose a kernel
  -- representative and split it via `K_{n + 1} + I ^ n M^∧ = K_n`.
  have hy_map :
      (y : AdicCompletion I M ⧸ I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M))) ∈
        Submodule.map
          (Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M))))
          ((eval I M (n : ℕ)).ker) := by
    rw [← ker_eval_quotient_stageMap_ker (I := I) (M := M) n]
    exact y.2
  rcases hy_map with ⟨x, hxker, hy_eq⟩
  have hxsplit :
      x ∈ ((eval I M ((n : ℕ) + 1)).ker) ⊔
        I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)) := by
    rw [ker_eval_succ_sup_pow_smul_top (I := I) (M := M) n]
    exact hxker
  rcases Submodule.mem_sup.1 hxsplit with ⟨z, hz, w, hw, rfl⟩
  have hz_left :
      Submodule.Quotient.mk z ∈
        LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (n + 1)) := by
    rw [ker_eval_quotient_stageMap_ker (I := I) (M := M) (n + 1)]
    exact ⟨z, hz, rfl⟩
  refine ⟨⟨Submodule.Quotient.mk z, hz_left⟩, ?_⟩
  apply Subtype.ext
  change positive_stage_transition (I := I) (M := M) n (Submodule.Quotient.mk z) =
    y
  calc
    positive_stage_transition (I := I) (M := M) n (Submodule.Quotient.mk z)
      = Submodule.Quotient.mk z := by
          simp [positive_stage_transition]
    _ = Submodule.Quotient.mk (z + w) := by
          exact (Submodule.Quotient.eq
            (I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)))).2 <| by
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using neg_mem hw
    _ = y := hy_eq

/-- Helper for Lemma 10.96.5: the positive-stage transition on completion quotients attached to
an arbitrary morphism in `OrderDual ℕ+`. -/
abbrev positive_stage_completion_map {i j : OrderDual ℕ+} (f : i ⟶ j) :
    (AdicCompletion I M ⧸
        I ^ (((OrderDual.ofDual i : ℕ+) : ℕ)) •
          (⊤ : Submodule R (AdicCompletion I M))) →ₗ[R]
      AdicCompletion I M ⧸
        I ^ (((OrderDual.ofDual j : ℕ+) : ℕ)) •
          (⊤ : Submodule R (AdicCompletion I M)) :=
  AdicCompletion.transitionMap I (AdicCompletion I M)
    (show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
      (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f))

/-- Helper for Lemma 10.96.5: the positive-stage transition on module quotients attached to an
arbitrary morphism in `OrderDual ℕ+`. -/
abbrev positive_stage_module_map {i j : OrderDual ℕ+} (f : i ⟶ j) :
    (M ⧸ I ^ (((OrderDual.ofDual i : ℕ+) : ℕ)) • (⊤ : Submodule R M)) →ₗ[R]
      M ⧸ I ^ (((OrderDual.ofDual j : ℕ+) : ℕ)) • (⊤ : Submodule R M) :=
  AdicCompletion.transitionMap I M
    (show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
      (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f))

/-- Helper for Lemma 10.96.5: the quotient-stage maps commute with arbitrary positive-stage
transition morphisms. This is the functor-level comparison square needed for the later packaging
into inverse systems. -/
lemma positive_stage_map_comm {i j : OrderDual ℕ+} (f : i ⟶ j) :
    (positive_stage_module_map (I := I) (M := M) f).comp
        (ker_eval_quotient_stageMap (I := I) (M := M) (OrderDual.ofDual i)) =
      (ker_eval_quotient_stageMap (I := I) (M := M) (OrderDual.ofDual j)).comp
        (positive_stage_completion_map (I := I) (M := M) f) := by
  -- Evaluate on representatives and use compatibility of `eval` with arbitrary transitions.
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (I ^ (((OrderDual.ofDual i : ℕ+) : ℕ)) •
        (⊤ : Submodule R (AdicCompletion I M))) x
  change
    AdicCompletion.transitionMap I M
        (show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
          (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f))
        (AdicCompletion.eval I M ((OrderDual.ofDual i : ℕ+) : ℕ) x) =
      AdicCompletion.eval I M ((OrderDual.ofDual j : ℕ+) : ℕ) x
  simpa using
    (AdicCompletion.transitionMap_comp_eval_apply (I := I) (M := M)
      (hmn := show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
        (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f))
      (x := x))

/-- Helper for Lemma 10.96.5: a readable name for the positive stage corresponding to an object of
`OrderDual ℕ+`. -/
abbrev stagePNat (i : OrderDual ℕ+) : ℕ+ :=
  OrderDual.ofDual i

/-- Helper for Lemma 10.96.5: the positive-stage inverse system
`M^∧ / I ^ n M^∧`. -/
noncomputable abbrev positive_stage_completion_system : ModuleInverseSystem where
  obj i := ModuleCat.of R
    (AdicCompletion I M ⧸
      I ^ ((stagePNat i : ℕ)) • (⊤ : Submodule R (AdicCompletion I M)))
  map f := ModuleCat.ofHom (positive_stage_completion_map (I := I) (M := M) f)
  map_id := by
    intro i
    -- On quotient representatives, the identity transition map is literally the identity.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    rfl
  map_comp := by
    intro i j k f g
    -- The positive-stage maps are quotient transition maps, so their composites act trivially on
    -- representatives.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    rfl

/-- Helper for Lemma 10.96.5: the positive-stage inverse system `M / I ^ n M`. -/
noncomputable abbrev positive_stage_module_system : ModuleInverseSystem where
  obj i := ModuleCat.of R (M ⧸ I ^ ((stagePNat i : ℕ)) • (⊤ : Submodule R M))
  map f := ModuleCat.ofHom (positive_stage_module_map (I := I) (M := M) f)
  map_id := by
    intro i
    -- On quotient representatives, the identity transition map is literally the identity.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    rfl
  map_comp := by
    intro i j k f g
    -- The quotient transition maps compose by keeping the same representative.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    rfl

/-- Helper for Lemma 10.96.5: an arbitrary positive-stage completion transition map preserves the
left kernels `K_n / I ^ n M^∧`. -/
lemma positive_stage_completion_map_mem_kernel {i j : OrderDual ℕ+} (f : i ⟶ j)
    {x : AdicCompletion I M ⧸
      I ^ ((stagePNat i : ℕ)) • (⊤ : Submodule R (AdicCompletion I M))}
    (hx : x ∈ LinearMap.ker
      (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i))) :
    positive_stage_completion_map (I := I) (M := M) f x ∈
      LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat j)) := by
  change ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i) x = 0 at hx
  -- Evaluate the commutative comparison square on `x` and use the source-side kernel hypothesis.
  have hcomm := congrArg (fun g => g x) (positive_stage_map_comm (I := I) (M := M) f)
  change
    ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat j)
        (positive_stage_completion_map (I := I) (M := M) f x) = 0
  calc
    ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat j)
        (positive_stage_completion_map (I := I) (M := M) f x)
      = positive_stage_module_map (I := I) (M := M) f
          (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i) x) := by
            simpa using hcomm.symm
    _ = positive_stage_module_map (I := I) (M := M) f 0 := by rw [hx]
    _ = 0 := by simp

/-- Helper for Lemma 10.96.5: the positive-stage inverse system
`K_n / I ^ n M^∧` cut out inside the completion-quotient system. -/
noncomputable abbrev positive_stage_left_system : ModuleInverseSystem where
  obj i := ModuleCat.of R
    (LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i)))
  map := by
    intro i j f
    exact ModuleCat.ofHom
      (((positive_stage_completion_map (I := I) (M := M) f).domRestrict
          (LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i)))).codRestrict
        (LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat j)))
        (fun x ↦ positive_stage_completion_map_mem_kernel (I := I) (M := M) f x.2))
  map_id := by
    intro i
    -- The restricted identity transition is still the identity on the kernel subtype.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change positive_stage_completion_map (I := I) (M := M) (𝟙 i) x.1 = x.1
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
      positive_stage_completion_map (I := I) (M := M) (f ≫ g) x.1 =
        positive_stage_completion_map (I := I) (M := M) g
          (positive_stage_completion_map (I := I) (M := M) f x.1)
    refine Quotient.inductionOn' x.1 ?_
    intro x
    rfl

/-- Helper for Lemma 10.96.5: on the immediate predecessor morphism
`(n + 1) ⟶ n`, the functorial map of `positive_stage_left_system` is exactly the restricted
successor map on the quotient kernels. -/
lemma positive_stage_left_system_map_succ (n : ℕ+) :
    ((positive_stage_left_system (R := R) (I := I) (M := M)).map
      (homOfLE
        (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from by
          change (n : ℕ) ≤ ((n + 1 : ℕ+) : ℕ)
          exact Nat.le_succ _))).hom =
      positive_stage_left_transition (I := I) (M := M) n := by
  -- Both sides are definitionally the same restricted transition map.
  rfl

/-- Helper for Lemma 10.96.5: shifting a positive stage by a natural gap still gives a positive
stage. -/
lemma stageShiftPNat_pos (n : ℕ+) (k : ℕ) : 0 < (n : ℕ) + k :=
  lt_of_lt_of_le n.2 (Nat.le_add_right _ _)

/-- Helper for Lemma 10.96.5: the positive stage obtained by adding a finite gap `k` to `n`. -/
abbrev stageShiftPNat (n : ℕ+) (k : ℕ) : ℕ+ :=
  ⟨(n : ℕ) + k, stageShiftPNat_pos n k⟩

/-- Helper for Lemma 10.96.5: the source-proof surjectivity of the successor maps iterates along
any finite positive-stage gap in the left kernel system. -/
lemma positive_stage_left_gap_map_surjective (n : ℕ+) :
    ∀ k : ℕ,
      Function.Surjective
        (((positive_stage_left_system (R := R) (I := I) (M := M)).map
          (homOfLE
            (show OrderDual.toDual (stageShiftPNat n k) ≤ OrderDual.toDual n from by
              change (n : ℕ) ≤ ((stageShiftPNat n k : ℕ+) : ℕ)
              exact Nat.le_add_right _ _))).hom) := by
  intro k
  induction k with
  | zero =>
      -- The zero-gap transition is the identity, so surjectivity is immediate.
      have hzero :
          (homOfLE
            (show OrderDual.toDual (stageShiftPNat n 0) ≤ OrderDual.toDual n from by
              change (n : ℕ) ≤ ((stageShiftPNat n 0 : ℕ+) : ℕ)
              simp [stageShiftPNat])) =
            𝟙 (OrderDual.toDual n) := by
        apply Subsingleton.elim
      intro y
      refine ⟨y, ?_⟩
      apply Subtype.ext
      change
        positive_stage_completion_map (I := I) (M := M)
            (homOfLE
              (show OrderDual.toDual (stageShiftPNat n 0) ≤ OrderDual.toDual n from by
                change (n : ℕ) ≤ ((stageShiftPNat n 0 : ℕ+) : ℕ)
                simp [stageShiftPNat])) y.1 = y.1
      -- The zero-gap completion transition is the identity on quotient representatives.
      refine Quotient.inductionOn' y.1 ?_
      intro x
      rfl
  | succ k ih =>
      -- Factor the gap-`k + 1` map as one successor step followed by the remaining gap-`k` map.
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
            (((positive_stage_left_system (R := R) (I := I) (M := M)).map step).hom) := by
        -- The first factor is exactly the successor transition handled above.
        simpa [step, positive_stage_left_system_map_succ] using
          positive_stage_left_transition_surjective (I := I) (M := M) (stageShiftPNat n k)
      have htail :
          Function.Surjective
            (((positive_stage_left_system (R := R) (I := I) (M := M)).map tail).hom) := ih
      have hbig :
          (((positive_stage_left_system (R := R) (I := I) (M := M)).map
            (homOfLE
              (show OrderDual.toDual (stageShiftPNat n (k + 1)) ≤ OrderDual.toDual n from by
                change (n : ℕ) ≤ ((stageShiftPNat n (k + 1) : ℕ+) : ℕ)
                exact Nat.le_add_right _ _))).hom) =
            (((positive_stage_left_system (R := R) (I := I) (M := M)).map tail).hom).comp
              (((positive_stage_left_system (R := R) (I := I) (M := M)).map step).hom) := by
        have hfactor :
            (homOfLE
              (show OrderDual.toDual (stageShiftPNat n (k + 1)) ≤ OrderDual.toDual n from by
                change (n : ℕ) ≤ ((stageShiftPNat n (k + 1) : ℕ+) : ℕ)
                exact Nat.le_add_right _ _)) =
              step ≫ tail := by
          apply Subsingleton.elim
        simpa [hfactor] using
          congrArg ModuleCat.Hom.hom
            ((positive_stage_left_system (R := R) (I := I) (M := M)).map_comp step tail)
      rw [hbig]
      intro y
      rcases htail y with ⟨z, rfl⟩
      rcases hstep z with ⟨w, rfl⟩
      exact ⟨w, rfl⟩

/-- Helper for Lemma 10.96.5: every `homOfLE` transition in the positive-stage left system is
surjective, because any inequality of positive stages is a finite gap and the gap maps were
already shown surjective. -/
lemma positive_stage_left_system_homOfLE_surjective
    {i j : ℕ+} (hij : i ≤ j) :
    Function.Surjective
      (((positive_stage_left_system (R := R) (I := I) (M := M)).map
        (homOfLE
          (show OrderDual.toDual j ≤ OrderDual.toDual i from by
            exact hij))).hom) := by
  -- Rewrite the larger stage as a finite successor gap above the smaller stage.
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  have hj : j = stageShiftPNat i k := by
    exact Subtype.ext (by simpa [stageShiftPNat] using hk)
  subst hj
  -- The general `homOfLE` case is exactly the previously established finite-gap case.
  simpa using positive_stage_left_gap_map_surjective (I := I) (M := M) i k

/-- Helper for Lemma 10.96.5: every morphism in the positive-stage left system is surjective.
This is the categorical form needed by `Functor.isMittagLeffler_of_surjective`. -/
lemma positive_stage_left_system_map_surjective
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    Function.Surjective
      (((positive_stage_left_system (R := R) (I := I) (M := M)).map f).hom) := by
  -- In the thin category `OrderDual ℕ+`, every morphism is the canonical `homOfLE`.
  have hf :
      f =
        homOfLE
          (show i ≤ j from
            leOfHom f) := by
    apply Subsingleton.elim
  -- The source-proof gap-surjectivity invariant now applies directly.
  simpa [hf] using
    positive_stage_left_system_homOfLE_surjective (I := I) (M := M)
      (i := OrderDual.ofDual j) (j := OrderDual.ofDual i)
      (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)

/-- Helper for Lemma 10.96.5: the positive-stage left system is Mittag-Leffler once every
transition map is known to be surjective. -/
lemma positive_stage_left_system_isMittagLeffler :
    ((positive_stage_left_system (R := R) (I := I) (M := M)) ⋙
      forget (ModuleCat R)).IsMittagLeffler := by
  -- The general Mittag-Leffler criterion only asks for surjectivity on all transition maps.
  exact Functor.isMittagLeffler_of_surjective
    (F := (positive_stage_left_system (R := R) (I := I) (M := M)) ⋙
      forget (ModuleCat R))
    (fun _ _ f ↦ by
      simpa using positive_stage_left_system_map_surjective (I := I) (M := M) f)

/-- Helper for Lemma 10.96.5: the projection from the inverse limit of the positive-stage left
system onto stage `n`. -/
private abbrev positive_stage_left_limitProjection (n : ℕ+) :
    (limit (positive_stage_left_system (R := R) (I := I) (M := M)) : ModuleCat R) →ₗ[R]
      LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) n) :=
  (limit.π (positive_stage_left_system (R := R) (I := I) (M := M)) (OrderDual.toDual n)).hom

/-- Helper for Lemma 10.96.5: every stage projection from the inverse limit of the positive-stage
left system is surjective. This is the source-proof descent from the inverse limit to each
quotient `K_n / I ^ n M^∧`. -/
lemma positive_stage_left_limitProjection_surjective (n : ℕ+) :
    Function.Surjective (positive_stage_left_limitProjection (R := R) (I := I) (M := M) n) := by
  classical
  let F := (positive_stage_left_system (R := R) (I := I) (M := M)) ⋙ forget (ModuleCat R)
  have hAllSurj :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j), Function.Surjective (F.map f) := by
    intro i j f
    simpa [F] using positive_stage_left_system_map_surjective (R := R) (I := I) (M := M) f
  have hML : F.IsMittagLeffler := by
    -- The set-valued positive-stage left system is Mittag-Leffler because every transition is
    -- already surjective.
    exact Functor.isMittagLeffler_of_surjective (F := F) hAllSurj
  intro x
  let s : Set (F.obj (OrderDual.toDual n)) := Set.singleton x
  haveI :
      ∀ j : OrderDual ℕ+, Nonempty ((F.toPreimages s).obj j) := by
    intro j
    exact F.toPreimages_nonempty_of_surjective s hAllSurj (Set.singleton_nonempty x) j
  obtain ⟨sec, hsec⟩ :=
    nonempty_sections_of_countable_mittagLeffler_inverse_system (A := F.toPreimages s)
      (Functor.IsMittagLeffler.toPreimages (F := F) (s := s) hML)
  let secF : F.sections :=
    ⟨fun j ↦ (sec j).1, fun f ↦ by
      exact congrArg Subtype.val (hsec f)⟩
  let y : limit F := (Types.limitEquivSections F).symm secF
  refine ⟨(preservesLimitIso (forget (ModuleCat R))
      (positive_stage_left_system (R := R) (I := I) (M := M))).inv y, ?_⟩
  have hmem : (sec (OrderDual.toDual n)).1 = x := by
    -- The chosen section is forced to hit the singleton target set at stage `n`.
    have hsecMem : (sec (OrderDual.toDual n)).1 ∈
        ⋂ f : OrderDual.toDual n ⟶ OrderDual.toDual n, F.map f ⁻¹' s := by
      simpa [Functor.toPreimages_obj] using (sec (OrderDual.toDual n)).2
    rw [Set.mem_iInter] at hsecMem
    have hid := hsecMem (𝟙 (OrderDual.toDual n))
    simpa [s] using hid
  have hsec' :
      limit.π F (OrderDual.toDual n) y = (secF : ∀ j, F.obj j) (OrderDual.toDual n) := by
    simpa [y] using
      (Types.limitEquivSections_symm_apply (F := F) (x := secF) (j := OrderDual.toDual n))
  have hy :
      limit.π F (OrderDual.toDual n) y = x := by
    -- Evaluating the section at stage `n` recovers the prescribed point `x`.
    simpa [secF, hmem] using hsec'
  have hπ :
      ((forget (ModuleCat R)).map
          (limit.π (positive_stage_left_system (R := R) (I := I) (M := M))
            (OrderDual.toDual n)))
          ((preservesLimitIso (forget (ModuleCat R))
            (positive_stage_left_system (R := R) (I := I) (M := M))).inv y) = x := by
    have hπ' :
        ((forget (ModuleCat R)).map
            (limit.π (positive_stage_left_system (R := R) (I := I) (M := M))
              (OrderDual.toDual n)))
            ((preservesLimitIso (forget (ModuleCat R))
              (positive_stage_left_system (R := R) (I := I) (M := M))).inv y) =
          limit.π F (OrderDual.toDual n) y := by
      simpa using
        congrArg
          (fun g ↦ g ((preservesLimitIso (forget (ModuleCat R))
            (positive_stage_left_system (R := R) (I := I) (M := M))).inv y))
          (preservesLimitIso_hom_π
            (G := forget (ModuleCat R))
            (F := positive_stage_left_system (R := R) (I := I) (M := M))
            (j := OrderDual.toDual n)).symm
    exact hπ'.trans hy
  change
    ((forget (ModuleCat R)).map
      (limit.π (positive_stage_left_system (R := R) (I := I) (M := M))
        (OrderDual.toDual n)))
      ((preservesLimitIso (forget (ModuleCat R))
        (positive_stage_left_system (R := R) (I := I) (M := M))).inv y) = x
  exact hπ

/-- Helper for Lemma 10.96.5: if the inverse limit of the positive-stage left system is zero, then
every stage quotient `K_n / I ^ n M^∧` is zero. -/
lemma positive_stage_left_stage_map_eq_bot_of_limit_isZero
    (hzero : IsZero (limit (positive_stage_left_system (R := R) (I := I) (M := M))))
    (n : ℕ+) :
    Submodule.map
        (Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M))))
        ((eval I M (n : ℕ)).ker) =
      ⊥ := by
  -- Surjective stage projections let the zero inverse limit force the stage object itself to be
  -- zero.
  apply (Submodule.eq_bot_iff _).2
  intro y hy
  rw [← ker_eval_quotient_stageMap_ker (I := I) (M := M) n] at hy
  let y' : LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) n) := ⟨y, hy⟩
  obtain ⟨x, hx⟩ :=
    positive_stage_left_limitProjection_surjective (R := R) (I := I) (M := M) n y'
  have hid :
      (𝟙 (limit (positive_stage_left_system (R := R) (I := I) (M := M))) :
        limit (positive_stage_left_system (R := R) (I := I) (M := M)) ⟶
          limit (positive_stage_left_system (R := R) (I := I) (M := M))) = 0 := by
    exact (IsZero.iff_id_eq_zero
      (X := limit (positive_stage_left_system (R := R) (I := I) (M := M)))).1 hzero
  have hx0 : x = 0 := by
    -- In a zero object, every point is equal to zero.
    calc
      x = (𝟙 _ :
          limit (positive_stage_left_system (R := R) (I := I) (M := M)) ⟶
            limit (positive_stage_left_system (R := R) (I := I) (M := M))) x := by simp
      _ = 0 := by simpa [hid]
  have hy' : y' = 0 := by
    -- Transport the vanishing of the limit point down to the stage projection.
    calc
      y' = positive_stage_left_limitProjection (R := R) (I := I) (M := M) n x := hx.symm
      _ = positive_stage_left_limitProjection (R := R) (I := I) (M := M) n 0 := by rw [hx0]
      _ = 0 := by
            simpa using
              (positive_stage_left_limitProjection (R := R) (I := I) (M := M) n).map_zero
  exact congrArg Subtype.val hy'

/-- Helper for Lemma 10.96.5: once the inverse limit of the quotient kernels vanishes, the source
kernel equality `K_n = I ^ n M^∧` follows at each positive stage. -/
lemma ker_eval_eq_pow_smul_top_of_left_limit_isZero
    (hzero : IsZero (limit (positive_stage_left_system (R := R) (I := I) (M := M))))
    (n : ℕ+) :
    (eval I M (n : ℕ)).ker =
      I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)) := by
  refine le_antisymm ?_ (AdicCompletion.pow_smul_top_le_ker_eval (I := I) (M := M) (n := n))
  intro x hx
  have hxmap :
      Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M))) x ∈
        Submodule.map
          (Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M))))
          ((eval I M (n : ℕ)).ker) := by
    exact ⟨x, hx, rfl⟩
  have hxbot :
      Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M))) x ∈
        (⊥ : Submodule R
          (AdicCompletion I M ⧸
            I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)))) := by
    simpa [positive_stage_left_stage_map_eq_bot_of_limit_isZero
      (R := R) (I := I) (M := M) hzero n] using hxmap
  have hxq :
      Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M))) x = 0 := by
    simpa using hxbot
  exact (Submodule.Quotient.mk_eq_zero
    (I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)))).1 hxq

/-- Helper for Lemma 10.96.5: the kernel inclusion
`K_n / I ^ n M^∧ → M^∧ / I ^ n M^∧` as a map of inverse systems. -/
noncomputable abbrev positive_stage_left_ι :
    (positive_stage_left_system (R := R) (I := I) (M := M)) ⟶
      (positive_stage_completion_system (R := R) (I := I) (M := M)) where
  app i := ModuleCat.ofHom
    (LinearMap.ker
      (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i))).subtype
  naturality := by
    intro i j f
    -- The left-system transition is defined by restricting the completion transition.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- Helper for Lemma 10.96.5: the stagewise quotient map
`M^∧ / I ^ n M^∧ → M / I ^ n M` as a map of inverse systems. -/
noncomputable abbrev positive_stage_stageMap :
    (positive_stage_completion_system (R := R) (I := I) (M := M)) ⟶
      (positive_stage_module_system (R := R) (I := I) (M := M)) where
  app i := ModuleCat.ofHom
    (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i))
  naturality := by
    intro i j f
    -- Naturality is exactly the arbitrary-stage commutative square proved above.
    apply ModuleCat.hom_ext
    simpa using (positive_stage_map_comm (I := I) (M := M) f).symm

/-- Helper for Lemma 10.96.5: the source-proof short complex of positive-stage inverse systems
`0 → K_n / I ^ n M^∧ → M^∧ / I ^ n M^∧ → M / I ^ n M → 0`. -/
noncomputable abbrev positive_stage_shortComplex : ShortComplex ModuleInverseSystem :=
  ShortComplex.mk
    (positive_stage_left_ι (R := R) (I := I) (M := M))
    (positive_stage_stageMap (R := R) (I := I) (M := M))
    (by
      -- Stagewise, the quotient-stage map vanishes on its kernel by definition.
      ext i x
      exact x.2)

/-- Helper for Lemma 10.96.5: the family of evaluation functors on `ModuleInverseSystem` is
jointly faithful, because a natural transformation is determined by its components. -/
private lemma positive_stage_evaluation_jointlyFaithful :
    CategoryTheory.JointlyFaithful
      (fun i : OrderDual ℕ+ ↦
        (evaluation (OrderDual ℕ+) (ModuleCat R)).obj i) where
  map_injective := by
    intro X Y f g hfg
    -- Equality of natural transformations is pointwise equality on every stage.
    ext i x
    exact congrArg (fun α ↦ α.hom x) (hfg i)

/-- Helper for Lemma 10.96.5: evaluating the positive-stage short complex at a fixed stage gives
the textbook quotient-stage kernel short exact sequence. -/
lemma positive_stage_shortComplex_eval_shortExact (i : OrderDual ℕ+) :
    ((positive_stage_shortComplex (R := R) (I := I) (M := M)).map
      ((evaluation (OrderDual ℕ+) (ModuleCat R)).obj i)).ShortExact := by
  -- Evaluating the inverse-system short complex at stage `i` recovers the stage-`stagePNat i`
  -- kernel short complex from the source proof.
  simpa [positive_stage_shortComplex, positive_stage_left_ι, positive_stage_stageMap] using
    ker_eval_quotient_stage_shortExact (I := I) (M := M) (stagePNat i)

/-- Helper for Lemma 10.96.5: the positive-stage short complex of inverse systems is short exact,
because each evaluation is exactly the quotient-stage kernel short exact sequence. -/
lemma positive_stage_quotient_system_shortExact :
    (positive_stage_shortComplex (R := R) (I := I) (M := M)).ShortExact := by
  let F : OrderDual ℕ+ → ModuleInverseSystem ⥤ ModuleCat R :=
    fun i ↦ (evaluation (OrderDual ℕ+) (ModuleCat R)).obj i
  let hReflect :
      CategoryTheory.JointlyReflectIsomorphisms F :=
    CategoryTheory.JointlyFaithful.jointlyReflectsIsomorphisms
      (F := F)
      (positive_stage_evaluation_jointlyFaithful (R := R))
  -- Reflect short exactness from the jointly faithful family of stage evaluations.
  refine
    (CategoryTheory.JointlyReflectIsomorphisms.shortExact_iff
      (F := F) hReflect
      (positive_stage_shortComplex (R := R) (I := I) (M := M))).2 ?_
  intro i
  exact positive_stage_shortComplex_eval_shortExact (R := R) (I := I) (M := M) i

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
    (fun {m n} hmn ↦ positive_stage_completion_eval_family_compat
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
  -- TODO: apply a universe-polymorphic copy of Lemma `10.87.1` to
  -- `positive_stage_shortComplex`. The imported theorem
  -- `moduleInverseLimit_shortExact_of_isMittagLeffler_left` is specialized to inverse systems in
  -- `ModuleCat R` at the ring universe, while this file works with `M : Type v`.
  sorry

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

/-- Lemma 10.96.5: the `I`-adic completion `AdicCompletion I M` is `I`-adically complete if and
only if, for every positive integer `n`, the kernel of the canonical projection
`AdicCompletion I M → M ⧸ (I ^ n • ⊤)` is exactly `I ^ n` times the completed module. -/
theorem isAdicComplete_adicCompletion_iff_ker_eval_eq_pow_smul_top :
    IsAdicComplete I (AdicCompletion I M) ↔
      ∀ n : ℕ+,
        (eval I M (n : ℕ)).ker =
          I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)) := by
  constructor
  · intro hcomplete
    have hleftZero :
        IsZero (limit (positive_stage_left_system (R := R) (I := I) (M := M))) := by
      -- Route correction: after the stagewise descent is installed, only the source-faithful
      -- inverse-limit exactness argument remains. The positive-stage comparison is rewritten as
      -- the completeness retraction `(M^∧)^∧ → M^∧`, so exactness and injectivity now finish.
      exact positive_stage_left_limit_isZero_of_complete
        (R := R) (I := I) (M := M) hcomplete
    intro n
    exact ker_eval_eq_pow_smul_top_of_left_limit_isZero
      (R := R) (I := I) (M := M) hleftZero n
  · intro hker
    refine
      { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
    · -- The kernel description forces every element vanishing modulo all `I ^ n` to be zero.
      refine ⟨fun x hx ↦ ?_⟩
      ext n
      cases n with
      | zero =>
          have hs : Subsingleton (M ⧸ (I ^ 0 • (⊤ : Submodule R M))) := by
            simpa using (show Subsingleton (M ⧸ (⊤ : Submodule R M)) from inferInstance)
          exact @Subsingleton.elim _ hs _ _
      | succ n =>
          have hxmem :
              x ∈ I ^ (n + 1) • (⊤ : Submodule R (AdicCompletion I M)) := by
            exact SModEq.zero.1 (hx (n + 1))
          have hkerStage :
              (eval I M (n + 1)).ker =
                I ^ (n + 1) • (⊤ : Submodule R (AdicCompletion I M)) := by
            simpa using hker ⟨n + 1, Nat.succ_pos _⟩
          have hxker : x ∈ (eval I M (n + 1)).ker := by
            rw [hkerStage]
            exact hxmem
          exact LinearMap.mem_ker.mp hxker
    · -- Reuse the standard completion proof skeleton, replacing finite generation by `hker`.
      refine ⟨fun x hx ↦ ?_⟩
      let L : AdicCompletion I M := {
        val i := (x i).val i
        property {m n} hmn := by
          cases m with
          | zero =>
              have hs : Subsingleton (M ⧸ (I ^ 0 • (⊤ : Submodule R M))) := by
                simpa using (show Subsingleton (M ⧸ (⊤ : Submodule R M)) from inferInstance)
              exact @Subsingleton.elim _ hs _ _
          | succ m =>
              have hkerStage :
                  I ^ (m + 1) • (⊤ : Submodule R (AdicCompletion I M)) =
                    (eval I M (m + 1)).ker := by
                simpa using (hker ⟨m + 1, Nat.succ_pos _⟩).symm
              have hcompat : (x n).val (m + 1) = (x (m + 1)).val (m + 1) := by
                have hcompat' := hx hmn
                rwa [SModEq.sub_mem, hkerStage, LinearMap.mem_ker,
                  _root_.map_sub, sub_eq_zero, eval_apply, eval_apply, eq_comm] at hcompat'
              calc
                AdicCompletion.transitionMap I M hmn ((fun i ↦ (x i).val i) n)
                    = (x n).val (m + 1) := by
                        simpa using AdicCompletion.transitionMap_comp_eval_apply
                          (I := I) (M := M) (m := m + 1) (n := n) (hmn := hmn) (x := x n)
                _ = (x (m + 1)).val (m + 1) := hcompat
      }
      use L
      intro i
      cases i with
      | zero =>
          rw [SModEq.sub_mem]
          simpa using
            (show x 0 - L ∈ (⊤ : Submodule R (AdicCompletion I M)) from Submodule.mem_top _)
      | succ i =>
          -- At stage `i + 1`, the difference vanishes because its image in the quotient is zero.
          have hkerStage :
              I ^ (i + 1) • (⊤ : Submodule R (AdicCompletion I M)) =
                (eval I M (i + 1)).ker := by
            simpa using (hker ⟨i + 1, Nat.succ_pos _⟩).symm
          rw [SModEq.sub_mem, hkerStage, LinearMap.mem_ker,
            _root_.map_sub, sub_eq_zero, eval_apply]
          simp [L]

end
