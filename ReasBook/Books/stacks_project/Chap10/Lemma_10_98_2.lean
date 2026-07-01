import Mathlib
import stacks_project.Chap10.Lemma_10_86_3
import stacks_project.Chap10.Lemma_10_87_1
import stacks_project.Chap10.Lemma_10_98_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

local notation "ModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat A
local notation "moduleInvLim" => (lim : ModuleInverseSystem ⥤ ModuleCat A)

/- Domain triage:
* `source-facing`: Lemma `10.98.2` studies a sequential inverse system of `A`-modules whose
  transition kernels are exactly the ideal-power submodules `I ^ n M_{n + 1}`, and concludes that
  each canonical quotient `(\varprojlim M_n) / I^n (\varprojlim M_n)` identifies with `M_n`.
* `core/canonical` owners: the inverse system itself as a functor `OrderDual ℕ+ ⥤ ModuleCat A`,
  its stages `M_.obj (OrderDual.toDual n)`, the canonical projections `limit.π`, the quotient
  equivalence API `LinearMap.quotKerEquivOfSurjective` and `Submodule.quotEquivOfEq`, and the
  owner predicate `IsAdicComplete`.
* `bridge/view`: the lower-level surjectivity and kernel calculation for the canonical projection
  `lim M_ → M_n` are companion ingredients used only to build the canonical quotient equivalence.

Relevant owner declarations sampled for this refinement:
* `CategoryTheory.Limits.limit.π`
* `IsAdicComplete`
* `isAdicComplete_inverseLimit_of_stagewise_pow_smul_top_eq_bot`
* the inverse-limit comparison pattern in `Lemma_10_98_4`

Primitive data are only the inverse system `M_` and the source hypotheses on its transition maps.
The stages, limit module, and limit projections are canonical derived API from that owner, so the
public statement keeps the stagewise surjectivity and kernel-identification hypotheses explicit
instead of packaging them into a second owner predicate. -/

private theorem pnat_le_succ (n : ℕ+) : n ≤ n + 1 := by
  exact_mod_cast Nat.le_succ (n : ℕ)

/-- Helper for Lemma 10.98.2: the transition map from stage `j` down to stage `i` for a
comparison `i ≤ j` in `ℕ+`. -/
private abbrev transitionMap (M_ : ModuleInverseSystem) {i j : ℕ+} (hij : i ≤ j) :
    M_.obj (OrderDual.toDual j) →ₗ[A] M_.obj (OrderDual.toDual i) :=
  (M_.map (homOfLE (show OrderDual.toDual j ≤ OrderDual.toDual i from hij))).hom

private abbrev stageMap (M_ : ModuleInverseSystem) (n : ℕ+) :
    M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n) :=
  transitionMap M_ (pnat_le_succ n)

private abbrev limitProjection (M_ : ModuleInverseSystem) (n : ℕ+) :
    (limit M_ : ModuleCat A) →ₗ[A] M_.obj (OrderDual.toDual n) :=
  (limit.π M_ (OrderDual.toDual n)).hom

/-- Helper for Lemma 10.98.2: the `n`th limit projection is the successor-stage projection
followed by the structure map `M_{n + 1} → M_n`. -/
private theorem stageMap_comp_limitProjection_eq
    (M_ : ModuleInverseSystem) (n : ℕ+) :
    (stageMap M_ n).comp (limitProjection M_ (n + 1)) = limitProjection M_ n := by
  -- This is the defining compatibility relation of the limit cone.
  ext x
  change
    ((limit.π M_ (OrderDual.toDual (n + 1))) ≫
        M_.map
          (homOfLE
            (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n))).hom x =
      (limit.π M_ (OrderDual.toDual n)).hom x
  simpa using
    congrArg (fun g ↦ g.hom x)
      (limit.w M_
        (homOfLE
          (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n)))

/-- Helper for Lemma 10.98.2: any transition from stage `j + 1` down to stage `i` factors through
the immediate successor map `M_{j + 1} → M_j`. -/
private theorem transitionMap_step_eq_comp
    (M_ : ModuleInverseSystem) {i j : ℕ+} (hij : i ≤ j) :
    transitionMap M_ (Nat.le.step hij) = (transitionMap M_ hij).comp (stageMap M_ j) := by
  -- In the preorder category `OrderDual ℕ+`, every comparison map is unique, so the long
  -- transition is the composite of the successor map with the shorter transition.
  ext x
  change (M_.map (homOfLE (show OrderDual.toDual (j + 1) ≤ OrderDual.toDual i from Nat.le.step hij))).hom x =
    (M_.map (homOfLE (show OrderDual.toDual j ≤ OrderDual.toDual i from hij))).hom
      ((M_.map (homOfLE (show OrderDual.toDual (j + 1) ≤ OrderDual.toDual j from pnat_le_succ j))).hom x)
  have hcomp :
      homOfLE (show OrderDual.toDual (j + 1) ≤ OrderDual.toDual i from Nat.le.step hij) =
        homOfLE (show OrderDual.toDual (j + 1) ≤ OrderDual.toDual j from pnat_le_succ j) ≫
          homOfLE (show OrderDual.toDual j ≤ OrderDual.toDual i from hij) := by
    exact Subsingleton.elim _ _
  rw [hcomp, Functor.map_comp]
  rfl

/-- Helper for Lemma 10.98.2: each stage `M_n` is annihilated by `I ^ n` because the successor
kernel is exactly `I ^ n M_{n + 1}` and the successor map is surjective. -/
private theorem stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients
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
    ∀ n : ℕ+,
      I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥ := by
  intro n
  -- Map the source-proof kernel description through the surjective successor map.
  have hmapker :
      Submodule.map (stageMap M_ n) (LinearMap.ker (stageMap M_ n)) = ⊥ := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, rfl⟩
      exact LinearMap.mem_ker.mp hx
    · intro hy
      rw [Submodule.mem_bot] at hy
      subst hy
      refine ⟨0, ?_, map_zero _⟩
      exact LinearMap.mem_ker.mpr (map_zero (stageMap M_ n))
  calc
    I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n)))
        = I ^ (n : ℕ) • LinearMap.range (stageMap M_ n) := by
            rw [LinearMap.range_eq_top.2 (hSurj n)]
    _ = Submodule.map (stageMap M_ n)
          (I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual (n + 1))))) := by
            rw [Submodule.map_smul'', Submodule.map_top]
    _ = Submodule.map (stageMap M_ n) (LinearMap.ker (stageMap M_ n)) := by
            rw [hKer n]
    _ = ⊥ := hmapker

/-- Helper for Lemma 10.98.2: every long transition map in the inverse system is surjective once
the successor maps are surjective. -/
private theorem transitionMap_surjective_of_successive_ideal_power_quotients
    (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    {i j : ℕ+} (hij : i ≤ j) :
    Function.Surjective (transitionMap M_ hij) := by
  let offsetStage : ℕ → ℕ+ := fun k ↦
    ⟨(i : ℕ) + k, Nat.add_pos_left i.2 k⟩
  have hoffset :
      ∀ k : ℕ,
        Function.Surjective
          (transitionMap M_ (show i ≤ offsetStage k from Nat.le_add_right i k)) := by
    intro k
    induction k with
    | zero =>
      -- Offset `0` is the identity transition from stage `i` to itself.
        have hId :
            transitionMap M_ (show i ≤ offsetStage 0 from Nat.le_add_right i 0) =
              (LinearMap.id : M_.obj (OrderDual.toDual i) →ₗ[A] M_.obj (OrderDual.toDual i)) := by
          ext x
          change (M_.map (homOfLE (show OrderDual.toDual i ≤ OrderDual.toDual i from le_rfl))).hom x = x
          have hhom : homOfLE (show OrderDual.toDual i ≤ OrderDual.toDual i from le_rfl) =
              𝟙 (OrderDual.toDual i) := by
            exact Subsingleton.elim _ _
          simpa [hhom]
        rw [hId]
        exact fun x ↦ ⟨x, rfl⟩
    | succ k ih =>
        -- Offset `k + 1` factors through the immediate successor of offset `k`.
        have hstep :
            offsetStage (k + 1) = offsetStage k + 1 := by
          apply Subtype.ext
          rfl
        have hcomp :
            transitionMap M_ (show i ≤ offsetStage (k + 1) from Nat.le_add_right i (k + 1)) =
              (transitionMap M_ (show i ≤ offsetStage k from Nat.le_add_right i k)).comp
                (stageMap M_ (offsetStage k)) := by
          simpa [hstep] using
            (transitionMap_step_eq_comp M_ (show i ≤ offsetStage k from Nat.le_add_right i k))
        rw [hcomp]
        exact ih.comp (hSurj (offsetStage k))
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  have hj : j = offsetStage k := by
    apply Subtype.ext
    simpa [offsetStage] using hk
  subst hj
  simpa using hoffset k

/-- Helper for Lemma 10.98.2: each canonical projection from the inverse limit onto stage `n` is
surjective. -/
private theorem limit_projection_surjective_of_successive_ideal_power_quotients
    (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (n : ℕ+) :
    Function.Surjective (limitProjection M_ n) := by
  classical
  let F := M_ ⋙ forget (ModuleCat A)
  have hAllSurj :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j), Function.Surjective (F.map f) := by
    intro i j f
    simpa [F, transitionMap] using
      transitionMap_surjective_of_successive_ideal_power_quotients M_ hSurj (leOfHom f)
  have hML : F.IsMittagLeffler := by
    -- The underlying set-valued system is Mittag-Leffler because every transition is surjective.
    exact Functor.isMittagLeffler_of_surjective (F := F) hAllSurj
  intro x
  let s : Set (F.obj (OrderDual.toDual n)) := Set.singleton x
  haveI :
      ∀ j : OrderDual ℕ+,
        Nonempty ((F.toPreimages s).obj j) := by
    intro j
    exact F.toPreimages_nonempty_of_surjective s hAllSurj (Set.singleton_nonempty x) j
  obtain ⟨sec, hsec⟩ :=
    nonempty_sections_of_countable_mittagLeffler_inverse_system (A := F.toPreimages s)
      (Functor.IsMittagLeffler.toPreimages (F := F) (s := s) hML)
  let secF : F.sections :=
    ⟨fun j ↦ (sec j).1, fun f ↦ by
      exact congrArg Subtype.val (hsec f)⟩
  let y : limit F := (Types.limitEquivSections F).symm secF
  refine ⟨(preservesLimitIso (forget (ModuleCat A)) M_).inv y, ?_⟩
  have hπ :=
    congrArg
      (fun g ↦ g ((preservesLimitIso (forget (ModuleCat A)) M_).inv y))
      (preservesLimitIso_hom_π (G := forget (ModuleCat A)) (F := M_) (j := OrderDual.toDual n))
  have hmem : (sec (OrderDual.toDual n)).1 = x := by
    -- Unpack the defining `toPreimages` condition at the identity morphism.
    have hsecMem : (sec (OrderDual.toDual n)).1 ∈
        ⋂ f : OrderDual.toDual n ⟶ OrderDual.toDual n, F.map f ⁻¹' s := by
      simpa [Functor.toPreimages_obj] using (sec (OrderDual.toDual n)).2
    rw [Set.mem_iInter] at hsecMem
    have hid := hsecMem (𝟙 (OrderDual.toDual n))
    simpa [s] using hid
  have hsec :
      limit.π F (OrderDual.toDual n) y = (secF : ∀ j, F.obj j) (OrderDual.toDual n) := by
    simpa [y] using
      (Types.limitEquivSections_symm_apply (F := F) (x := secF) (j := OrderDual.toDual n))
  have hy :
      limit.π F (OrderDual.toDual n) y = x := by
    -- Evaluate the chosen section at stage `n` and use that this stage is forced to equal `x`.
    simpa [secF, hmem]
      using hsec
  have hproj0 :
      limitProjection M_ n ((preservesLimitIso (forget (ModuleCat A)) M_).inv y) =
        ((forget (ModuleCat A)).map (limit.π M_ (OrderDual.toDual n)))
          ((preservesLimitIso (forget (ModuleCat A)) M_).inv y) := by
    rfl
  have hproj1 :
      ((forget (ModuleCat A)).map (limit.π M_ (OrderDual.toDual n)))
          ((preservesLimitIso (forget (ModuleCat A)) M_).inv y) =
        ((preservesLimitIso (forget (ModuleCat A)) M_).hom ≫
          limit.π F (OrderDual.toDual n))
            ((preservesLimitIso (forget (ModuleCat A)) M_).inv y) := by
    exact hπ.symm
  have hproj2 :
      ((preservesLimitIso (forget (ModuleCat A)) M_).hom ≫
          limit.π F (OrderDual.toDual n))
            ((preservesLimitIso (forget (ModuleCat A)) M_).inv y) =
        limit.π F (OrderDual.toDual n) y := by
    simp
  exact hproj0.trans (hproj1.trans (hproj2.trans hy))

/-- Helper for Lemma 10.98.2: a readable name for the positive stage attached to an object of
`OrderDual ℕ+`. -/
private abbrev stagePNat (i : OrderDual ℕ+) : ℕ+ :=
  OrderDual.ofDual i

/-- Helper for Lemma 10.98.2: the stage obtained by shifting `n` forward by `k` successor steps. -/
private abbrev stageShiftPNat (n : ℕ+) (k : ℕ) : ℕ+ :=
  ⟨(n : ℕ) + k, Nat.add_pos_left n.2 k⟩

/-- Helper for Lemma 10.98.2: the source identity
`N_{n + 1} + I ^ n (\varprojlim M_i) = N_n` for the kernels of the limit projections. -/
private theorem limit_projection_ker_succ_sup_pow_smul_top_of_successive_ideal_power_quotients
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
    LinearMap.ker (limitProjection M_ (n + 1)) ⊔
        I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)) =
      LinearMap.ker (limitProjection M_ n) := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer
  apply le_antisymm
  · -- The two source summands already map to zero in stage `n`.
    rw [sup_le_iff]
    constructor
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      calc
        limitProjection M_ n x =
            stageMap M_ n (limitProjection M_ (n + 1) x) := by
              simpa [LinearMap.comp_apply] using
                congrArg (fun g ↦ g x) (stageMap_comp_limitProjection_eq M_ n).symm
        _ = stageMap M_ n 0 := by rw [hx]
        _ = 0 := by exact map_zero (stageMap M_ n)
    · exact limit_projection_pow_smul_top_le_ker I M_ hStage n
  · intro x hx
    -- Route correction: follow the source proof and split `x` using the stagewise kernel
    -- description at `M_{n + 1} → M_n`, instead of attacking injectivity directly.
    have hxstage :
        limitProjection M_ (n + 1) x ∈
          I ^ (n : ℕ) •
            (⊤ : Submodule A (M_.obj (OrderDual.toDual (n + 1)))) := by
      have hxker :
          limitProjection M_ (n + 1) x ∈ LinearMap.ker (stageMap M_ n) := by
        rw [LinearMap.mem_ker]
        rw [LinearMap.mem_ker] at hx
        calc
          stageMap M_ n (limitProjection M_ (n + 1) x) =
              limitProjection M_ n x := by
                simpa [LinearMap.comp_apply] using
                  congrArg (fun g ↦ g x) (stageMap_comp_limitProjection_eq M_ n)
          _ = 0 := hx
      rw [hKer n] at hxker
      exact hxker
    have hmap :
        limitProjection M_ (n + 1) x ∈
          Submodule.map (limitProjection M_ (n + 1))
            (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A))) := by
      have hmap_smul :
          Submodule.map (limitProjection M_ (n + 1))
              (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A))) =
            I ^ (n : ℕ) •
              (⊤ : Submodule A (M_.obj (OrderDual.toDual (n + 1)))) := by
        calc
          Submodule.map (limitProjection M_ (n + 1))
              (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A))) =
            I ^ (n : ℕ) •
              Submodule.map (limitProjection M_ (n + 1))
                (⊤ : Submodule A (limit M_ : ModuleCat A)) := by
                  rw [Submodule.map_smul'']
          _ = I ^ (n : ℕ) • LinearMap.range (limitProjection M_ (n + 1)) := by
                rw [Submodule.map_top]
          _ = I ^ (n : ℕ) •
                (⊤ : Submodule A (M_.obj (OrderDual.toDual (n + 1)))) := by
                  rw [LinearMap.range_eq_top.2
                    (limit_projection_surjective_of_successive_ideal_power_quotients
                      M_ hSurj (n + 1))]
      rw [hmap_smul]
      exact hxstage
    rcases hmap with ⟨y, hyI, hyproj⟩
    refine Submodule.mem_sup.2 ⟨x - y, ?_, y, hyI, by simp⟩
    rw [LinearMap.mem_ker]
    calc
      limitProjection M_ (n + 1) (x - y) =
          limitProjection M_ (n + 1) x - limitProjection M_ (n + 1) y := by
            simpa using (limitProjection M_ (n + 1)).map_sub x y
      _ = 0 := by
            rw [hyproj]
            exact sub_self _

/-- Helper for Lemma 10.98.2: the successor quotient transition on
`(\varprojlim M_i) / I ^ n (\varprojlim M_i)`. -/
private abbrev limit_projection_positive_stage_map
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
private theorem limit_projection_quotient_desc_ker
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
private theorem limit_projection_positive_stage_map_comm
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
private theorem limit_projection_positive_stage_map_mem_kernel
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
private abbrev quotient_desc_kernel_transition
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
private theorem quotient_desc_kernel_transition_surjective_of_successive_ideal_power_quotients
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
private noncomputable abbrev limit_projection_quotient_system
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
private noncomputable abbrev limit_projection_kernel_system
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
private theorem limit_projection_kernel_system_map_succ
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
private theorem limit_projection_kernel_gap_map_surjective
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
private theorem limit_projection_kernel_system_homOfLE_surjective
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
private theorem limit_projection_kernel_system_map_surjective
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
private theorem limit_projection_kernel_system_isMittagLeffler_of_successive_ideal_power_quotients
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
private noncomputable abbrev limit_projection_kernel_ι
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
private noncomputable abbrev limit_projection_stageMap
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
private noncomputable abbrev limit_projection_quotient_shortComplex
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
private lemma limit_projection_evaluation_jointlyFaithful :
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
private theorem limit_projection_quotient_shortComplex_shortExact
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

/-- Helper for Lemma 10.98.2: extend a cone on the positive-stage quotient system of `limit M_`
by the trivial zeroth quotient. -/
private noncomputable def limit_projection_quotient_family
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
private theorem limit_projection_quotient_family_compat
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
private theorem limit_projection_quotient_family_pnat
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
private theorem limit_projection_quotient_completion_cone_naturality
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
private noncomputable abbrev limit_projection_quotient_completion_cone
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
private theorem limit_projection_quotient_completion_hom_ext
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
private noncomputable abbrev limit_projection_quotient_completion_lift
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
private theorem limit_projection_quotient_completion_lift_fac
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
private theorem limit_projection_quotient_completion_lift_uniq
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
private noncomputable def limit_projection_quotient_completion_isLimit
    (I : Ideal A) (M_ : ModuleInverseSystem) :
    IsLimit (limit_projection_quotient_completion_cone I M_) where
  lift := limit_projection_quotient_completion_lift I M_
  fac := limit_projection_quotient_completion_lift_fac I M_
  uniq := limit_projection_quotient_completion_lift_uniq I M_

/-- Helper for Lemma 10.98.2: the positive-stage quotient system of `limit M_` has inverse limit
the adic completion of `limit M_`. -/
private noncomputable abbrev limit_projection_quotient_limitCone
    (I : Ideal A) (M_ : ModuleInverseSystem) :
    LimitCone (limit_projection_quotient_system I M_) :=
  { cone := limit_projection_quotient_completion_cone I M_
    isLimit := limit_projection_quotient_completion_isLimit I M_ }

/-- Helper for Lemma 10.98.2: the positive-stage quotient system attached to `limit M_` is
canonically identified with the adic completion of `limit M_`. -/
private noncomputable abbrev limit_projection_quotient_limit_iso
    (I : Ideal A) (M_ : ModuleInverseSystem) :
    limit (limit_projection_quotient_system I M_) ≅
      ModuleCat.of A (AdicCompletion I (limit M_ : ModuleCat A)) :=
  show limit (limit_projection_quotient_system I M_) ≅
      ModuleCat.of A (AdicCompletion I (limit M_ : ModuleCat A)) from
    limit.isoLimitCone (limit_projection_quotient_limitCone I M_)

/-- Helper for Lemma 10.98.2: the inverse of the quotient-system limit identification evaluates to
the canonical completion quotient map at each positive stage. -/
private theorem limit_projection_quotient_limit_iso_inv_π
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
private theorem limit_projection_quotient_limit_iso_hom_π
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
private theorem quotient_limit_map_eq_completion_to_inverse_limit
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
private theorem completion_to_inverse_limit_bijective_of_complete
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
private theorem stage_annihilation_witness_eq
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
private abbrev limit_projection_quotient_shortComplex_input
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
private theorem limit_projection_quotient_shortComplex_input_shortExact
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
private theorem limit_projection_kernel_system_isMittagLeffler_input
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
private theorem limit_projection_quotient_shortComplex_input_f_eq
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
private theorem limit_projection_quotient_shortComplex_input_g_eq
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
private abbrev limit_projection_forgetToAbelianGroup : ModuleCat A ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat A) AddCommGrpCat.{u}

/-- Helper for Lemma 10.98.2: the ambient category of abelian-group inverse systems over `ℕ+`. -/
private abbrev limit_projection_AbelianGroupInverseSystem : Type (u + 1) :=
  OrderDual ℕ+ ⥤ AddCommGrpCat.{u}

/-- Helper for Lemma 10.98.2: the inverse-limit functor on abelian-group inverse systems. -/
private abbrev limit_projection_abelianInvLim :
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
private abbrev limit_projection_forgetInverseSystemFunctor :
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
private abbrev limit_projection_moduleInvLim : ModuleInverseSystem ⥤ ModuleCat A where
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
private instance limit_projection_moduleInvLim_preservesZeroMorphisms :
    (limit_projection_moduleInvLim (A := A)).PreservesZeroMorphisms where
  map_zero X Y := by
    -- A morphism of inverse limits is zero once all its stagewise projections are zero.
    apply limit.hom_ext
    intro j
    simp [limit_projection_moduleInvLim]

/-- Helper for Lemma 10.98.2: the canonical comparison between forgetting after inverse limits and
taking inverse limits after forgetting commutes with every morphism of inverse systems. -/
private theorem limit_projection_preservesLimitIso_hom_limMap_forget
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
private theorem limit_projection_forgetInverseSystemFunctor_map_eq
    {X Y : ModuleInverseSystem} (α : X ⟶ Y) :
    (limit_projection_forgetInverseSystemFunctor (A := A)).map α =
      Functor.whiskerRight α limit_projection_forgetToAbelianGroup := by
  rfl

/-- Helper for Lemma 10.98.2: applying Lemma `10.87.1` to the frozen source short complex gives a
short exact sequence on inverse limits. -/
private theorem limit_projection_quotient_shortComplex_limit_shortExact
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
    ((limit_projection_quotient_shortComplex_input I M_ hSurj hKer).map
      limit_projection_moduleInvLim).ShortExact := by
  -- TODO: replay Lemma `10.87.1` in the low-universe adapter category built above, then reflect
  -- the forgotten short exactness back along `limit_projection_forgetToAbelianGroup`.
  -- The remaining blocker is the categorical comparison between the custom functor
  -- `limit_projection_moduleInvLim` and the forgotten inverse-limit functor used by
  -- Lemma `10.86.4`.
  sorry

/-- Helper for Lemma 10.98.2: the inverse-limit row coming from the frozen source short complex is
exact in the concrete linear-map form used later in the proof. -/
private theorem limit_projection_limit_row_exact
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
    Function.Exact
        ((limMap
            (limit_projection_kernel_ι I M_
              (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients
                I M_ hSurj hKer))).hom)
        ((limMap
            (limit_projection_stageMap I M_
              (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients
                I M_ hSurj hKer))).hom) := by
  have hLimitShortExact :
      ((limit_projection_quotient_shortComplex_input I M_ hSurj hKer).map
        limit_projection_moduleInvLim).ShortExact :=
    limit_projection_quotient_shortComplex_limit_shortExact I M_ hSurj hKer
  -- Rewrite the categorical exactness field into the concrete `Function.Exact` statement
  -- requested by the downstream completion argument.
  simpa [limit_projection_quotient_shortComplex_input_f_eq,
    limit_projection_quotient_shortComplex_input_g_eq, limit_projection_moduleInvLim] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      ((limit_projection_quotient_shortComplex_input I M_ hSurj hKer).map
        limit_projection_moduleInvLim)).1 hLimitShortExact.exact

/-- Helper for Lemma 10.98.2: the two inverse-limit consequences needed from the source short
exact row, namely exactness in the middle and monicity on the left. -/
private theorem limit_projection_quotient_limit_exact_and_mono_of_successive_ideal_power_quotients
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
    Function.Exact
        ((limMap
            (limit_projection_kernel_ι I M_
              (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients
                I M_ hSurj hKer))).hom)
        ((limMap
            (limit_projection_stageMap I M_
              (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients
                I M_ hSurj hKer))).hom) ∧
      Mono
        (limMap
        (limit_projection_kernel_ι I M_
          (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients
              I M_ hSurj hKer))) := by
  have hLimitShortExact :
      ((limit_projection_quotient_shortComplex_input I M_ hSurj hKer).map
        limit_projection_moduleInvLim).ShortExact :=
    limit_projection_quotient_shortComplex_limit_shortExact I M_ hSurj hKer
  constructor
  · -- First extract exactness from the short exact inverse-limit row in the concrete form needed.
    exact limit_projection_limit_row_exact I M_ hSurj hKer
  · -- Then project the monomorphism of the left map from the same short exact sequence.
    simpa [limit_projection_quotient_shortComplex_input_f_eq, limit_projection_moduleInvLim] using
      hLimitShortExact.mono_f

/-- Helper for Lemma 10.98.2: applying the frozen inverse-limit short exact sequence gives
exactness of
`lim K_n → lim ((lim M_i)/I^n lim M_i) → lim M_n`. -/
private theorem limit_projection_quotient_limit_exact_of_successive_ideal_power_quotients
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
    Function.Exact
      ((limMap
          (limit_projection_kernel_ι I M_
            (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer))).hom)
      ((limMap
          (limit_projection_stageMap I M_
            (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer))).hom) := by
  -- Project the exactness component from the single remaining source-faithful blocker.
  exact
    (limit_projection_quotient_limit_exact_and_mono_of_successive_ideal_power_quotients
      I M_ hSurj hKer).1

/-- Helper for Lemma 10.98.2: the left map in the inverse-limit short complex is monic. -/
private theorem limit_projection_kernel_limit_map_mono_of_successive_ideal_power_quotients
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
    Mono
      (limMap
        (limit_projection_kernel_ι I M_
          (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer))) := by
  -- Project the monomorphism component from the same remaining blocker theorem.
  exact
    (limit_projection_quotient_limit_exact_and_mono_of_successive_ideal_power_quotients
      I M_ hSurj hKer).2

/-- Helper for Lemma 10.98.2: the map on inverse limits
`\varprojlim ((\varprojlim M_i) / I^n (\varprojlim M_i)) → \varprojlim M_n`
is injective, because after identifying the middle limit with the adic completion it is the
completion comparison from Lemma `10.98.1`. -/
private theorem limit_projection_quotient_limit_map_injective_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
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
    Function.Injective
      ((limMap
          (limit_projection_stageMap I M_
            (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer))).hom) := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer
  have hcomplete :
      IsAdicComplete I (limit M_ : ModuleCat A) := by
    exact isAdicComplete_inverseLimit_of_stagewise_pow_smul_top_eq_bot I hI M_ hStage
  have hbij :
      Function.Bijective (completion_to_inverse_limit I M_ hStage) := by
    exact completion_to_inverse_limit_bijective_of_complete I M_ hStage hcomplete
  -- Rewrite the right map as the completion comparison preceded by the canonical middle isomorphism.
  rw [quotient_limit_map_eq_completion_to_inverse_limit I M_ hStage]
  intro x y hxy
  have hmid :
      (limit_projection_quotient_limit_iso I M_).hom x =
        (limit_projection_quotient_limit_iso I M_).hom y := by
    exact hbij.1 hxy
  have hmid_inj :
      Function.Injective ((limit_projection_quotient_limit_iso I M_).hom) := by
    intro a b hab
    have hab' := congrArg (fun z ↦ (limit_projection_quotient_limit_iso I M_).inv z) hab
    simpa using hab'
  exact hmid_inj hmid

/-- Helper for Lemma 10.98.2: the inverse limit of the kernel system
`ker((\varprojlim M_i) / I^n (\varprojlim M_i) → M_n)` vanishes. -/
private theorem limit_projection_kernel_limit_isZero_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
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
    IsZero
      (limit
        (limit_projection_kernel_system I M_
          (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer))) := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer
  have hExact :
      Function.Exact
        ((limMap (limit_projection_kernel_ι I M_ hStage)).hom)
        ((limMap (limit_projection_stageMap I M_ hStage)).hom) := by
    -- Lemma `10.87.1` gives the exact inverse-limit row from the source short complex.
    simpa [hStage] using
      limit_projection_quotient_limit_exact_of_successive_ideal_power_quotients
        I M_ hSurj hKer
  have hRightInj :
      Function.Injective ((limMap (limit_projection_stageMap I M_ hStage)).hom) := by
    -- The right map is the completion comparison in disguise, hence injective by completeness.
    simpa [hStage] using
      limit_projection_quotient_limit_map_injective_of_successive_ideal_power_quotients
        I hI M_ hSurj hKer
  have hf_zero : limMap (limit_projection_kernel_ι I M_ hStage) = 0 := by
    -- Exactness forces the image of the left map into the kernel of an injective right map.
    apply ModuleCat.hom_ext
    ext x
    apply hRightInj
    simpa using
      LinearMap.congr_fun (Function.Exact.linearMap_comp_eq_zero hExact) x
  letI :
      Mono (limMap (limit_projection_kernel_ι I M_ hStage)) := by
    simpa [hStage] using
      limit_projection_kernel_limit_map_mono_of_successive_ideal_power_quotients
        I M_ hSurj hKer
  have hzero :
      IsZero (limit (limit_projection_kernel_system I M_ hStage)) := by
    -- A monomorphism which is also the zero map can only have the zero object as source.
    exact IsZero.of_mono_eq_zero (limMap (limit_projection_kernel_ι I M_ hStage)) hf_zero
  simpa [hStage] using hzero

/-- Helper for Lemma 10.98.2: the descended quotient-stage map is bijective once the source-proof
inverse-system-of-kernels argument is installed. -/
private theorem inverse_limit_quotient_desc_bijective_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
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
    ∀ n : ℕ+,
      Function.Bijective
        (limit_projection_quotient_desc I M_
          (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer) n) := by
  intro n
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer
  have hKernelLimitZero :
      IsZero (limit (limit_projection_kernel_system I M_ hStage)) := by
    -- This is the source step `lim N_n/(N_n ∩ I^n M) = 0`.
    simpa [hStage] using
      limit_projection_kernel_limit_isZero_of_successive_ideal_power_quotients
        I hI M_ hSurj hKer
  refine ⟨?_, ?_⟩
  · -- Route correction: injectivity is the remaining kernel-vanishing step from the source proof.
    have hsurjKernel :
        Function.Surjective (limitProjection (limit_projection_kernel_system I M_ hStage) n) := by
      -- The kernel system itself has surjective successor maps, so its limit projects
      -- surjectively onto every stage.
      apply limit_projection_surjective_of_successive_ideal_power_quotients
        (M_ := limit_projection_kernel_system I M_ hStage)
      intro m
      simpa [hStage, limit_projection_kernel_system_map_succ] using
        quotient_desc_kernel_transition_surjective_of_successive_ideal_power_quotients
          I M_ hSurj hKer m
    have hker_bot :
        LinearMap.ker (limit_projection_quotient_desc I M_ hStage n) = ⊥ := by
      apply (Submodule.eq_bot_iff _).mpr
      intro y hy
      let y' : LinearMap.ker (limit_projection_quotient_desc I M_ hStage n) := ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hsurjKernel y'
      have hid :
          (𝟙 (limit (limit_projection_kernel_system I M_ hStage)) :
            limit (limit_projection_kernel_system I M_ hStage) ⟶
              limit (limit_projection_kernel_system I M_ hStage)) = 0 := by
        exact (IsZero.iff_id_eq_zero
          (X := limit (limit_projection_kernel_system I M_ hStage))).1 hKernelLimitZero
      have hx0 : x = 0 := by
        calc
          x = (𝟙 _ :
              limit (limit_projection_kernel_system I M_ hStage) ⟶
                limit (limit_projection_kernel_system I M_ hStage)) x := by simp
          _ = 0 := by simpa [hid]
      have hy' : y' = 0 := by
        calc
          y' = (limitProjection (limit_projection_kernel_system I M_ hStage) n) x := hx.symm
          _ = (limitProjection (limit_projection_kernel_system I M_ hStage) n) 0 := by rw [hx0]
          _ = 0 := by
                simpa using (limitProjection (limit_projection_kernel_system I M_ hStage) n).map_zero
      have hy0 : y = 0 := by
        exact congrArg Subtype.val hy'
      exact hy0
    exact LinearMap.ker_eq_bot.1 hker_bot
  · intro x
    -- Surjectivity descends from the already-proved surjectivity of `lim M_ → M_n`.
    rcases limit_projection_surjective_of_successive_ideal_power_quotients M_ hSurj n x with
      ⟨y, rfl⟩
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    simpa [hStage] using
      congrArg (fun g ↦ g y) (limit_projection_quotient_desc_comp_mkQ I M_ hStage n)

/-- Lemma 10.98.2: if a sequential inverse system of `A`-modules has transition maps
`M_{n + 1} → M_n` that are surjective with kernel `I^n M_{n + 1}`, then for every `n` the
canonical quotient `(\varprojlim M_n) / I^n (\varprojlim M_n)` is linearly equivalent to the `n`th
stage. -/
abbrev inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
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
    ((limit M_ : ModuleCat A) ⧸
        (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)))) ≃ₗ[A]
      M_.obj (OrderDual.toDual n) :=
  LinearEquiv.ofBijective
    (limit_projection_quotient_desc I M_
      (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer) n)
    (inverse_limit_quotient_desc_bijective_of_successive_ideal_power_quotients
      I hI M_ hSurj hKer n)

-- Proof sketch: unfold the quotient equivalence into the kernel-identification equivalence followed
-- by the first isomorphism theorem for the surjective projection `lim M_ → M_n`, then apply the
-- corresponding `quotKerEquivOfSurjective_apply_mk` computation rule.
/-- The quotient equivalence of Lemma `10.98.2` sends the class of an inverse-limit element to its
`n`th stage projection. -/
theorem inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_apply_mk
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
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
    (n : ℕ+) (x : (limit M_ : ModuleCat A)) :
    inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients
        I hI M_ hSurj hKer n (Submodule.Quotient.mk x) =
      limitProjection M_ n x := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer
  -- Evaluate the imported quotient-desc computation rule on the representative `x`.
  simpa [inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients, hStage] using
    congrArg (fun g ↦ g x) (limit_projection_quotient_desc_comp_mkQ I M_ hStage n)

-- Proof sketch: the kernel computation implies `I^n M_n = 0` for every stage, so Lemma `10.98.1`
-- applies directly to the inverse system `M_`.
/-- The inverse limit of a sequential system with successive quotients `M_n = M_{n + 1} / I^n
M_{n + 1}` is `I`-adically complete. -/
theorem isAdicComplete_inverseLimit_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
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
    IsAdicComplete I (limit M_ : ModuleCat A) := by
  -- Apply Lemma `10.98.1` to the stagewise annihilation statement just proved above.
  exact isAdicComplete_inverseLimit_of_stagewise_pow_smul_top_eq_bot I hI M_
    (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer)

end
