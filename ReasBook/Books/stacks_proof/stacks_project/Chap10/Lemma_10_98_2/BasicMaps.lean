import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_86_3
import stacks_proof.stacks_project.Chap10.Lemma_10_87_1
import stacks_proof.stacks_project.Chap10.Lemma_10_98_1

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

local notation "ModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat A
local notation "moduleInvLim" => (lim : ModuleInverseSystem ⥤ ModuleCat A)

/-- Helper for Chap10 Lemma 10 98 2: every positive natural number is at most its successor. -/
theorem pnat_le_succ (n : ℕ+) : n ≤ n + 1 := by
  exact_mod_cast Nat.le_succ (n : ℕ)

/-- Helper for Lemma 10.98.2: the transition map from stage `j` down to stage `i` for a
comparison `i ≤ j` in `ℕ+`. -/
abbrev transitionMap (M_ : ModuleInverseSystem) {i j : ℕ+} (hij : i ≤ j) :
    M_.obj (OrderDual.toDual j) →ₗ[A] M_.obj (OrderDual.toDual i) :=
  (M_.map (homOfLE (show OrderDual.toDual j ≤ OrderDual.toDual i from hij))).hom

/-- Helper for Chap10 Lemma 10 98 2: the immediate transition map `M_{n + 1} → M_n`. -/
abbrev stageMap (M_ : ModuleInverseSystem) (n : ℕ+) :
    M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n) :=
  transitionMap M_ (pnat_le_succ n)

/-- Helper for Chap10 Lemma 10 98 2: the canonical projection from `limit M_` to stage `n`. -/
abbrev limitProjection (M_ : ModuleInverseSystem) (n : ℕ+) :
    (limit M_ : ModuleCat A) →ₗ[A] M_.obj (OrderDual.toDual n) :=
  (limit.π M_ (OrderDual.toDual n)).hom

/-- Helper for Lemma 10.98.2: the `n`th limit projection is the successor-stage projection
followed by the structure map `M_{n + 1} → M_n`. -/
theorem stageMap_comp_limitProjection_eq
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
theorem transitionMap_step_eq_comp
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
theorem stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients
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
theorem transitionMap_surjective_of_successive_ideal_power_quotients
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
theorem limit_projection_surjective_of_successive_ideal_power_quotients
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
abbrev stagePNat (i : OrderDual ℕ+) : ℕ+ :=
  OrderDual.ofDual i

/-- Helper for Lemma 10.98.2: the stage obtained by shifting `n` forward by `k` successor steps. -/
abbrev stageShiftPNat (n : ℕ+) (k : ℕ) : ℕ+ :=
  ⟨(n : ℕ) + k, Nat.add_pos_left n.2 k⟩

/-- Helper for Lemma 10.98.2: the source identity
`N_{n + 1} + I ^ n (\varprojlim M_i) = N_n` for the kernels of the limit projections. -/
theorem limit_projection_ker_succ_sup_pow_smul_top_of_successive_ideal_power_quotients
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


end
