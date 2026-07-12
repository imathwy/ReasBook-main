import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 0BNG]
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
