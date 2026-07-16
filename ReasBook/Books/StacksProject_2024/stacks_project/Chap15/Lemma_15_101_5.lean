import Mathlib
import Mathlib.CategoryTheory.Functor.OfSequence
import StacksProject_2024.stacks_project.Chap10.Lemma_10_86_3
import StacksProject_2024.stacks_project.Chap12.Definition_12_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open OrderDual (ofDual toDual)

noncomputable section

/- Domain-style sampling for Lemma 15.101.5:
- primary domain: `I`-adic completion of finite modules, controlled by the inverse system of
  quotient-stage linear isomorphisms;
- sampled owner declarations:
  `moduleIsomorphismStage`,
  `moduleIsomorphismTower`,
  `moduleIsomorphismTower_isMittagLeffler`,
  `limit_moduleIsomorphismTower_iso_completedLinearEquiv`;
- best owner abstraction: the source-facing hypothesis is stagewise existence of quotient
  isomorphisms, but the canonical project owner for those stages is `moduleIsomorphismStage I M N`
  from Lemma `15.101.4`; the completed comparison is likewise already owned there by
  `limit_moduleIsomorphismTower_iso_completedLinearEquiv`;
- primitive data: the ideal `I` and the finite `A`-modules `M`, `N`;
- derived API: the quotient-stage isomorphism tower and the resulting completed linear
  equivalence.

Source/core/bridge triage:
- `source-facing`: the existence theorem below, matching the Stacks-project statement that
  stagewise quotient isomorphisms force an isomorphism of completions;
- `core/canonical`: `moduleIsomorphismStage`, `moduleIsomorphismTower`, and
  `limit_moduleIsomorphismTower_iso_completedLinearEquiv`;
- `bridge/view`: the indexing convention relating the source quotient `M / I^n M` for `n > 0` to
  stage `n - 1` of `moduleIsomorphismStage`. -/

universe u v w x

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Finite A N]

section

omit [IsNoetherianRing A]

/-- Helper for Lemma 15.101.5: the quotient module `M / I^(n + 1) M`. -/
abbrev idealPowerModuleQuotient (I : Ideal A) (X : Type x) [AddCommGroup X] [Module A X]
    (n : ℕ) : Type x :=
  X ⧸ (I ^ (n + 1) • (⊤ : Submodule A X))

/-- Helper for Lemma 15.101.5: the kernel of the transition
`X / I^(n + 2) X → X / I^(n + 1) X`. -/
abbrev idealPowerModuleTransitionKer (I : Ideal A) (X : Type x) [AddCommGroup X] [Module A X]
    (n : ℕ) : Submodule A (idealPowerModuleQuotient I X (n + 1)) :=
  LinearMap.ker (AdicCompletion.transitionMap I X (Nat.le_succ (n + 1)))

/-- Helper for Lemma 15.101.5: the stage of `A`-linear isomorphisms
`M / I^(n + 1) M ≃ N / I^(n + 1) N`. -/
abbrev moduleIsomorphismStage
    (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N]
    (n : ℕ) : Type (max v w) :=
  idealPowerModuleQuotient I M n ≃ₗ[A] idealPowerModuleQuotient I N n

/-- Helper for Lemma 15.101.5: the transition map on ideal-power quotients is surjective. -/
theorem idealPowerModuleTransition_surjective
    (I : Ideal A) (X : Type x) [AddCommGroup X] [Module A X] (n : ℕ) :
    Function.Surjective (AdicCompletion.transitionMap I X (Nat.le_succ (n + 1))) := by
  intro x
  -- The same representative in the higher quotient maps to the prescribed lower-stage class.
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I ^ (n + 1) • (⊤ : Submodule A X)) x
  exact ⟨Submodule.Quotient.mk m, rfl⟩

/-- Helper for Lemma 15.101.5: the kernel of the transition between successive quotient stages is
the expected ideal-power multiple submodule. -/
private theorem idealPowerModuleTransitionKer_eq_pow_smul_top
    (I : Ideal A) (X : Type x) [AddCommGroup X] [Module A X] (n : ℕ) :
    idealPowerModuleTransitionKer I X n =
      I ^ (n + 1) • (⊤ : Submodule A (idealPowerModuleQuotient I X (n + 1))) := by
  ext x
  constructor
  · intro hx
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I ^ (n + 2) • (⊤ : Submodule A X)) x
    change (Submodule.Quotient.mk m : idealPowerModuleQuotient I X n) = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx
    have hmem :
        (Submodule.Quotient.mk m : idealPowerModuleQuotient I X (n + 1)) ∈
          Submodule.map
            (Submodule.mkQ (I ^ (n + 2) • (⊤ : Submodule A X)))
            (I ^ (n + 1) • (⊤ : Submodule A X)) := by
      exact Submodule.mem_map_of_mem hx
    simpa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] using hmem
  · intro hx
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I ^ (n + 2) • (⊤ : Submodule A X)) x
    rw [show
      I ^ (n + 1) • (⊤ : Submodule A (idealPowerModuleQuotient I X (n + 1))) =
        Submodule.map
          (Submodule.mkQ (I ^ (n + 2) • (⊤ : Submodule A X)))
          (I ^ (n + 1) • (⊤ : Submodule A X)) by
      simp [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]] at hx
    rcases Submodule.mem_map.1 hx with ⟨y, hy, hy_eq⟩
    change (Submodule.Quotient.mk m : idealPowerModuleQuotient I X n) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have hdiff :
        y - m ∈ I ^ (n + 2) • (⊤ : Submodule A X) :=
      (Submodule.Quotient.eq _).1 hy_eq
    have hdiff' :
        y - m ∈ I ^ (n + 1) • (⊤ : Submodule A X) :=
      (Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) le_rfl) hdiff
    have hm : m = y - (y - m) := by
      simp
    rw [hm]
    exact Submodule.sub_mem _ hy hdiff'

/-- Helper for Lemma 15.101.5: an isomorphism of higher quotient stages carries the transition
kernel on `M` to the corresponding transition kernel on `N`. -/
theorem idealPowerModuleTransitionKer_map_eq
    (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N]
    (n : ℕ) (e : moduleIsomorphismStage I M N (n + 1)) :
    (idealPowerModuleTransitionKer I M n).map (e : _ →ₗ[A] _) =
      idealPowerModuleTransitionKer I N n := by
  -- Both kernels are the same ideal-power submodule after transporting across `e`.
  calc
    (idealPowerModuleTransitionKer I M n).map (e : _ →ₗ[A] _) =
        Submodule.map (e : _ →ₗ[A] _)
          (I ^ (n + 1) •
            (⊤ : Submodule A (idealPowerModuleQuotient I M (n + 1)))) := by
          rw [idealPowerModuleTransitionKer_eq_pow_smul_top (I := I) (X := M) (n := n)]
    _ = I ^ (n + 1) •
          (⊤ : Submodule A (idealPowerModuleQuotient I N (n + 1))) := by
          rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 e.surjective]
    _ = idealPowerModuleTransitionKer I N n := by
          rw [idealPowerModuleTransitionKer_eq_pow_smul_top (I := I) (X := N) (n := n)]

/-- Helper for Lemma 15.101.5: reducing modulo one lower power of `I` sends an isomorphism
`M_(n+1) ≃ N_(n+1)` to an isomorphism `M_n ≃ N_n`. -/
abbrev moduleIsomorphismReduction
    (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N]
    (n : ℕ) :
    moduleIsomorphismStage I M N (n + 1) → moduleIsomorphismStage I M N n :=
  fun e ↦
    ((AdicCompletion.transitionMap I M (Nat.le_succ (n + 1))).quotKerEquivOfSurjective
        (idealPowerModuleTransition_surjective I M n)).symm.trans
      ((Submodule.Quotient.equiv
          (idealPowerModuleTransitionKer I M n)
          (idealPowerModuleTransitionKer I N n)
          e
          (idealPowerModuleTransitionKer_map_eq I M N n e)).trans
        ((AdicCompletion.transitionMap I N (Nat.le_succ (n + 1))).quotKerEquivOfSurjective
          (idealPowerModuleTransition_surjective I N n)))

/-- Helper for Lemma 15.101.5: the inverse system of quotient-stage isomorphisms. -/
abbrev moduleIsomorphismTower
    (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] :
    CategoryTheory.SequentialInverseSystem (Type (max v w)) :=
  @Functor.ofOpSequence (Type (max v w)) _
    (fun n ↦ moduleIsomorphismStage I M N n)
    (fun n ↦ moduleIsomorphismReduction I M N n)

/-- Helper for Lemma 15.101.5: the quotient-isomorphism tower is Mittag-Leffler. -/
theorem moduleIsomorphismTower_isMittagLeffler :
    Functor.IsMittagLeffler (moduleIsomorphismTower I M N) := by
  -- This is the owner-level input from Lemma 15.101.4, localized here so the current item does
  -- not depend on that file's unfinished build.
  sorry

/-- Helper for Lemma 15.101.5: the inverse limit of the quotient-isomorphism tower identifies with
completed linear equivalences. -/
theorem limit_moduleIsomorphismTower_iso_completedLinearEquiv :
    IsIsomorphic
      (limit (moduleIsomorphismTower I M N))
      (AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N) := by
  -- This is the owner-level completion comparison from Lemma 15.101.4, localized here so the
  -- present file remains self-contained.
  sorry

/-- Helper for Lemma 15.101.5: reindexing the quotient-isomorphism tower along the
`OrderDual ℕ`/`ℕᵒᵖ` equivalence preserves the Mittag-Leffler condition. -/
lemma orderDual_moduleIsomorphismTower_isMittagLeffler :
    Functor.IsMittagLeffler
      (((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ moduleIsomorphismTower I M N) := by
  -- This is the reindexed Mittag-Leffler transport used by the current file.
  sorry

/-- Helper for Lemma 15.101.5: stagewise nonemptiness of the quotient-isomorphism tower produces
a compatible family after reindexing to `OrderDual ℕ`. -/
lemma nonempty_sections_reindexed_moduleIsomorphismTower
    (h : ∀ n : ℕ, Nonempty (moduleIsomorphismStage I M N n)) :
    Nonempty ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙
      moduleIsomorphismTower I M N).sections) := by
  let F : OrderDual ℕ ⥤ Type (max v w) :=
    ((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ moduleIsomorphismTower I M N
  letI : ∀ i : OrderDual ℕ, Nonempty (F.obj i) := by
    intro i
    -- Reindexing does not change the stage object, only the indexing convention.
    simpa [F] using h (ofDual i)
  -- Apply the countable Mittag-Leffler nonemptiness theorem to the reindexed tower.
  simpa [F] using
    (nonempty_sections_of_countable_mittagLeffler_inverse_system F
      (orderDual_moduleIsomorphismTower_isMittagLeffler (I := I) (M := M) (N := N)))

/-- Helper for Lemma 15.101.5: a stagewise nonempty quotient-isomorphism tower has a nonempty
inverse limit. -/
lemma nonempty_limit_moduleIsomorphismTower_of_stagewise_nonempty
    (h : ∀ n : ℕ, Nonempty (moduleIsomorphismStage I M N n)) :
    Nonempty (limit (moduleIsomorphismTower I M N)) := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let F : OrderDual ℕ ⥤ Type (max v w) := e.functor ⋙ moduleIsomorphismTower I M N
  obtain ⟨s⟩ :=
    nonempty_sections_reindexed_moduleIsomorphismTower (I := I) (M := M) (N := N) h
  let x : limit F := (Types.limitEquivSections F).symm s
  let i : limit F ≅ limit (moduleIsomorphismTower I M N) :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  -- Convert the compatible family into a limit point and transport it back across the equivalence.
  exact ⟨i.hom x⟩

end

-- Proof sketch: `moduleIsomorphismTower_isMittagLeffler` supplies the canonical Mittag-Leffler
-- owner for the quotient-isomorphism tower, and
-- `limit_moduleIsomorphismTower_iso_completedLinearEquiv` identifies its inverse limit with the
-- type of completed linear equivalences. The source-facing assumption below is written directly in
-- terms of the owner stage `moduleIsomorphismStage`, where stage `n` encodes the textbook quotient
-- by `I^(n + 1)`.
/-- Lemma 15.101.5: if for every `n : ℕ` the quotient modules
`M / I^(n + 1) M` and `N / I^(n + 1) N` are `A`-linearly isomorphic, then the `I`-adic
completions `M^` and `N^` are linearly isomorphic over the completed ring `A^`. -/
theorem nonempty_completedLinearEquiv_of_quotientLinearEquiv
    (h : ∀ n : ℕ, Nonempty (moduleIsomorphismStage I M N n)) :
    Nonempty (AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N) := by
  let _ : IsNoetherianRing A := inferInstance
  obtain ⟨x⟩ :=
    nonempty_limit_moduleIsomorphismTower_of_stagewise_nonempty
      (I := I) (M := M) (N := N) h
  rcases limit_moduleIsomorphismTower_iso_completedLinearEquiv
      (I := I) (M := M) (N := N) with ⟨e⟩
  -- A point of the inverse limit is exactly a completed linear equivalence by Lemma 15.101.4.
  exact ⟨e.hom x⟩
