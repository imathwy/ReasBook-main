import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_10_2
import StacksProject_2024.Chap10.Lemma_10_62_7
import StacksProject_2024.Chap15.Lemma_15_23_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped ENat

/-
Domain-style sampling:
- primary domain: Serre conditions of finite modules over Noetherian rings and torsion-freeness of
  linear-map modules;
- sampled owner declarations:
  `Module.SerreConditionS`,
  `moduleDepth_linearMap_ge_one`,
  `moduleDepth_linearMap_ge_two`,
  `LinearMap.instIsTorsionFree`;
- best owner abstraction:
  `Module.SerreConditionS` for the `(S₁)` and `(S₂)` clauses, with Lemma `15.23.10` supplying the
  primitive local-depth input, and `LinearMap.instIsTorsionFree` for the torsion-free clause;
- source/core/bridge triage:
  clauses `(1)` and `(2)` are `bridge/view` packaging from the local owner `moduleDepth`, while
  clause `(3)` is a direct `core/canonical` recall.

Primitive data are the local depth inequalities from Lemma `15.23.10`. The
`Module.SerreConditionS` statements below are derived packaging of that owner-level data, and the
torsion-free statement should reuse the canonical upstream owner instead of keeping a parallel
local wrapper.
-/

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type u} [AddCommGroup N] [Module R N]

/-- Helper for Lemma 15.23.11: finite powers of a module have support dimension at most the
support dimension of the original module. -/
private lemma finFun_supportDim_le {A : Type*} [CommRing A] {Q : Type*} [AddCommGroup Q]
    [Module A Q] (n : ℕ) :
    Module.supportDim A (Fin n → Q) ≤ Module.supportDim A Q := by
  induction n with
  | zero =>
      let hsub : Subsingleton (Fin 0 → Q) := by
        refine ⟨?_⟩
        intro f g
        ext i
        exact Fin.elim0 i
      letI := hsub
      -- The zero power is the zero module, so its support dimension is bottom.
      rw [Module.supportDim_eq_bot_of_subsingleton A (Fin 0 → Q)]
      exact bot_le
  | succ n ih =>
      let e₁ : (Fin (n + 1) → Q) ≃ₗ[A] ((Fin n ⊕ Fin 1) → Q) :=
        LinearEquiv.funCongrLeft (R := A) (M := Q) (finSumFinEquiv (m := n) (n := 1))
      let e₂ : ((Fin n ⊕ Fin 1) → Q) ≃ₗ[A] ((Fin n → Q) × (Fin 1 → Q)) :=
        LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin 1) A Q
      let e₃ : ((Fin n → Q) × (Fin 1 → Q)) ≃ₗ[A] ((Fin n → Q) × Q) :=
        LinearEquiv.prodCongr (LinearEquiv.refl A _) (LinearEquiv.funUnique (Fin 1) A Q)
      let e₄ : ((Fin n → Q) × Q) ≃ₗ[A] (Q × (Fin n → Q)) :=
        LinearEquiv.prodComm A (Fin n → Q) Q
      let e : (Fin (n + 1) → Q) ≃ₗ[A] (Q × (Fin n → Q)) := e₁.trans (e₂.trans (e₃.trans e₄))
      let S : CategoryTheory.ShortComplex (ModuleCat A) :=
        CategoryTheory.ShortComplex.mk
          (ModuleCat.ofHom (LinearMap.inl A Q (Fin n → Q)))
          (ModuleCat.ofHom (LinearMap.snd A Q (Fin n → Q)))
          (by ext x <;> rfl)
      have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
        (by
          simpa [S] using
            (Function.Exact.inl_snd : Function.Exact
              (LinearMap.inl A Q (Fin n → Q)) (LinearMap.snd A Q (Fin n → Q))))
        LinearMap.inl_injective
        LinearMap.snd_surjective
      have hEq :
          Module.supportDim A (Fin (n + 1) → Q) = Module.supportDim A (Q × (Fin n → Q)) :=
        Module.supportDim_eq_of_equiv e
      -- Rewrite `Q^(n+1)` as a product and use the short-exact support-dimension formula.
      calc
        Module.supportDim A (Fin (n + 1) → Q)
            = Module.supportDim A (Q × (Fin n → Q)) := hEq
        _ = max (Module.supportDim A Q) (Module.supportDim A (Fin n → Q)) := by
            simpa [S] using supportDim_eq_max_of_shortExact hS
        _ ≤ Module.supportDim A Q := max_le le_rfl ih

/-- Helper for Lemma 15.23.11: `Hom_A(A^n, Q)` has support dimension at most that of `Q`. -/
private lemma linearMap_fin_supportDim_le_codomain {A : Type*} [CommRing A] {Q : Type*}
    [AddCommGroup Q] [Module A Q] (n : ℕ) :
    Module.supportDim A ((Fin n → A) →ₗ[A] Q) ≤ Module.supportDim A Q := by
  have hEq :
      Module.supportDim A ((Fin n → A) →ₗ[A] Q) = Module.supportDim A (Fin n → Q) :=
    Module.supportDim_eq_of_equiv (LinearEquiv.piRing A Q (Fin n) A)
  rw [hEq]
  exact finFun_supportDim_le (A := A) (Q := Q) n

/-- Helper for Lemma 15.23.11: over a Noetherian ring, the support dimension of `Hom_A(P, Q)` is
bounded above by the support dimension of `Q`. -/
private lemma linearMap_supportDim_le_codomain {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P Q : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] :
    Module.supportDim A (P →ₗ[A] Q) ≤ Module.supportDim A Q := by
  letI : Module.FinitePresentation A P := Module.finitePresentation_of_finite A P
  -- Present `P` by a finite free module and inject `Hom_A(P, Q)` into `Hom_A(A^n, Q)`.
  rcases (Module.FinitePresentation.iff_exists_exact_free_sequence A P).mp inferInstance with
    ⟨n, _, _, g, _, hg⟩
  let α : (P →ₗ[A] Q) →ₗ[A] ((Fin n → A) →ₗ[A] Q) := LinearMap.lcomp A Q g
  have hα : Function.Injective α := LinearMap.lcomp_injective_of_surjective g hg
  have hαdim :
      Module.supportDim A (P →ₗ[A] Q) ≤ Module.supportDim A ((Fin n → A) →ₗ[A] Q) := by
    simpa [α] using Module.supportDim_le_of_injective α hα
  exact hαdim.trans (linearMap_fin_supportDim_le_codomain (A := A) (Q := Q) n)

/-- Helper for Lemma 15.23.11: a local `(S_1)` bound on `Q` induces the corresponding bound on
`Hom_A(P, Q)`. -/
private lemma linearMap_serre_bound_one_of_codomain {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {P Q : Type u} [AddCommGroup P] [Module A P] [Module.Finite A P]
    [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
    (hQ :
      WithBot.some (moduleDepth A Q : ℕ∞) ≥
        min (1 : WithBot ℕ∞) (Module.supportDim A Q)) :
    WithBot.some (moduleDepth A (P →ₗ[A] Q) : ℕ∞) ≥
      min (1 : WithBot ℕ∞) (Module.supportDim A (P →ₗ[A] Q)) := by
  let d : WithBot ℕ∞ := min (1 : WithBot ℕ∞) (Module.supportDim A (P →ₗ[A] Q))
  let e : WithBot ℕ∞ := min (1 : WithBot ℕ∞) (Module.supportDim A Q)
  change WithBot.some (moduleDepth A (P →ₗ[A] Q) : ℕ∞) ≥ d
  have hde : d ≤ e := by
    -- First compare the support dimensions, then apply `min`.
    dsimp [d, e]
    exact min_le_min_left _ (linearMap_supportDim_le_codomain (A := A) (P := P) (Q := Q))
  have hd_le_one : d ≤ (1 : WithBot ℕ∞) := by
    dsimp [d]
    exact min_le_left _ _
  by_cases hd_bot : d = ⊥
  · -- If the truncated support dimension is bottom, the target inequality is automatic.
    simpa [d, hd_bot]
  obtain ⟨δ, hδ⟩ := WithBot.ne_bot_iff_exists.mp hd_bot
  rw [← hδ] at hde hd_le_one ⊢
  have hδ_le_one : ((δ : ℕ∞) : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) := by
    simpa using hd_le_one
  have hδ_ne_top : δ ≠ ⊤ := by
    intro htop
    have hEqTop : (((1 : ℕ∞) : WithBot ℕ∞)) = ⊤ := by
      simpa [htop] using hδ_le_one
    exact ENat.coe_ne_top 1 (WithBot.coe_eq_top.mp hEqTop)
  rcases ENat.ne_top_iff_exists.mp hδ_ne_top with ⟨n, rfl⟩
  have hn_le_one : n ≤ 1 := by
    exact ENat.coe_le_coe.mp (WithBot.coe_le_coe.mp hδ_le_one)
  interval_cases n
  · simp
  · -- The only nontrivial truncated value is `1`, so apply Lemma `15.23.10 (1)`.
    have hQ_ge_one : (1 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth A Q : ℕ∞) := by
      have hOne_le_e : (1 : WithBot ℕ∞) ≤ e := by
        simpa using hde
      exact hOne_le_e.trans hQ
    have hDepthQ : (1 : ℕ∞) ≤ moduleDepth A Q :=
      WithBot.coe_le_coe.mp hQ_ge_one
    have hDepthHom : 1 ≤ moduleDepth A (P →ₗ[A] Q) :=
      moduleDepth_linearMap_ge_one (R := A) (M := P) (N := Q) hDepthQ
    exact WithBot.coe_le_coe.mpr hDepthHom

/-- Helper for Lemma 15.23.11: a local `(S_2)` bound on `Q` induces the corresponding bound on
`Hom_A(P, Q)`. -/
private lemma linearMap_serre_bound_two_of_codomain {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {P Q : Type u} [AddCommGroup P] [Module A P] [Module.Finite A P]
    [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
    (hQ :
      WithBot.some (moduleDepth A Q : ℕ∞) ≥
        min (2 : WithBot ℕ∞) (Module.supportDim A Q)) :
    WithBot.some (moduleDepth A (P →ₗ[A] Q) : ℕ∞) ≥
      min (2 : WithBot ℕ∞) (Module.supportDim A (P →ₗ[A] Q)) := by
  let d : WithBot ℕ∞ := min (2 : WithBot ℕ∞) (Module.supportDim A (P →ₗ[A] Q))
  let e : WithBot ℕ∞ := min (2 : WithBot ℕ∞) (Module.supportDim A Q)
  change WithBot.some (moduleDepth A (P →ₗ[A] Q) : ℕ∞) ≥ d
  have hde : d ≤ e := by
    -- First compare the support dimensions, then apply `min`.
    dsimp [d, e]
    exact min_le_min_left _ (linearMap_supportDim_le_codomain (A := A) (P := P) (Q := Q))
  have hd_le_two : d ≤ (2 : WithBot ℕ∞) := by
    dsimp [d]
    exact min_le_left _ _
  by_cases hd_bot : d = ⊥
  · -- If the truncated support dimension is bottom, the target inequality is automatic.
    simpa [d, hd_bot]
  obtain ⟨δ, hδ⟩ := WithBot.ne_bot_iff_exists.mp hd_bot
  rw [← hδ] at hde hd_le_two ⊢
  have hδ_le_two : ((δ : ℕ∞) : WithBot ℕ∞) ≤ (2 : WithBot ℕ∞) := by
    simpa using hd_le_two
  have hδ_ne_top : δ ≠ ⊤ := by
    intro htop
    have hEqTop : (((2 : ℕ∞) : WithBot ℕ∞)) = ⊤ := by
      simpa [htop] using hδ_le_two
    exact ENat.coe_ne_top 2 (WithBot.coe_eq_top.mp hEqTop)
  rcases ENat.ne_top_iff_exists.mp hδ_ne_top with ⟨n, rfl⟩
  have hn_le_two : n ≤ 2 := by
    exact ENat.coe_le_coe.mp (WithBot.coe_le_coe.mp hδ_le_two)
  interval_cases n
  · simp
  · -- If the truncated support dimension is `1`, Lemma `15.23.10 (1)` already closes the goal.
    have hQ_ge_one : (1 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth A Q : ℕ∞) := by
      have hOne_le_e : (1 : WithBot ℕ∞) ≤ e := by
        simpa using hde
      exact hOne_le_e.trans hQ
    have hDepthQ : (1 : ℕ∞) ≤ moduleDepth A Q :=
      WithBot.coe_le_coe.mp hQ_ge_one
    have hDepthHom : 1 ≤ moduleDepth A (P →ₗ[A] Q) :=
      moduleDepth_linearMap_ge_one (R := A) (M := P) (N := Q) hDepthQ
    exact WithBot.coe_le_coe.mpr hDepthHom
  · -- If the truncated support dimension is `2`, use Lemma `15.23.10 (2)`.
    have hQ_ge_two : (2 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth A Q : ℕ∞) := by
      have hTwo_le_e : (2 : WithBot ℕ∞) ≤ e := by
        simpa using hde
      exact hTwo_le_e.trans hQ
    have hDepthQ : (2 : ℕ∞) ≤ moduleDepth A Q :=
      WithBot.coe_le_coe.mp hQ_ge_two
    have hDepthHom : 2 ≤ moduleDepth A (P →ₗ[A] Q) :=
      moduleDepth_linearMap_ge_two (R := A) (M := P) (N := Q) hDepthQ
    exact WithBot.coe_le_coe.mpr hDepthHom

instance LinearMap.instSerreConditionSOneOfCodomain
    [Module.SerreConditionS R N 1] :
    Module.SerreConditionS R (M →ₗ[R] N) 1 where
  toFinite := inferInstance
  moduleDepth_localizationAtPrime_ge_min_supportDim := by
    intro p
    letI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    let e :
        LocalizedModule.AtPrime p.asIdeal (M →ₗ[R] N) ≃ₗ[Localization.AtPrime p.asIdeal]
          (LocalizedModule.AtPrime p.asIdeal M →ₗ[Localization.AtPrime p.asIdeal]
            LocalizedModule.AtPrime p.asIdeal N) :=
      LinearEquiv.extendScalarsOfIsLocalization p.asIdeal.primeCompl
        (Localization.AtPrime p.asIdeal)
        (Module.FinitePresentation.linearEquivMapExtendScalars p.asIdeal.primeCompl)
    have hSN : Module.SerreConditionS R N 1 := inferInstance
    have hLocalN :
        WithBot.some
            (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal N) : ℕ∞) ≥
          min (1 : WithBot ℕ∞)
            (Module.supportDim (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal N)) :=
      hSN.moduleDepth_localizationAtPrime_ge_min_supportDim p
    -- Transport the localized `Hom` module to `Hom` of the localized modules and apply the local
    -- `(S₁)` bound proved above.
    have hLocalHom :
        WithBot.some
            (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M →ₗ[Localization.AtPrime p.asIdeal]
                LocalizedModule.AtPrime p.asIdeal N) : ℕ∞) ≥
          min (1 : WithBot ℕ∞)
            (Module.supportDim (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M →ₗ[Localization.AtPrime p.asIdeal]
                LocalizedModule.AtPrime p.asIdeal N)) :=
      linearMap_serre_bound_one_of_codomain
        (A := Localization.AtPrime p.asIdeal)
        (P := LocalizedModule.AtPrime p.asIdeal M)
        (Q := LocalizedModule.AtPrime p.asIdeal N)
        hLocalN
    have hsupport :
        Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal (M →ₗ[R] N)) =
        Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M →ₗ[Localization.AtPrime p.asIdeal]
            LocalizedModule.AtPrime p.asIdeal N) :=
      Module.supportDim_eq_of_equiv e
    have hdepth :
        moduleDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal (M →ₗ[R] N)) =
        moduleDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M →ₗ[Localization.AtPrime p.asIdeal]
            LocalizedModule.AtPrime p.asIdeal N) :=
      moduleDepth_eq_of_equiv e
    simpa [hdepth, hsupport] using hLocalHom

-- Proof sketch: localize at each prime ideal and use that localization commutes with finite-module
-- `Hom`. Then apply the depth estimate from Lemma `15.23.10 (1)` to the localized linear-map
-- module, and package the resulting local inequalities back into the definition of
-- `Module.SerreConditionS ... 1`.
/-- Lemma 15.23.11 (1): if the finite `R`-module `N` satisfies Serre's condition `(S_1)`, then
the module `Hom_R(M, N)` also satisfies Serre's condition `(S_1)`. -/
@[stacks 0AV6]
theorem linearMap_serreConditionS_one_of_codomain
    [Module.SerreConditionS R N 1] :
    Module.SerreConditionS R (M →ₗ[R] N) 1 := inferInstance

instance LinearMap.instSerreConditionSTwoOfCodomain
    [Module.SerreConditionS R N 2] :
    Module.SerreConditionS R (M →ₗ[R] N) 2 where
  toFinite := inferInstance
  moduleDepth_localizationAtPrime_ge_min_supportDim := by
    intro p
    letI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    let e :
        LocalizedModule.AtPrime p.asIdeal (M →ₗ[R] N) ≃ₗ[Localization.AtPrime p.asIdeal]
          (LocalizedModule.AtPrime p.asIdeal M →ₗ[Localization.AtPrime p.asIdeal]
            LocalizedModule.AtPrime p.asIdeal N) :=
      LinearEquiv.extendScalarsOfIsLocalization p.asIdeal.primeCompl
        (Localization.AtPrime p.asIdeal)
        (Module.FinitePresentation.linearEquivMapExtendScalars p.asIdeal.primeCompl)
    have hSN : Module.SerreConditionS R N 2 := inferInstance
    have hLocalN :
        WithBot.some
            (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal N) : ℕ∞) ≥
          min (2 : WithBot ℕ∞)
            (Module.supportDim (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal N)) :=
      hSN.moduleDepth_localizationAtPrime_ge_min_supportDim p
    -- Transport the localized `Hom` module to `Hom` of the localized modules and apply the local
    -- `(S₂)` bound proved above.
    have hLocalHom :
        WithBot.some
            (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M →ₗ[Localization.AtPrime p.asIdeal]
                LocalizedModule.AtPrime p.asIdeal N) : ℕ∞) ≥
          min (2 : WithBot ℕ∞)
            (Module.supportDim (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M →ₗ[Localization.AtPrime p.asIdeal]
                LocalizedModule.AtPrime p.asIdeal N)) :=
      linearMap_serre_bound_two_of_codomain
        (A := Localization.AtPrime p.asIdeal)
        (P := LocalizedModule.AtPrime p.asIdeal M)
        (Q := LocalizedModule.AtPrime p.asIdeal N)
        hLocalN
    have hsupport :
        Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal (M →ₗ[R] N)) =
        Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M →ₗ[Localization.AtPrime p.asIdeal]
            LocalizedModule.AtPrime p.asIdeal N) :=
      Module.supportDim_eq_of_equiv e
    have hdepth :
        moduleDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal (M →ₗ[R] N)) =
        moduleDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M →ₗ[Localization.AtPrime p.asIdeal]
            LocalizedModule.AtPrime p.asIdeal N) :=
      moduleDepth_eq_of_equiv e
    simpa [hdepth, hsupport] using hLocalHom

-- Proof sketch: localize at a prime ideal, identify localization of `Hom_R(M, N)` with the `Hom`
-- module of the localized finite modules, and invoke Lemma `15.23.10 (2)` to get the depth bound
-- required in the definition of `Module.SerreConditionS ... 2`.
/-- Lemma 15.23.11 (2): if the finite `R`-module `N` satisfies Serre's condition `(S_2)`, then
the module `Hom_R(M, N)` also satisfies Serre's condition `(S_2)`. -/
@[stacks 0AV6]
theorem linearMap_serreConditionS_two_of_codomain
    [Module.SerreConditionS R N 2] :
    Module.SerreConditionS R (M →ₗ[R] N) 2 := inferInstance

end

section

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N] [Module.IsTorsionFree R N]

/- Lemma 15.23.11 (3): the torsion-free conclusion for `Hom_R(M, N)` is already the canonical
owner instance `LinearMap.instIsTorsionFree`, which is stronger than the source hypotheses used in
the textbook packaging of Lemma `15.23.11`. -/
recall LinearMap.instIsTorsionFree

end
