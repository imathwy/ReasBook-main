import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_157_4_Serre_s_criterion_for_normality
import StacksProject_2024.Chap15.Lemma_15_23_2
import StacksProject_2024.Chap15.Lemma_15_23_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped nonZeroDivisors
open Module
open LocalizedModule (liftOfLE mkLinearMap)

universe u v

/-
Domain-style sampling:
- primary domain: reflexive finite modules over Noetherian normal domains, together with the
  height-one localization intersection criterion inside the generic localization;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.IsTorsionFree`,
  `Module.SerreConditionS`,
  `LocalizedModule.mkLinearMap`;
- best owner abstraction:
  `Module.IsReflexive` is the core/canonical owner of the theorem, while the intersection of the
  height-one localizations is only a bridge/view used to express the source-facing third clause;
- source/core/bridge triage:
  `source-facing`: the textbook TFAE criterion for finite modules over a Noetherian normal domain;
  `core/canonical`: `Module.IsReflexive`, `Module.IsTorsionFree`, `Module.SerreConditionS`;
  `bridge/view`: the submodule of the generic localization obtained by intersecting the images of
    the height-one localization maps.

Primitive data are only the ambient domain `R`, the finite `R`-module `M`, and the canonical
generic localization map `mkLinearMap R⁰ M`. The `(S₂)` clause and reflexivity clause are already
owned by the chapter/mathlib owners above, so this file should keep only the minimal bridge object
for the height-one-localization intersection instead of introducing any heavier wrapper API.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The intersection of the height-one localizations of `M`, viewed inside the generic
localization `M ⊗[R] Frac(R)` and modeled as `LocalizedModule R⁰ M`. -/
noncomputable abbrev moduleHeightOneLocalizationIntersection (R : Type u) (M : Type v)
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] :
    Submodule R (LocalizedModule R⁰ M) :=
  ⨅ p : { p : PrimeSpectrum R // p.asIdeal.height = 1 },
    LinearMap.range
      (liftOfLE p.1.asIdeal.primeCompl R⁰
        (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal))

end

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

omit [IsNoetherianRing R] [IsIntegrallyClosed R] [Module.Finite R M] in
/-- Helper for Lemma 15.23.18: every element coming from `M` belongs to the intersection of the
height-one localizations inside the generic localization. -/
private lemma mkLinearMap_range_le_moduleHeightOneLocalizationIntersection :
    LinearMap.range (mkLinearMap R⁰ M) ≤ moduleHeightOneLocalizationIntersection R M := by
  -- Check membership in the intersection one height-one branch at a time.
  intro x hx
  rw [moduleHeightOneLocalizationIntersection, Submodule.mem_iInf]
  intro p
  rcases hx with ⟨m, rfl⟩
  refine ⟨mkLinearMap p.1.asIdeal.primeCompl M m, ?_⟩
  -- The comparison map from `M_p` to the generic localization agrees with the generic map on
  -- numerator generators.
  simpa using LinearMap.congr_fun
    (IsLocalizedModule.liftOfLE_comp p.1.asIdeal.primeCompl R⁰
      (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal)
      (mkLinearMap p.1.asIdeal.primeCompl M)
      (mkLinearMap R⁰ M)) m

-- Proof sketch: apply Serre's criterion for normality to deduce `(R_1)` and `(S_2)` for `R`.
-- Then use Lemma `15.23.2` and Lemma `15.23.16` for `(1) → (2)`, Lemma `15.23.14` for
-- `(2) → (3)` after comparing the height-one localizations inside the generic fiber, and the DVR
-- freeness criterion from Lemma `15.22.11` for `(3) → (1)`.
/-- Lemma 15.23.18: for a finite module `M` over a Noetherian normal domain `R`, the following are
equivalent: `M` is reflexive; `M` is torsion free and satisfies Serre's condition `(S_2)`; and
`M` is torsion free and agrees with the intersection of its height-one localizations inside the
generic localization `M ⊗[R] Frac(R)`. -/
@[stacks 0AVB]
theorem reflexive_tfae_torsionFree_serreS2_heightOneLocalizationIntersection :
    List.TFAE
      [ IsReflexive R M
      , IsTorsionFree R M ∧ SerreConditionS R M 2
      , IsTorsionFree R M ∧
          LinearMap.range (mkLinearMap R⁰ M) =
            moduleHeightOneLocalizationIntersection R M ] :=
  by
    have hNormal : IsNormalRing R := inferInstance
    have hSerre :
        R ⊧ (R₁) ∧ R ⊧ (S₂) :=
      isNormalRing_iff_serreConditionR_one_and_serreConditionS_two.mp hNormal
    -- The reflexive owner API immediately gives torsion-freeness and, after Serre normality,
    -- the `(S₂)` clause.
    tfae_have 1 → 2 := by
      intro hReflexive
      have hTorsionFree : IsTorsionFree R M := by
        letI : IsReflexive R M := hReflexive
        exact IsReflexive.to_isTorsionFree (R := R) (M := M)
      -- TODO for Lemma 15.23.18: reuse Lemma `15.23.16` after a universe-general bridge for the
      -- `(S₂)` instance on reflexive modules. The existing owner theorem is restricted to modules
      -- in the same universe as `R`, while the current statement keeps separate universes `u` and
      -- `v`.
      let _ := hTorsionFree
      let _ : R ⊧ (S₂) := hSerre.2
      sorry
    tfae_have 2 → 3 := by
      intro hTorsionFreeS2
      rcases hTorsionFreeS2 with ⟨hTorsionFree, hS2⟩
      refine ⟨hTorsionFree, le_antisymm ?_ ?_⟩
      · -- The easy inclusion is the tautological one: a global section belongs to every branch.
        exact mkLinearMap_range_le_moduleHeightOneLocalizationIntersection (R := R) (M := M)
      · -- TODO for Lemma 15.23.18: localize the cod-restriction
        -- `M → moduleHeightOneLocalizationIntersection R M`, prove it is bijective in
        -- codimension `≤ 1`, and apply the source-faithful map criterion from Lemma `15.23.14`
        -- using the `(S₂)` depth bound away from codimension one.
        sorry
    tfae_have 3 → 1 := by
      intro hTorsionFreeIntersection
      rcases hTorsionFreeIntersection with ⟨hTorsionFree, hIntersection⟩
      have hEvalInj : Function.Injective (Module.Dual.eval R M) :=
        (eval_injective_iff_isTorsionFree (R := R) (M := M)).2 hTorsionFree
      -- TODO for Lemma 15.23.18: follow the textbook generic-fiber descent argument.
      -- Prove the generic localization of `Module.Dual.eval R M` is bijective, show every
      -- height-one localization of the bidual lifts through the localized evaluation map, then use
      -- `hIntersection` to descend the resulting generic element back to `M`.
      let _ := hEvalInj
      let _ := hIntersection
      sorry
    tfae_finish

end
