import Mathlib
import stacks_project.Chap10.Definition_10_157_1

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

-- Proof sketch: apply Serre's criterion for normality to deduce `(R_1)` and `(S_2)` for `R`.
-- Then use Lemma `15.23.2` and Lemma `15.23.16` for `(1) → (2)`, Lemma `15.23.14` for
-- `(2) → (3)` after comparing the height-one localizations inside the generic fiber, and the DVR
-- freeness criterion from Lemma `15.22.11` for `(3) → (1)`.
/-- Lemma 15.23.18: for a finite module `M` over a Noetherian normal domain `R`, the following are
equivalent: `M` is reflexive; `M` is torsion free and satisfies Serre's condition `(S_2)`; and
`M` is torsion free and agrees with the intersection of its height-one localizations inside the
generic localization `M ⊗[R] Frac(R)`. -/
theorem reflexive_tfae_torsionFree_serreS2_heightOneLocalizationIntersection :
    List.TFAE
      [ IsReflexive R M
      , IsTorsionFree R M ∧ SerreConditionS R M 2
      , IsTorsionFree R M ∧
          LinearMap.range (mkLinearMap R⁰ M) =
            moduleHeightOneLocalizationIntersection R M ] :=
  sorry

end
