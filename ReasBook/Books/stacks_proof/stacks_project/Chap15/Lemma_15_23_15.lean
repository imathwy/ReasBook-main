import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_23_4
import stacks_proof.stacks_project.Chap15.Lemma_15_23_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Module
open Module.Dual (eval)
open LocalizedModule (AtPrime)
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-
Domain-style sampling:
- primary domain: reflexive modules over Noetherian domains, detected by primewise local
  reflexivity and local depth bounds;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.Dual.eval`,
  `moduleDepth`,
  `isReflexive_localization_tfae`,
  `bijective_of_localizedMap_bijective_or_depth_localizedModule_ge_two_of_isTorsionFree`;
- best owner abstraction:
  `Module.IsReflexive` is the core/canonical owner for the global property, `moduleDepth` is the
  canonical local depth owner, and the preceding chapter lemmas already provide the needed
  source-facing local-global bridge;
- source/core/bridge triage:
  `source-facing`: the textbook criterion characterizing reflexivity by the primewise disjunction;
  `core/canonical`: `Module.IsReflexive`, `Module.Dual.eval`, `moduleDepth`;
  `bridge/view`: `Lemma 15.23.4` packages the source-facing local-global TFAE,
    `isReflexive_atPrime_iff_bijective_eval` packages the localized evaluation-map comparison, and
    `Lemma 15.23.14` packages the local-depth-or-isomorphism criterion for a map into a
    torsion-free module.

Primitive data are only the module `M` and the primewise disjunction itself. The local reflexive
branch and the global reflexive conclusion are both derived from the owner `Module.IsReflexive`,
so this file should reuse the chapter bridge lemmas directly rather than introducing a parallel
wrapper around localized evaluation maps or local depth data.
-/

-- Proof sketch: if `M` is reflexive, then every localization `Mₚ` is reflexive by
-- Lemma `15.23.4`, so the local disjunction holds at every prime. Conversely, apply
-- Lemma `15.23.14` to the evaluation map `M → Hom_R(Hom_R(M, R), R)`. By Algebra `10.10.2`,
-- its localization at `p` identifies with the evaluation map of `Mₚ`; the reflexive branch gives
-- a localized isomorphism, while the other branch is exactly the required depth bound.
/-- Lemma 15.23.15: for a finite module `M` over a Noetherian domain `R`, `M` is reflexive if and
only if for every prime ideal `p` of `R`, either the localized module `Mₚ` is reflexive over
`Rₚ` or `Mₚ` has depth at least `2`. -/
@[stacks 0AVA]
theorem isReflexive_iff_localizedModuleAtPrime_isReflexive_or_depth_ge_two :
    IsReflexive R M ↔
      ∀ p : PrimeSpectrum R,
        IsReflexive (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M) ∨
          (2 : ℕ∞) ≤
            moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M) := by
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  letI : Module.IsTorsionFree R (Dual R (Dual R M)) := inferInstance
  constructor
  · intro hM p
    -- Localize the global reflexivity hypothesis and take the reflexive branch of the disjunction.
    have hAtPrime :
        ∀ (P : Ideal R) [P.IsPrime], IsReflexive (Localization.AtPrime P) (AtPrime P M) :=
      (isReflexive_localization_tfae.out 0 1).mp hM
    exact .inl (hAtPrime p.asIdeal)
  · intro hlocal
    -- Apply the local-to-global bijectivity criterion to the canonical evaluation map.
    let hEval : Function.Bijective (eval R M) :=
      bijective_of_localizedMap_bijective_or_depth_localizedModule_ge_two_of_isTorsionFree
        (R := R) (M := M) (N := Dual R (Dual R M)) (eval R M) fun p ↦ by
          rcases hlocal p with hreflexive | hdepth
          -- In the reflexive branch, the localized evaluation map is bijective by the primewise criterion.
          · exact .inl ((isReflexive_atPrime_iff_bijective_eval p.asIdeal).mp hreflexive)
          -- In the depth branch, feed the bound directly into Lemma `15.23.14`.
          · exact .inr hdepth
    exact ⟨hEval⟩

end
