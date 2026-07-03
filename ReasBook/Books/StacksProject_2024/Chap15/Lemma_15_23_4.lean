import Mathlib
import StacksProject_2024.Chap10.Lemma_10_10_2
import StacksProject_2024.Chap10.Lemma_10_23_1
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Module
open Module.Dual (eval)
open LocalizedModule (AtPrime map)

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

/-
Domain-style sampling:
- primary domain: reflexive finitely presented modules, detected by localization of the canonical
  double-dual evaluation map;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.Dual.eval`,
  `bijective_localization_tfae`,
  `Module.FinitePresentation.linearEquivMapExtendScalars`,
  `LinearMap.extendScalarsOfIsLocalizationEquiv`;
- best owner abstraction: `Module.IsReflexive` is the core/canonical owner of the source notion,
  with `Module.Dual.eval` as the canonical comparison map and `bijective_localization_tfae` as the
  canonical local-global owner theorem for bijectivity under prime and maximal localization;
- source/core/bridge triage:
  `source-facing`: the TFAE criterion comparing reflexivity of `M`, of every `Mₚ`, and of every
    `Mₘ`;
  `core/canonical`: `Module.IsReflexive`, `Module.Dual.eval`, `bijective_localization_tfae`;
  `bridge/view`: Lemma `10.10.2`, which identifies the localization of `Dual.eval R M` with the
    evaluation map of the localized module; there is no exact upstream theorem for this
    comparison, so the minimal chapter-level bridge theorem
    `isReflexive_atPrime_iff_bijective_eval` is kept as the public companion built from that
    identification.

Primitive data are only the finitely presented module `M` and its canonical evaluation map into
the double dual. Local reflexivity is derived API from that owner map after localization, so the
theorem should be proved by instantiating the canonical local-global bijectivity theorem in its
native ideal-indexed form rather than by keeping a parallel
`PrimeSpectrum`/`MaximalSpectrum` wrapper layer around that owner theorem.
-/

/-- Bridge/view: for a prime localization of a finitely presented module, reflexivity of the
localized module is equivalent to bijectivity of the localized canonical evaluation map. -/
theorem isReflexive_atPrime_iff_bijective_eval
    (P : Ideal R) [P.IsPrime] :
    IsReflexive (Localization.AtPrime P) (AtPrime P M) ↔
      Function.Bijective (map P.primeCompl (eval R M)) := by
  -- Proof sketch: localize `eval R M`, identify the localized `Hom` spaces with the
  -- corresponding `Localization.AtPrime P`-linear `Hom` spaces via Lemma `10.10.2`, and compare
  -- the resulting localized map with `Dual.eval (Localization.AtPrime P)
  -- (LocalizedModule.AtPrime P M)`.
  sorry

-- Proof sketch: localize the canonical evaluation map `M → Hom_R(Hom_R(M, R), R)` at a prime
-- ideal and identify it with the corresponding evaluation map for `M_p`, using Algebra
-- `10.10.2`. Then apply the local criterion from Algebra `10.23.1` to pass between reflexivity of
-- `M`, reflexivity at every prime localization, and reflexivity at every maximal localization.
/-- Lemma 15.23.4: for a finitely presented module, the following are equivalent: the module is
reflexive; every localization at a prime ideal is reflexive; and every localization at a maximal
ideal is reflexive. In the source Noetherian finite setting, finite presentation is automatic. -/
theorem isReflexive_localization_tfae :
    List.TFAE
      [ IsReflexive R M
      , ∀ (P : Ideal R) [P.IsPrime], IsReflexive (Localization.AtPrime P) (AtPrime P M)
      , ∀ (P : Ideal R) [P.IsMaximal], IsReflexive (Localization.AtPrime P) (AtPrime P M)
      ] := by
  have hEval := bijective_localization_tfae (eval R M)
  have hPrimeEval [IsReflexive R M] :
      ∀ (P : Ideal R) [P.IsPrime], Function.Bijective (map P.primeCompl (eval R M)) :=
    (hEval.out 0 1).mp (bijective_dual_eval R M)
  tfae_have 1 → 2 := by
    intro hM P _
    letI := hM
    exact (isReflexive_atPrime_iff_bijective_eval P).2 (hPrimeEval P)
  tfae_have 2 → 3 := by
    intro h P _
    exact h P
  tfae_have 3 → 1 := by
    intro hM
    have hMaxEval :
        ∀ (P : Ideal R) [P.IsMaximal], Function.Bijective (map P.primeCompl (eval R M)) := by
      intro P _
      letI : P.IsPrime := inferInstance
      exact (isReflexive_atPrime_iff_bijective_eval P).1 (hM P)
    exact ⟨(hEval.out 2 0).mp hMaxEval⟩
  tfae_finish

end
