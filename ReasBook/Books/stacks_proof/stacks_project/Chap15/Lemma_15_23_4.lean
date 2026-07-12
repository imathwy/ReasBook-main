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

/-- Helper for Lemma 15.23.4: localizing the ring module `R` at a prime ideal identifies the
localized module with the local ring itself. -/
private noncomputable def atPrime_target_equiv (P : Ideal R) [P.IsPrime] :
    LocalizedModule P.primeCompl R ≃ₗ[R] Localization.AtPrime P :=
  IsLocalizedModule.linearEquiv P.primeCompl
    (LocalizedModule.mkLinearMap P.primeCompl R)
    (Algebra.linearMap R (Localization.AtPrime P))

section AtPrimeDual

variable {N : Type v} [AddCommGroup N] [Module R N] [Module.FinitePresentation R N]

/-- Helper for Lemma 15.23.4: localizing the dual of a finitely presented module identifies it
with the dual of the localized module. -/
private noncomputable def atPrime_dual_linearEquiv (P : Ideal R) [P.IsPrime] :
    LocalizedModule P.primeCompl (Dual R N) ≃ₗ[R]
      Dual (Localization.AtPrime P) (AtPrime P N) :=
  (Module.FinitePresentation.linearEquivMapExtendScalars
      (M := N) (N := R) P.primeCompl).trans
    (LinearEquiv.restrictScalars R <|
      (LinearEquiv.extendScalarsOfIsLocalization P.primeCompl (Localization.AtPrime P)
        (atPrime_target_equiv (R := R) P)).congrRight)

/-- Helper for Lemma 15.23.4: the localized dual comparison sends a denominator-`1` scalar to
the obvious element of the prime-local ring. -/
private theorem atPrime_target_equiv_apply_mk_one
    (P : Ideal R) [P.IsPrime] (r : R) :
    atPrime_target_equiv (R := R) P (LocalizedModule.mk r 1) =
      algebraMap R (Localization.AtPrime P) r := by
  -- Evaluate the canonical localization equivalence on a numerator generator.
  simpa [atPrime_target_equiv] using
    (IsLocalizedModule.linearEquiv_apply P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl R)
      (Algebra.linearMap R (Localization.AtPrime P))
      r)

/-- Helper for Lemma 15.23.4: evaluating the codomain transport on `mk n 1` just applies the
localized target equivalence to the value at `mk n 1`. -/
private theorem atPrime_extendScalars_congrRight_eval_on_mk_one
    (P : Ideal R) [P.IsPrime]
    (ψ : AtPrime P N →ₗ[Localization.AtPrime P] LocalizedModule P.primeCompl R) (n : N) :
    ((LinearEquiv.restrictScalars R <|
        (LinearEquiv.extendScalarsOfIsLocalization P.primeCompl (Localization.AtPrime P)
          (atPrime_target_equiv (R := R) P)).congrRight) ψ)
      (LocalizedModule.mk n 1) =
      atPrime_target_equiv (R := R) P (ψ (LocalizedModule.mk n 1)) := by
  -- First evaluate the codomain transport on the localized generator `mk n 1`.
  rw [LinearEquiv.restrictScalars_apply]
  change (LinearEquiv.extendScalarsOfIsLocalization P.primeCompl (Localization.AtPrime P)
      (atPrime_target_equiv (R := R) P)) (ψ (LocalizedModule.mk n 1)) = _
  rw [LinearEquiv.extendScalarsOfIsLocalization_apply]

/-- Helper for Lemma 15.23.4: on denominator-`1` generators, the localized dual comparison
recovers ordinary evaluation transported into the prime-local ring. -/
private theorem atPrime_dual_linearEquiv_apply_mk_apply_mk
    (P : Ideal R) [P.IsPrime] (φ : Dual R N) (n : N) :
    ((atPrime_dual_linearEquiv (R := R) (N := N) P) (LocalizedModule.mk φ 1))
      (LocalizedModule.mk n 1) =
      algebraMap R (Localization.AtPrime P) (φ n) := by
  -- Normalize the localized dual map on denominator-`1` generators before comparing scalars.
  rw [atPrime_dual_linearEquiv, LinearEquiv.trans_apply]
  rw [show (Module.FinitePresentation.linearEquivMapExtendScalars
      (M := N) (N := R) P.primeCompl) (LocalizedModule.mk φ 1) =
      (IsLocalizedModule.mapExtendScalars P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl N)
        (LocalizedModule.mkLinearMap P.primeCompl R)
        (Localization.AtPrime P)) φ by
      simpa using Module.FinitePresentation.linearEquivMapExtendScalars_apply
        (S := P.primeCompl) (f := φ)]
  rw [atPrime_extendScalars_congrRight_eval_on_mk_one (R := R) (N := N) P
    ((IsLocalizedModule.mapExtendScalars P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl N)
      (LocalizedModule.mkLinearMap P.primeCompl R)
      (Localization.AtPrime P)) φ) n]
  have hmap :
      ((IsLocalizedModule.mapExtendScalars P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl N)
          (LocalizedModule.mkLinearMap P.primeCompl R)
          (Localization.AtPrime P)) φ)
        (LocalizedModule.mk n 1) = LocalizedModule.mk (φ n) 1 := by
    -- The localized linear map still satisfies the defining localization square on `n`.
    change ((LinearMap.restrictScalars R
        ((IsLocalizedModule.mapExtendScalars P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl N)
          (LocalizedModule.mkLinearMap P.primeCompl R)
          (Localization.AtPrime P)) φ))
        (LocalizedModule.mk n 1)) = _
    simpa using
      LinearMap.congr_fun
        (IsLocalizedModule.map_comp P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl N)
          (LocalizedModule.mkLinearMap P.primeCompl R) φ)
        n
  rw [hmap]
  simpa using atPrime_target_equiv_apply_mk_one (R := R) P (φ n)

/-- Helper for Lemma 15.23.4: the dual localization comparison itself is a localization map. -/
private noncomputable def atPrime_dual_localization_map
    (P : Ideal R) [P.IsPrime] :
    Dual R N →ₗ[R] Dual (Localization.AtPrime P) (AtPrime P N) :=
  ((atPrime_dual_linearEquiv (R := R) (N := N) P).toLinearMap).comp
    (LocalizedModule.mkLinearMap P.primeCompl (Dual R N))

/-- Helper for Lemma 15.23.4: the transported dual map inherits the localization universal
property from the canonical localization map. -/
private theorem atPrime_dual_localization_map_isLocalizedModule
    (P : Ideal R) [P.IsPrime] :
    IsLocalizedModule P.primeCompl
      (atPrime_dual_localization_map (R := R) (N := N) P) := by
  let e := atPrime_dual_linearEquiv (R := R) (N := N) P
  -- Transport the localization structure across the dual comparison equivalence.
  simpa [atPrime_dual_localization_map, e] using
    (show IsLocalizedModule P.primeCompl
      (e.toLinearMap ∘ₗ LocalizedModule.mkLinearMap P.primeCompl (Dual R N))
      from inferInstance)

end AtPrimeDual

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
  -- TODO: the source-faithful route is to identify `map P.primeCompl (eval R M)` with
  -- `Dual.eval (Localization.AtPrime P) (AtPrime P M)` by localizing the bidual. The current file
  -- only assumes `[Module.FinitePresentation R M]`, and both attempted bridges fail exactly at the
  -- missing comparison between `(Dual R (Dual R M))_P` and `Dual R_P (Dual R_P M_P)` without
  -- further control on `Dual R M`.
  sorry

-- Proof sketch: localize the canonical evaluation map `M → Hom_R(Hom_R(M, R), R)` at a prime
-- ideal and identify it with the corresponding evaluation map for `M_p`, using Algebra
-- `10.10.2`. Then apply the local criterion from Algebra `10.23.1` to pass between reflexivity of
-- `M`, reflexivity at every prime localization, and reflexivity at every maximal localization.
/-- Lemma 15.23.4: for a finitely presented module, the following are equivalent: the module is
reflexive; every localization at a prime ideal is reflexive; and every localization at a maximal
ideal is reflexive. In the source Noetherian finite setting, finite presentation is automatic. -/
@[stacks 0AV1]
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
