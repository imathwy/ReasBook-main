import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_119_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_22_11
import StacksProject_2024.stacks_project.Chap15.Lemma_15_23_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_23_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_23_8
import StacksProject_2024.stacks_project.Chap15.Lemma_15_23_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped nonZeroDivisors
open Module
open Module.Dual (eval)
open LocalizedModule (map mkLinearMap)
open Ideal IsLocalRing

universe u v

/-
Domain-style sampling:
- primary domain: generic localization of finite modules over domains, together with the
  height-one localization intersection criterion for finite modules over Noetherian normal domains;
- sampled owner declarations:
  `Module.Dual.eval`,
  `Submodule.torsion`,
  `moduleHeightOneLocalizationIntersection`,
  `eval_ker_isTorsion`,
  `reflexive_tfae_torsionFree_serreS2_heightOneLocalizationIntersection`;
- best owner abstraction: the bridge should stay centered on the canonical double dual owner
  `Module.Dual R (Module.Dual R M)` and the canonical quotient by `Submodule.torsion`, while the
  source-facing final statement should use the chapter owner
  `moduleHeightOneLocalizationIntersection`;
- primitive data: the canonical maps `Dual.eval R M`, `(Submodule.torsion R M).mkQ`, and
  `LocalizedModule.mkLinearMap R⁰`;
- derived API: the localization-bijectivity statements and the induced localization equivalences.

Source/core/bridge triage:
- `source-facing`: the final equality identifying the image of the reflexive hull inside the
  generic localization of `M / M_tors`;
- `core/canonical`: `Dual.eval`, `Submodule.torsion`, and
  `moduleHeightOneLocalizationIntersection`;
- `bridge/view`: the comparison map from the double dual into the generic localization of the
  torsion-free quotient.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Helper for Lemma 15.23.19: localizing a torsion submodule at the generic point kills it. -/
private theorem localized_torsion_submodule_eq_bot
    {A : Type v} [AddCommGroup A] [Module R A]
    (P : Submodule R A) (hP : IsTorsion R P) :
    Submodule.localized' (Localization R⁰) R⁰
      (LocalizedModule.mkLinearMap R⁰ A) P = ⊥ := by
  -- Proof comment: each localized generator already vanishes because a torsion annihilator in `R⁰`
  -- becomes an allowed denominator witness for `mk' = 0`.
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_localized'] at hx
  rcases hx with ⟨m, hm, s, rfl⟩
  obtain ⟨a, ha⟩ := hP (x := ⟨m, hm⟩)
  rw [IsLocalizedModule.mk'_eq_zero']
  refine ⟨a, ?_⟩
  simpa [smul_smul] using congrArg Subtype.val ha

/-- The localization of the evaluation map `M → M**` at the generic point is bijective. -/
-- Proof sketch: Lemma `15.23.2` shows that the kernel and cokernel of `M → M**` are torsion.
-- Localizing at the non-zero-divisors of the domain `R` kills torsion, so the induced map on the
-- generic localization is both injective and surjective.
private theorem genericLocalization_map_eval_bijective :
    Function.Bijective (map R⁰ (eval R M)) := by
  let D : Type max u v := Dual R (Dual R M)
  let Q : Submodule R D := (eval R M).range
  refine ⟨?_, ?_⟩
  · have hkerLocalized :
        LinearMap.ker (LocalizedModule.map R⁰ (eval R M)) = ⊥ := by
      -- The localized kernel is the localization of the torsion kernel, hence zero.
      calc
        LinearMap.ker (LocalizedModule.map R⁰ (eval R M)) =
            Submodule.localized' (Localization R⁰) R⁰
              (LocalizedModule.mkLinearMap R⁰ M)
              (LinearMap.ker (eval R M)) := by
                symm
                simpa using
                  (LinearMap.localized'_ker_eq_ker_localizedMap
                    (S := Localization R⁰)
                    (p := R⁰)
                    (f := LocalizedModule.mkLinearMap R⁰ M)
                    (f' := LocalizedModule.mkLinearMap R⁰ D)
                    (g := eval R M))
        _ = ⊥ := by
              simpa using
                (localized_torsion_submodule_eq_bot
                  (R := R)
                  (P := LinearMap.ker (eval R M))
                  (hP := eval_ker_isTorsion (R := R) (M := M)))
    -- A localized linear map with zero kernel is injective.
    simpa [LinearMap.ker_eq_bot] using hkerLocalized
  · have hsub :
        Subsingleton (LocalizedModule R⁰ (D ⧸ Q)) := by
      rw [LocalizedModule.subsingleton_iff]
      intro x
      obtain ⟨a, ha⟩ := eval_cokernel_isTorsion (R := R) (M := M) (x := x)
      exact ⟨a, a.2, ha⟩
    let e :
        (LocalizedModule R⁰ D ⧸ Submodule.localized (p := R⁰) Q) ≃ₗ[FractionRing R]
          LocalizedModule R⁰ (D ⧸ Q) :=
      localizedQuotientEquiv R⁰ Q
    have hquot :
        Subsingleton (LocalizedModule R⁰ D ⧸ Submodule.localized (p := R⁰) Q) := by
      letI : Subsingleton (LocalizedModule R⁰ (D ⧸ Q)) := hsub
      exact e.toEquiv.subsingleton
    have hlocalized_top : Submodule.localized (p := R⁰) Q = ⊤ := by
      -- The localized cokernel is trivial, so the localized range is the whole generic fiber.
      rw [Submodule.eq_top_iff']
      intro z
      have hz :
          ((Submodule.localized (p := R⁰) Q).mkQ z :
            LocalizedModule R⁰ D ⧸ Submodule.localized (p := R⁰) Q) = 0 := by
        letI : Subsingleton (LocalizedModule R⁰ D ⧸ Submodule.localized (p := R⁰) Q) := hquot
        exact Subsingleton.elim _ 0
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
    intro z
    have hz : z ∈ Submodule.localized (p := R⁰) Q := by
      simpa [hlocalized_top]
    rw [Submodule.mem_localized'] at hz
    rcases hz with ⟨y, hyQ, s, rfl⟩
    rcases hyQ with ⟨x, rfl⟩
    refine ⟨IsLocalizedModule.mk' (LocalizedModule.mkLinearMap R⁰ M) x s, ?_⟩
    exact
      IsLocalizedModule.map_mk' (S := R⁰)
        (f := LocalizedModule.mkLinearMap R⁰ M)
        (g := LocalizedModule.mkLinearMap R⁰ D)
        (h := eval R M) x s

/-- Helper for Lemma 15.23.19: after inverting `R⁰`, the torsion submodule of `M` vanishes. -/
private theorem localized_torsion_eq_bot :
    Submodule.localized' (Localization R⁰) R⁰
      (LocalizedModule.mkLinearMap R⁰ M) (Submodule.torsion R M) = ⊥ := by
  -- Proof comment: every localized torsion generator is already zero because its numerator is
  -- killed by a non-zero divisor that becomes invertible after localization.
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_localized'] at hx
  rcases hx with ⟨m, hm, s, rfl⟩
  rw [Submodule.mem_torsion_iff] at hm
  rcases hm with ⟨a, ha⟩
  -- The torsion annihilator for `m` is exactly the denominator witness for `mk' = 0`.
  rw [IsLocalizedModule.mk'_eq_zero']
  exact ⟨a, by simpa [smul_smul] using ha⟩

/-- The generic localization of `M` agrees with the generic localization of `M / M_tors`. -/
-- Proof sketch: the quotient map `M → M / M_tors` is surjective, and its kernel is the torsion
-- submodule `Submodule.torsion R M`. After localizing at `R⁰`, that kernel vanishes, so the
-- induced map on generic localizations is bijective.
private theorem genericLocalization_map_torsionQuotient_bijective :
    Function.Bijective (map R⁰ (Submodule.torsion R M).mkQ) := by
  let T : Submodule R M := Submodule.torsion R M
  refine ⟨?_, ?_⟩
  · have hkerLocalized :
        LinearMap.ker (LocalizedModule.map R⁰ T.mkQ) = ⊥ := by
      -- Localization identifies the kernel with the localized torsion submodule, which is zero.
      calc
        LinearMap.ker (LocalizedModule.map R⁰ T.mkQ) =
            Submodule.localized' (Localization R⁰) R⁰
              (LocalizedModule.mkLinearMap R⁰ M)
              (LinearMap.ker T.mkQ) := by
                symm
                simpa using
                  (LinearMap.localized'_ker_eq_ker_localizedMap
                    (S := Localization R⁰)
                    (p := R⁰)
                    (f := LocalizedModule.mkLinearMap R⁰ M)
                    (f' := LocalizedModule.mkLinearMap R⁰ (M ⧸ T))
                    (g := T.mkQ))
        _ = ⊥ := by
              simpa [T, Submodule.ker_mkQ] using
                (localized_torsion_eq_bot (R := R) (M := M))
    -- A localized linear map with zero kernel is injective.
    simpa [T, LinearMap.ker_eq_bot] using hkerLocalized
  · -- Surjectivity is preserved by the canonical localization map.
    simpa [T] using
      (IsLocalizedModule.map_surjective (S := R⁰)
        (f := LocalizedModule.mkLinearMap R⁰ M)
        (g := LocalizedModule.mkLinearMap R⁰ (M ⧸ T))
        (h := T.mkQ)
        (Submodule.mkQ_surjective T))

/-- Bridge/view: the canonical comparison map from the double dual of `M` into the generic
localization of the torsion-free quotient `M / M_tors`. -/
noncomputable def doubleDualToTorsionQuotientGenericLocalization :
    Dual R (Dual R M) →ₗ[R] LocalizedModule R⁰ (M ⧸ Submodule.torsion R M) :=
  let T := Submodule.torsion R M
  let evalEquiv :
      LocalizedModule R⁰ M ≃ₗ[Localization R⁰]
        LocalizedModule R⁰ (Dual R (Dual R M)) :=
    LinearEquiv.ofBijective (map R⁰ (eval R M)) genericLocalization_map_eval_bijective
  let torsionQuotEquiv :
      LocalizedModule R⁰ M ≃ₗ[Localization R⁰]
        LocalizedModule R⁰ (M ⧸ T) :=
    LinearEquiv.ofBijective (map R⁰ T.mkQ)
      genericLocalization_map_torsionQuotient_bijective
  (LinearMap.restrictScalars R torsionQuotEquiv.toLinearMap).comp
    ((LinearMap.restrictScalars R evalEquiv.symm.toLinearMap).comp
      (mkLinearMap R⁰ (Dual R (Dual R M))))

end

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Helper for Lemma 15.23.19: a height-one localization of a Noetherian normal domain is a
discrete valuation ring. -/
private theorem localizationAtHeightOnePrime_isDiscreteValuationRing
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) := by
  let S := Localization.AtPrime p.1.asIdeal
  have hnormal_dim_one :
      ∃ (_ : IsLocalRing S) (_ : IsNoetherianRing S) (_ : IsDomain S)
        (_ : IsIntegrallyClosed S), ringKrullDim S = 1 := by
    -- The source hypotheses localize, so only the height-one dimension computation remains.
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    calc
      ringKrullDim S = ↑p.1.asIdeal.height := by
        simpa [S] using
          (IsLocalization.AtPrime.ringKrullDim_eq_height p.1.asIdeal S)
      _ = (1 : WithBot ℕ∞) := by
        simpa [p.2] using congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat p.2).symm
  have hdvr :
      ∃ (_ : IsDomain S), IsDiscreteValuationRing S := by
    -- The dimension-one normal-local clause of Lemma `10.119.7` is exactly the DVR criterion.
    have htfae :=
      (show List.TFAE
          [ (∃ (_ : IsDomain S), IsDiscreteValuationRing S),
            ∃ (_ : IsDomain S) (_ : IsNoetherianRing S), ValuationRing S ∧ ¬ IsField S,
            IsRegularLocalRing S ∧ ringKrullDim S = 1,
            ∃ (_ : IsLocalRing S) (_ : IsNoetherianRing S) (_ : IsDomain S),
              IsLocalRing.maximalIdeal S ≠ ⊥ ∧ (IsLocalRing.maximalIdeal S).IsPrincipal,
            ∃ (_ : IsLocalRing S) (_ : IsNoetherianRing S) (_ : IsDomain S)
              (_ : IsIntegrallyClosed S), ringKrullDim S = 1 ] from
        discreteValuationRing_tfae (A := S))
    exact (htfae.out 4 0).mp hnormal_dim_one
  exact hdvr.choose_spec

/-- Helper for Lemma 15.23.19: after localizing the torsion quotient at a height-one prime, the
resulting module is reflexive because it is finite torsion free over a discrete valuation ring,
hence finite free. -/
private theorem localized_torsion_quotient_reflexive_at_height_one
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    IsReflexive (Localization.AtPrime p.1.asIdeal)
      (LocalizedModule.AtPrime p.1.asIdeal (M ⧸ Submodule.torsion R M)) := by
  let S := Localization.AtPrime p.1.asIdeal
  let N := LocalizedModule.AtPrime p.1.asIdeal (M ⧸ Submodule.torsion R M)
  -- The height-one localization is a DVR, so finite torsion-free modules over it are free.
  letI : IsDiscreteValuationRing S := localizationAtHeightOnePrime_isDiscreteValuationRing
    (R := R) p
  letI : IsPrincipalIdealRing S := inferInstance
  letI : Module.Free S N := Module.free_of_finite_type_torsion_free'
  -- Reflexivity is the owner theorem for finite free modules.
  exact Module.IsReflexive.of_finite_of_free (R := S) (M := N)

omit [IsNoetherianRing R] [IsIntegrallyClosed R] [Module.Finite R M] in
/-- Helper for Lemma 15.23.19: every functional on `M` kills the torsion submodule. -/
private theorem dual_mem_torsion_dualAnnihilator (φ : Dual R M) :
    φ ∈ (Submodule.torsion R M).dualAnnihilator := by
  -- Every torsion element is killed by some non-zero divisor, and linearity transports that
  -- annihilating scalar to the value of `φ`.
  rw [Submodule.mem_dualAnnihilator]
  intro x hx
  rcases hx with ⟨a, hax⟩
  have ha0 : (a : R) ≠ 0 := nonZeroDivisors.ne_zero a.2
  have hax' : a • φ x = 0 := by
    simpa [map_smul] using congrArg φ hax
  exact (smul_eq_zero_iff_right ha0).mp hax'

/-- Helper for Lemma 15.23.19: dualizing the quotient by the torsion submodule is bijective. -/
private theorem dualMap_torsion_quotient_bijective :
    Function.Bijective
      (((Submodule.torsion R M).mkQ : M →ₗ[R] M ⧸ Submodule.torsion R M).dualMap) := by
  refine ⟨LinearMap.dualMap_injective_of_surjective (Submodule.torsion R M).mkQ_surjective, ?_⟩
  intro φ
  refine
    ⟨(Submodule.torsion R M).dualQuotEquivDualAnnihilator.symm
        ⟨φ, dual_mem_torsion_dualAnnihilator (R := R) (M := M) φ⟩, ?_⟩
  ext x
  exact
    (Submodule.torsion R M).dualQuotEquivDualAnnihilator_symm_apply_mk
      ⟨φ, dual_mem_torsion_dualAnnihilator (R := R) (M := M) φ⟩ x

/-- Helper for Lemma 15.23.19: the dual of `M / M_tors` identifies canonically with the dual of
`M`. -/
private noncomputable def torsionQuotientDualEquiv :
    Dual R (M ⧸ Submodule.torsion R M) ≃ₗ[R] Dual R M :=
  LinearEquiv.ofBijective
    (((Submodule.torsion R M).mkQ : M →ₗ[R] M ⧸ Submodule.torsion R M).dualMap)
    (dualMap_torsion_quotient_bijective (R := R) (M := M))

/-- Helper for Lemma 15.23.19: the induced double-dual equivalence between `M**` and
`(M / M_tors)**`. -/
private noncomputable def torsionQuotientDoubleDualEquiv :
    Dual R (Dual R M) ≃ₗ[R] Dual R (Dual R (M ⧸ Submodule.torsion R M)) :=
  (torsionQuotientDualEquiv (R := R) (M := M)).dualMap

/-- Helper for Lemma 15.23.19: the canonical map from the double dual of `N` into the generic
localization of `N` obtained by inverting the localized evaluation map. -/
private noncomputable def reflexiveHullGenericLocalizationMap
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] :
    Dual R (Dual R N) →ₗ[R] LocalizedModule R⁰ N :=
  let evalEquiv :
      LocalizedModule R⁰ N ≃ₗ[Localization R⁰]
        LocalizedModule R⁰ (Dual R (Dual R N)) :=
    LinearEquiv.ofBijective (LocalizedModule.map R⁰ (eval R N))
      (genericLocalization_map_eval_bijective (R := R) (M := N))
  (LinearMap.restrictScalars R evalEquiv.symm.toLinearMap).comp
    (LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R N)))

/-- Helper for Lemma 15.23.19: applying the generic localized evaluation map to the reflexive-hull
map of `N` recovers the generic numerator embedding of `N**`. -/
private theorem reflexiveHullGenericLocalizationMap_comp_localized_eval
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] :
    (LinearMap.restrictScalars R (LocalizedModule.map R⁰ (eval R N))).comp
        (reflexiveHullGenericLocalizationMap (R := R) (N := N)) =
      LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R N)) := by
  -- The reflexive-hull map is defined by inverting the generic localized evaluation map.
  ext x
  simp [reflexiveHullGenericLocalizationMap]

/-- Helper for Lemma 15.23.19: if `N_p` is reflexive at a height-one prime, then the localized
evaluation map at that prime is bijective. -/
private theorem localized_eval_bijective_at_height_one_of_reflexive
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 })
    (hRef :
      IsReflexive (Localization.AtPrime p.1.asIdeal)
        (LocalizedModule.AtPrime p.1.asIdeal N)) :
    Function.Bijective (LocalizedModule.map p.1.asIdeal.primeCompl (eval R N)) := by
  letI : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
  exact
    (isReflexive_atPrime_iff_bijective_eval (R := R) (M := N) p.1.asIdeal).1 hRef

/-- Helper for Lemma 15.23.19: at a height-one prime, local reflexivity of `N` identifies the
localized double dual with the localized module itself. -/
private noncomputable def heightOneLocalizedEvalEquiv
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 })
    (hRef :
      IsReflexive (Localization.AtPrime p.1.asIdeal)
        (LocalizedModule.AtPrime p.1.asIdeal N)) :
    LocalizedModule.AtPrime p.1.asIdeal (Dual R (Dual R N)) ≃ₗ[Localization.AtPrime p.1.asIdeal]
      LocalizedModule.AtPrime p.1.asIdeal N :=
  (LinearEquiv.ofBijective
    (LocalizedModule.map p.1.asIdeal.primeCompl (eval R N))
    (localized_eval_bijective_at_height_one_of_reflexive
      (R := R) (N := N) p hRef)).symm

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Module.Finite R M] in
/-- Helper for Lemma 15.23.19: the inverse of a localized evaluation equivalence sends a
denominator generator coming from `eval R N x` back to the denominator generator of `x`. -/
private theorem localized_eval_equiv_symm_mk'_of_generator
    {S : Submonoid R} {N : Type v} [AddCommGroup N] [Module R N]
    (hbij : Function.Bijective (LocalizedModule.map S (eval R N)))
    (x : N) (s : S) :
    let E : LocalizedModule S N ≃ₗ[Localization S]
        LocalizedModule S (Dual R (Dual R N)) :=
      LinearEquiv.ofBijective (LocalizedModule.map S (eval R N)) hbij
    E.symm (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (Dual R (Dual R N)))
      (eval R N x) s) =
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S N) x s := by
  -- Route correction: normalize the inverse evaluation equivalence on `mk'` generators once,
  -- rather than asking later transport lemmas to unfold `LinearEquiv.ofBijective` repeatedly.
  dsimp
  apply (LinearEquiv.ofBijective (LocalizedModule.map S (eval R N)) hbij).injective
  rw [LinearEquiv.apply_symm_apply]
  -- The forward localized evaluation map is exactly the canonical `mk'` numerator map.
  exact (IsLocalizedModule.map_mk' (S := S)
      (f := LocalizedModule.mkLinearMap S N)
      (g := LocalizedModule.mkLinearMap S (Dual R (Dual R N)))
      (h := eval R N) x s).symm

/-- Helper for Lemma 15.23.19: after lifting a height-one localized evaluation generator to the
generic fiber, the generic inverse-evaluation equivalence recovers the corresponding generator of
`N`. -/
private theorem height_one_liftOfLE_mk'_transport_via_localized_eval_equiv
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 })
    (hRef :
      IsReflexive (Localization.AtPrime p.1.asIdeal)
        (LocalizedModule.AtPrime p.1.asIdeal N))
    (x : N) (s : p.1.asIdeal.primeCompl) :
    let E :
        LocalizedModule R⁰ N ≃ₗ[Localization R⁰]
          LocalizedModule R⁰ (Dual R (Dual R N)) :=
      LinearEquiv.ofBijective (LocalizedModule.map R⁰ (eval R N))
        (genericLocalization_map_eval_bijective (R := R) (M := N))
    (LinearMap.restrictScalars R E.symm.toLinearMap)
        ((LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
          (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal))
          (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl
            (Dual R (Dual R N))) (eval R N x) s)) =
      (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
        (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal) :
        LocalizedModule.AtPrime p.1.asIdeal N →ₗ[R] LocalizedModule R⁰ N)
        (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl N) x s) := by
  -- Proof comment: first rewrite the height-one branch on `N**` to the corresponding generic
  -- `mk'` generator, then use the inverse generic evaluation equivalence to remove `eval`.
  dsimp
  rw [IsLocalizedModule.liftOfLE_mk']
  rw [localized_eval_equiv_symm_mk'_of_generator
    (R := R)
    (S := R⁰)
    (N := N)
    (hbij := genericLocalization_map_eval_bijective (R := R) (M := N))
    x
    ⟨↑s, Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal s.2⟩]
  rw [IsLocalizedModule.liftOfLE_mk']

/-- Helper for Lemma 15.23.19: the height-one localized evaluation equivalence is the inverse of
the localized evaluation map after restricting scalars back to `R`. -/
private theorem height_one_localized_eval_equiv_comp_localized_eval_restrictScalars
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 })
    (hRef :
      IsReflexive (Localization.AtPrime p.1.asIdeal)
        (LocalizedModule.AtPrime p.1.asIdeal N)) :
    let ep := heightOneLocalizedEvalEquiv (R := R) (N := N) p hRef
    (LinearMap.restrictScalars R ep.toLinearMap).comp
        (LinearMap.restrictScalars R
          (LocalizedModule.map p.1.asIdeal.primeCompl (eval R N))) =
      LinearMap.id := by
  -- Proof comment: by construction `ep` is the inverse of the localized evaluation equivalence.
  dsimp [heightOneLocalizedEvalEquiv]
  ext z
  exact
    LinearEquiv.symm_apply_apply
      (LinearEquiv.ofBijective
        (LocalizedModule.map p.1.asIdeal.primeCompl (eval R N))
        (localized_eval_bijective_at_height_one_of_reflexive
          (R := R) (N := N) p hRef))
      z

/-- Helper for Lemma 15.23.19: the global reflexive-hull equivalence for `N` intertwines the
height-one branch maps with the local evaluation equivalence. -/
private theorem height_one_liftOfLE_transport_comp
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 })
    (hRef :
      IsReflexive (Localization.AtPrime p.1.asIdeal)
        (LocalizedModule.AtPrime p.1.asIdeal N)) :
    let E :
        LocalizedModule R⁰ N ≃ₗ[Localization R⁰]
          LocalizedModule R⁰ (Dual R (Dual R N)) :=
      LinearEquiv.ofBijective (LocalizedModule.map R⁰ (eval R N))
        (genericLocalization_map_eval_bijective (R := R) (M := N))
    let ep := heightOneLocalizedEvalEquiv (R := R) (N := N) p hRef
    (LinearMap.restrictScalars R E.symm.toLinearMap).comp
        (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
          (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal)) =
      (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
        (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal)).comp
        (LinearMap.restrictScalars R ep.toLinearMap) := by
  -- Route correction: cancel the local evaluation map after precomposing both sides, then remove
  -- that precomposition using surjectivity of the localized evaluation map.
  dsimp
  let E :
      LocalizedModule R⁰ N ≃ₗ[Localization R⁰]
        LocalizedModule R⁰ (Dual R (Dual R N)) :=
    LinearEquiv.ofBijective (LocalizedModule.map R⁰ (eval R N))
      (genericLocalization_map_eval_bijective (R := R) (M := N))
  let ep := heightOneLocalizedEvalEquiv (R := R) (N := N) p hRef
  let evalp :
      LocalizedModule.AtPrime p.1.asIdeal N →ₗ[R]
        LocalizedModule.AtPrime p.1.asIdeal (Dual R (Dual R N)) :=
    LinearMap.restrictScalars R
      (LocalizedModule.map p.1.asIdeal.primeCompl (eval R N))
  have hleft :
      (((LinearMap.restrictScalars R E.symm.toLinearMap).comp
          (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
            (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal))).comp evalp) =
        (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
          (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal) :
          LocalizedModule.AtPrime p.1.asIdeal N →ₗ[R] LocalizedModule R⁰ N) := by
    -- Proof comment: on localized numerator generators, the left side is exactly the previously
    -- normalized `mk'` transport statement.
    ext z
    obtain ⟨⟨x, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective p.1.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl N) z
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    dsimp [evalp]
    have hmap :
        (((LocalizedModule.map p.1.asIdeal.primeCompl) (eval R N))
          (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl N) x s)) =
          IsLocalizedModule.mk'
            (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl (Dual R (Dual R N)))
            (eval R N x) s := by
      exact IsLocalizedModule.map_mk' (S := p.1.asIdeal.primeCompl)
        (f := LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl N)
        (g := LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl (Dual R (Dual R N)))
        (h := eval R N) x s
    rw [hmap]
    rw [IsLocalizedModule.liftOfLE_mk']
    simpa [E, evalp] using
      (height_one_liftOfLE_mk'_transport_via_localized_eval_equiv
        (R := R) (N := N) p hRef x s)
  have hright :
      (((LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
          (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal)).comp
          (LinearMap.restrictScalars R ep.toLinearMap)).comp evalp) =
        (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
          (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal) :
          LocalizedModule.AtPrime p.1.asIdeal N →ₗ[R] LocalizedModule R⁰ N) := by
    -- Proof comment: the new adapter lemma collapses the local equivalence against localized
    -- evaluation to the identity on `N_p`.
    rw [LinearMap.comp_assoc]
    rw [height_one_localized_eval_equiv_comp_localized_eval_restrictScalars
      (R := R) (N := N) p hRef]
    simp
  have hpre :
      (((LinearMap.restrictScalars R E.symm.toLinearMap).comp
          (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
            (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal))).comp evalp) =
        (((LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
            (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal)).comp
            (LinearMap.restrictScalars R ep.toLinearMap)).comp evalp) := by
    exact hleft.trans hright.symm
  ext z
  rcases (localized_eval_bijective_at_height_one_of_reflexive
      (R := R) (N := N) p hRef).2 z with ⟨y, rfl⟩
  exact LinearMap.congr_fun hpre y

/-- Helper for Lemma 15.23.19: after transporting a height-one branch of the double dual of `N`
through the generic evaluation equivalence, one recovers the corresponding branch of `N`. -/
private theorem height_one_range_transport_reflexiveHull
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 })
    (hRef :
      IsReflexive (Localization.AtPrime p.1.asIdeal)
        (LocalizedModule.AtPrime p.1.asIdeal N)) :
    let E :
        LocalizedModule R⁰ N ≃ₗ[Localization R⁰]
          LocalizedModule R⁰ (Dual R (Dual R N)) :=
      LinearEquiv.ofBijective (LocalizedModule.map R⁰ (eval R N))
        (genericLocalization_map_eval_bijective (R := R) (M := N))
    ((LinearMap.range
        (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
          (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal))) :
      Submodule R (LocalizedModule R⁰ (Dual R (Dual R N)))).map
        (LinearMap.restrictScalars R E.symm.toLinearMap) =
      LinearMap.range
        (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
          (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal) :
          LocalizedModule.AtPrime p.1.asIdeal N →ₗ[R] LocalizedModule R⁰ N) := by
  dsimp
  let E :
      LocalizedModule R⁰ N ≃ₗ[Localization R⁰]
        LocalizedModule R⁰ (Dual R (Dual R N)) :=
    LinearEquiv.ofBijective (LocalizedModule.map R⁰ (eval R N))
      (genericLocalization_map_eval_bijective (R := R) (M := N))
  let ep := heightOneLocalizedEvalEquiv (R := R) (N := N) p hRef
  let evalp :
      LocalizedModule.AtPrime p.1.asIdeal N →ₗ[R]
        LocalizedModule.AtPrime p.1.asIdeal (Dual R (Dual R N)) :=
    LinearMap.restrictScalars R
      (LocalizedModule.map p.1.asIdeal.primeCompl (eval R N))
  -- Proof comment: transport membership in the height-one branch by the commuting square, and use
  -- the inverse-local-evaluation identity for the reverse inclusion.
  ext z
  constructor
  · intro hz
    rw [Submodule.mem_map] at hz
    rw [LinearMap.mem_range]
    rcases hz with ⟨w, hw, rfl⟩
    rw [LinearMap.mem_range] at hw
    rcases hw with ⟨t, rfl⟩
    refine ⟨(LinearMap.restrictScalars R ep.toLinearMap) t, ?_⟩
    exact
      (LinearMap.congr_fun
        (height_one_liftOfLE_transport_comp (R := R) (N := N) p hRef)
        t).symm
  · intro hz
    rw [LinearMap.mem_range] at hz
    rcases hz with ⟨t, rfl⟩
    rw [Submodule.mem_map]
    let fdd :
        LocalizedModule.AtPrime p.1.asIdeal (Dual R (Dual R N)) →ₗ[R]
          LocalizedModule R⁰ (Dual R (Dual R N)) :=
      LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
        (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal)
    let fN :
        LocalizedModule.AtPrime p.1.asIdeal N →ₗ[R]
          LocalizedModule R⁰ N :=
      LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
        (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal)
    refine ⟨fdd (evalp t), ?_, ?_⟩
    · rw [LinearMap.mem_range]
      exact ⟨evalp t, rfl⟩
    · have hid :
          ((LinearMap.restrictScalars R ep.toLinearMap).comp evalp) t = t := by
        exact
          LinearMap.congr_fun
            (height_one_localized_eval_equiv_comp_localized_eval_restrictScalars
              (R := R) (N := N) p hRef)
            t
      have htransport :
          (LinearMap.restrictScalars R E.symm.toLinearMap) (fdd (evalp t)) =
            fN (((LinearMap.restrictScalars R ep.toLinearMap).comp evalp) t) := by
        simpa [fdd, fN, LinearMap.comp_apply] using
          LinearMap.congr_fun
            (height_one_liftOfLE_transport_comp (R := R) (N := N) p hRef)
            (evalp t)
      calc
        (LinearMap.restrictScalars R E.symm.toLinearMap) (fdd (evalp t)) =
            fN (((LinearMap.restrictScalars R ep.toLinearMap).comp evalp) t) := htransport
        _ = fN t := by
              simpa [LinearMap.comp_apply] using congrArg fN hid

/-- Helper for Lemma 15.23.19: double duals of finite modules over the present normal domain are
reflexive. -/
private theorem doubleDual_isReflexive
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] :
    IsReflexive R (Dual R (Dual R N)) := by
  letI : Module.FinitePresentation R (Dual R N) := Module.finitePresentation_of_finite R (Dual R N)
  exact isReflexive_linearMap (R := R) (M := Dual R N) (N := R)

/-- Helper for Lemma 15.23.19: if every height-one localization of `N` is reflexive, then the
generic image of `N**` is the intersection of the height-one localizations of `N`. -/
private theorem reflexiveHull_range_eq_heightOneLocalizationIntersection_of_heightOneReflexive
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hLocal :
      ∀ p : { p : PrimeSpectrum R // p.asIdeal.height = 1 },
        IsReflexive (Localization.AtPrime p.1.asIdeal)
          (LocalizedModule.AtPrime p.1.asIdeal N)) :
    (reflexiveHullGenericLocalizationMap (R := R) (N := N)).range =
      moduleHeightOneLocalizationIntersection R N := by
  let E :
      LocalizedModule R⁰ N ≃ₗ[Localization R⁰]
        LocalizedModule R⁰ (Dual R (Dual R N)) :=
    LinearEquiv.ofBijective (LocalizedModule.map R⁰ (eval R N))
      (genericLocalization_map_eval_bijective (R := R) (M := N))
  have hDoubleRange :
      LinearMap.range (LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R N))) =
        moduleHeightOneLocalizationIntersection R (Dual R (Dual R N)) := by
    -- Proof comment: Lemma `15.23.18` applied to `N**` identifies its generic image with the
    -- intersection of its height-one branches because double duals are reflexive.
    have hTfae :=
      reflexive_tfae_torsionFree_serreS2_heightOneLocalizationIntersection
        (R := R) (M := Dual R (Dual R N))
    have hThird :
        IsTorsionFree R (Dual R (Dual R N)) ∧
          LinearMap.range (LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R N))) =
            moduleHeightOneLocalizationIntersection R (Dual R (Dual R N)) :=
      (hTfae.out 0 2).mp (doubleDual_isReflexive (R := R) (N := N))
    exact hThird.2
  -- Proof comment: transport the height-one intersection for `N**` back through the inverse
  -- generic evaluation equivalence, one branch at a time.
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rw [moduleHeightOneLocalizationIntersection, Submodule.mem_iInf]
    have hyInter :
        (LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R N))) y ∈
          moduleHeightOneLocalizationIntersection R (Dual R (Dual R N)) := by
      rw [← hDoubleRange]
      exact ⟨y, rfl⟩
    rw [moduleHeightOneLocalizationIntersection, Submodule.mem_iInf] at hyInter
    intro p
    have hzMap :
        (reflexiveHullGenericLocalizationMap (R := R) (N := N) y) ∈
          ((LinearMap.range
              (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
                (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal))) :
            Submodule R (LocalizedModule R⁰ (Dual R (Dual R N)))).map
              (LinearMap.restrictScalars R E.symm.toLinearMap) := by
      rw [Submodule.mem_map]
      refine ⟨(LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R N))) y, hyInter p, ?_⟩
      simp [E, reflexiveHullGenericLocalizationMap]
    rw [height_one_range_transport_reflexiveHull
      (R := R) (N := N) p (hLocal p)] at hzMap
    simpa [E] using hzMap
  · intro hz
    rw [moduleHeightOneLocalizationIntersection, Submodule.mem_iInf] at hz
    have hzInter :
        (LinearMap.restrictScalars R E.toLinearMap z) ∈
          moduleHeightOneLocalizationIntersection R (Dual R (Dual R N)) := by
      rw [moduleHeightOneLocalizationIntersection, Submodule.mem_iInf]
      intro p
      have hpMap :
          z ∈
            ((LinearMap.range
                (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
                  (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal))) :
              Submodule R (LocalizedModule R⁰ (Dual R (Dual R N)))).map
                (LinearMap.restrictScalars R E.symm.toLinearMap) := by
        have hp :
            z ∈ LinearMap.range
              (LocalizedModule.liftOfLE p.1.asIdeal.primeCompl R⁰
                (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal) :
                LocalizedModule.AtPrime p.1.asIdeal N →ₗ[R] LocalizedModule R⁰ N) := hz p
        rw [← height_one_range_transport_reflexiveHull
          (R := R) (N := N) p (hLocal p)] at hp
        exact hp
      rw [Submodule.mem_map] at hpMap
      rcases hpMap with ⟨w, hw, hwz⟩
      have hEz : (LinearMap.restrictScalars R E.toLinearMap) z = w := by
        calc
          (LinearMap.restrictScalars R E.toLinearMap) z =
              (LinearMap.restrictScalars R E.toLinearMap)
                ((LinearMap.restrictScalars R E.symm.toLinearMap) w) := by
                  simpa [hwz]
          _ = w := by
                simp
      exact hEz ▸ hw
    rw [← hDoubleRange] at hzInter
    rw [LinearMap.mem_range] at hzInter
    rcases hzInter with ⟨y, hy⟩
    rw [LinearMap.mem_range]
    refine ⟨y, ?_⟩
    apply E.injective
    change
      (LinearMap.restrictScalars R E.toLinearMap)
          ((reflexiveHullGenericLocalizationMap (R := R) (N := N)) y) =
        (LinearMap.restrictScalars R E.toLinearMap) z
    calc
      (LinearMap.restrictScalars R E.toLinearMap)
          ((reflexiveHullGenericLocalizationMap (R := R) (N := N)) y) =
        (LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R N))) y := by
          simpa [E, LinearMap.comp_apply] using
            LinearMap.congr_fun
              (reflexiveHullGenericLocalizationMap_comp_localized_eval
                (R := R) (N := N))
              y
      _ = (LinearMap.restrictScalars R E.toLinearMap) z := by
            simpa [hy]

/-- Helper for Lemma 15.23.19: localizing the natural map `M → M / M_tors` and then evaluating on
the quotient commutes with the induced double-dual equivalence. -/
private theorem localized_torsionQuotient_eval_naturality :
    let T := Submodule.torsion R M
    let q : M →ₗ[R] M ⧸ T := T.mkQ
    let eDouble := torsionQuotientDoubleDualEquiv (R := R) (M := M)
    (LinearMap.restrictScalars R (LocalizedModule.map R⁰ (eval R (M ⧸ T)))).comp
        (LinearMap.restrictScalars R (LocalizedModule.map R⁰ q)) =
      (LinearMap.restrictScalars R (LocalizedModule.map R⁰ eDouble.toLinearMap)).comp
        (LinearMap.restrictScalars R (LocalizedModule.map R⁰ (eval R M))) := by
  -- Proof comment: compare the two localized maps after precomposing with the numerator embedding
  -- `M → M[R⁰⁻¹]`; on generators both sides are just the localized form of
  -- `Module.Dual.eval_naturality` for the quotient map.
  dsimp [torsionQuotientDoubleDualEquiv, torsionQuotientDualEquiv]
  apply IsLocalizedModule.linearMap_ext (S := R⁰)
    (LocalizedModule.mkLinearMap R⁰ M)
    (LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R (M ⧸ Submodule.torsion R M))))
  ext x
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
  change (LocalizedModule.map R⁰ (eval R (M ⧸ Submodule.torsion R M)))
      ((LocalizedModule.map R⁰ ((Submodule.torsion R M).mkQ)) (LocalizedModule.mk x 1)) =
    (LocalizedModule.map R⁰
      ((((LinearEquiv.ofBijective
        (((Submodule.torsion R M).mkQ : M →ₗ[R] M ⧸ Submodule.torsion R M).dualMap)
        (dualMap_torsion_quotient_bijective (R := R) (M := M))).dualMap :
          Dual R (Dual R M) ≃ₗ[R] Dual R (Dual R (M ⧸ Submodule.torsion R M))) :
        Dual R (Dual R M) →ₗ[R] Dual R (Dual R (M ⧸ Submodule.torsion R M)))))
      ((LocalizedModule.map R⁰ (eval R M)) (LocalizedModule.mk x 1))
  rw [LocalizedModule.map_mk, LocalizedModule.map_mk]
  have hEvalMk :
      (LocalizedModule.map R⁰ (eval R M)) (LocalizedModule.mk x 1) =
        LocalizedModule.mk ((eval R M) x) 1 := by
    rw [LocalizedModule.map_mk]
  rw [hEvalMk]
  have hEDoubleMk :
      (LocalizedModule.map R⁰
        ((((LinearEquiv.ofBijective
          (((Submodule.torsion R M).mkQ : M →ₗ[R] M ⧸ Submodule.torsion R M).dualMap)
          (dualMap_torsion_quotient_bijective (R := R) (M := M))).dualMap :
            Dual R (Dual R M) ≃ₗ[R] Dual R (Dual R (M ⧸ Submodule.torsion R M))) :
          Dual R (Dual R M) →ₗ[R] Dual R (Dual R (M ⧸ Submodule.torsion R M)))))
        (LocalizedModule.mk ((eval R M) x) 1) =
      LocalizedModule.mk
        (((((LinearEquiv.ofBijective
          (((Submodule.torsion R M).mkQ : M →ₗ[R] M ⧸ Submodule.torsion R M).dualMap)
          (dualMap_torsion_quotient_bijective (R := R) (M := M))).dualMap :
            Dual R (Dual R M) ≃ₗ[R] Dual R (Dual R (M ⧸ Submodule.torsion R M))) :
          Dual R (Dual R M) →ₗ[R] Dual R (Dual R (M ⧸ Submodule.torsion R M))))
          ((eval R M) x)) 1 := by
    rw [LocalizedModule.map_mk]
  rw [hEDoubleMk]
  -- The remaining numerator equality is exactly the double-dual naturality square for `mkQ`.
  congr 1

/-- Helper for Lemma 15.23.19: the map from `M**` into the generic localization of
`M / M_tors` factors through the reflexive-hull map of the torsion quotient. -/
private theorem doubleDualToTorsionQuotientGenericLocalization_eq_reflexiveHull_comp :
    doubleDualToTorsionQuotientGenericLocalization (R := R) (M := M) =
      (reflexiveHullGenericLocalizationMap (R := R)
        (N := M ⧸ Submodule.torsion R M)).comp
          (torsionQuotientDoubleDualEquiv (R := R) (M := M)).toLinearMap := by
  -- Proof comment: compare the two maps after postcomposing with the generic localized evaluation
  -- map of the torsion quotient; the localized naturality square and the reflexive-hull
  -- computation reduce both sides to the same numerator embedding.
  dsimp [doubleDualToTorsionQuotientGenericLocalization]
  ext x
  apply (genericLocalization_map_eval_bijective
    (R := R) (M := M ⧸ Submodule.torsion R M)).injective
  let y : LocalizedModule R⁰ M :=
    (LinearEquiv.ofBijective
      (LocalizedModule.map R⁰ (eval R M))
      (genericLocalization_map_eval_bijective (R := R) (M := M))).symm
        ((LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R M))) x)
  have hNat := localized_torsionQuotient_eval_naturality (R := R) (M := M)
  have hNaty := congrArg
      (fun f :
        LocalizedModule R⁰ M →ₗ[R]
          LocalizedModule R⁰ (Dual R (Dual R (M ⧸ Submodule.torsion R M))) => f y) hNat
  have hRefx := congrArg
      (fun f :
        Dual R (Dual R (M ⧸ Submodule.torsion R M)) →ₗ[R]
          LocalizedModule R⁰ (Dual R (Dual R (M ⧸ Submodule.torsion R M))) =>
          f (((torsionQuotientDoubleDualEquiv (R := R) (M := M)).toLinearMap) x))
      (reflexiveHullGenericLocalizationMap_comp_localized_eval
        (R := R) (N := M ⧸ Submodule.torsion R M))
  calc
    (LocalizedModule.map R⁰ (eval R (M ⧸ Submodule.torsion R M)))
        ((LinearEquiv.ofBijective
          (LocalizedModule.map R⁰ ((Submodule.torsion R M).mkQ))
          (genericLocalization_map_torsionQuotient_bijective (R := R) (M := M))) y)
        =
      (LocalizedModule.map R⁰
          (((torsionQuotientDoubleDualEquiv (R := R) (M := M)).toLinearMap)))
          ((LocalizedModule.map R⁰ (eval R M)) y) := by
            simpa [y, LinearMap.comp_apply] using hNaty
    _ =
      (LocalizedModule.map R⁰
          (((torsionQuotientDoubleDualEquiv (R := R) (M := M)).toLinearMap)))
          ((LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R M))) x) := by
            simp [y]
    _ = LocalizedModule.mk
          ((((torsionQuotientDoubleDualEquiv (R := R) (M := M)).toLinearMap) x)) 1 := by
            change
              (LocalizedModule.map R⁰
                (((torsionQuotientDoubleDualEquiv (R := R) (M := M)).toLinearMap)))
                (LocalizedModule.mk x 1) =
              _
            rw [LocalizedModule.map_mk]
    _ =
      (LocalizedModule.map R⁰ (eval R (M ⧸ Submodule.torsion R M)))
          ((reflexiveHullGenericLocalizationMap (R := R)
            (N := M ⧸ Submodule.torsion R M))
            ((((torsionQuotientDoubleDualEquiv (R := R) (M := M)).toLinearMap) x))) := by
            simpa [LinearMap.comp_apply] using hRefx.symm

-- Proof sketch: for every height-one prime `p`, the localized quotient `(M / M_tors)_p` is
-- finite free over the discrete valuation ring `R_p` by Lemma `15.22.11`, hence reflexive. Thus
-- Lemma `15.23.18` applied to `M / M_tors` identifies the intersection of the height-one
-- localizations with its reflexive hull. The torsion quotient and `M` have the same generic
-- localization, and the reflexive hull of `M / M_tors` identifies canonically with `M**`.
/-- Lemma 15.23.19: for a finite module `M` over a Noetherian normal domain `R`, the image of the
reflexive hull `M**` inside the generic localization of the torsion-free quotient `M / M_tors`
coincides with the intersection of the height-one localizations of `M / M_tors`. This is the
canonical Lean form of the textbook equality
`M** = ⋂_{height(𝔭)=1} M_𝔭 / (M_𝔭)_tors = ⋂_{height(𝔭)=1} (M / M_tors)_𝔭`
taken in `M ⊗_R K`. -/
theorem doubleDual_range_eq_heightOneLocalizationIntersection_torsionQuotient :
    doubleDualToTorsionQuotientGenericLocalization.range =
      moduleHeightOneLocalizationIntersection R (M ⧸ Submodule.torsion R M) := by
  let N := M ⧸ Submodule.torsion R M
  -- First factor the source-facing map through the reflexive hull of the torsion quotient.
  rw [doubleDualToTorsionQuotientGenericLocalization_eq_reflexiveHull_comp (R := R) (M := M)]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range
    (torsionQuotientDoubleDualEquiv (R := R) (M := M)))]
  -- Then apply the height-one intersection criterion to the torsion quotient itself.
  refine reflexiveHull_range_eq_heightOneLocalizationIntersection_of_heightOneReflexive
    (R := R) (N := N) ?_
  intro p
  -- Route correction: work with the torsion quotient `N` directly, whose height-one localizations
  -- are finite free over DVRs, instead of transporting local branches from `M**` by hand first.
  simpa [N] using localized_torsion_quotient_reflexive_at_height_one (R := R) (M := M) p

end
