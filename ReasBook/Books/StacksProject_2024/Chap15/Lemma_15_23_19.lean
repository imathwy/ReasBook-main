import Mathlib
import stacks_project.Chap15.Lemma_15_23_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped nonZeroDivisors
open Module
open Module.Dual (eval)
open LocalizedModule (map mkLinearMap)

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

/-- The localization of the evaluation map `M → M**` at the generic point is bijective. -/
-- Proof sketch: Lemma `15.23.2` shows that the kernel and cokernel of `M → M**` are torsion.
-- Localizing at the non-zero-divisors of the domain `R` kills torsion, so the induced map on the
-- generic localization is both injective and surjective.
private theorem genericLocalization_map_eval_bijective :
    Function.Bijective (map R⁰ (eval R M)) := sorry

/-- The generic localization of `M` agrees with the generic localization of `M / M_tors`. -/
-- Proof sketch: the quotient map `M → M / M_tors` is surjective, and its kernel is the torsion
-- submodule `Submodule.torsion R M`. After localizing at `R⁰`, that kernel vanishes, so the
-- induced map on generic localizations is bijective.
private theorem genericLocalization_map_torsionQuotient_bijective :
    Function.Bijective (map R⁰ (Submodule.torsion R M).mkQ) := sorry

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
      moduleHeightOneLocalizationIntersection R (M ⧸ Submodule.torsion R M) := sorry

end
