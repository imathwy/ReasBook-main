import Mathlib
import stacks_project.Chap10.Lemma_10_161_3
import stacks_project.Chap10.Lemma_10_161_4
import stacks_project.Chap10.Lemma_10_161_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsDomain R]

/- 
Domain triage:
* primary domain: commutative algebra of the `N-1` property, localization of normalization, and
  descent from maximal-local data;
* sampled owner/bridge declarations:
  - `IsN1Ring`, the source-facing owner from `Definition_10_161_1`;
  - `isN1Ring_of_isLocalization`, the localization-stability bridge from `Lemma_10_161_3`;
  - `IsLocalization.integralClosure`, the canonical localization bridge for normalization;
  - `RingHom.finite_ofLocalizationSpan`, the canonical finite-descent owner for integral maps.
* best owner abstraction: the main owner throughout is `IsN1Ring R`; the normal-away statement in
  clause `(1)` remains source-facing via `IsNormalRing (Localization.Away f)`, while clause `(3)`
  is the reverse implication combining that source-facing witness with maximal-local `N-1` data.

Layer triage:
* `source-facing`: the three numbered clauses of Lemma `10.161.15`;
* `core/canonical`: `IsN1Ring`, `IsNormalRing`, `Localization.Away`, `Localization.AtPrime`, and
  the normalization map `R → integralClosure R (FractionRing R)`;
* `bridge/view`: specialization of localization stability to maximal ideals and identification of
  localized normalization via `IsLocalization.integralClosure`.
-/

-- Proof sketch: identify the integral closure of `R` in `FractionRing R` as a finite `R`-module,
-- choose finitely many generators, and clear denominators to find a nonzero `f` such that the
-- localization away from `f` identifies with the integral closure and is therefore normal.
/-- Lemma 10.161.15 (1): if a domain `R` is `N-1`, then there exists a nonzero
element `f : R` such that `R_f` is normal. -/
theorem exists_isNormalRing_localizationAway_of_isN1Ring
    (hR : IsN1Ring R) :
    ∃ f : R, f ≠ 0 ∧ IsNormalRing (Localization.Away f) := sorry

-- Proof sketch: apply localization stability of `N-1` from `Lemma 10.161.3` to the localization
-- of `R` at the complement of each maximal ideal.
/-- Lemma 10.161.15 (2): if a domain `R` is `N-1`, then every localization `R_𝔪` at a
maximal ideal is `N-1`. -/
theorem isN1Ring_localizationAtMaximal_of_isN1Ring
    (hR : IsN1Ring R) (m : MaximalSpectrum R) :
    IsN1Ring (Localization.AtPrime m.asIdeal) := by
  letI : IsN1Ring R := hR
  exact isN1Ring_of_isLocalization m.asIdeal.primeCompl

section

variable [IsNoetherianRing R]

-- Proof sketch: let `M = integralClosure R (FractionRing R)`. The hypothesis `hnormalAway`
-- supplies the source-facing principal-open normality witness needed to control the non-normal
-- locus of finite intermediate rings. For each maximal ideal `m`, the hypothesis `hlocal m` and
-- localization compatibility of integral closure identify `Mₘ` with the finite normalization of
-- `Localization.AtPrime m.asIdeal`. These local finite normalizations glue, via the quasi-compact
-- closed-set argument of the Stacks proof, to a global finite normalization map.
/-- Lemma 10.161.15 (3): if there exists a nonzero `f : R` such that `R_f` is normal, and every
localization `R_𝔪` at a maximal ideal is `N-1`, then `R` is `N-1`. -/
theorem isN1Ring_of_exists_isNormalRing_localizationAway_of_forall_maximal_isN1Ring_localizationAtMaximal
    (hnormalAway : ∃ f : R, f ≠ 0 ∧ IsNormalRing (Localization.Away f))
    (hlocal : ∀ m : MaximalSpectrum R, IsN1Ring (Localization.AtPrime m.asIdeal)) :
    IsN1Ring R := sorry

end

end
