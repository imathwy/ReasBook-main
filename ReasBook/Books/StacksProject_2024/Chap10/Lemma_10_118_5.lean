import StacksProject_2024.Chap10.«10_118_3_2»
import StacksProject_2024.Chap10.Lemma_10_17_6

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped PrimeSpectrum

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/- Domain triage:
* primary domain: generic-flatness loci on prime spectra under localization away from one element;
* source-facing owner: `goodLocus R S M` from `10_118_3_2`;
* core/canonical bridge: `primeSpectrum_localizationAway_homeomorph_D f` and its pointwise
  description via `PrimeSpectrum.comap`;
* bridge/view target of this file: transport `goodLocus` across the canonical identification
  `Spec(R_f) ≃ D(f)`, with the restriction to `D(f)` expressed canonically as a subtype preimage
  rather than a separate wrapper set. -/

/-- Helper for Lemma 10.118.5: membership in `goodLocus` is equivalent to the existence of a
single witness element avoiding the given prime. -/
lemma mem_goodLocus_iff (p : PrimeSpectrum R) :
    p ∈ goodLocus R S M ↔ ∃ g : R, LocalizationCondition R S M g ∧ g ∉ p.asIdeal := by
  -- Unfold the defining union and rewrite basic-open membership into non-membership in the prime.
  rw [goodLocus_eq_iUnion]
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨g, hg⟩
    exact ⟨g.1, g.2, (PrimeSpectrum.mem_basicOpen g.1 p).mp hg⟩
  · rintro ⟨g, hgcond, hg⟩
    refine Set.mem_iUnion.mpr ?_
    exact ⟨⟨g, hgcond⟩, (PrimeSpectrum.mem_basicOpen g p).mpr hg⟩

/-- Helper for Lemma 10.118.5: the canonical map `R_f → R_(fg)` is compatible with the original
`R`-algebra structures, so `R_(fg)` sits in a scalar tower over `R_f`. -/
lemma away_mul_isScalarTower (f g : R) :
    letI : Algebra (Localization.Away f) (Localization.Away (f * g)) :=
      (IsLocalization.Away.awayToAwayRight
        (S := Localization.Away f) (P := Localization.Away (f * g)) f g).toAlgebra
    IsScalarTower R (Localization.Away f) (Localization.Away (f * g)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (f * g)) :=
    (IsLocalization.Away.awayToAwayRight
      (S := Localization.Away f) (P := Localization.Away (f * g)) f g).toAlgebra
  -- The comparison map `R_f → R_(fg)` still agrees with the original structure map from `R`.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  symm
  simpa using
    (IsLocalization.Away.awayToAwayRight_eq
      (S := Localization.Away f) (P := Localization.Away (f * g)) (x := f) (y := g) x)

/-- Helper for Lemma 10.118.5: inside `R_f`, the elements `(fg) / 1` and `g / 1` are associated
because `f / 1` is a unit. -/
lemma away_mul_associated_right (f g : R) :
    Associated (algebraMap R (Localization.Away f) (f * g))
      (algebraMap R (Localization.Away f) g) := by
  -- After rewriting `(fg) / 1` as `(f / 1) * (g / 1)`, cancel the unit `f / 1`.
  rw [map_mul]
  simpa [mul_comm] using
    (associated_mul_unit_left
      (algebraMap R (Localization.Away f) g)
      (algebraMap R (Localization.Away f) f)
      (IsLocalization.Away.algebraMap_isUnit (R := R) (S := Localization.Away f) (x := f)))

/-- Helper for Lemma 10.118.5: the iterated localization `(R_f)_(g / 1)` carries the composed
`R`-algebra structure, and this agrees with the evident scalar tower through `R_f`. -/
lemma away_map_isScalarTower (f g : R) :
    letI : Algebra R (Localization.Away (algebraMap R (Localization.Away f) g)) :=
      ((algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R (Localization.Away f) g))).comp
        (algebraMap R (Localization.Away f))).toAlgebra
    IsScalarTower R (Localization.Away f)
      (Localization.Away (algebraMap R (Localization.Away f) g)) := by
  -- TODO: pin down the composed `R`-algebra structure on `(R_f)_(g / 1)` so that the resulting
  -- `SMul` fields agree definitionally with the scalar tower expected by `IsLocalization`.
  sorry

/-- Helper for Lemma 10.118.5: both `R_(fg)` and `(R_f)_(g / 1)` localize `R` away from `fg`, so
they are canonically isomorphic as `R`-algebras. -/
noncomputable def away_mul_base_algEquiv (f g : R) :
    Localization.Away (f * g) ≃ₐ[R]
      Localization.Away (algebraMap R (Localization.Away f) g) := by
  -- TODO: after `away_map_isScalarTower` is available with the canonical `SMul` data, register
  -- `(R_f)_(g / 1)` as an away-localization of `R` at `fg` via `Away.mul_of_associated`, and then
  -- use `IsLocalization.algEquiv` to compare it with `R_(fg)`.
  sorry

/-- Helper for Lemma 10.118.5: a witness for `U(R → S, M)` remains a witness after localizing the
whole setup away from `f`. -/
lemma localizationCondition_map_away (f g : R) (hg : LocalizationCondition R S M g) :
    LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g) := by
  -- Route correction: the remaining gap is no longer the base-ring tower.
  -- TODO: first build the explicit comparison
  -- `Localization.Away (f * g) ≃ₐ[Localization.Away f] Localization.Away (algebraMap R (Localization.Away f) g)`
  -- using `away_mul_isScalarTower` and `away_mul_associated_right`; then transport the codomain
  -- algebra and localized module across the corresponding `AlgEquiv` and `LinearEquiv`.
  sorry

/-- Helper for Lemma 10.118.5: a witness in the localized pair can be cleared to a witness in the
original pair by multiplying by the numerator returned by `IsLocalization.Away.sec`. -/
lemma localizationCondition_of_localized_witness (f : R) (u : Localization.Away f)
    (hu :
      LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) u) :
    LocalizationCondition R S M (f * (IsLocalization.Away.sec f u).1) := by
  -- Route correction: the denominator-clearing step should reuse the same comparison package as
  -- `localizationCondition_map_away`, with `g` replaced by `(IsLocalization.Away.sec f u).1` and
  -- the localized basic open replaced by `u`.
  -- TODO: use `away_of_sec_fst` to identify `Localization.Away u` with
  -- `Localization.Away (f * (IsLocalization.Away.sec f u).1)`, then transport the codomain ring
  -- and localized module through the induced `AlgEquiv` and `LinearEquiv`.
  sorry

/-- Lemma 10.118.5: pulling back `U(R → S, M)` along `Spec(R_f) → Spec(R)` gives the good locus of
the localized pair `(R_f → S_f, M_f)`. Equivalently, under the identification
`Spec(R_f) ≃ D(f)`, this is the equality `U(R_f → S_f, M_f) = D(f) ∩ U(R → S, M)`. -/
-- Proof sketch: membership in the localized good locus means there is `g ∈ R_f` such that
-- `(10.118.3.1)` holds after localizing once more at `g`. Write `g = a / f^n`, replace it by an
-- element of `R` giving the same doubly localized rings and modules, and use that the image of
-- `Spec(R_f) → Spec(R)` is `D(f)`.
theorem goodLocus_localizationAway_eq_preimage (f : R) :
    goodLocus (Localization.Away f) (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) =
    PrimeSpectrum.comap (algebraMap R (Localization.Away f)) ⁻¹'
      goodLocus R S M := by
  ext p
  -- Rewrite both sides as existence of a single witness avoiding the relevant prime.
  rw [mem_goodLocus_iff, Set.mem_preimage, mem_goodLocus_iff]
  constructor
  · rintro ⟨u, hucond, hu⟩
    let a : R := (IsLocalization.Away.sec f u).1
    refine ⟨f * a, localizationCondition_of_localized_witness (R := R) (S := S) (M := M) f u hucond, ?_⟩
    -- Clearing the denominator multiplies by `f`, and `f` is already invertible in `R_f`.
    intro hfa_mem
    have hf_not_mem : algebraMap R (Localization.Away f) f ∉ p.asIdeal := by
      intro hf_mem
      exact p.2.ne_top <| Ideal.eq_top_of_isUnit_mem _ hf_mem
        (IsLocalization.Away.algebraMap_isUnit (R := R) (S := Localization.Away f) (x := f))
    have ha_mem : algebraMap R (Localization.Away f) a ∈ p.asIdeal := by
      have hprod_mem : algebraMap R (Localization.Away f) (f * a) ∈ p.asIdeal := by
        simpa using hfa_mem
      have hmul_mem :
          algebraMap R (Localization.Away f) f * algebraMap R (Localization.Away f) a ∈ p.asIdeal := by
        simpa [map_mul] using hprod_mem
      exact (p.2.mem_or_mem hmul_mem).resolve_left hf_not_mem
    have hu_mem : u ∈ p.asIdeal := by
      exact (Ideal.mem_iff_of_associated
        (IsLocalization.Away.associated_sec_fst (R := R) (S := Localization.Away f) (x := f) u)).mp ha_mem
    exact hu hu_mem
  · rintro ⟨g, hgcond, hg⟩
    refine ⟨algebraMap R (Localization.Away f) g,
      localizationCondition_map_away (R := R) (S := S) (M := M) f g hgcond, ?_⟩
    simpa using hg

/-- Under the canonical homeomorphism `Spec(R_f) ≃ D(f)`, the localized good locus is the
restriction of `U(R → S, M)` to the basic open `D(f)`. -/
-- Proof sketch: rewrite `goodLocus_localizationAway_eq_preimage` through
-- `primeSpectrum_localizationAway_homeomorph_D f`, using the explicit description of that
-- homeomorphism on points. Express the restriction to `D(f)` as the preimage of `goodLocus R S M`
-- under the subtype coercion `D(f) → Spec(R)`.
theorem goodLocus_localizationAway_eq_D_restrict (f : R) :
    Set.image (primeSpectrum_localizationAway_homeomorph_D f)
      (goodLocus (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M)) =
    ((↑) : D(f) → PrimeSpectrum R) ⁻¹' goodLocus R S M := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    -- Transport membership across theorem 1, then read the homeomorphism pointwise.
    have hp' : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) p ∈ goodLocus R S M := by
      simpa [goodLocus_localizationAway_eq_preimage (R := R) (S := S) (M := M) (f := f)] using hp
    simpa [primeSpectrum_localizationAway_homeomorph_D_apply] using hp'
  · intro hx
    let p : PrimeSpectrum (Localization.Away f) := (primeSpectrum_localizationAway_homeomorph_D f).symm x
    -- Pull the point back along the homeomorphism and apply theorem 1 in the reverse direction.
    have hp_eq : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) p = x.1 := by
      change (primeSpectrum_localizationAway_homeomorph_D f p).1 = x.1
      simpa [p] using congrArg Subtype.val
        ((primeSpectrum_localizationAway_homeomorph_D f).apply_symm_apply x)
    have hp' : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) p ∈ goodLocus R S M := by
      simpa [hp_eq] using hx
    have hp : p ∈ goodLocus (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) := by
      simpa [goodLocus_localizationAway_eq_preimage (R := R) (S := S) (M := M) (f := f)] using hp'
    refine ⟨p, hp, ?_⟩
    simpa [p] using (primeSpectrum_localizationAway_homeomorph_D f).apply_symm_apply x

end GenericFlatness

end
