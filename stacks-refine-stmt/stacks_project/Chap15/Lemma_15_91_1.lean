import stacks_project.Chap15.Lemma_15_89_9
import stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/-
Domain-style sampling:
* primary domain: principal-power quotient comparison maps in commutative algebra, specialized
  later to principal adic completion.
* sampled owner declarations:
  `principalIdeal`,
  `principalPowerIdealQuotientMap`,
  `principalPowerIdeal`,
  `AdicCompletion`,
  `adicCompletion_quotientMap_bijective`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`.
* owner abstraction: the source-facing quotient map is the chapter owner
  `principalPowerIdealQuotientMap`, while its completion comparison is supplied canonically by
  `adicCompletion_quotientMap_bijective` after specializing to `AdicCompletion (principalIdeal f) R`.
* primitive data: the ring `R`, the principal ideal `principalIdeal f`, and the exponent `n : ℕ`.
* derived API: bijectivity of the induced quotient maps, and the completion specialization below.
* triage: `core/canonical` owner = `adicCompletion_quotientMap_bijective` for the ideal powers
  `((Ideal.map _ (principalIdeal f))^n)` on the completion side; the Beauville-Laszlo completion
  statement below is the positive-integer specialization to the principal ideal `(f)`.
-/

section

variable {R : Type u} [CommRing R] (f : R)

-- Proof sketch: this is the canonical adic-completion quotient-map bijectivity theorem applied to
-- the finitely generated principal ideal `(f)`, then specialized through the chapter owner
-- `AdicCompletion (principalIdeal f) R`.
/-- Lemma 15.91.1: for every positive integer `n`, the canonical map
`R / (f)^n → R^∧ / (f)^n R^∧` for the `(f)`-adic completion is bijective. This is the thin
completion-specialized bridge to the canonical `Ideal.quotientMap` owner used by the later
base-change API. -/
theorem principalAdicCompletion_quotientMap_bijective (n : ℕ+) :
    Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R (principalAdicCompletion f)) f n) := by
  let σ : R →+* principalAdicCompletion f := algebraMap R (principalAdicCompletion f)
  let qraw :
      R ⧸ principalPowerIdeal f n →+* principalAdicCompletion f ⧸
        Ideal.map σ (principalIdeal f ^ (n : ℕ)) :=
    Ideal.quotientMap (Ideal.map σ (principalIdeal f ^ (n : ℕ))) σ Ideal.le_comap_map
  have hraw : Function.Bijective qraw := by
    simpa [qraw, σ, principalPowerIdeal] using
      adicCompletion_quotientMap_bijective
        (principalIdeal f)
        (Submodule.fg_span_singleton f)
        n
  have hmap :
      Ideal.map σ (principalIdeal f ^ (n : ℕ)) =
        principalPowerIdeal (σ f) n := by
    simp [σ, principalPowerIdeal, principalIdeal, Ideal.map_pow, Ideal.map_span,
      Set.image_singleton]
  have hcomp :
      principalPowerIdealImageQuotientMap σ f n =
        (Ideal.quotEquivOfEq hmap).toRingHom.comp qraw := by
    apply Ideal.Quotient.ringHom_ext
    exact RingHom.ext fun x ↦ by
      simpa [RingHom.comp_apply, qraw, σ, principalPowerIdealImageQuotientMap,
        principalPowerIdealQuotientMap, Ideal.quotientMap_mk] using
        (Ideal.quotEquivOfEq_mk hmap (σ x)).symm
  rw [hcomp]
  exact (RingEquiv.bijective <| Ideal.quotEquivOfEq hmap).comp hraw

end
