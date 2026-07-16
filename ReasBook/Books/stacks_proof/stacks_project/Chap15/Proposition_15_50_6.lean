import stacks_proof.stacks_project.Chap10.Definition_10_160_1
import stacks_proof.stacks_project.Chap10.Lemma_10_17_7
import stacks_proof.stacks_project.Chap10.Lemma_10_97_3
import stacks_proof.stacks_project.Chap10.Lemma_10_160_2
import stacks_proof.stacks_project.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Algebra

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/-- Helper for Proposition 15.50.6: quotienting by the lower prime produces the corresponding
prime upstairs in the quotient spectrum. -/
private noncomputable def quotientPrimeOfLE
    (p q : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) :
    PrimeSpectrum (R ⧸ q.asIdeal) :=
  (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus q.asIdeal).symm
    ⟨p, (PrimeSpectrum.mem_zeroLocus p (q.asIdeal : Set R)).2 hqp⟩

/-- Helper for Proposition 15.50.6: the quotient prime chosen from `p` contracts back to `p`
along the quotient map. -/
private theorem comap_quotientPrimeOfLE
    (p q : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) :
    PrimeSpectrum.comap (Ideal.Quotient.mk q.asIdeal)
      (quotientPrimeOfLE (R := R) p q hqp) = p := by
  -- This is exactly the defining property of the inverse quotient-spectrum homeomorphism.
  have hp'' :
      ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus q.asIdeal)
        (quotientPrimeOfLE (R := R) p q hqp)).1 = p := by
    exact congrArg Subtype.val <|
      (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus q.asIdeal).apply_symm_apply
        ⟨p, (PrimeSpectrum.mem_zeroLocus p (q.asIdeal : Set R)).2 hqp⟩
  have hp' :
      PrimeSpectrum.comap (Ideal.Quotient.mk q.asIdeal)
        (quotientPrimeOfLE (R := R) p q hqp) = p := by
    simpa [Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply] using hp''
  exact hp'

/-- Helper for Proposition 15.50.6: the quotient by a prime of a complete local ring is again a
complete local ring. -/
private theorem quotientByPrime_isCompleteLocalRing (q : PrimeSpectrum R) :
    IsCompleteLocalRing (R ⧸ q.asIdeal) := by
  -- Completion and locality descend along proper quotients.
  exact quotient_isCompleteLocalRing q.asIdeal q.2.ne_top

/-- Helper for Proposition 15.50.6: the prime-pair formal fiber on `R` should be compared with the
zero-prime formal fiber of the quotient domain `R / q`. -/
private theorem quotientByPrime_formalFiber_isGeometricallyRegular_iff
    (p q : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) :
    let B := R ⧸ q.asIdeal
    let pbar : PrimeSpectrum B := quotientPrimeOfLE (R := R) p q hqp
    IsGeometricallyRegular (⊥ : Ideal B).ResidueField
      ((⊥ : Ideal B).Fiber (CompletedLocalizationAtPrime B pbar)) ↔
        IsGeometricallyRegular q.asIdeal.ResidueField
          (q.asIdeal.Fiber (CompletedLocalizationAtPrime R p)) := by
  -- TODO: compare the two fiber rings through the quotient-spectrum homeomorphism and the
  -- canonical identification of residue fields for the prime `q` and the zero prime of `R / q`.
  sorry

/-- Helper for Proposition 15.50.6: after quotienting to the domain case, the remaining source
proof is the generic formal fiber statement over the zero prime. -/
private theorem completeLocalDomain_zeroPrime_formalFiber_isGeometricallyRegular
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] [IsDomain A]
    (p : PrimeSpectrum A) :
    IsGeometricallyRegular (⊥ : Ideal A).ResidueField
      ((⊥ : Ideal A).Fiber (CompletedLocalizationAtPrime A p)) := by
  -- TODO: follow the source proof in the domain case: choose a finite regular complete local
  -- subring by Cohen structure, transfer along the finite quasi-finite inclusion, and close the
  -- regular complete local case via the characteristic-zero argument and Lemma `15.50.5`.
  sorry

/-- Helper for Proposition 15.50.6: the fiber of the local completion map over a prime of `R_p`
is the same formal fiber as for its contracted prime in `R`. -/
private theorem formalFiber_over_localizationPrime_isGeometricallyRegular_iff_contractedPrime
    (p : PrimeSpectrum R) (q' : PrimeSpectrum (Localization.AtPrime p.asIdeal)) :
    let q : PrimeSpectrum R :=
      PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q'
    IsGeometricallyRegular q'.asIdeal.ResidueField
      (q'.asIdeal.Fiber (CompletedLocalizationAtPrime R p)) ↔
      IsGeometricallyRegular q.asIdeal.ResidueField
        (q.asIdeal.Fiber (CompletedLocalizationAtPrime R p)) := by
  -- TODO: identify `κ(q')` with `κ(q)` for the prime of `R_p` lying over `q`, then rewrite both
  -- tensor-defined fibers by the same `κ(q)`-algebra using the localization/base-change
  -- cancellation comparison.
  sorry

/-- Helper for Proposition 15.50.6: the prime-pair criterion reduces geometric regularity to the
complete-local-domain zero-prime case after quotienting by the lower prime. -/
private theorem primePair_formalFiber_isGeometricallyRegular
    (p q : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) :
    IsGeometricallyRegular q.asIdeal.ResidueField
      (q.asIdeal.Fiber (CompletedLocalizationAtPrime R p)) := by
  let B := R ⧸ q.asIdeal
  letI : IsCompleteLocalRing B := quotientByPrime_isCompleteLocalRing (R := R) q
  letI : IsDomain B := Ideal.Quotient.isDomain q.asIdeal
  let pbar : PrimeSpectrum B := quotientPrimeOfLE (R := R) p q hqp
  -- First solve the zero-prime formal fiber for the quotient domain.
  have hdomain :
      IsGeometricallyRegular (⊥ : Ideal B).ResidueField
        ((⊥ : Ideal B).Fiber (CompletedLocalizationAtPrime B pbar)) :=
    completeLocalDomain_zeroPrime_formalFiber_isGeometricallyRegular (A := B) pbar
  -- Then transport that result back to the original prime pair `(q ≤ p)`.
  exact
    (quotientByPrime_formalFiber_isGeometricallyRegular_iff
      (R := R) p q hqp).mp hdomain

/-- Helper for Proposition 15.50.6: the remaining owner-level goal is regularity of the
completion map at each localization. -/
private theorem regular_localization_completion_of_completeLocalRing
    (p : PrimeSpectrum R) :
    (algebraMap (Localization.AtPrime p.asIdeal) (CompletedLocalizationAtPrime R p)).IsRegularRingMap := by
  -- Proof comment: build the regularity structure directly. Flatness is the completion-map
  -- theorem, and geometric regularity of each fiber is transported from the contracted prime in
  -- `R`, where the prime-pair formal-fiber statement has already been reduced to the domain case.
  refine
    { toFlat := RingHom.flat_algebraMap_iff.mpr <|
        (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat
          (Localization.AtPrime p.asIdeal)).flat
      isGeometricallyRegular_fiber := ?_ }
  intro q'
  let q : PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q'
  have hqp : q.asIdeal ≤ p.asIdeal := by
    -- Proof comment: every prime of `R_p` contracts to a prime of `R` contained in `p`.
    change Ideal.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q'.asIdeal ≤ p.asIdeal
    intro x hx
    by_contra hxp
    exact q'.2.ne_top <|
      Ideal.eq_top_of_isUnit_mem _ hx <|
        IsLocalization.map_units (Localization.AtPrime p.asIdeal)
          (⟨x, hxp⟩ : p.asIdeal.primeCompl)
  have hgeom :
      IsGeometricallyRegular q.asIdeal.ResidueField
        (q.asIdeal.Fiber (CompletedLocalizationAtPrime R p)) :=
    primePair_formalFiber_isGeometricallyRegular (R := R) p q hqp
  -- Proof comment: the only remaining transport is from the contracted prime `q` back to the
  -- original prime `q'` of `R_p`.
  exact
    (formalFiber_over_localizationPrime_isGeometricallyRegular_iff_contractedPrime
      (R := R) p q').2 hgeom

/- Domain triage:
- primary domain: `G`-rings, completed localizations, and geometric regularity of formal fibers in
  commutative algebra;
- sampled owner declarations:
  `CompletedLocalizationAtPrime`,
  `IsGRing`,
  `isGRing_iff_forall_regular_localization_completion`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`;
- best owner abstraction: the chapter owner predicate `IsGRing`, with the completed localization
  owner `R̂_[p]` and the prime-pair criterion from Lemma `15.50.2` only as supporting bridge API;
- primitive data: the ring `R` together with the Noetherian and complete-local hypotheses;
- derived API: the formal-fiber regularity statements used to prove the owner instance below.

Layering:
- this proposition is `source-facing`;
- `IsGRing` is the `core/canonical` owner;
- the prime-pair geometric-regularity criterion is the `bridge/view`.
-/
/-- Proposition 15.50.6: a Noetherian complete local ring is a `G`-ring. -/
-- Proof sketch: by Lemma `15.50.2`, it is enough to check geometric regularity of the formal
-- fibres over minimal primes. Quotient by a minimal prime to reduce to the domain case, choose a
-- regular complete local subring from Cohen structure, descend the `G`-ring property along the
-- resulting finite quasi-finite map using Lemma `15.50.3`, and then handle the regular complete
-- local source by the characteristic-zero regularity argument together with the positive
-- characteristic power-series case from Lemma `15.50.5`.
instance : IsGRing R := by
  -- Apply the owner-level criterion from the definition of `G`-rings.
  refine isGRing_iff_forall_regular_localization_completion.2 ?_
  intro p
  -- Route correction: the source proof is already reduced above to the quotient/domain formal-fiber
  -- problem, but the public owner here asks for regularity of the completion map.
  exact regular_localization_completion_of_completeLocalRing (R := R) p

end
