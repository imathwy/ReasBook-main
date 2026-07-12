import Mathlib
import Mathlib.RingTheory.Unramified.LocalStructure
import StacksProject_2024.Chap10.Definition_10_151_1
import StacksProject_2024.Chap10.Proposition_10_152_1
import StacksProject_2024.Chap15.Definition_15_107_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped Unibranch

/-
Domain-style sampling for Lemma 15.108.2:
- primary domain: local commutative algebra at a prime, with localized maps and local étaleness;
- sampled owner declarations:
  `Algebra.UnramifiedAt`,
  `Algebra.unramifiedAt_iff_isUnramifiedAt`,
  `Localization.localRingHom`,
  `IsGeometricallyUnibranch`,
  `Algebra.Etale`;
- best owner abstraction: the source prime should be carried by `q : PrimeSpectrum B`, and the
  base prime is then canonically its contraction `q.asIdeal.under A`; keeping a separate
  parameter `p` together with `[q.asIdeal.LiesOver p]` is redundant public data.

Primitive data vs. derived API:
- primitive data: the prime `q`, geometric unibranchness of `Localization.AtPrime (q ∩ A)`, the
  source-facing unramified-at-prime hypothesis `Algebra.UnramifiedAt A B q`, and injectivity of
  the canonical localized map `A_(q ∩ A) → B_q`;
- derived API: an étale basic-open neighbourhood of `q`.

Source/core/bridge triage:
- `source-facing`: the existence of an étale basic-open neighbourhood of `q`;
- `core/canonical`: `Algebra.UnramifiedAt`, `Localization.localRingHom`, and
  `IsGeometricallyUnibranch`;
- `bridge/view`: the contraction `q.asIdeal.under A`, which replaces the redundant explicit
  parameter `p`.
-/
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A]

/-- Helper for Lemma 15.108.2: localizing at the trivial submonoid does not change the ring. -/
lemma trivial_submonoid_isLocalization_self
    (R : Type*) [CommRing R] :
    IsLocalization (⊥ : Submonoid R) R := by
  -- Proof comment: every element of the trivial submonoid is already a unit, and every element
  -- of `R` is represented by the obvious numerator-over-`1` fraction.
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rcases y with ⟨y, hy⟩
    simp only [Submonoid.mem_bot] at hy
    subst hy
    exact isUnit_one
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

/-- Helper for Lemma 15.108.2: a ring equivalence transports the trivial-submonoid localization
structure to the target ring. -/
lemma trivial_submonoid_isLocalization_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    let _ : Algebra R S := e.toRingHom.toAlgebra
    IsLocalization (⊥ : Submonoid R) S := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  let _ : IsLocalization (⊥ : Submonoid R) R :=
    trivial_submonoid_isLocalization_self R
  let eAlg : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) (fun _ ↦ rfl)
  -- Proof comment: once both rings are identified as `R`-algebras, localization at `⊥`
  -- transports across the algebra equivalence.
  exact IsLocalization.isLocalization_of_algEquiv (⊥ : Submonoid R) eAlg

/-- Helper for Lemma 15.108.2: a reduced unibranch local ring is a domain, because reducedness
identifies it with its reduced quotient and unibranchness makes that quotient a domain. -/
lemma isDomain_of_isReduced_of_isUnibranch
    (R : Type*) [CommRing R] [IsReduced R] [IsUnibranch R] :
    IsDomain R := by
  let eRed : (R)_red ≃+* R :=
    (Ideal.quotEquivOfEq (nilradical_eq_zero R)).trans (RingEquiv.quotientBot R)
  -- Proof comment: `IsUnibranch` already says the reduction is a domain, and reducedness turns
  -- the quotient by the nilradical into the original ring.
  exact eRed.symm.toMulEquiv.isDomain (R)_red

/-- Helper for Lemma 15.108.2: if `f ∉ q`, then the image of `q` in `R_f` is still a prime. -/
lemma isPrime_map_localizationAway_of_not_mem
    {R : Type*} [CommRing R] (q : PrimeSpectrum R) {f : R} (hfq : f ∉ q.asIdeal) :
    (Ideal.map (algebraMap R (Localization.Away f)) q.asIdeal).IsPrime := by
  -- Proof comment: localizing away from an element outside `q` keeps the corresponding prime.
  refine IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ q.2 ?_
  rw [Set.disjoint_iff]
  intro x hx
  rcases hx with ⟨hxf, hxq⟩
  rcases Submonoid.mem_powers_iff.mp hxf with ⟨n, rfl⟩
  exact hfq (q.2.mem_of_pow_mem hxq)

/-- Helper for Lemma 15.108.2: the local unramified hypothesis at `q` first yields a
standard-étale surjection on an already-localized neighborhood `B[f₀⁻¹]`, before the later
away-of-away descent back to one denominator of `B`. -/
lemma exists_localized_standardEtaleSurjectionOn_of_unramifiedAtPrime
    (q : PrimeSpectrum B) (hunram : Algebra.UnramifiedAt A B q) :
    ∃ f₀ : B, f₀ ∉ q.asIdeal ∧
      ∃ u : Localization.Away f₀,
        u ∉ Ideal.map (algebraMap B (Localization.Away f₀)) q.asIdeal ∧
        Algebra.HasStandardEtaleSurjectionOn A u := by
  rcases hunram with ⟨f₀, hf₀q, hUnram⟩
  let qf : PrimeSpectrum (Localization.Away f₀) :=
    ⟨Ideal.map (algebraMap B (Localization.Away f₀)) q.asIdeal,
      isPrime_map_localizationAway_of_not_mem (q := q) hf₀q⟩
  letI : Algebra.Unramified A (Localization.Away f₀) := hUnram
  letI : Algebra.IsUnramifiedAt A qf.asIdeal := by
    -- Proof comment: once the already-localized algebra `B[f₀⁻¹]` is globally unramified over
    -- `A`, the owner predicate at its induced prime `qf` is available by instance search.
    infer_instance
  refine ⟨f₀, hf₀q, ?_⟩
  -- Proof comment: Proposition `10.152.1` is now applied exactly at the localized prime `qf`.
  simpa [qf] using
    (Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn
      (R := A) (A := Localization.Away f₀) qf.asIdeal)

/-- Helper for Lemma 15.108.2: an element of `B[f⁻¹]` that avoids the prime over `q` admits a
fraction presentation whose numerator already avoids `q`. This is the source-faithful first step
in collapsing the iterated basic open `B[f⁻¹][u⁻¹]` back to one denominator of `B`. -/
lemma exists_fraction_rep_not_mem_map_localizationAway
    (q : PrimeSpectrum B) {f : B} (hfq : f ∉ q.asIdeal)
    (u : Localization.Away f)
    (huq : u ∉ Ideal.map (algebraMap B (Localization.Away f)) q.asIdeal) :
    ∃ r : B, ∃ n : ℕ,
      r ∉ q.asIdeal ∧
      IsLocalization.mk' (Localization.Away f) r (away_power f n) = u := by
  rcases IsLocalization.mk'_surjective (Submonoid.powers f) u with ⟨⟨r, s⟩, hs⟩
  rcases s with ⟨_, ⟨n, rfl⟩⟩
  have hrq : r ∉ q.asIdeal := by
    intro hrq
    apply huq
    rw [← hs]
    -- Proof comment: the localization-membership criterion reduces containment of the fraction to
    -- containment of its numerator, because we can witness the criterion with denominator `1`.
    exact
      (IsLocalization.mk'_mem_map_algebraMap_iff
        (Submonoid.powers f) (Localization.Away f) q.asIdeal r (away_power f n)).2
        ⟨1, Submonoid.one_mem _, by simpa using hrq⟩
  -- Proof comment: the chosen surjective fraction presentation now has numerator outside `q`.
  exact ⟨r, n, hrq, hs⟩

-- Proof sketch: use the local unramified hypothesis at `q` to shrink `B` to a standard étale
-- neighborhood of `q`, localize further to isolate the unique branch coming from the
-- geometrically unibranch local ring `A_p`, and then apply Lemma `15.108.1` to the kernel of the
-- resulting surjection to prove that the map is injective after shrinking. The localized target is
-- then étale over `A`.
/-- Lemma 15.108.2: if `q` lies over `p`, `A` is a domain, `A_p` is geometrically unibranch,
`A → B` is unramified at `q`, and the induced local map `A_p → B_q` is injective, then there
exists `g ∈ B \ q` such that `B_g` is étale over `A`. -/
theorem exists_etale_localizationAway_of_geometricallyUnibranch_of_unramifiedAtPrime_of_injective_localRingHom
    (q : PrimeSpectrum B)
    [IsGeometricallyUnibranch (Localization.AtPrime (q.asIdeal.under A))]
    (hunram : Algebra.UnramifiedAt A B q)
    (hinj : Function.Injective
      (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)) :
    ∃ g : B, g ∉ q.asIdeal ∧ Algebra.Etale A (Localization.Away g) := by
  -- Route correction: keep the source proof architecture. First shrink `B` at `q` to a standard
  -- étale surjection by Proposition `10.152.1`, then shrink the standard-étale source to a
  -- domain near the pulled-back prime, apply Lemma `15.108.1` to the kernel of the localized
  -- surjection to force injectivity, and finally transport étaleness back to a single basic open
  -- of the original ring.
  obtain ⟨f₀, hf₀q, u, huqf, hstd⟩ :=
    exists_localized_standardEtaleSurjectionOn_of_unramifiedAtPrime
      (A := A) (B := B) q hunram
  obtain ⟨r, n, hrq, hu_repr⟩ :=
    exists_fraction_rep_not_mem_map_localizationAway
      (B := B) q hf₀q u huqf
  obtain ⟨P, φ, hφsurj⟩ := hstd
  let qf : PrimeSpectrum (Localization.Away f₀) :=
    ⟨Ideal.map (algebraMap B (Localization.Away f₀)) q.asIdeal,
      isPrime_map_localizationAway_of_not_mem (q := q) hf₀q⟩
  let qu : PrimeSpectrum (Localization.Away u) :=
    ⟨Ideal.map (algebraMap (Localization.Away f₀) (Localization.Away u)) qf.asIdeal,
      isPrime_map_localizationAway_of_not_mem (q := qf) huqf⟩
  let q' : PrimeSpectrum P.Ring := PrimeSpectrum.comap φ.toRingHom qu
  let g₀ : B := f₀ * r
  have hg₀q : g₀ ∉ q.asIdeal := by
    intro hg₀q
    exact (q.2.mem_or_mem hg₀q).elim hf₀q hrq
  -- Proof comment: this reaches the exact source-faithful frontier. `q'` is now the pulled-back
  -- prime in the standard-étale source after the two localizations prescribed by the owner API.
  -- The fraction presentation `u = r / f₀^n` with `r ∉ q` also isolates the intended single
  -- denominator `g₀ = f₀ * r` for the eventual away-of-away collapse.
  -- TODO: compare `Localization.Away u` with `Localization.Away g₀` by first replacing `u` by
  -- the numerator `r` up to a unit using `hu_repr`, then use the canonical `awayToAwayRight/Left`
  -- maps to descend from `B[f₀⁻¹][u⁻¹]` to `B[g₀⁻¹]`. After that, prove the source-faithful
  -- domain shrink around `q'`: show `Localization.AtPrime q'.asIdeal` is a domain from geometric
  -- unibranchness, prove `(minimalPrimes P.Ring).Finite`, apply Lemma `10.31.9` to obtain a
  -- domain basic open of `P.Ring`, and finally use Lemma `15.108.1` on the localized kernel to
  -- contradict `hinj`.
  sorry

end
