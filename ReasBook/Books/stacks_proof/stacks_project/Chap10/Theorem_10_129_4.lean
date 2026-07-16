import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_39_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Module

section

open TensorProduct

variable (R : Type u) (S : Type v) (M : Type w)
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/- Domain-style sampling:
- primary domain: flatness loci of finitely presented modules over a base ring on `Spec(S)`;
- sampled owner declarations in the surrounding chapter/project:
  `GenericFlatness.goodLocus`,
  `relativeDimensionAtLELocus`,
  `Ideal.IsFlatOverBaseLocus`,
  `Module.flatOverBaseLocus`;
- best owner abstraction here: the point-set owner
  `Module.flatOverBaseLocus R S M : Set (PrimeSpectrum S)`;
- primitive data: the base ring `R`, the target algebra `S`, and the `S`-module `M` viewed over
  `R`;
- derived API: the membership lemma and the openness theorem under finite-presentation
  hypotheses.

Source/core/bridge triage:
- `source-facing`: the Stacks-theorem openness statement for the flatness locus on `Spec(S)`;
- `core/canonical`: `Module.flatOverBaseLocus`;
- `bridge/view`: downstream closed-subset reformulations such as `Ideal.IsFlatOverBaseLocus`.
-/

/-- The locus in `Spec(S)` where the localized `S`-module `M_q` is flat over the base ring `R`. -/
def flatOverBaseLocus : Set (PrimeSpectrum S) :=
  { q | Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) }

/-- Membership in `flatOverBaseLocus R S M` means that `M_q` is flat over `R`. -/
@[simp] theorem mem_flatOverBaseLocus (q : PrimeSpectrum S) :
    q ∈ flatOverBaseLocus R S M ↔
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) :=
  Iff.rfl

variable [Algebra.FinitePresentation R S] [Module.FinitePresentation S M]

omit [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Theorem 10 129 4: the locus where the stalk is flat over the localized
source ring `R_(q ∩ R)`. -/
private def localizedBaseFlatLocus : Set (PrimeSpectrum S) :=
  { q | Module.Flat (Localization.AtPrime (q.asIdeal.under R))
      (LocalizedModule.AtPrime q.asIdeal M) }

omit [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Theorem 10 129 4: flatness of the stalk over `R_(q ∩ R)` is equivalent
to flatness over the original base ring `R`. -/
private theorem flatAtPrime_over_under_iff_flatOverBase
    {q : PrimeSpectrum S} :
    Module.Flat (Localization.AtPrime (q.asIdeal.under R))
        (LocalizedModule.AtPrime q.asIdeal M) ↔
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := by
  -- Proof comment: this is the standard localization criterion for flatness, specialized to
  -- the source prime lying under `q`.
  exact Module.flat_iff_of_isLocalization
    (Localization.AtPrime (q.asIdeal.under R)) (q.asIdeal.under R).primeCompl
    (M := LocalizedModule.AtPrime q.asIdeal M)

omit [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Theorem 10 129 4: the localized-base flat locus is the same set as
`flatOverBaseLocus R S M`. -/
private theorem flatOverBaseLocus_eq_localizedBaseFlatLocus :
    flatOverBaseLocus R S M = localizedBaseFlatLocus R S M := by
  -- Proof comment: compare the two pointwise flatness predicates by localizing the source ring at
  -- the contracted prime.
  ext q
  exact (flatAtPrime_over_under_iff_flatOverBase (R := R) (S := S) (M := M) (q := q)).symm

omit [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Theorem 10 129 4: `R`-flatness of the stalk `M_q` gives flatness over
the localized source ring `R_(q ∩ R)`. -/
private theorem flatAtPrime_over_under_of_flatOverBase
    {q : PrimeSpectrum S}
    (hflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)) :
    Module.Flat (Localization.AtPrime (q.asIdeal.under R))
      (LocalizedModule.AtPrime q.asIdeal M) := by
  -- Proof comment: apply the biconditional bridge in the direction needed by the spreading
  -- adapter below.
  exact (flatAtPrime_over_under_iff_flatOverBase (R := R) (S := S) (M := M) (q := q)).mpr hflat

omit [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Theorem 10 129 4: a principal-open spreading result stated after
localizing the base at `q.asIdeal.under R` implies the corresponding statement from
`R`-flatness of the stalk. -/
private theorem exists_flat_localizedAway_of_flatAtPrime_of_localizedBaseSpread
    {q : PrimeSpectrum S}
    (hspread :
      Module.Flat (Localization.AtPrime (q.asIdeal.under R))
        (LocalizedModule.AtPrime q.asIdeal M) →
        ∃ f : S, f ∉ q.asIdeal ∧ Module.Flat R (LocalizedModule (.powers f) M))
    (hflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)) :
    ∃ f : S, f ∉ q.asIdeal ∧ Module.Flat R (LocalizedModule (.powers f) M) := by
  -- Proof comment: first convert the target's `R`-flat stalk hypothesis to flatness over the
  -- localized source ring, then apply the source-level spreading theorem supplied as input.
  exact hspread (flatAtPrime_over_under_of_flatOverBase (R := R) (S := S) (M := M) hflat)

omit [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Theorem 10 129 4: a pointwise localized-base spreading theorem gives the
pointwise `R`-flat spreading theorem needed for the flat-over-base locus. -/
private theorem exists_flat_localizedAway_of_flatAtPrime_of_localizedBaseSpread_forall
    (hspread :
      ∀ {q : PrimeSpectrum S},
        Module.Flat (Localization.AtPrime (q.asIdeal.under R))
          (LocalizedModule.AtPrime q.asIdeal M) →
          ∃ f : S, f ∉ q.asIdeal ∧ Module.Flat R (LocalizedModule (.powers f) M))
    {q : PrimeSpectrum S}
    (hflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)) :
    ∃ f : S, f ∉ q.asIdeal ∧ Module.Flat R (LocalizedModule (.powers f) M) := by
  -- Proof comment: this packages the already-proved single-prime adapter uniformly over all
  -- primes, so the main openness proof can consume one pointwise spreading input.
  exact exists_flat_localizedAway_of_flatAtPrime_of_localizedBaseSpread
    (R := R) (S := S) (M := M) (q := q) hspread hflat

omit [Algebra.FinitePresentation R S] in
/-- Helper for Chap10 Theorem 10 129 4: localizing an `R`-flat `S`-module at any submonoid of
`S` leaves it flat over `R`. -/
private theorem flat_of_isLocalizedModule_over_algebra
    {N : Type*} {N' : Type*}
    [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommMonoid N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
    (T : Submonoid S) (g : N →ₗ[S] N') [IsLocalizedModule T g]
    (hflat : Module.Flat R N) :
    Module.Flat R N' := by
  -- Proof comment: use the injectivity criterion for flatness and rewrite the tensor map as an
  -- `S`-linear tensor map so the localized-module map API can apply.
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ L
  rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  have hinjN : Function.Injective ⇑((AlgebraTensorModule.lTensor S N) L.subtype) := by
    -- Proof comment: the original module is `R`-flat, so tensoring it with a submodule inclusion
    -- is injective; the same coercion rewrite puts it in the `S`-linear form.
    have h0 := Module.Flat.iff_lTensor_injectiveₛ.mp hflat (P := P) L
    rwa [← AlgebraTensorModule.coe_lTensor (A := S)] at h0
  have hmap := IsLocalizedModule.map_lTensor (S := T) (N := L) (P := P)
      (f := L.subtype) (g := g)
  -- Proof comment: localizing the already-injective tensor map remains injective, and the
  -- comparison lemma identifies that localization with the tensor map for `N'`.
  simpa [hmap] using
    (IsLocalizedModule.map_injective T
      (AlgebraTensorModule.rTensor R L g)
      (AlgebraTensorModule.rTensor R P g)
      ((AlgebraTensorModule.lTensor S N) L.subtype) hinjN)

omit [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Theorem 10 129 4: global `R`-flatness gives a principal localization
witness, namely the trivial basic open `D(1)`. -/
private theorem exists_flat_localizedAway_of_global_flat
    {q : PrimeSpectrum S} (hflat : Module.Flat R M) :
    ∃ f : S, f ∉ q.asIdeal ∧ Module.Flat R (LocalizedModule (.powers f) M) := by
  -- Proof comment: choose the unit `1`, which is outside every prime ideal.
  refine ⟨1, q.asIdeal.primeCompl.one_mem, ?_⟩
  -- Proof comment: localization preserves `R`-flatness by the algebra-localization adapter.
  exact flat_of_isLocalizedModule_over_algebra (R := R) (S := S) (N := M)
    (N' := LocalizedModule (.powers (1 : S)) M) (.powers (1 : S))
    (LocalizedModule.mkLinearMap (.powers (1 : S)) M) hflat

omit [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Theorem 10 129 4: if `M` is already `R`-flat, every stalk belongs to the
flat-over-base locus. -/
private theorem flatOverBaseLocus_eq_univ_of_global_flat
    (hflat : Module.Flat R M) :
    flatOverBaseLocus R S M = Set.univ := by
  ext q
  rw [mem_flatOverBaseLocus]
  constructor
  · -- Proof comment: the forward implication is immediate because the target set is all points.
    intro _
    trivial
  · -- Proof comment: the stalk at `q` is a localization of the globally flat module `M`.
    intro _
    exact flat_of_isLocalizedModule_over_algebra (R := R) (S := S) (N := M)
      (N' := LocalizedModule.AtPrime q.asIdeal M) q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) hflat

omit [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Theorem 10 129 4: flatness over `R` survives further localization from
`M_f` to the stalk `M_q` for every `q ∈ D(f)`. -/
private theorem flat_atPrime_of_flat_localizedAway
    {f : S} {q : PrimeSpectrum S} (hfq : f ∉ q.asIdeal)
    (hflat : Module.Flat R (LocalizedModule (.powers f) M)) :
    Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := by
  -- Proof comment: `f ∉ q` says that the powers of `f` are already among the elements inverted
  -- at `q`, so `M_q` is a further localization of `M_f`.
  have hle : Submonoid.powers f ≤ q.asIdeal.primeCompl := by
    rw [Submonoid.powers_le]
    exact hfq
  -- Proof comment: apply the general flatness-preservation helper to this further localization.
  exact flat_of_isLocalizedModule_over_algebra (R := R) (S := S)
    (N := LocalizedModule (.powers f) M) (N' := LocalizedModule.AtPrime q.asIdeal M)
    q.asIdeal.primeCompl
    (LocalizedModule.liftOfLE (M := M) (.powers f) q.asIdeal.primeCompl hle) hflat

omit [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Theorem 10 129 4: if `M_f` is flat over `R`, then the whole basic open
`D(f)` is contained in `flatOverBaseLocus R S M`. -/
private theorem basicOpen_subset_flatOverBaseLocus_of_flat_localizedAway
    {f : S} (hflat : Module.Flat R (LocalizedModule (.powers f) M)) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum S)) ⊆ flatOverBaseLocus R S M := by
  intro q hq
  -- Proof comment: rewrite the owner set to the stalk flatness condition at the chosen point.
  rw [mem_flatOverBaseLocus]
  have hfq : f ∉ q.asIdeal := by
    -- Proof comment: membership in the principal basic open is exactly nonmembership of `f`.
    simpa [PrimeSpectrum.mem_basicOpen] using hq
  -- Proof comment: the further-localization adapter converts flatness on `D(f)` to flatness at
  -- this particular prime of `D(f)`.
  exact flat_atPrime_of_flat_localizedAway (R := R) (S := S) (M := M) hfq hflat

omit [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Theorem 10 129 4: a principal localization that is flat over `R` gives the
open-neighborhood witness required at every prime of its basic open. -/
private theorem flatOverBaseLocus_openNeighborhood_of_flat_localizedAway
    {f : S} {q : PrimeSpectrum S} (hfq : f ∉ q.asIdeal)
    (hflat : Module.Flat R (LocalizedModule (.powers f) M)) :
    ∃ U : Set (PrimeSpectrum S),
      U ⊆ flatOverBaseLocus R S M ∧ IsOpen U ∧ q ∈ U := by
  -- Proof comment: use the principal basic open `D(f)` as the neighborhood.
  refine ⟨PrimeSpectrum.basicOpen f,
    basicOpen_subset_flatOverBaseLocus_of_flat_localizedAway
      (R := R) (S := S) (M := M) hflat,
    (PrimeSpectrum.basicOpen f).2, ?_⟩
  -- Proof comment: the nonmembership condition is exactly membership in the basic open.
  simpa [PrimeSpectrum.mem_basicOpen] using hfq

omit [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] in
/-- Helper for Chap10 Theorem 10 129 4: pointwise spreading of flatness to principal
localizations makes `flatOverBaseLocus R S M` open. -/
private theorem isOpen_flatOverBaseLocus_of_exists_flat_localizedAway
    (hspread :
      ∀ {q : PrimeSpectrum S},
        Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) →
          ∃ f : S, f ∉ q.asIdeal ∧ Module.Flat R (LocalizedModule (.powers f) M)) :
    IsOpen (flatOverBaseLocus R S M) := by
  -- Proof comment: reduce openness to finding an open neighborhood around each point of the
  -- locus, then use the principal-open spreading witness supplied by `hspread`.
  refine isOpen_iff_forall_mem_open.mpr fun q hq ↦ ?_
  rw [mem_flatOverBaseLocus] at hq
  obtain ⟨f, hfq, hflatf⟩ := hspread hq
  -- Proof comment: the earlier neighborhood helper packages the principal basic open `D(f)`.
  exact flatOverBaseLocus_openNeighborhood_of_flat_localizedAway
    (R := R) (S := S) (M := M) hfq hflatf

/-- Helper for Chap10 Theorem 10 129 4: the localized-base flat locus is open for a finitely
presented algebra and finitely presented module. -/
private theorem isOpen_localizedBaseFlatLocus_of_finitePresentation :
    IsOpen (localizedBaseFlatLocus R S M) := by
  -- Route correction: the main theorem no longer asks for the stronger pointwise principal-open
  -- spreading witness. The remaining source-facing input should prove openness of this locus
  -- directly from the finite-presentation approximation and finite-free-complex exactness APIs.
  -- TODO: prove the direct open-locus theorem using the noetherian finite-type stage, the
  -- finite-free-complex fiber exactness locus, and the flatness criterion.
  sorry

/-- Theorem 10.129.4: for a finitely presented ring map `R → S` and a finitely presented
`S`-module `M`, the set of primes `q` of `S` such that the localization `M_q` is flat over `R`
is an open subset of `Spec(S)`. -/
-- Proof sketch: for a prime `q` where `M_q` is flat over `R`, first descend the data to a finite
-- type `ℤ`-model using Lemma `10.127.18` and recover flatness at a stage via Lemma `10.128.3`.
-- Then reduce to the Noetherian case, resolve `M` by a bounded finite free complex, show the top
-- syzygy becomes free near `q`, and apply Lemma `10.129.3` together with the flatness criterion
-- from Lemma `10.99.5` to obtain a basic open neighborhood contained in the flat locus.
@[stacks 00RC]
theorem isOpen_flatOverBaseLocus_of_finitePresentation :
    IsOpen (flatOverBaseLocus R S M) := by
  -- Proof comment: rewrite the target owner to the localized-base locus, where the remaining
  -- source theorem is a direct openness statement instead of a stronger pointwise witness.
  rw [flatOverBaseLocus_eq_localizedBaseFlatLocus]
  exact isOpen_localizedBaseFlatLocus_of_finitePresentation (R := R) (S := S) (M := M)

end

end Module
