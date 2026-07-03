import Mathlib
import Mathlib.RingTheory.Localization.AsSubring

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_25_1 (from Chap10) -/
universe u

section

variable {R : Type u} [CommSemiring R]

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-!
Domain-style sampling for zero-dimensional localizations at minimal primes:
- source-facing items:
  the nilpotence statement for elements of the maximal ideal of `Localization.AtPrime p.1`,
  and under `[IsReduced R]` the field corollary for the same localization.
- core/canonical owners inspected:
  `Ring.KrullDimLE.of_isLocalization`,
  `Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal`,
  `Ring.KrullDimLE.isField_of_isReduced`,
  `IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes`.
- owner abstraction: the chapter already treats `minimalPrimes R` as the canonical minimal-prime
  owner, so the theorem should use that owner directly rather than a parallel `PrimeSpectrum`
  point plus a separate minimality proof.
- bridge/view layer here: the file remains a thin source-facing specialization that derives the
  local `Ring.KrullDimLE 0` instance from minimality of `p` and then reuses the canonical
  nilpotence and reduced-field criteria. No additional wrapper API is needed.
-/

/-- Lemma 10.25.1: if `p` is a minimal prime of `R`, then every element of the maximal ideal of
`Localization.AtPrime p.1` is nilpotent. -/
theorem isNilpotent_of_mem_maximalIdeal_localizationAtPrime_of_minimalPrime
    (p : minimalPrimes R) {x : Localization.AtPrime p.1}
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p.1)) :
    IsNilpotent x := by
  letI : Ring.KrullDimLE 0 (Localization.AtPrime p.1) :=
    Ring.KrullDimLE.of_isLocalization p.1 p.2 (Localization.AtPrime p.1)
  simpa using
    Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.2 hx

end

section

variable {R : Type u} [CommRing R] [IsReduced R]

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-- Lemma 10.25.1 companion: if `R` is reduced and `p` is a minimal prime of `R`, then
`Localization.AtPrime p.1` is a field. -/
theorem isField_localizationAtPrime_of_minimalPrime (p : minimalPrimes R) :
    IsField (Localization.AtPrime p.1) := by
  letI : Ring.KrullDimLE 0 (Localization.AtPrime p.1) :=
    Ring.KrullDimLE.of_isLocalization p.1 p.2 (Localization.AtPrime p.1)
  exact Ring.KrullDimLE.isField_of_isReduced

end

/-! ### Lemma_10_25_2 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsReduced R]

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

private theorem radical_bot_eq_bot : (⊥ : Ideal R).radical = ⊥ := by
  simpa [nilradical, Ideal.zero_eq_bot] using nilradical_eq_zero R

-- Proof sketch: the `p`-component of the canonical `algebraMap` into the product is the
-- localization map
-- `R → Localization.AtPrime p`, whose kernel is `p` by
-- `Localization.AtPrime.comap_maximalIdeal`. Intersecting these kernels over all minimal primes
-- gives `⊥`, since `R` is reduced and the intersection of the minimal primes is zero.
/-- The canonical map from `R` to the product of the localizations `R_𝔭` over all minimal
primes `𝔭` is injective. -/
private theorem algebraMap_minimalPrimeLocalizations_injective :
    Function.Injective (algebraMap R (∀ p : minimalPrimes R, Localization.AtPrime p.1)) := by
  intro x y hxy
  have hxy' : x - y ∈ sInf (minimalPrimes R) := by
    rw [Ideal.mem_sInf]
    intro p hp
    haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hp
    have hcomp : algebraMap R (Localization.AtPrime p) (x - y) = 0 := by
      have hcomp' := congrArg (fun f ↦ f ⟨p, hp⟩) hxy
      simpa [map_sub] using sub_eq_zero.mpr hcomp'
    obtain ⟨s, hs⟩ :=
      (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) (x - y)).mp hcomp
    have hmul : (s : R) * (x - y) ∈ p := by
      rw [hs]
      exact p.zero_mem
    exact (Ideal.IsPrime.mem_or_mem inferInstance hmul).resolve_left s.property
  rw [show minimalPrimes R = (⊥ : Ideal R).minimalPrimes by rfl,
    Ideal.sInf_minimalPrimes, radical_bot_eq_bot, Ideal.mem_bot] at hxy'
  exact sub_eq_zero.mp hxy'

/-- Lemma 10.25.2 (2): the canonical map to the product of the localizations at minimal primes
embeds `R` into a product of fields. -/
theorem algebraMap_embedding_into_product_of_fields :
    Function.Injective (algebraMap R (∀ p : minimalPrimes R, Localization.AtPrime p.1)) ∧
      ∀ p : minimalPrimes R, IsField (Localization.AtPrime p.1) := by
  refine ⟨algebraMap_minimalPrimeLocalizations_injective, ?_⟩
  exact isField_localizationAtPrime_of_minimalPrime

/-- Lemma 10.25.2 (1): a reduced ring admits an injective ring hom into a product of fields. -/
theorem exists_injective_ringHom_into_product_of_fields :
    ∃ f : R →+* ∀ p : minimalPrimes R, Localization.AtPrime p.1,
      Function.Injective f ∧
        ∀ p : minimalPrimes R, IsField (Localization.AtPrime p.1) := by
  exact ⟨algebraMap R (∀ p : minimalPrimes R, Localization.AtPrime p.1),
    algebraMap_embedding_into_product_of_fields⟩

-- Proof sketch: specialize `Ideal.iUnion_minimalPrimes` to `I = ⊥`; because `R` is reduced, the
-- radical of `⊥` is `⊥`, so the right-hand side simplifies to the complement of
-- `nonZeroDivisors R`.
/-- Lemma 10.25.2 (3), canonical form: the union of the minimal prime ideals of a reduced ring is
exactly the complement of `nonZeroDivisors R`. -/
theorem iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors :
    (⋃ p ∈ minimalPrimes R, (p : Set R)) = { x | x ∉ nonZeroDivisors R } := by
  rw [show minimalPrimes R = (⊥ : Ideal R).minimalPrimes by rfl]
  rw [Ideal.iUnion_minimalPrimes]
  ext x
  have hx : x ∉ nonZeroDivisors R ↔ { y | x * y = 0 ∧ y ≠ 0 }.Nonempty :=
    notMem_nonZeroDivisors_iff_left
  simpa [radical_bot_eq_bot, Set.nonempty_def, and_comm] using hx.symm

-- Proof sketch: rewrite the canonical zerodivisor statement using
-- `notMem_nonZeroDivisors_iff_left`.
/-- Lemma 10.25.2 (3), specification form: the union of the minimal prime ideals of a reduced ring
is exactly the set of zerodivisors. -/
theorem iUnion_minimalPrimes_eq_setOf_exists_mul_eq_zero :
    (⋃ p ∈ minimalPrimes R, (p : Set R)) = { x | ∃ y, y ≠ 0 ∧ x * y = 0 } := by
  ext x
  rw [iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors]
  have hx : x ∉ nonZeroDivisors R ↔ { y | x * y = 0 ∧ y ≠ 0 }.Nonempty :=
    notMem_nonZeroDivisors_iff_left
  simpa [Set.nonempty_def, and_comm] using hx

end

/-! ### Lemma_10_25_3 (from Chap10) -/
universe u

open Localization FractionRing

section

variable (R : Type u) [CommRing R]
variable (S : Submonoid R)

/- Lemma 10.25.3 is a `bridge/view` item. The owner abstractions are
`Localization.mapToFractionRing`, which equips `FractionRing R` with the canonical
`Localization S`-algebra structure when `S ≤ nonZeroDivisors R`, and `FractionRing.algEquiv`,
which identifies any fraction ring of `Localization S` with `FractionRing (Localization S)`. -/

/-- Lemma 10.25.3: if `S` is a multiplicative subset of nonzerodivisors in `R`, then the total
quotient ring `Q(R)` is canonically isomorphic to the total quotient ring of the localization
`S⁻¹R`. -/
noncomputable def fractionRing_localization_equiv (hS : S ≤ nonZeroDivisors R) :
    FractionRing R ≃ₐ[R] FractionRing (Localization S) :=
  let f := mapToFractionRing (FractionRing R) S (Localization S) hS
  letI : Algebra (Localization S) (FractionRing R) := RingHom.toAlgebra f.toRingHom
  letI : IsScalarTower R (Localization S) (FractionRing R) :=
    .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  letI : IsFractionRing (Localization S) (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization S (Localization S) (FractionRing R) hS
  (FractionRing.algEquiv (Localization S) (FractionRing R)).symm.restrictScalars R

/-- The canonical equivalence from `Q(R)` to `Q(S⁻¹R)` commutes with the map from `R`. -/
@[simp]
theorem fractionRing_localization_equiv_apply_algebraMap (hS : S ≤ nonZeroDivisors R) (r : R) :
    fractionRing_localization_equiv R S hS (algebraMap R (FractionRing R) r) =
      algebraMap R (FractionRing (Localization S)) r := by
  exact AlgEquiv.commutes (fractionRing_localization_equiv R S hS) r

end

/-! ### Lemma_10_25_4 (from Chap10) -/
universe u

open FractionRing IsLocalization Localization
open PrimeSpectrum

noncomputable section

section

variable (R : Type u) [CommRing R]

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-
Lemma 10.25.4 is a `source-facing` total-quotient-ring splitting statement.
The owner abstractions are the canonical minimal-prime index type `minimalPrimes R`, the
localizations `Localization.AtPrime p.1`, and the canonical map
`Algebra.ofId (FractionRing R) (∀ p : minimalPrimes R, Localization.AtPrime p.1)`.
The bijectivity statement below is derived API used only to build the canonical algebra
equivalence, so it is kept private rather than exposed as a second public owner.
-/

-- Proof sketch: a minimal prime is disjoint from the nonzerodivisors by
-- `Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes`; rewriting that disjointness gives the
-- required containment in the prime complement.
/-- Every nonzerodivisor lies in the prime complement of a minimal prime ideal. -/
private theorem nonZeroDivisors_le_primeCompl_of_mem_minimalPrimes
    (p : minimalPrimes R) :
    nonZeroDivisors R ≤ p.1.primeCompl := by
  intro x hx hxI
  exact (Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes p.2)) hxI hx

local instance (p : minimalPrimes R) :
    Algebra (FractionRing R) (Localization.AtPrime p.1) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (FractionRing R)
    (Localization.AtPrime p.1)
    (nonZeroDivisors R)
    p.1.primeCompl
    (nonZeroDivisors_le_primeCompl_of_mem_minimalPrimes R p)

local instance (p : minimalPrimes R) :
    IsScalarTower R (FractionRing R) (Localization.AtPrime p.1) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le
    (FractionRing R)
    (Localization.AtPrime p.1)
    (nonZeroDivisors R)
    p.1.primeCompl
    (nonZeroDivisors_le_primeCompl_of_mem_minimalPrimes R p)

variable [Finite (minimalPrimes R)]

/-- Helper for Lemma 10.25.4: a prime ideal of `R` survives in the total quotient ring exactly
when it is a minimal prime. -/
private theorem prime_disjoint_nonZeroDivisors_iff_mem_minimalPrimes
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R })
    (P : PrimeSpectrum R) :
    Disjoint (nonZeroDivisors R : Set R) P.asIdeal ↔ P.asIdeal ∈ minimalPrimes R := by
  constructor
  · intro hdisj
    -- Every element of `P` is a zerodivisor, so prime avoidance forces `P` into one minimal prime.
    have hsubset :
        (P.asIdeal : Set R) ⊆ ⋃ p : minimalPrimes R, (p.1 : Set R) := by
      intro x hx
      rw [hzdiv]
      intro hxnd
      exact (Set.disjoint_left.mp hdisj) hxnd hx
    obtain ⟨q, hq, hqleP⟩ := Ideal.exists_minimalPrimes_le (R := R) (I := ⊥) (J := P.asIdeal) bot_le
    let qmin : minimalPrimes R := ⟨q, hq⟩
    obtain ⟨p, -, hPlep⟩ :=
      (P.asIdeal.subset_union_prime_finite
        (s := (Set.univ : Set (minimalPrimes R)))
        (Set.toFinite (Set.univ : Set (minimalPrimes R)))
        qmin
        qmin
        (fun p _ _ _ ↦ Ideal.minimalPrimes_isPrime p.2)).mp <| by
          simpa using hsubset
    have hpmin : Minimal Ideal.IsPrime p.1 := by
      simpa [minimalPrimes_eq_minimals] using p.2
    have hpeq : P.asIdeal = p.1 := hpmin.eq_of_le P.2 hPlep
    simpa [hpeq] using p.2
  · intro hP
    exact (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP).symm

/-- Helper for Lemma 10.25.4: the disjoint-prime locus for the total quotient ring is exactly the
minimal-prime locus in `Spec R`. -/
private theorem fractionRing_disjoint_primes_eq_minimalPrimeSubtype
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R }) :
    { P : PrimeSpectrum R | Disjoint (nonZeroDivisors R : Set R) P.asIdeal } =
      { P : PrimeSpectrum R | P.asIdeal ∈ minimalPrimes R } := by
  ext P
  simp [prime_disjoint_nonZeroDivisors_iff_mem_minimalPrimes, hzdiv]

/-- Helper for Lemma 10.25.4: `Spec(Q(R))` identifies with the minimal-prime subspace of
`Spec R`. -/
private noncomputable def fractionRing_primeSpectrum_homeomorph_minimalPrimeSubtype
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R }) :
    PrimeSpectrum (FractionRing R) ≃ₜ { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R } :=
  (primeSpectrum_localization_homeomorph (R := R) (nonZeroDivisors R)).trans
    (Homeomorph.setCongr
      (fractionRing_disjoint_primes_eq_minimalPrimeSubtype (R := R) hzdiv))

/-- Helper for Lemma 10.25.4: the minimal-prime subtype of `Spec R` is indexed by
`minimalPrimes R`. -/
private theorem minimalPrimeSubtypeEquivMinimalPrimes_left_inv
    (P : { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R }) :
    (⟨⟨P.1.asIdeal, Ideal.minimalPrimes_isPrime P.2⟩, P.2⟩ :
      { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R }) = P := by
  apply Subtype.ext
  exact PrimeSpectrum.ext rfl

/-- Helper for Lemma 10.25.4: the canonical point of the minimal-prime subtype contracts back to
the same minimal prime ideal. -/
private theorem minimalPrimeSubtypeEquivMinimalPrimes_right_inv
    (p : minimalPrimes R) :
    (⟨(⟨⟨p.1, Ideal.minimalPrimes_isPrime p.2⟩, p.2⟩ :
      { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R }).1.asIdeal, p.2⟩ :
      minimalPrimes R) = p := by
  rfl

/-- Helper for Lemma 10.25.4: the minimal-prime points of `Spec R` and the canonical type
`minimalPrimes R` are equivalent. -/
private noncomputable def minimalPrimeSubtypeEquivMinimalPrimes :
    { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R } ≃ minimalPrimes R where
  toFun := fun P ↦ ⟨P.1.asIdeal, P.2⟩
  invFun := fun p ↦ ⟨⟨p.1, Ideal.minimalPrimes_isPrime p.2⟩, p.2⟩
  left_inv := minimalPrimeSubtypeEquivMinimalPrimes_left_inv (R := R)
  right_inv := minimalPrimeSubtypeEquivMinimalPrimes_right_inv (R := R)

/-- Helper for Lemma 10.25.4: `Spec(Q(R))` is indexed by the minimal primes of `R`. -/
private noncomputable def fractionRingPrimeEquivMinimalPrimes
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R }) :
    PrimeSpectrum (FractionRing R) ≃ minimalPrimes R :=
  (fractionRing_primeSpectrum_homeomorph_minimalPrimeSubtype (R := R) hzdiv).toEquiv.trans
    (minimalPrimeSubtypeEquivMinimalPrimes (R := R))

/-- Helper for Lemma 10.25.4: under the spectrum identification, a prime of `Q(R)` contracts to
its corresponding minimal prime of `R`. -/
private theorem fractionRingPrimeEquivMinimalPrimes_apply_comap
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R })
    (P : PrimeSpectrum (FractionRing R)) :
    (fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv P).1 =
      P.asIdeal.comap (algebraMap R (FractionRing R)) := by
  -- The homeomorphism is induced by contraction along `R → Q(R)`.
  rfl

/-- Helper for Lemma 10.25.4: the inverse spectrum equivalence sends a minimal prime to a prime of
`Q(R)` lying over it. -/
private theorem fractionRingPrimeEquivMinimalPrimes_symm_comap
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R })
    (p : minimalPrimes R) :
    p.1 =
      ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal.comap
        (algebraMap R (FractionRing R)) := by
  -- Apply the forward contraction formula to the inverse point and simplify.
  simpa using
    fractionRingPrimeEquivMinimalPrimes_apply_comap
      (R := R) hzdiv ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p)

/-- Helper for Lemma 10.25.4: the minimal-prime subtype is finite because it injects into
`minimalPrimes R`. -/
private theorem minimalPrimeSubtype_finite :
    Finite { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R } := by
  -- Forgetting from a prime-spectrum point to its underlying minimal prime is injective.
  refine Finite.of_injective
    (fun P : { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R } ↦
      (⟨P.1.asIdeal, P.2⟩ : minimalPrimes R))
    ?_
  intro P Q hPQ
  apply Subtype.ext
  exact PrimeSpectrum.ext (congrArg Subtype.val hPQ)

/-- Helper for Lemma 10.25.4: equality of minimal-prime spectrum points is detected on the
underlying ideals. -/
private theorem minimalPrimeSubtype_eq_of_asIdeal_eq
    {P Q : { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R }}
    (hPQ : P.1.asIdeal = Q.1.asIdeal) :
    P = Q := by
  apply Subtype.ext
  exact PrimeSpectrum.ext hPQ

/-- Helper for Lemma 10.25.4: a minimal prime contains an element outside all the other minimal
primes. -/
private theorem exists_separator_of_minimalPrimeSubtype
    (p : { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R }) :
    ∃ x : R, x ∈ p.1.asIdeal ∧
      ∀ q : { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R }, q ≠ p → x ∉ q.1.asIdeal := by
  let pmin : minimalPrimes R := ⟨p.1.asIdeal, p.2⟩
  let S : Set (minimalPrimes R) := { q | q ≠ pmin }
  have hnot_subset :
      ¬ ((p.1.asIdeal : Set R) ⊆ ⋃ q ∈ S, (q.1 : Set R)) := by
    intro hsubset
    obtain ⟨q, hqS, hpleq⟩ :=
      (p.1.asIdeal.subset_union_prime_finite
        (s := S)
        (Set.toFinite S)
        pmin
        pmin
        (fun q _ _ _ ↦ Ideal.minimalPrimes_isPrime q.2)).mp hsubset
    have hqmin : Minimal Ideal.IsPrime q.1 := by
      simpa [minimalPrimes_eq_minimals] using q.2
    have hpq : p.1.asIdeal = q.1 := hqmin.eq_of_le p.1.2 hpleq
    have hqeq : q = pmin := by
      apply Subtype.ext
      exact hpq.symm
    exact hqS hqeq
  obtain ⟨x, hxp, hxnot⟩ := Set.not_subset.mp hnot_subset
  refine ⟨x, hxp, ?_⟩
  intro q hqp hxq
  apply hxnot
  refine Set.mem_iUnion.2 ?_
  refine ⟨(⟨q.1.asIdeal, q.2⟩ : minimalPrimes R), Set.mem_iUnion.2 ?_⟩
  refine ⟨?_, hxq⟩
  intro hqeq
  apply hqp
  exact minimalPrimeSubtype_eq_of_asIdeal_eq (R := R) (congrArg Subtype.val hqeq)

/-- Helper for Lemma 10.25.4: singletons in the minimal-prime subtype are closed. -/
private theorem minimalPrimeSubtype_singleton_isClosed
    (p : { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R }) :
    IsClosed ({p} : Set { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R }) := by
  -- Prime avoidance isolates `p` as the unique minimal prime containing the chosen separator.
  obtain ⟨x, hxp, hsep⟩ := exists_separator_of_minimalPrimeSubtype (R := R) p
  have hset :
      ({p} : Set { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R }) =
        { q : { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R } |
          q.1 ∈ PrimeSpectrum.zeroLocus ({x} : Set R) } := by
    ext q
    constructor
    · intro hq
      subst hq
      simpa [mem_zeroLocus, Set.singleton_subset_iff] using hxp
    · intro hq
      have hxq : x ∈ q.1.asIdeal := by
        simpa [mem_zeroLocus, Set.singleton_subset_iff] using hq
      by_cases hqp : q = p
      · exact hqp
      · exact False.elim (hsep q hqp hxq)
  -- Closedness comes from the ambient closed zero locus.
  have hclosed :
      IsClosed
        { q : { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R } |
          q.1 ∈ PrimeSpectrum.zeroLocus ({x} : Set R) } :=
    (PrimeSpectrum.isClosed_zeroLocus ({x} : Set R)).preimage continuous_subtype_val
  rw [hset]
  exact hclosed

/-- Helper for Lemma 10.25.4: the minimal-prime subtype is a `T1` space. -/
private theorem minimalPrimeSubtype_t1Space :
    T1Space { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R } := by
  exact ⟨minimalPrimeSubtype_singleton_isClosed (R := R)⟩

/-- Helper for Lemma 10.25.4: the minimal-prime subtype is discrete because it is finite and
`T1`. -/
private theorem minimalPrimeSubtype_discreteTopology :
    DiscreteTopology { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R } := by
  letI : Finite { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R } :=
    minimalPrimeSubtype_finite (R := R)
  letI : T1Space { P : PrimeSpectrum R // P.asIdeal ∈ minimalPrimes R } :=
    minimalPrimeSubtype_t1Space (R := R)
  infer_instance

/-- Helper for Lemma 10.25.4: the prime spectrum of the total quotient ring is discrete. -/
private theorem fractionRing_discreteTopology
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R }) :
    DiscreteTopology (PrimeSpectrum (FractionRing R)) := by
  -- Transport discreteness across the source-faithful spectrum identification.
  exact
    (fractionRing_primeSpectrum_homeomorph_minimalPrimeSubtype (R := R) hzdiv).discreteTopology_iff.mpr
      (minimalPrimeSubtype_discreteTopology (R := R))

/-- Helper for Lemma 10.25.4: a comap equality lets us identify the localization of the total
quotient ring at `P` with the localization of `R` at the corresponding contracted prime. -/
private noncomputable abbrev fractionRing_localization_atPrime_algEquiv_of_comap_eq
    {P : Ideal (FractionRing R)} [P.IsPrime]
    {I : Ideal R} [I.IsPrime]
    (hI : I = P.comap (algebraMap R (FractionRing R))) :
    Localization.AtPrime I ≃ₐ[R] Localization.AtPrime P := by
  -- Route correction: substitute the contracted prime into the owner equivalence directly, so
  -- the proof never has to transport across an equality of dependent `AlgEquiv` types.
  subst hI
  exact
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (M := nonZeroDivisors R)
      P

/-- Helper for Lemma 10.25.4: localizing the total quotient ring at the prime over a minimal prime
recovers the original localization at that minimal prime. -/
private noncomputable def fractionRing_localization_factor_equiv
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R })
    (p : minimalPrimes R) :
    Localization.AtPrime p.1 ≃ₐ[R]
      Localization.AtPrime ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal :=
  -- Use the source-faithful contracted-prime equality as the input to the canonical
  -- localization-of-a-localization equivalence.
  fractionRing_localization_atPrime_algEquiv_of_comap_eq
    (R := R)
    (P := ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal)
    (I := p.1)
    (fractionRingPrimeEquivMinimalPrimes_symm_comap (R := R) hzdiv p)

/-- Helper for Lemma 10.25.4: the factor equivalence is induced by the canonical local map from
`R_p` to `Q(R)_P`. -/
private theorem fractionRing_localization_factor_equiv_toRingHom
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R })
    (p : minimalPrimes R) :
    (fractionRing_localization_factor_equiv (R := R) hzdiv p).toRingHom =
      Localization.localRingHom
        p.1
        (((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal)
        (algebraMap R (FractionRing R))
        (fractionRingPrimeEquivMinimalPrimes_symm_comap (R := R) hzdiv p) := by
  -- The localization-of-a-localization equivalence is characterized by its action on the
  -- original ring, so uniqueness of localized maps identifies it with `localRingHom`.
  symm
  apply Localization.localRingHom_unique
  intro x
  calc
    (fractionRing_localization_factor_equiv (R := R) hzdiv p)
        (algebraMap R (Localization.AtPrime p.1) x) =
      algebraMap R
        (Localization.AtPrime ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal)
        x := (fractionRing_localization_factor_equiv (R := R) hzdiv p).commutes x
    _ =
      algebraMap
        (FractionRing R)
        (Localization.AtPrime ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal)
        ((algebraMap R (FractionRing R)) x) := by
        symm
        exact IsScalarTower.algebraMap_apply R (FractionRing R)
          (Localization.AtPrime ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal)
          x

/-- Helper for Lemma 10.25.4: the local map from `R_p` to `Q(R)_P` is compatible with the
`Q(R)`-algebra structures. -/
private theorem fractionRing_localization_factor_equiv_comp_fractionRing_algebraMap
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R })
    (p : minimalPrimes R) :
    ((fractionRing_localization_factor_equiv (R := R) hzdiv p).toRingHom).comp
      (algebraMap (FractionRing R) (Localization.AtPrime p.1)) =
    algebraMap (FractionRing R)
      (Localization.AtPrime ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal) := by
  -- Equality of maps out of the total quotient ring is detected on the image of `R`.
  apply IsLocalization.ringHom_ext (M := nonZeroDivisors R)
  ext x
  calc
    ((fractionRing_localization_factor_equiv (R := R) hzdiv p).toRingHom.comp
        (algebraMap (FractionRing R) (Localization.AtPrime p.1)))
        ((algebraMap R (FractionRing R)) x) =
      (fractionRing_localization_factor_equiv (R := R) hzdiv p)
        (algebraMap R (Localization.AtPrime p.1) x) := by
          exact congrArg
            (fractionRing_localization_factor_equiv (R := R) hzdiv p)
            ((IsScalarTower.algebraMap_apply R (FractionRing R) (Localization.AtPrime p.1) x).symm)
    _ =
      algebraMap R
        (Localization.AtPrime ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal)
        x := (fractionRing_localization_factor_equiv (R := R) hzdiv p).commutes x
    _ =
      (algebraMap (FractionRing R)
        (Localization.AtPrime ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal))
        ((algebraMap R (FractionRing R)) x) := by
          symm
          exact IsScalarTower.algebraMap_apply R (FractionRing R)
            (Localization.AtPrime ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal)
            x

/-- Helper for Lemma 10.25.4: undoing the factor equivalence recovers the canonical
`Q(R)`-algebra map into `R_p`. -/
private theorem fractionRing_localization_factor_equiv_symm_comp_fractionRing_algebraMap
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R })
    (p : minimalPrimes R) :
    ((fractionRing_localization_factor_equiv (R := R) hzdiv p).symm.toRingHom).comp
      (algebraMap
        (FractionRing R)
        (Localization.AtPrime
          ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal)) =
    algebraMap (FractionRing R) (Localization.AtPrime p.1) := by
  -- Apply the forward factor equivalence and use the normalized compatibility above.
  apply IsLocalization.ringHom_ext (M := nonZeroDivisors R)
  ext x
  calc
    ((fractionRing_localization_factor_equiv (R := R) hzdiv p).symm.toRingHom.comp
        (algebraMap
          (FractionRing R)
          (Localization.AtPrime
            ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal)))
        ((algebraMap R (FractionRing R)) x) =
      (fractionRing_localization_factor_equiv (R := R) hzdiv p).symm
        (algebraMap R
          (Localization.AtPrime
            ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal)
          x) := by
          exact congrArg
            ((fractionRing_localization_factor_equiv (R := R) hzdiv p).symm)
            ((IsScalarTower.algebraMap_apply R
              (FractionRing R)
              (Localization.AtPrime
                ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p).asIdeal)
              x).symm)
    _ = algebraMap R (Localization.AtPrime p.1) x :=
      (fractionRing_localization_factor_equiv (R := R) hzdiv p).symm.commutes x
    _ = (algebraMap (FractionRing R) (Localization.AtPrime p.1))
        ((algebraMap R (FractionRing R)) x) := by
          exact IsScalarTower.algebraMap_apply R (FractionRing R) (Localization.AtPrime p.1) x

/-- Helper for Lemma 10.25.4: reindexing `Spec(Q(R))` by the minimal primes and replacing each
factor by the corresponding localization `R_p` gives a product algebra equivalence. -/
private noncomputable def fractionRingPiLocalization_equiv_piMinimalPrimeLocalizations
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R }) :
    PrimeSpectrum.PiLocalization (FractionRing R) ≃ₐ[R]
      ∀ p : minimalPrimes R, Localization.AtPrime p.1 :=
  (AlgEquiv.piCongrLeft' R
      (fun P : PrimeSpectrum (FractionRing R) ↦ Localization.AtPrime P.asIdeal)
      (fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv)).trans
    (AlgEquiv.piCongrRight fun p ↦
      (fractionRing_localization_factor_equiv (R := R) hzdiv p).symm)

/-- Helper for Lemma 10.25.4: composing the target map with the product adapter recovers the
canonical `Spec(Q(R))` localization map. -/
private theorem fractionRingPiLocalization_equiv_piMinimalPrimeLocalizations_comp_toPiLocalization
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R }) :
    ((fractionRingPiLocalization_equiv_piMinimalPrimeLocalizations (R := R) hzdiv).toRingHom).comp
      (PrimeSpectrum.toPiLocalization (FractionRing R)) =
    (Algebra.ofId
      (FractionRing R)
      (∀ p : minimalPrimes R, Localization.AtPrime p.1)).toRingHom := by
  -- After reindexing the prime-product, each component is the inverse factor equivalence applied
  -- to the canonical map into the corresponding localization of `Q(R)`.
  ext x p
  change
      ((fractionRing_localization_factor_equiv (R := R) hzdiv p).symm.toRingHom)
          (((PrimeSpectrum.toPiLocalization (FractionRing R)) x)
            ((fractionRingPrimeEquivMinimalPrimes (R := R) hzdiv).symm p)) =
        algebraMap (FractionRing R) (Localization.AtPrime p.1) x
  simpa [RingHom.comp_apply] using
    RingHom.congr_fun
      (fractionRing_localization_factor_equiv_symm_comp_fractionRing_algebraMap
        (R := R) hzdiv p) x

-- Proof sketch: use the zerodivisor hypothesis to identify `Spec(Q(R))` with the finite set of
-- minimal primes of `R`, then apply the finite-discrete-spectrum splitting result from the
-- previous item and identify each factor with the localization at the corresponding minimal prime.
private theorem fractionRing_to_minimalPrimeLocalizations_bijective
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R }) :
    Function.Bijective
      (Algebra.ofId
        (FractionRing R)
        (∀ p : minimalPrimes R, Localization.AtPrime p.1)) := by
  letI : DiscreteTopology (PrimeSpectrum (FractionRing R)) :=
    fractionRing_discreteTopology (R := R) hzdiv
  let e := fractionRingPiLocalization_equiv_piMinimalPrimeLocalizations (R := R) hzdiv
  -- Transport the canonical bijection for a finite discrete prime spectrum across the bundled
  -- product equivalence built from the source-faithful minimal-prime identification.
  have hbijComp :
      Function.Bijective (e.toRingHom.comp (PrimeSpectrum.toPiLocalization (FractionRing R))) := by
    refine ⟨e.injective.comp (PrimeSpectrum.toPiLocalization_injective (R := FractionRing R)), ?_⟩
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := (PrimeSpectrum.toPiLocalization_bijective (R := FractionRing R)).2 z
    exact ⟨x, rfl⟩
  have hcomp :
      e.toRingHom.comp (PrimeSpectrum.toPiLocalization (FractionRing R)) =
        (Algebra.ofId
          (FractionRing R)
          (∀ p : minimalPrimes R, Localization.AtPrime p.1)).toRingHom :=
    fractionRingPiLocalization_equiv_piMinimalPrimeLocalizations_comp_toPiLocalization
      (R := R) hzdiv
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hxy' :
        ((Algebra.ofId
          (FractionRing R)
          (∀ p : minimalPrimes R, Localization.AtPrime p.1)).toRingHom x) =
        ((Algebra.ofId
          (FractionRing R)
          (∀ p : minimalPrimes R, Localization.AtPrime p.1)).toRingHom y) := hxy
    apply hbijComp.1
    calc
      (e.toRingHom.comp (PrimeSpectrum.toPiLocalization (FractionRing R))) x =
          ((Algebra.ofId
            (FractionRing R)
            (∀ p : minimalPrimes R, Localization.AtPrime p.1)).toRingHom x) :=
        RingHom.congr_fun hcomp x
      _ =
          ((Algebra.ofId
            (FractionRing R)
            (∀ p : minimalPrimes R, Localization.AtPrime p.1)).toRingHom y) := hxy'
      _ = (e.toRingHom.comp (PrimeSpectrum.toPiLocalization (FractionRing R))) y :=
        (RingHom.congr_fun hcomp y).symm
  · intro y
    obtain ⟨x, hx⟩ := hbijComp.2 y
    have hx' :
        ((Algebra.ofId
          (FractionRing R)
          (∀ p : minimalPrimes R, Localization.AtPrime p.1)).toRingHom x) = y := by
      calc
        ((Algebra.ofId
          (FractionRing R)
          (∀ p : minimalPrimes R, Localization.AtPrime p.1)).toRingHom x) =
            (e.toRingHom.comp (PrimeSpectrum.toPiLocalization (FractionRing R))) x :=
          (RingHom.congr_fun hcomp x).symm
        _ = y := hx
    exact ⟨x, hx'⟩

/-- Lemma 10.25.4: if `R` has finitely many minimal primes and their union is exactly the set of
zerodivisors, then the total quotient ring `Q(R)` is canonically isomorphic to the product of the
localizations of `R` at its minimal prime ideals. -/
noncomputable def fractionRing_equiv_pi_minimalPrimeLocalizations
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R }) :
    FractionRing R ≃ₐ[R] ∀ p : minimalPrimes R, Localization.AtPrime p.1 :=
  (AlgEquiv.ofBijective
      (Algebra.ofId
        (FractionRing R)
        (∀ p : minimalPrimes R, Localization.AtPrime p.1))
      (fractionRing_to_minimalPrimeLocalizations_bijective R hzdiv)).restrictScalars R

/-- The canonical equivalence from `Q(R)` to the product of the minimal-prime localizations
commutes with the map from `R`. -/
@[simp]
theorem fractionRing_equiv_pi_minimalPrimeLocalizations_apply_algebraMap
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        { x : R | x ∉ nonZeroDivisors R })
    (r : R) :
    fractionRing_equiv_pi_minimalPrimeLocalizations R hzdiv
        (algebraMap R (FractionRing R) r) =
      algebraMap R (∀ p : minimalPrimes R, Localization.AtPrime p.1) r := by
  exact AlgEquiv.commutes (fractionRing_equiv_pi_minimalPrimeLocalizations R hzdiv) r

end
