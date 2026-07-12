import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap05.Definition_5_10_1
import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap10.Lemma_10_33_2
import StacksProject_2024.Chap10.Lemma_10_116_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum
open TopologicalSpace
open scoped PrimeSpectrum

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- Domain-style sampling for Lemma 10.122.1:
- primary domain: isolated points of `Spec(S)` for a finite type `k`-algebra over a field, together
  with the resulting localization and product-splitting structure;
- sampled owner declarations:
  `PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing`,
  `PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`,
  `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`,
  `exists_idempotent_algEquiv_localization_prod_quotient_of_isClosed_range_comap`;
- best owner abstraction: the canonical prime-spectrum owner `PrimeSpectrum`, with the chapter's
  source-facing basic-open notation `D(-)` and canonical localization/product decomposition
  owners supplying the derived structure;
- primitive data: a prime `q : PrimeSpectrum S`;
- derived API: the TFAE clauses, the localized factor `Localization.AtPrime q.asIdeal`, and the
  complementary finite type factor.

Source/core/bridge triage:
- `source-facing`: `isolatedPoint_tfae` and the complementary-factor decomposition theorem;
- `core/canonical`: `PrimeSpectrum`, `D(-)`, `Localization.AtPrime`, and
  `PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`;
- `bridge/view`: the product decomposition theorem, which presents the source-facing splitting
  while deriving it from canonical idempotent/localization owners.
-/

/-- Helper for Chap10 Lemma 10 122 1: a sum in `WithBot ℕ∞` of an extended natural number and a
natural number is zero only when both summands are zero. -/
private theorem withBotENat_add_nat_eq_zero {a : WithBot ℕ∞} {n : ℕ}
    (h : a + (n : WithBot ℕ∞) = 0) : a = 0 ∧ n = 0 := by
  -- Proof comment: split off the bottom and top cases, then reduce the finite case to `Nat`.
  cases a with
  | bot =>
      simp [WithBot.bot_add] at h
  | coe a =>
      cases a with
      | top =>
          rw [← WithBot.coe_natCast, ← WithBot.coe_add] at h
          exact False.elim (ENat.top_ne_zero (WithBot.coe_eq_zero.mp h))
      | coe m =>
          have hm : m + n = 0 := by
            rw [← WithBot.coe_natCast, ← WithBot.coe_add, ← ENat.coe_add] at h
            have h' : ((m + n : ℕ) : ℕ∞) = 0 := WithBot.coe_eq_zero.mp h
            simpa using h'
          constructor
          · have hm0 := Nat.eq_zero_of_add_eq_zero_right hm
            simp [hm0]
          · exact Nat.eq_zero_of_add_eq_zero_left hm

/-- Helper for Chap10 Lemma 10 122 1: an essentially finite type field extension has finite
transcendence degree. -/
private lemma trdeg_lt_aleph0_of_essFiniteType_field
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] : Algebra.trdeg K L < Cardinal.aleph0 := by
  -- Proof comment: choose finitely many generators of the top intermediate field, then use the
  -- standard algebraic-over-adjoin bound for transcendence degree.
  obtain ⟨t, ht⟩ := IntermediateField.fg_top K L
  have ht_alg : Algebra.IsAlgebraic (Algebra.adjoin K (t : Set L)) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, ht,
      Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  exact
    lt_of_le_of_lt
      (Algebra.IsAlgebraic.trdeg_le_cardinalMk K (t : Set L))
      (by simpa using t.finite_toSet.lt_aleph0)

/-- Helper for Chap10 Lemma 10 122 1: for an essentially finite type field extension, vanishing
of the finite cardinal representative of the transcendence degree implies algebraicity. -/
private lemma isAlgebraic_of_trdeg_toNat_eq_zero_of_essFiniteType_field
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L]
    (h : Cardinal.toNat (Algebra.trdeg K L) = 0) : Algebra.IsAlgebraic K L := by
  -- Proof comment: finite transcendence degree lets us recover the cardinal from `toNat`, so
  -- the zero natural representative gives zero transcendence degree.
  have hlt : Algebra.trdeg K L < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field (K := K) (L := L)
  have hzero : Algebra.trdeg K L = 0 := by
    have hcast : ((Cardinal.toNat (Algebra.trdeg K L) : ℕ) : Cardinal) =
        Algebra.trdeg K L :=
      Cardinal.cast_toNat_of_lt_aleph0 hlt
    simpa [h] using hcast.symm
  exact (trdeg_eq_zero_iff (R := K) (A := L)).mp hzero

/-- Helper for Chap10 Lemma 10 122 1: closed points over a finite type algebra over a field are
exactly those with finite residue field over the base field. -/
private theorem isClosed_singleton_iff_moduleFinite_residueField (q : PrimeSpectrum S) :
    IsClosed ({q} : Set (PrimeSpectrum S)) ↔ Module.Finite k q.asIdeal.ResidueField := by
  constructor
  · -- Proof comment: a closed singleton is maximal, and the finite type Nullstellensatz makes the
    -- residue field finite over the base.
    intro hq
    have hmax : q.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hq
    letI : q.asIdeal.IsMaximal := hmax
    exact finite_residueField_of_isMaximal_of_finiteType k q.asIdeal
  · -- Proof comment: finite residue field gives an integral residue algebra, whose kernel is a
    -- maximal ideal; that kernel is the prime `q`.
    intro hfin
    apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr
    letI : Module.Finite k q.asIdeal.ResidueField := hfin
    letI : Algebra.IsIntegral k q.asIdeal.ResidueField :=
      Algebra.IsIntegral.of_finite k q.asIdeal.ResidueField
    letI : Algebra.IsIntegral S q.asIdeal.ResidueField :=
      ⟨fun x => (Algebra.IsIntegral.isIntegral (R := k) x).tower_top⟩
    have hmax : (RingHom.ker (algebraMap S q.asIdeal.ResidueField)).IsMaximal := by
      exact Algebra.ker_algebraMap_isMaximal_of_isIntegral S q.asIdeal.ResidueField
    rwa [Ideal.ker_algebraMap_residueField] at hmax

/-- Helper for Chap10 Lemma 10 122 1: the AtPrime localization has Krull dimension zero exactly
at minimal primes. -/
private theorem ringKrullDim_localizationAtPrime_eq_zero_iff_mem_minimalPrimes
    (q : PrimeSpectrum S) :
    ringKrullDim (Localization.AtPrime q.asIdeal) = 0 ↔ q.asIdeal ∈ minimalPrimes S := by
  -- Proof comment: identify the local Krull dimension with the height of `q`, then use the
  -- standard zero-height characterization of minimal primes.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal)]
  rw [Ideal.height_eq_primeHeight q.asIdeal]
  rw [WithBot.coe_eq_zero]
  exact Ideal.primeHeight_eq_zero_iff

/-- Helper for Chap10 Lemma 10 122 1: in the finite type Jacobson/Noetherian setting, an open
singleton is the same as a closed point with zero-dimensional local ring. -/
private theorem isOpen_singleton_iff_isClosed_and_ringKrullDim_localizationAtPrime_eq_zero
    (k : Type u) [Field k] [Algebra k S] [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    IsOpen ({q} : Set (PrimeSpectrum S)) ↔
      IsClosed ({q} : Set (PrimeSpectrum S)) ∧
        ringKrullDim (Localization.AtPrime q.asIdeal) = 0 := by
  -- Proof comment: the Jacobson-space TFAE converts openness to closedness plus
  -- generalization-stability, and the latter is minimality of `q`.
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k)
  calc
    IsOpen ({q} : Set (PrimeSpectrum S)) ↔
        IsClosed ({q} : Set (PrimeSpectrum S)) ∧
          StableUnderGeneralization ({q} : Set (PrimeSpectrum S)) :=
      (PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing q).out 0 2 rfl rfl
    _ ↔ IsClosed ({q} : Set (PrimeSpectrum S)) ∧
          ringKrullDim (Localization.AtPrime q.asIdeal) = 0 := by
      exact and_congr_right fun _ => by
        rw [PrimeSpectrum.stableUnderGeneralization_singleton]
        exact (ringKrullDim_localizationAtPrime_eq_zero_iff_mem_minimalPrimes q).symm

/-- Helper for Chap10 Lemma 10 122 1: the topological local dimension formula reduces zero
topological dimension to the closed-point and zero-local-Krull-dimension normal form. -/
private theorem topologicalKrullDimAt_eq_zero_iff_isClosed_and_ringKrullDim_localizationAtPrime_eq_zero
    (k : Type u) [Field k] [Algebra k S] [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    topologicalKrullDimAt q = 0 ↔
      IsClosed ({q} : Set (PrimeSpectrum S)) ∧
        ringKrullDim (Localization.AtPrime q.asIdeal) = 0 := by
  constructor
  · -- Proof comment: the dimension formula splits the zero sum into local dimension zero and
    -- zero transcendence degree, hence algebraicity and finiteness of the residue field.
    intro htop
    have hformula :=
      topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
        (k := k) (S := S) q
    have hsum : ringKrullDim (Localization.AtPrime q.asIdeal) +
        (Cardinal.toNat (Algebra.trdeg k q.asIdeal.ResidueField) : WithBot ℕ∞) = 0 := by
      rwa [← hformula]
    have hparts := withBotENat_add_nat_eq_zero hsum
    letI : Algebra.EssFiniteType k S := Algebra.EssFiniteType.of_finiteType k S
    letI : Algebra.EssFiniteType k q.asIdeal.ResidueField :=
      Algebra.EssFiniteType.comp k S q.asIdeal.ResidueField
    have halg : Algebra.IsAlgebraic k q.asIdeal.ResidueField :=
      isAlgebraic_of_trdeg_toNat_eq_zero_of_essFiniteType_field
        (K := k) (L := q.asIdeal.ResidueField) hparts.2
    letI : Algebra.IsAlgebraic k q.asIdeal.ResidueField := halg
    letI : Module.Finite k q.asIdeal.ResidueField :=
      Algebra.finite_of_essFiniteType_of_isAlgebraic
    constructor
    · exact
        (isClosed_singleton_iff_moduleFinite_residueField (k := k) (S := S) (q := q)).mpr
          (inferInstance : Module.Finite k q.asIdeal.ResidueField)
    · exact hparts.1
  · -- Proof comment: closedness gives finite residue field, so the transcendence-degree term in
    -- the formula is zero and the remaining local dimension is the supplied hypothesis.
    intro h
    have hformula :=
      topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
        (k := k) (S := S) q
    have hfin : Module.Finite k q.asIdeal.ResidueField :=
      (isClosed_singleton_iff_moduleFinite_residueField (k := k) (S := S) (q := q)).mp h.1
    letI : Module.Finite k q.asIdeal.ResidueField := hfin
    letI : Algebra.IsAlgebraic k q.asIdeal.ResidueField :=
      Algebra.IsAlgebraic.of_finite k q.asIdeal.ResidueField
    have htrdeg : Cardinal.toNat (Algebra.trdeg k q.asIdeal.ResidueField) = 0 := by
      simpa using congrArg Cardinal.toNat
        (trdeg_eq_zero (R := k) (A := q.asIdeal.ResidueField))
    rw [hformula, h.2, htrdeg]
    simp

/-- Helper for Chap10 Lemma 10 122 1: an isolated point is equivalent to finiteness of its local
ring over the base field. -/
private theorem isOpen_singleton_iff_moduleFinite_localizationAtPrime (q : PrimeSpectrum S) :
    IsOpen ({q} : Set (PrimeSpectrum S)) ↔
      Module.Finite k (Localization.AtPrime q.asIdeal) := by
  constructor
  · -- Proof comment: an isolated point is quasi-finite at `q`, and quasi-finiteness over an
    -- Artinian base field gives a finite local algebra.
    intro hq
    letI : Algebra.QuasiFiniteAt k q.asIdeal := Algebra.QuasiFiniteAt.of_isOpen_singleton q hq
    exact Module.Finite.of_quasiFinite
  · -- Proof comment: a finite local algebra is quasi-finite, so the quasi-finite-at clopen
    -- singleton theorem makes `{q}` open.
    intro hfin
    letI : Module.Finite k (Localization.AtPrime q.asIdeal) := hfin
    letI : Algebra.QuasiFinite k (Localization.AtPrime q.asIdeal) :=
      (Algebra.QuasiFinite.iff_of_isArtinianRing
        (R := k) (S := Localization.AtPrime q.asIdeal)).mpr hfin
    exact (Algebra.QuasiFiniteAt.isClopen_singleton (R := k) q).isOpen

/-- Helper for Chap10 Lemma 10 122 1: an isolated point is equivalent to being cut out by one
basic open subset. -/
private theorem isOpen_singleton_iff_exists_basicOpen_eq_singleton
    (k : Type u) [Field k] [Algebra k S] [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    IsOpen ({q} : Set (PrimeSpectrum S)) ↔
      ∃ g : S, g ∉ q.asIdeal ∧ (D(g) : Set (PrimeSpectrum S)) = {q} := by
  constructor
  · -- Proof comment: the quasi-finite-at basic-open criterion produces the desired `D(g)`.
    intro hq
    letI : Algebra.EssFiniteType k S := Algebra.EssFiniteType.of_finiteType k S
    letI : Algebra.QuasiFiniteAt k q.asIdeal := Algebra.QuasiFiniteAt.of_isOpen_singleton q hq
    simpa using Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton (R := k) q.asIdeal
  · -- Proof comment: the reverse implication is immediate because each basic open is open.
    rintro ⟨g, hg, hD⟩
    rw [← hD]
    exact isOpen_basicOpen

/-- Helper for Chap10 Lemma 10 122 1: the AtPrime localization has image exactly the isolated
singleton when that singleton is open. -/
private theorem range_comap_localizationAtPrime_eq_singleton_of_isOpen_singleton
    (k : Type u) [Field k] [Algebra k S] [Algebra.FiniteType k S]
    (q : PrimeSpectrum S) (hq : IsOpen ({q} : Set (PrimeSpectrum S))) :
    Set.range (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q.asIdeal))) =
      ({q} : Set (PrimeSpectrum S)) := by
  -- Proof comment: openness gives generalization-stability of the singleton, hence minimality of
  -- `q`; the localization range consists of primes disjoint from `q.primeCompl`, i.e. primes below
  -- `q`, so minimality forces equality.
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k)
  have hsg : StableUnderGeneralization ({q} : Set (PrimeSpectrum S)) :=
    ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing q).out
      0 2 rfl rfl).mp hq |>.2
  have hmin : q.asIdeal ∈ minimalPrimes S :=
    PrimeSpectrum.stableUnderGeneralization_singleton.mp hsg
  rw [PrimeSpectrum.localization_comap_range
    (S := Localization.AtPrime q.asIdeal) (M := q.asIdeal.primeCompl)]
  ext p
  constructor
  · intro hp
    have hle : p.asIdeal ≤ q.asIdeal := by
      intro x hx
      by_contra hxq
      exact Set.disjoint_left.mp hp hxq hx
    have hge : q.asIdeal ≤ p.asIdeal := hmin.2 ⟨p.isPrime, bot_le⟩ hle
    exact Set.mem_singleton_iff.mpr (PrimeSpectrum.ext (le_antisymm hle hge))
  · intro hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    change Disjoint (q.asIdeal.primeCompl : Set S) q.asIdeal
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hx1 hx2

/-- Helper for Chap10 Lemma 10 122 1: a closed AtPrime localization image gives a finite type
complementary factor in the original algebra universe. -/
private theorem exists_finiteType_complementaryFactor_of_isClosed_range_comap
    (q : PrimeSpectrum S)
    (hclosed : IsClosed
      (Set.range (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q.asIdeal))))) :
    ∃ (S' : Type v) (_ : CommRing S') (_ : Algebra k S') (_ : Algebra.FiniteType k S')
      (e : S ≃ₐ[k] Localization.AtPrime q.asIdeal × S'),
      (RingHom.fst (Localization.AtPrime q.asIdeal) S').comp e.toRingHom =
        algebraMap S (Localization.AtPrime q.asIdeal) := by
  -- Proof comment: apply the closed-range idempotent decomposition, restrict the resulting
  -- `S`-algebra equivalence to scalars over `k`, and keep the quotient factor in universe `v`.
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  let hNoeth : NoetherianSpace (PrimeSpectrum S) := inferInstance
  obtain ⟨e, he, φS, hfst⟩ :=
    exists_idempotent_algEquiv_localization_prod_quotient_of_isClosed_range_comap
      q.asIdeal.primeCompl hclosed (Or.inl hNoeth)
  let Q : Type v := S ⧸ Ideal.span ({e} : Set S)
  letI : CommRing Q := inferInstance
  letI : Algebra k Q := inferInstance
  letI : Algebra.FiniteType k Q := inferInstance
  let φk : S ≃ₐ[k] Localization.AtPrime q.asIdeal × Q := φS.restrictScalars k
  refine ⟨Q, inferInstance, inferInstance, inferInstance, φk, ?_⟩
  ext r
  simpa [φk] using DFunLike.congr_fun hfst r

-- Proof sketch: combine the Jacobson-space criterion for isolated points in a Noetherian Jacobson
-- spectrum with the characterization of finite type zero-dimensional algebras over a field as
-- finite algebras. Clause `(3)` is the basic-open reformulation of an isolated point; clauses
-- `(4)`, `(5)`, and `(6)` come from the local Krull-dimension formulas at a point of a finite type
-- `k`-algebra and the finite residue-field criterion for closed points.
/-- Lemma 10.122.1: for a prime `q` of a finite type `k`-algebra `S`, the following are
equivalent: `q` is an isolated point of `Spec(S)`; the local ring `S_q` is finite over `k`; there
exists `g ∉ q` with `D(g) = {q}`; the local topological dimension of `Spec(S)` at `q` is zero;
`q` is a closed point and `S_q` has Krull dimension zero; and the residue field extension
`κ(q) / k` is finite while `S_q` has Krull dimension zero. -/
@[stacks 00PJ]
theorem isolatedPoint_tfae (q : PrimeSpectrum S) :
    List.TFAE
      [ IsOpen ({q} : Set (PrimeSpectrum S))
      , Module.Finite k (Localization.AtPrime q.asIdeal)
      , ∃ g : S, g ∉ q.asIdeal ∧ (D(g) : Set (PrimeSpectrum S)) = {q}
      , topologicalKrullDimAt q = 0
      , IsClosed ({q} : Set (PrimeSpectrum S)) ∧
          ringKrullDim (Localization.AtPrime q.asIdeal) = 0
      , Module.Finite k q.asIdeal.ResidueField ∧
          ringKrullDim (Localization.AtPrime q.asIdeal) = 0
      ] := by
  -- Proof comment: normalize every clause to the open-singleton clause or to the shared
  -- closed-and-zero-local-dimension normal form, then let `tfae_finish` assemble the graph.
  tfae_have 1 ↔ 2 := isOpen_singleton_iff_moduleFinite_localizationAtPrime q
  tfae_have 1 ↔ 3 := isOpen_singleton_iff_exists_basicOpen_eq_singleton k q
  tfae_have 1 ↔ 5 :=
    isOpen_singleton_iff_isClosed_and_ringKrullDim_localizationAtPrime_eq_zero k q
  tfae_have 4 ↔ 5 :=
    topologicalKrullDimAt_eq_zero_iff_isClosed_and_ringKrullDim_localizationAtPrime_eq_zero k q
  tfae_have 5 ↔ 6 := by
    exact and_congr_left fun _ => isClosed_singleton_iff_moduleFinite_residueField q
  tfae_finish

-- Proof sketch: an isolated point gives a clopen singleton in `Spec(S)`, hence a decomposition of
-- `S` by the standard correspondence between clopen subsets of the spectrum and product
-- decompositions of the ring. The factor corresponding to `{q}` is canonically `S_q`, and finite
-- type over `k` passes to the complementary factor.
/-- If `q` is an isolated point of `Spec(S)`, then `S` splits as the product of `S_q` and another
finite type `k`-algebra, with first projection equal to the localization map `S → S_q`. -/
theorem exists_finiteType_complementary_factor_of_isolatedPoint
    (q : PrimeSpectrum S) (hq : IsOpen ({q} : Set (PrimeSpectrum S))) :
    ∃ (S' : Type v) (_ : CommRing S') (_ : Algebra k S') (_ : Algebra.FiniteType k S')
      (e : S ≃ₐ[k] Localization.AtPrime q.asIdeal × S'),
      (RingHom.fst (Localization.AtPrime q.asIdeal) S').comp e.toRingHom =
        algebraMap S (Localization.AtPrime q.asIdeal) := by
  -- Proof comment: reduce the isolated point to a closed image for the AtPrime localization, then
  -- invoke the idempotent product decomposition in the same universe as the original finite type
  -- algebra, matching the source statement's existential complement.
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k)
  have hrange :=
    range_comap_localizationAtPrime_eq_singleton_of_isOpen_singleton k q hq
  have hclosedSingleton : IsClosed ({q} : Set (PrimeSpectrum S)) :=
    (((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing q).out
      0 1 rfl rfl).mp hq).isClosed
  have hclosedRange :
      IsClosed (Set.range
        (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q.asIdeal)))) := by
    rw [hrange]
    exact hclosedSingleton
  have hsameUniverse :=
    exists_finiteType_complementaryFactor_of_isClosed_range_comap
      (k := k) (S := S) (q := q) hclosedRange
  exact hsameUniverse

/- Canonical owner reuse: the `D(g) = {q}` localization comparison is exactly
`PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`. -/
recall PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton

end
