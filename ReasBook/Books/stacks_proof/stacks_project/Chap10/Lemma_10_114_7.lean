import StacksProject_2024.Chap05.Definition_5_10_5
import StacksProject_2024.Chap05.Lemma_5_10_2
import StacksProject_2024.Chap05.Lemma_5_20_3
import StacksProject_2024.Chap10.Lemma_10_17_7
import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap10.Lemma_10_114_5
import StacksProject_2024.Chap10.Lemma_10_104_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum TopologicalSpace Topology
open Algebra.FiniteType

namespace PrimeSpectrum

section

variable (S : Type v) [CommRing S]

/-- The dimension-`d` stratum of `Spec(S)`, defined by local Krull dimension. The source uses the
dimension stratification itself, not an auxiliary finite package, so this set is the source-facing
owner for Lemma `10.114.7`. -/
def dimensionStratum (d : ℕ) : Set (PrimeSpectrum S) :=
  { x | topologicalKrullDimAt x = d }

/-- Membership in the dimension-`d` stratum means that the local topological Krull dimension is
exactly `d`. -/
@[simp] theorem mem_dimensionStratum (x : PrimeSpectrum S) (d : ℕ) :
    x ∈ dimensionStratum S d ↔ topologicalKrullDimAt x = d := by
  -- The stratum was defined as exactly this local-dimension fiber.
  rfl

/-- Distinct dimension strata are disjoint. -/
theorem disjoint_dimensionStratum_of_ne {d e : ℕ} (hde : d ≠ e) :
    Disjoint (dimensionStratum S d) (dimensionStratum S e) := by
  -- A point in both strata would give two equal natural values for its local dimension.
  refine Set.disjoint_left.2 ?_
  intro x hxd hxe
  have hcast : (d : WithBot ℕ∞) = e := by
    exact ((mem_dimensionStratum S x d).mp hxd).symm.trans
      ((mem_dimensionStratum S x e).mp hxe)
  have hnat : d = e := by
    exact_mod_cast hcast
  exact hde hnat

/-- Helper for Chap10 Lemma 10 114 7: the dimension strata form a pairwise disjoint family. -/
theorem pairwiseDisjoint_dimensionStratum :
    Pairwise fun d e : ℕ ↦ Disjoint (dimensionStratum S d) (dimensionStratum S e) := by
  -- Package the two-strata disjointness lemma in the form needed by finite partitions.
  intro d e hde
  exact disjoint_dimensionStratum_of_ne S hde

/-- Helper for Chap10 Lemma 10 114 7: membership in the union of all natural dimension strata is
exactly natural-valuedness of the local topological Krull dimension. -/
theorem mem_iUnion_dimensionStratum_iff (x : PrimeSpectrum S) :
    x ∈ (⋃ d : ℕ, dimensionStratum S d) ↔
      ∃ d : ℕ, topologicalKrullDimAt x = d := by
  -- Unfold the indexed union one step and use the defining membership lemma for each fiber.
  simp only [Set.mem_iUnion, mem_dimensionStratum]

/-- Helper for Chap10 Lemma 10 114 7: the natural dimension strata cover the spectrum precisely
when every local topological Krull dimension is a natural value. -/
theorem iUnion_dimensionStratum_eq_univ_iff :
    (⋃ d : ℕ, dimensionStratum S d) = Set.univ ↔
      ∀ x : PrimeSpectrum S, ∃ d : ℕ, topologicalKrullDimAt x = d := by
  constructor
  · intro h x
    -- Read the cover at `x` through the pointwise membership characterization.
    have hx : x ∈ (⋃ d : ℕ, dimensionStratum S d) := by
      simp [h]
    exact (mem_iUnion_dimensionStratum_iff S x).mp hx
  · intro h
    -- Prove equality of sets pointwise; the reverse inclusion is supplied by the local witness.
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact (mem_iUnion_dimensionStratum_iff S x).mpr (h x)

/-- Helper for Chap10 Lemma 10 114 7: a global finite upper bound on topological dimension bounds
the index of any dimension stratum containing a given point. -/
theorem dimensionStratum_index_le_of_topologicalKrullDim_le {n d : ℕ}
    (hbound : topologicalKrullDim (PrimeSpectrum S) ≤ n)
    {x : PrimeSpectrum S} (hx : x ∈ dimensionStratum S d) :
    d ≤ n := by
  -- Compare the local dimension at `x` with the global dimension, then read the stratum index
  -- from the defining equality of the fiber.
  have hlocal_le_global : topologicalKrullDimAt x ≤ topologicalKrullDim (PrimeSpectrum S) := by
    let U : OpenNhdsOf x := ⊤
    have hU : topologicalKrullDim U ≤ topologicalKrullDim (PrimeSpectrum S) := by
      simpa [U] using
        topologicalKrullDim_subspace_le (PrimeSpectrum S) (Set.univ : Set (PrimeSpectrum S))
    exact (topologicalKrullDimAt_le x U).trans hU
  have hd_le_withBot : (d : WithBot ℕ∞) ≤ n := by
    simpa [(mem_dimensionStratum S x d).mp hx] using hlocal_le_global.trans hbound
  exact_mod_cast hd_le_withBot

/-- Helper for Chap10 Lemma 10 114 7: a global finite upper bound on topological dimension bounds
all nonempty dimension strata. -/
theorem finite_nonempty_dimensionStrata_of_topologicalKrullDim_le {n : ℕ}
    (hbound : topologicalKrullDim (PrimeSpectrum S) ≤ n) :
    { d : ℕ | (dimensionStratum S d).Nonempty }.Finite := by
  -- Reduce nonempty strata to indices in the finite interval `{d | d ≤ n}`.
  refine (Set.finite_Iic n).subset ?_
  intro d hd
  rcases hd with ⟨x, hx⟩
  exact dimensionStratum_index_le_of_topologicalKrullDim_le S hbound hx

/-- Helper for Chap10 Lemma 10 114 7: once all local dimensions are natural and bounded by `n`,
the first `n + 1` dimension strata cover the spectrum. -/
theorem iUnion_fin_dimensionStratum_eq_univ_of_topologicalKrullDim_le {n : ℕ}
    (hcover : (⋃ d : ℕ, dimensionStratum S d) = Set.univ)
    (hbound : topologicalKrullDim (PrimeSpectrum S) ≤ n) :
    (⋃ d : Fin (n + 1), dimensionStratum S (d : ℕ)) = Set.univ := by
  -- Convert the natural-indexed cover to a finite-indexed cover using the global dimension bound.
  ext x
  constructor
  · intro _
    trivial
  · intro _
    have hxcover : x ∈ (⋃ d : ℕ, dimensionStratum S d) := by
      simp [hcover]
    obtain ⟨d, hxd⟩ := (mem_iUnion_dimensionStratum_iff S x).mp hxcover
    have hdle : d ≤ n :=
      dimensionStratum_index_le_of_topologicalKrullDim_le S hbound hxd
    exact Set.mem_iUnion.2 ⟨⟨d, Nat.lt_succ_of_le hdle⟩, hxd⟩

end

end PrimeSpectrum

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [CohenMacaulayRing S]

include k

omit [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: the local Krull dimension at `x` is the supremum of the
dimensions of the irreducible components of `Spec(S)` containing `x`. -/
private theorem topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through_local
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) // x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S)) := by
  -- Reuse the owner theorem from Lemma `10.114.5`; this file only needs a local alias.
  simpa using
    (@topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
      k inferInstance S inferInstance inferInstance inferInstance x)

omit [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: the local Krull dimension at `x` is the infimum of the
Krull dimensions of the localizations `Sₘ` over maximal ideals containing `x.asIdeal`. -/
private theorem topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over_local
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ⨅ m : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal },
        ringKrullDim (Localization.AtPrime m.1.asIdeal) := by
  -- Reuse the owner theorem from Lemma `10.114.5`; this file only needs a local alias.
  simpa using
    (@topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over
      k inferInstance S inferInstance inferInstance inferInstance x)

omit [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: at a closed point, the local topological Krull dimension
equals the Krull dimension of the corresponding maximal localization. -/
private theorem topologicalKrullDimAt_closedPoint_eq_ringKrullDim_localizationAtMaximal_local
    (m : MaximalSpectrum S) :
    topologicalKrullDimAt m.toPrimeSpectrum =
      ringKrullDim (Localization.AtPrime m.asIdeal) := by
  -- Collapse the infimum over maximal ideals above a closed point to the unique maximal ideal
  -- itself.
  rw [topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over_local
    (k := k) (S := S) m.toPrimeSpectrum]
  letI : Subsingleton { n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal } := by
    refine ⟨fun a b ↦ Subtype.ext <| MaximalSpectrum.ext <| ?_⟩
    have ha : m.asIdeal = a.1.asIdeal :=
      Ideal.IsMaximal.eq_of_le m.isMaximal a.1.isMaximal.ne_top a.2
    have hb : m.asIdeal = b.1.asIdeal :=
      Ideal.IsMaximal.eq_of_le m.isMaximal b.1.isMaximal.ne_top b.2
    exact ha.symm.trans hb
  let e : { n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal } := ⟨m, le_rfl⟩
  simpa [e] using
    (ciInf_subsingleton e fun n ↦ ringKrullDim (Localization.AtPrime n.1.asIdeal))

/-- Helper for Chap10 Lemma 10 114 7: the local topological Krull dimension at every point of a
finite type Cohen-Macaulay affine scheme over a field is a natural number. -/
private theorem existsNatTopologicalKrullDimAtOfFiniteTypeCohenMacaulay
    (x : PrimeSpectrum S) :
    ∃ d : ℕ, topologicalKrullDimAt x = d := by
  classical
  -- Choose a closed point above `x`; this makes the indexing type in Lemma 10.114.5 nonempty.
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal x.asIdeal x.2.1
  let m0 : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal } := ⟨⟨M, hM⟩, hxM⟩
  letI : Nonempty { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal } := ⟨m0⟩
  -- Work in `ℕ∞` by removing the artificial `WithBot` bottom from each local-ring dimension.
  let f : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal } → ℕ∞ :=
    fun m ↦ (ringKrullDim (Localization.AtPrime m.1.asIdeal)).unbotD ⊤
  have hcoe : ∀ m : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal },
      (f m : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime m.1.asIdeal) := by
    intro m
    -- Noetherian local rings have finite Krull dimension, so their dimension is not `⊥`.
    have hnotbot :
        ringKrullDim (Localization.AtPrime m.1.asIdeal) ≠ (⊥ : WithBot ℕ∞) :=
      ringKrullDim_ne_bot
    cases hdim : ringKrullDim (Localization.AtPrime m.1.asIdeal) with
    | bot =>
        exact False.elim (hnotbot hdim)
    | coe e =>
        simp [f, hdim]
  -- Lemma 10.114.5 rewrites the local dimension as the infimum of those local-ring dimensions.
  rw [topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over_local
    (k := k) (S := S) x]
  have hiInf :
      (⨅ m : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal },
          ringKrullDim (Localization.AtPrime m.1.asIdeal)) =
        (⨅ m : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal }, (f m : WithBot ℕ∞)) := by
    simp_rw [← hcoe]
  rw [hiInf]
  -- The infimum of a nonempty family of extended natural numbers is attained.
  obtain ⟨mmin, hmmin⟩ := ENat.exists_eq_iInf f
  have hmin :
      (⨅ m : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal }, (f m : WithBot ℕ∞)) =
        (f mmin : WithBot ℕ∞) := by
    rw [← WithBot.coe_iInf f (OrderBot.bddBelow _)]
    rw [← hmmin]
  rw [hmin]
  -- The chosen local ring has finite Krull dimension, so the attained value is not `⊤`.
  have hf_ne_top : f mmin ≠ ⊤ := by
    intro htopf
    have hdimtop :
        ringKrullDim (Localization.AtPrime mmin.1.asIdeal) = (⊤ : WithBot ℕ∞) := by
      rw [← hcoe mmin, htopf]
      rfl
    exact ringKrullDim_ne_top hdimtop
  cases hfm : f mmin with
  | top =>
      exact False.elim (hf_ne_top hfm)
  | coe n =>
      exact ⟨n, by simp⟩

omit k

/-- Helper for Chap10 Lemma 10 114 7: finite type affine spectra over a field have topological
Krull dimension bounded by a natural number. -/
private theorem existsNatTopologicalKrullDimLeOfFiniteTypeAlgebra
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] :
    ∃ n : ℕ, topologicalKrullDim (PrimeSpectrum S) ≤ n := by
  -- Present `S` as a quotient of a polynomial ring in finitely many variables.
  obtain ⟨n, f, hf⟩ :=
    (iff_quotient_mvPolynomial'' :
      Algebra.FiniteType k S ↔
        ∃ n, ∃ f : MvPolynomial (Fin n) k →ₐ[k] S, Function.Surjective f).mp inferInstance
  refine ⟨n, ?_⟩
  -- Compare topological dimension with ring Krull dimension and use the quotient map.
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have hsurj : Function.Surjective f.toRingHom := hf
  have hle : ringKrullDim S ≤ ringKrullDim (MvPolynomial (Fin n) k) :=
    ringKrullDim_le_of_surjective f.toRingHom hsurj
  -- A polynomial ring in `n` variables over a field has dimension exactly `n`.
  have hpoly : ringKrullDim (MvPolynomial (Fin n) k) = n := by
    simp
  exact hle.trans_eq hpoly

-- Keep the field in the following theorem signatures; otherwise Lean erases the finite-type
-- hypotheses from declarations whose visible proposition only mentions `S`.
include k

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: finite algebra fibers have zero-dimensional local rings. -/
private lemma ringKrullDim_fiberLocalRingAt_eq_zero_of_moduleFinite
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
    [Module.Finite R T] (q : PrimeSpectrum T) :
    ringKrullDim (fiberLocalRingAt R T q) = 0 := by
  -- Finiteness makes the fiber Artinian, hence zero-dimensional.
  have hArt : IsArtinianRing (fiberLocalRingAt R T q) := by
    dsimp [fiberLocalRingAt]
    exact IsArtinianRing.localization_artinian
      ((fiberPrimeAt R T q).asIdeal.primeCompl)
      (Localization.AtPrime (fiberPrimeAt R T q).asIdeal)
  letI : IsArtinianRing (fiberLocalRingAt R T q) := hArt
  have hNoeth : IsNoetherianRing (fiberLocalRingAt R T q) := inferInstance
  letI : IsNoetherianRing (fiberLocalRingAt R T q) := hNoeth
  have hle : Ring.KrullDimLE 0 (fiberLocalRingAt R T q) :=
    (isArtinianRing_iff_krullDimLE_zero (R := fiberLocalRingAt R T q)).mp hArt
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hle

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: under a finite going-down map, local dimensions agree with
the contracted prime. -/
private lemma ringKrullDim_localizationAtPrime_eq_under_of_moduleFinite_hasGoingDown
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
    [IsNoetherianRing R] [IsNoetherianRing T] [Module.Finite R T]
    [Algebra.HasGoingDown R T] (q : PrimeSpectrum T) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) := by
  -- Lemma `10.112.7` gives the fiber summand, and the finite fiber has dimension zero.
  calc
    ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
          ringKrullDim (fiberLocalRingAt R T q) :=
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
        q
    _ = ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) := by
      rw [ringKrullDim_fiberLocalRingAt_eq_zero_of_moduleFinite (R := R) (T := T) q]
      simp

omit [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: a polynomial ring over a field has the same dimension as
each of its maximal localizations. -/
private lemma ringKrullDim_mvPolynomial_eq_localizationAtMaximal
    {n : ℕ} (m : MaximalSpectrum (MvPolynomial (Fin n) k)) :
    ringKrullDim (MvPolynomial (Fin n) k) =
      ringKrullDim (Localization.AtPrime m.asIdeal) := by
  -- Both sides are the number of variables.
  calc
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
      simp
    _ = ringKrullDim (Localization.AtPrime m.asIdeal) :=
      (ringKrullDim_localizationAtMaximal_mvPolynomial (m := m)).symm

omit [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: a finite injective polynomial normalization reduces the
target equality to the polynomial-ring equality. -/
private lemma ringKrullDim_eq_localizationAtMaximal_of_finite_injective_mvPolynomial
    {R : Type v} [CommRing R] [Algebra k R] [IsDomain R]
    {n : ℕ} (g : MvPolynomial (Fin n) k →ₐ[k] R)
    (hg_inj : Function.Injective g) (hg_fin : g.Finite) (m : MaximalSpectrum R) :
    ringKrullDim R = ringKrullDim (Localization.AtPrime m.asIdeal) := by
  let A := MvPolynomial (Fin n) k
  letI : Algebra A R := g.toAlgebra
  have hFinite : Module.Finite A R := by
    simpa [A, AlgHom.Finite, RingHom.Finite] using hg_fin
  letI : Module.Finite A R := hFinite
  letI : Algebra.IsIntegral A R := inferInstance
  have hFaithful : FaithfulSMul A R :=
    (faithfulSMul_iff_algebraMap_injective A R).mpr (by
      simpa [A, RingHom.algebraMap_toAlgebra] using hg_inj)
  letI : FaithfulSMul A R := hFaithful
  have hNoethR : IsNoetherianRing R := IsNoetherianRing.of_finite A R
  letI : IsNoetherianRing R := hNoethR
  letI : Algebra.HasGoingDown A R := inferInstance
  let p : Ideal A := m.asIdeal.under A
  have hpMax : p.IsMaximal := by
    dsimp [p]
    infer_instance
  let pMax : MaximalSpectrum A := ⟨p, hpMax⟩
  have hglobal : ringKrullDim R = ringKrullDim A := by
    exact
      (ringKrullDim_eq_of_injective_algebraMap_of_isIntegral (R := A) (S := R)
        (by simpa [A, RingHom.algebraMap_toAlgebra] using hg_inj)).symm
  have hpoly : ringKrullDim A = ringKrullDim (Localization.AtPrime p) := by
    simpa [A, pMax] using ringKrullDim_mvPolynomial_eq_localizationAtMaximal (k := k) pMax
  have hlocal :
      ringKrullDim (Localization.AtPrime m.asIdeal) =
        ringKrullDim (Localization.AtPrime p) := by
    simpa [A, p] using
      ringKrullDim_localizationAtPrime_eq_under_of_moduleFinite_hasGoingDown
        (R := A) (T := R) m.toPrimeSpectrum
  calc
    ringKrullDim R = ringKrullDim A := hglobal
    _ = ringKrullDim (Localization.AtPrime p) := hpoly
    _ = ringKrullDim (Localization.AtPrime m.asIdeal) := hlocal.symm

omit [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: finite type domains over a field have the same dimension
as each maximal localization. -/
private theorem ringKrullDim_eq_ringKrullDim_localizationAtMaximal_of_finiteType_domain_over_field_local
    {R : Type v} [CommRing R] [Algebra k R] [Algebra.FiniteType k R] [IsDomain R]
    (m : MaximalSpectrum R) :
    ringKrullDim R = ringKrullDim (Localization.AtPrime m.asIdeal) := by
  -- Noether normalization supplies the finite injective polynomial subalgebra used above.
  obtain ⟨n, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg k R
  exact ringKrullDim_eq_localizationAtMaximal_of_finite_injective_mvPolynomial
    (k := k) g hg_inj hg_fin m

/- Domain-style sampling for finite-type Cohen-Macaulay spectra by dimension:
- primary domain: topological dimension strata in `Spec(S)` and clopen/product decompositions of
  affine schemes;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt`,
  `topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over`,
  `topologicalKrullDimAt_closedPoint_eq_ringKrullDim_localizationAtMaximal`,
  `TopologicalSpace.EquidimensionalSpace`,
  `exists_idempotent_partition_of_isCompl_open`,
  `exists_product_decomposition_by_pure_fiber_dimension_of_finitePresentation_flat`;
- best owner abstraction: the source-facing owner is the actual dimension-`d` stratum
  `{x : Spec(S) | topologicalKrullDimAt x = d}`; the product decomposition is only a
  `bridge/view` built from those strata;
- primitive data: the stratum itself, defined from the canonical owner `topologicalKrullDimAt`;
- derived API: clopen-ness, disjointness, equidimensionality, dimension equalities, finiteness of
  the nonempty strata, and the quotient-factor decomposition attached to them.

Source/core/bridge triage:
* `source-facing`: `PrimeSpectrum.dimensionStratum S d`;
* `core/canonical`: `topologicalKrullDimAt`, `EquidimensionalSpace`, and clopen subsets of
  `Spec(S)`;
* `bridge/view`: quotient ideals `I` with `zeroLocus (I : Set S) = dimensionStratum S d`, and the
  resulting `AlgEquiv` product decomposition of `S`.

Semantic search note: `lean_leansearch` confirmed the ambient owner layer around
`topologicalKrullDim`/`IsHomeomorph.topologicalKrullDim_eq`; the final owner choices were then
checked locally against `Definition_5_10_5`, `Lemma_10_24_3`, `Lemma_10_114_4`, and
`Lemma_10_130_8`.
-/

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: a locally constant local-dimension function has clopen
dimension fibers. -/
private theorem isClopen_dimensionStratum_of_isLocallyConstant
    (hloc : IsLocallyConstant fun x : PrimeSpectrum S ↦ topologicalKrullDimAt x) (d : ℕ) :
    IsClopen (PrimeSpectrum.dimensionStratum S d) := by
  -- The dimension stratum is exactly the fiber of the local-dimension function at `d`.
  simpa [PrimeSpectrum.dimensionStratum] using
    hloc.isClopen_fiber ((d : ℕ) : WithBot ℕ∞)

omit [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: an intersecting pair of irreducible components contains a
closed point. -/
private theorem existsMaximalSpectrum_mem_inter_irreducibleComponents
    (Z W : irreducibleComponents (PrimeSpectrum S))
    (hZW : ((Z : Set (PrimeSpectrum S)) ∩ (W : Set (PrimeSpectrum S))).Nonempty) :
    ∃ m : MaximalSpectrum S,
      m.toPrimeSpectrum ∈ (Z : Set (PrimeSpectrum S)) ∧
        m.toPrimeSpectrum ∈ (W : Set (PrimeSpectrum S)) := by
  classical
  -- Finite type algebras over fields have Jacobson spectra, so a nonempty locally closed
  -- intersection of closed components contains a closed point.
  have hJacobson : IsJacobsonRing S :=
    @isJacobsonRing_of_finiteType k S inferInstance inferInstance inferInstance inferInstance
      inferInstance
  letI : IsJacobsonRing S := hJacobson
  letI : JacobsonSpace (PrimeSpectrum S) :=
    PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp inferInstance
  have hclosed :
      IsClosed ((Z : Set (PrimeSpectrum S)) ∩ (W : Set (PrimeSpectrum S))) := by
    exact (isClosed_of_mem_irreducibleComponents (Z : Set (PrimeSpectrum S)) Z.2).inter
      (isClosed_of_mem_irreducibleComponents (W : Set (PrimeSpectrum S)) W.2)
  obtain ⟨x, hxZW, hxclosed⟩ :=
    nonempty_inter_closedPoints hZW hclosed.isLocallyClosed
  have hxMax : x.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp
      (by simpa [closedPoints] using hxclosed)
  let m : MaximalSpectrum S := ⟨x.asIdeal, hxMax⟩
  -- Repackage the selected closed point as a maximal-spectrum point.
  refine ⟨m, ?_, ?_⟩
  · simpa [m] using hxZW.1
  · simpa [m] using hxZW.2

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: the vanishing ideal of an irreducible component of an
affine spectrum is prime. -/
private theorem vanishingIdeal_irreducibleComponent_isPrime
    (Z : irreducibleComponents (PrimeSpectrum S)) :
    (PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum S))).IsPrime := by
  have hclosed : IsClosed (Z : Set (PrimeSpectrum S)) :=
    isClosed_of_mem_irreducibleComponents (Z : Set (PrimeSpectrum S)) Z.2
  have hmin :
      PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum S)) ∈ minimalPrimes S := by
    -- Closed irreducible components correspond to minimal prime ideals under vanishing ideals.
    rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
    simpa [hclosed.closure_eq] using Z.2
  exact Ideal.minimalPrimes_isPrime hmin

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: an irreducible component of an affine spectrum has the
Krull dimension of the quotient by its vanishing ideal. -/
private theorem componentTopologicalKrullDim_eq_ringKrullDim_quotient_vanishingIdeal
    (Z : irreducibleComponents (PrimeSpectrum S)) :
    topologicalKrullDim (Z : Set (PrimeSpectrum S)) =
      ringKrullDim (S ⧸ PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum S))) := by
  let I := PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum S))
  have hzero :
      PrimeSpectrum.zeroLocus (I : Set S) = (Z : Set (PrimeSpectrum S)) := by
    -- The zero locus of the vanishing ideal is the closure, and irreducible components are
    -- already closed.
    calc
      PrimeSpectrum.zeroLocus (I : Set S) = closure (Z : Set (PrimeSpectrum S)) := by
        simpa [I] using
          PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (Z : Set (PrimeSpectrum S))
      _ = (Z : Set (PrimeSpectrum S)) := by
        exact (isClosed_of_mem_irreducibleComponents
          (Z : Set (PrimeSpectrum S)) Z.2).closure_eq
  have hhomeo :
      topologicalKrullDim (PrimeSpectrum (S ⧸ I)) =
        topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set S)) := by
    -- Compare the quotient spectrum with the zero locus cut out by the quotient ideal.
    simpa using
      IsHomeomorph.topologicalKrullDim_eq
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I)
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).isHomeomorph
  calc
    topologicalKrullDim (Z : Set (PrimeSpectrum S)) =
        topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set S)) := by
      rw [hzero]
    _ = topologicalKrullDim (PrimeSpectrum (S ⧸ I)) := hhomeo.symm
    _ = ringKrullDim (S ⧸ I) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (S ⧸ I)

omit k [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
  [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: in a local Cohen-Macaulay ring, quotienting by a
minimal prime preserves Krull dimension. -/
private theorem ringKrullDim_quotient_minimalPrime_eq_of_cohenMacaulay_local
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hCM : Module.CohenMacaulay R R) (q : minimalPrimes R) :
    ringKrullDim (R ⧸ q.1) = ringKrullDim R := by
  letI : q.1.IsPrime := Ideal.minimalPrimes_isPrime q.2
  have hloc : ringKrullDim (Localization.AtPrime q.1) = 0 := by
    have hprimeHeightZero : q.1.primeHeight = 0 :=
      (Ideal.primeHeight_eq_zero_iff).2 q.2
    calc
      ringKrullDim (Localization.AtPrime q.1) = q.1.height := by
        exact IsLocalization.AtPrime.ringKrullDim_eq_height q.1
          (Localization.AtPrime q.1)
      _ = 0 := by
        simpa [Ideal.height_eq_primeHeight] using hprimeHeightZero
  have hdim :=
    ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_cohenMacaulayRing
      hCM q.1
  -- A minimal prime has zero-height localization, so the quotient keeps the full dimension.
  rw [hloc, zero_add] at hdim
  exact hdim.symm

omit k [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
  [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: after passing to a quotient ring, the image of the
complement of a contracted prime is exactly the complement of the quotient prime. -/
private theorem quotient_primeCompl_eq_algebraMapSubmonoid
    {A : Type*} [CommRing A] {p : Ideal A} [p.IsPrime] (I : Ideal A)
    (q : PrimeSpectrum (A ⧸ I))
    (hq : Ideal.comap (Ideal.Quotient.mk I) q.asIdeal = p) :
    Algebra.algebraMapSubmonoid (A ⧸ I) p.primeCompl = q.asIdeal.primeCompl := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    -- Read non-membership in the contracted prime through the quotient contraction formula.
    change y ∉ Ideal.comap (Ideal.Quotient.mk I) q.asIdeal
    simpa [hq] using hy
  · intro hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨y, ?_, rfl⟩
    -- Any representative of a quotient class outside `q` already avoids the contracted prime.
    intro hy
    have hy' : Ideal.Quotient.mk I y ∈ q.asIdeal := by
      change y ∈ Ideal.comap (Ideal.Quotient.mk I) q.asIdeal
      simpa [hq] using hy
    exact hx hy'

omit k [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
  [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: localizing a quotient at a quotient prime identifies with
quotienting the source localization at the contracted prime. -/
private noncomputable def quotientLocalizationAtPrimeAlgEquiv
    {A : Type*} [CommRing A] {p : Ideal A} [p.IsPrime] (I : Ideal A)
    (q : PrimeSpectrum (A ⧸ I))
    (hq : Ideal.comap (Ideal.Quotient.mk I) q.asIdeal = p) :
    ((Localization.AtPrime p) ⧸ Ideal.map (algebraMap A (Localization.AtPrime p)) I) ≃ₐ[A ⧸ I]
      Localization.AtPrime q.asIdeal := by
  let q' : PrimeSpectrum A := PrimeSpectrum.comap (Ideal.Quotient.mk I) q
  have hq' : q'.asIdeal = p := by
    simpa [q', PrimeSpectrum.comap_asIdeal] using hq
  let hloc :
      IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) q'.asIdeal.primeCompl)
        ((Localization.AtPrime q'.asIdeal) ⧸
          Ideal.map (algebraMap A (Localization.AtPrime q'.asIdeal)) I) := by
    infer_instance
  have hSubmonoid :
      Algebra.algebraMapSubmonoid (A ⧸ I) q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
    -- The quotient prime complement is exactly the image of the contracted prime complement.
    simpa [q', PrimeSpectrum.comap_asIdeal] using
      quotient_primeCompl_eq_algebraMapSubmonoid (I := I) (p := q'.asIdeal) q rfl
  let _ :
      IsLocalization q.asIdeal.primeCompl
        ((Localization.AtPrime q'.asIdeal) ⧸
          Ideal.map (algebraMap A (Localization.AtPrime q'.asIdeal)) I) := by
    -- Rewrite the owner localization structure to the canonical localization at `q`.
    exact hSubmonoid ▸ hloc
  -- Both sides are now localizations of `A ⧸ I` at the same prime complement.
  cases hq'
  exact IsLocalization.algEquiv q.asIdeal.primeCompl
    ((Localization.AtPrime q'.asIdeal) ⧸
      Ideal.map (algebraMap A (Localization.AtPrime q'.asIdeal)) I)
    (Localization.AtPrime q.asIdeal)

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: if a minimal prime specializes to a maximal ideal, then its
localization at that maximal ideal remains a minimal prime. -/
-- TODO: Re-derive the localization/minimal-prime propagation from
-- `IsLocalization.minimalPrimes_map` and the specialization hypothesis `q.1 ≤ m.asIdeal`.
private theorem localizedMinimalPrime_mem_minimalPrimes_of_le
    (q : minimalPrimes S) (m : MaximalSpectrum S) (hqm : q.1 ≤ m.asIdeal) :
    Ideal.map (algebraMap S (Localization.AtPrime m.asIdeal)) q.1 ∈
      minimalPrimes (Localization.AtPrime m.asIdeal) := by
  let Rm := Localization.AtPrime m.asIdeal
  letI : q.1.IsPrime := Ideal.minimalPrimes_isPrime q.2
  have hdisj : Disjoint (m.asIdeal.primeCompl : Set S) q.1 := by
    -- Any element inverted in `S_m` avoids `m`, hence cannot lie in the smaller prime `q`.
    refine Set.disjoint_left.mpr fun x hxS hxq ↦ ?_
    exact hxS (hqm hxq)
  have hcomap :
      Ideal.comap (algebraMap S Rm)
        (Ideal.map (algebraMap S Rm) q.1) = q.1 := by
    -- Localization preserves `q` because `q` is disjoint from the prime complement of `m`.
    simpa [Rm] using
      IsLocalization.comap_map_of_isPrime_disjoint m.asIdeal.primeCompl Rm (show q.1.IsPrime by infer_instance)
        hdisj
  have hmap :
      Ideal.map (algebraMap S Rm) q.1 ∈
        (Ideal.map (algebraMap S Rm) (⊥ : Ideal S)).minimalPrimes := by
    -- Rewrite the localized minimal-prime set back to the source ring and use `q ∈ minimalPrimes S`.
    rw [IsLocalization.minimalPrimes_map m.asIdeal.primeCompl Rm (⊥ : Ideal S)]
    change Ideal.comap (algebraMap S Rm)
        (Ideal.map (algebraMap S Rm) q.1) ∈ minimalPrimes S
    simpa [hcomap] using q.2
  simpa [Rm] using hmap

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 114 7: the quotient closed point on a component has the same local
Krull dimension as the original closed point. -/
private theorem closedPointQuotientLocalization_ringKrullDim_eq_localRing
    (I : Ideal S) (m : MaximalSpectrum S) (hI_min : I ∈ minimalPrimes S)
    (hI_le_m : I ≤ m.asIdeal) (qbar : PrimeSpectrum (S ⧸ I))
    (hqbar_comap : Ideal.comap (Ideal.Quotient.mk I) qbar.asIdeal = m.asIdeal) :
    ringKrullDim (Localization.AtPrime qbar.asIdeal) =
      ringKrullDim (Localization.AtPrime m.asIdeal) := by
  let Sm := Localization.AtPrime m.asIdeal
  let qmin : minimalPrimes S := ⟨I, hI_min⟩
  let qloc : minimalPrimes Sm :=
    ⟨Ideal.map (algebraMap S Sm) I,
      localizedMinimalPrime_mem_minimalPrimes_of_le qmin m hI_le_m⟩
  have eLocQuot :
      (Sm ⧸ Ideal.map (algebraMap S Sm) I) ≃ₐ[S ⧸ I] Localization.AtPrime qbar.asIdeal := by
    -- The quotient of the maximal localization is itself the localization of `S / I` at `qbar`.
    simpa [Sm] using
      (quotientLocalizationAtPrimeAlgEquiv (I := I) (p := m.asIdeal) qbar hqbar_comap)
  let hCMloc : Module.CohenMacaulay Sm Sm :=
    localizedRing_cohenMacaulay (R := S) m.toPrimeSpectrum
  -- Compare the quotient-side localization with the localized quotient, then remove the quotient
  -- by the localized minimal prime inside the Cohen-Macaulay local ring `S_m`.
  calc
    ringKrullDim (Localization.AtPrime qbar.asIdeal) =
        ringKrullDim (Sm ⧸ Ideal.map (algebraMap S Sm) I) := by
      exact (ringKrullDim_eq_of_ringEquiv eLocQuot.toRingEquiv).symm
    _ = ringKrullDim Sm :=
      ringKrullDim_quotient_minimalPrime_eq_of_cohenMacaulay_local hCMloc qloc
    _ = ringKrullDim (Localization.AtPrime m.asIdeal) := rfl

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: a quotient prime whose contraction is `m` is the image of
`m` under the quotient map. -/
private theorem quotientPrime_asIdeal_eq_map_of_comap_eq
    {A : Type*} [CommRing A] (I : Ideal A) {m : Ideal A} [m.IsPrime]
    (q : PrimeSpectrum (A ⧸ I))
    (hq : Ideal.comap (Ideal.Quotient.mk I) q.asIdeal = m) :
    q.asIdeal = Ideal.map (Ideal.Quotient.mk I) m := by
  have hI_le_m : I ≤ m := by
    intro x hxI
    rw [← hq]
    change Ideal.Quotient.mk I x ∈ q.asIdeal
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr hxI) ▸ q.asIdeal.zero_mem
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rw [hq, Ideal.comap_map_of_surjective]
  · rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact (sup_eq_left.mpr hI_le_m).symm
  · exact Ideal.Quotient.mk_surjective

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: a quotient prime over a maximal ideal is maximal. -/
private theorem quotientPrime_isMaximal_of_comap_eq_maximal
    {A : Type*} [CommRing A] (I : Ideal A) (m : MaximalSpectrum A)
    (q : PrimeSpectrum (A ⧸ I))
    (hq : Ideal.comap (Ideal.Quotient.mk I) q.asIdeal = m.asIdeal) :
    q.asIdeal.IsMaximal := by
  have hI_le_m : I ≤ m.asIdeal := by
    intro x hxI
    rw [← hq]
    change Ideal.Quotient.mk I x ∈ q.asIdeal
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr hxI) ▸ q.asIdeal.zero_mem
  rw [quotientPrime_asIdeal_eq_map_of_comap_eq (I := I) (m := m.asIdeal) q hq]
  simpa using
    (Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk I) (m := m.asIdeal) Ideal.Quotient.mk_surjective
      (by simpa [Ideal.mk_ker] using hI_le_m))

/-- Helper for Chap10 Lemma 10 114 7: components meeting in a finite type Cohen-Macaulay
spectrum compare with the local Krull dimension at a closed point they contain. -/
-- TODO: Combine the quotient-localization equivalence, minimal-prime localization, and the
-- domain case from Lemma `10.114.4` to identify a component's dimension with the closed-point
-- local ring dimension.
private theorem irreducibleComponent_dimension_eq_closedPoint_localKrullDim
    (Z : irreducibleComponents (PrimeSpectrum S)) (m : MaximalSpectrum S)
    (hmZ : m.toPrimeSpectrum ∈ (Z : Set (PrimeSpectrum S))) :
    topologicalKrullDim (Z : Set (PrimeSpectrum S)) =
      ringKrullDim (Localization.AtPrime m.asIdeal) := by
  let I := PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum S))
  have hzero :
      PrimeSpectrum.zeroLocus (I : Set S) = (Z : Set (PrimeSpectrum S)) := by
    -- The vanishing ideal cuts out the component because irreducible components are closed.
    calc
      PrimeSpectrum.zeroLocus (I : Set S) = closure (Z : Set (PrimeSpectrum S)) := by
        simpa [I] using
          PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (Z : Set (PrimeSpectrum S))
      _ = (Z : Set (PrimeSpectrum S)) := by
        exact (isClosed_of_mem_irreducibleComponents
          (Z : Set (PrimeSpectrum S)) Z.2).closure_eq
  have hmZero : m.toPrimeSpectrum ∈ PrimeSpectrum.zeroLocus (I : Set S) := by
    rw [hzero]
    exact hmZ
  have hI_le_m : I ≤ m.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus m.toPrimeSpectrum (I : Set S)).mp hmZero
  have hI_min : I ∈ minimalPrimes S := by
    -- The vanishing ideal of a closed irreducible component is a minimal prime.
    rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
    simpa [(isClosed_of_mem_irreducibleComponents
      (Z : Set (PrimeSpectrum S)) Z.2).closure_eq] using Z.2
  let qbar : PrimeSpectrum (S ⧸ I) :=
    I.primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨m.toPrimeSpectrum, hI_le_m⟩
  have hqbar_comap :
      Ideal.comap (Ideal.Quotient.mk I) qbar.asIdeal = m.asIdeal := by
    -- The quotient-spectrum point was chosen to contract back to the original closed point.
    exact congrArg
      (fun z : PrimeSpectrum.zeroLocus (R := S) I => z.1.asIdeal)
      (I.primeSpectrumQuotientOrderIsoZeroLocus.apply_symm_apply
        ⟨m.toPrimeSpectrum, hI_le_m⟩)
  let mbar : MaximalSpectrum (S ⧸ I) :=
    ⟨qbar.asIdeal, quotientPrime_isMaximal_of_comap_eq_maximal I m qbar hqbar_comap⟩
  letI : I.IsPrime := by
    simpa [I] using vanishingIdeal_irreducibleComponent_isPrime Z
  letI : IsDomain (S ⧸ I) := Ideal.Quotient.isDomain I
  -- Route correction: first compute the component dimension on the quotient domain, then transport
  -- the quotient closed-point localization back to the original local ring in one dedicated step.
  calc
    topologicalKrullDim (Z : Set (PrimeSpectrum S)) = ringKrullDim (S ⧸ I) :=
      componentTopologicalKrullDim_eq_ringKrullDim_quotient_vanishingIdeal Z
    _ = ringKrullDim (Localization.AtPrime mbar.asIdeal) := by
      exact
        ringKrullDim_eq_ringKrullDim_localizationAtMaximal_of_finiteType_domain_over_field_local
          (k := k) (R := S ⧸ I) mbar
    _ = ringKrullDim (Localization.AtPrime m.asIdeal) := by
      simpa [I, qbar] using
        closedPointQuotientLocalization_ringKrullDim_eq_localRing
          (S := S) I m hI_min hI_le_m qbar hqbar_comap

/-- Helper for Chap10 Lemma 10 114 7: components meeting in a finite type Cohen-Macaulay
spectrum have the same dimension. -/
private theorem topologicalKrullDim_irreducibleComponents_eq_of_nonempty_inter
    (Z W : irreducibleComponents (PrimeSpectrum S))
    (hZW : ((Z : Set (PrimeSpectrum S)) ∩ (W : Set (PrimeSpectrum S))).Nonempty) :
    topologicalKrullDim (Z : Set (PrimeSpectrum S)) =
      topologicalKrullDim (W : Set (PrimeSpectrum S)) := by
  -- Choose a closed point in the intersection and compare both components to the same local ring.
  obtain ⟨m, hmZ, hmW⟩ :=
    existsMaximalSpectrum_mem_inter_irreducibleComponents (k := k) (S := S) Z W hZW
  calc
    topologicalKrullDim (Z : Set (PrimeSpectrum S)) =
        ringKrullDim (Localization.AtPrime m.asIdeal) := by
      exact (@irreducibleComponent_dimension_eq_closedPoint_localKrullDim
        k S inferInstance inferInstance inferInstance inferInstance inferInstance Z m hmZ)
    _ = topologicalKrullDim (W : Set (PrimeSpectrum S)) := by
      exact (@irreducibleComponent_dimension_eq_closedPoint_localKrullDim
        k S inferInstance inferInstance inferInstance inferInstance inferInstance W m hmW).symm

omit k [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 114 7: the component-neighborhood of `x` consists exactly of the
points whose irreducible components all pass through `x`. -/
private lemma mem_componentNeighborhood_iff
    {X : Type*} [TopologicalSpace X] (x y : X) :
    y ∈ (((⋃₀ {Z : Set X | Z ∈ irreducibleComponents X ∧ x ∉ Z})ᶜ : Set X)) ↔
      ∀ Z : irreducibleComponents X, y ∈ (Z : Set X) → x ∈ (Z : Set X) := by
  -- Unpack the complement of the union of bad components into the equivalent universal
  -- containment condition.
  constructor
  · intro hy Z hyZ
    by_contra hxZ
    exact hy (Set.mem_sUnion.2 ⟨(Z : Set X), ⟨Z.2, hxZ⟩, hyZ⟩)
  · intro h hy_bad
    rcases Set.mem_sUnion.1 hy_bad with ⟨Z, hZbad, hyZ⟩
    exact hZbad.2 (h ⟨Z, hZbad.1⟩ hyZ)

/-- Helper for Chap10 Lemma 10 114 7: local dimension is constant on the standard
component-neighborhood once meeting components are known to have equal dimension. -/
private theorem topologicalKrullDimAt_eq_on_componentNeighborhood
    (x y : PrimeSpectrum S)
    (hy : y ∈
      (((⋃₀ {Z : Set (PrimeSpectrum S) |
        Z ∈ irreducibleComponents (PrimeSpectrum S) ∧ x ∉ Z})ᶜ :
          Set (PrimeSpectrum S)))) :
    topologicalKrullDimAt y = topologicalKrullDimAt x := by
  -- Rewrite both local dimensions as suprema over component dimensions through the point.
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through_local
    (k := k) (S := S) y]
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through_local
    (k := k) (S := S) x]
  have hcomponents := (mem_componentNeighborhood_iff x y).1 hy
  refine le_antisymm ?_ ?_
  · -- Components through `y` also pass through `x`, giving the easy supremum inequality.
    refine iSup_le fun Z ↦ ?_
    exact le_iSup_of_le ⟨Z.1, hcomponents Z.1 Z.2⟩ le_rfl
  · -- For the reverse inequality, compare every component through `x` with one component
    -- through `y`; these components meet at `x`.
    let W : irreducibleComponents (PrimeSpectrum S) :=
      ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
    have hyW : y ∈ (W : Set (PrimeSpectrum S)) := by
      have hySelf : y ∈ irreducibleComponent y := mem_irreducibleComponent
      simpa [W] using hySelf
    have hxW : x ∈ (W : Set (PrimeSpectrum S)) := hcomponents W hyW
    refine iSup_le fun Z ↦ ?_
    have hZW : ((Z.1 : Set (PrimeSpectrum S)) ∩ (W : Set (PrimeSpectrum S))).Nonempty :=
      ⟨x, Z.2, hxW⟩
    have hdim :
        topologicalKrullDim (Z.1 : Set (PrimeSpectrum S)) =
          topologicalKrullDim (W : Set (PrimeSpectrum S)) :=
      @topologicalKrullDim_irreducibleComponents_eq_of_nonempty_inter
        k S inferInstance inferInstance inferInstance inferInstance inferInstance Z.1 W hZW
    exact hdim.le.trans (le_iSup_of_le ⟨W, hyW⟩ le_rfl)

/-- Helper for Chap10 Lemma 10 114 7: the local dimension function is locally constant on a
finite type Cohen-Macaulay affine spectrum over a field. -/
private theorem isLocallyConstant_topologicalKrullDimAt_of_finiteType_cohenMacaulay :
    IsLocallyConstant fun x : PrimeSpectrum S ↦ topologicalKrullDimAt x := by
  classical
  -- Around `x`, remove exactly the components not passing through `x`; the preceding helper shows
  -- the local-dimension value is constant on this open component-neighborhood.
  refine (IsLocallyConstant.iff_exists_open _).2 fun x ↦ ?_
  let U : Set (PrimeSpectrum S) :=
    ((⋃₀ {Z : Set (PrimeSpectrum S) |
      Z ∈ irreducibleComponents (PrimeSpectrum S) ∧ x ∉ Z})ᶜ :
        Set (PrimeSpectrum S))
  have hU_open : IsOpen U := by
    letI : IsNoetherianRing k := inferInstance
    letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
    simpa [U] using IsDimensionFunction.isOpen_component_neighborhood x
  have hxU : x ∈ U := by
    exact (mem_componentNeighborhood_iff x x).2 fun _ hxZ ↦ hxZ
  refine ⟨U, hU_open, hxU, ?_⟩
  intro y hy
  exact (@topologicalKrullDimAt_eq_on_componentNeighborhood
    k S inferInstance inferInstance inferInstance inferInstance inferInstance x y
    (by simpa [U] using hy))

-- Proof sketch: for each point `x : Spec(S)`, Lemmas `10.114.5` and `10.114.6` identify
-- `topologicalKrullDimAt x` with the common dimension of the irreducible components through `x`,
-- equivalently with the Krull dimensions of maximal localizations above `x`. In a
-- Cohen-Macaulay finite-type algebra over a field, irreducible components that meet have the same
-- dimension, so the dimension-`d` locus is a union of connected components and hence clopen.
-- Route correction: the direct component-normal-form route is still the main blocker; this pass
-- separates off natural-valuedness and the finite global dimension bound, leaving the remaining
-- clopen proof to the planned minimal-prime/quotient-dimension comparison.
/-- For a finite type Cohen-Macaulay algebra over a field, the dimension-`d` stratum of `Spec(S)`
is open and closed. -/
theorem isClopen_dimensionStratum_of_finiteType_cohenMacaulay (d : ℕ) :
    IsClopen (PrimeSpectrum.dimensionStratum S d) := by
  -- Route correction: avoid the failed global zero-locus normal form; once local dimension is
  -- locally constant, each dimension stratum is a clopen fiber.
  exact isClopen_dimensionStratum_of_isLocallyConstant (S := S)
    (isLocallyConstant_topologicalKrullDimAt_of_finiteType_cohenMacaulay
      (k := k) (S := S)) d

/-- Helper for Chap10 Lemma 10 114 7: an ambient irreducible component through a point of the
dimension-`d` stratum has topological Krull dimension `d`. -/
private theorem topologicalKrullDim_irreducibleComponent_eq_of_mem_dimensionStratum
    (Z : irreducibleComponents (PrimeSpectrum S)) {x : PrimeSpectrum S} {d : ℕ}
    (hxZ : x ∈ (Z : Set (PrimeSpectrum S)))
    (hx : x ∈ PrimeSpectrum.dimensionStratum S d) :
    topologicalKrullDim (Z : Set (PrimeSpectrum S)) = d := by
  -- Rewrite the local dimension at `x` as the supremum of all component dimensions through `x`.
  have hlocalSup :=
    topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through_local
      (k := k) (S := S) x
  have hfiber : topologicalKrullDimAt x = d :=
    (PrimeSpectrum.mem_dimensionStratum S x d).mp hx
  have hsup_eq_component :
      (⨆ W : { W : irreducibleComponents (PrimeSpectrum S) //
          x ∈ (W : Set (PrimeSpectrum S)) },
        topologicalKrullDim (W.1 : Set (PrimeSpectrum S))) =
      topologicalKrullDim (Z : Set (PrimeSpectrum S)) := by
    -- Every component through `x` meets `Z` at `x`, so all terms in the supremum equal `Z`'s
    -- dimension; the component `Z` itself supplies the reverse inequality.
    refine le_antisymm ?_ ?_
    · refine iSup_le fun W ↦ ?_
      have hWZ : ((W.1 : Set (PrimeSpectrum S)) ∩ (Z : Set (PrimeSpectrum S))).Nonempty :=
        ⟨x, W.2, hxZ⟩
      exact
        (@topologicalKrullDim_irreducibleComponents_eq_of_nonempty_inter
          k S inferInstance inferInstance inferInstance inferInstance inferInstance W.1 Z hWZ).le
    · exact le_iSup_of_le ⟨Z, hxZ⟩ le_rfl
  calc
    topologicalKrullDim (Z : Set (PrimeSpectrum S)) =
        (⨆ W : { W : irreducibleComponents (PrimeSpectrum S) //
            x ∈ (W : Set (PrimeSpectrum S)) },
          topologicalKrullDim (W.1 : Set (PrimeSpectrum S))) := hsup_eq_component.symm
    _ = topologicalKrullDimAt x := hlocalSup.symm
    _ = d := hfiber

/-- Helper for Chap10 Lemma 10 114 7: an ambient irreducible component meeting the
dimension-`d` stratum is contained in that stratum. -/
private theorem irreducibleComponent_subset_dimensionStratum_of_mem
    {d : ℕ} (Z : irreducibleComponents (PrimeSpectrum S)) {x : PrimeSpectrum S}
    (hxZ : x ∈ (Z : Set (PrimeSpectrum S)))
    (hx : x ∈ PrimeSpectrum.dimensionStratum S d) :
    (Z : Set (PrimeSpectrum S)) ⊆ PrimeSpectrum.dimensionStratum S d := by
  have hdimZ :
      topologicalKrullDim (Z : Set (PrimeSpectrum S)) = d :=
    topologicalKrullDim_irreducibleComponent_eq_of_mem_dimensionStratum
      (k := k) (S := S) Z hxZ hx
  intro y hyZ
  -- Rewrite the local dimension at `y` as the supremum over the ambient components through `y`.
  rw [PrimeSpectrum.mem_dimensionStratum]
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through_local
    (k := k) (S := S) y]
  refine le_antisymm ?_ ?_
  · -- Any component through `y` meets `Z` at `y`, so it has the same dimension as `Z`.
    refine iSup_le fun W ↦ ?_
    have hWZ : ((W.1 : Set (PrimeSpectrum S)) ∩ (Z : Set (PrimeSpectrum S))).Nonempty :=
      ⟨y, W.2, hyZ⟩
    exact le_of_eq
      ((@topologicalKrullDim_irreducibleComponents_eq_of_nonempty_inter
        k S inferInstance inferInstance inferInstance inferInstance inferInstance W.1 Z hWZ).trans
        hdimZ)
  · -- The component `Z` itself contributes the reverse inequality to the supremum.
    exact le_iSup_of_le ⟨Z, hyZ⟩ (le_of_eq hdimZ.symm)

/-- Helper for Chap10 Lemma 10 114 7: every irreducible component of a nonempty dimension
stratum has topological Krull dimension equal to the stratum index. -/
private theorem topologicalKrullDim_subtypeComponent_dimensionStratum_eq
    {d : ℕ} (C : irreducibleComponents (PrimeSpectrum.dimensionStratum S d)) :
    topologicalKrullDim (C : Set (PrimeSpectrum.dimensionStratum S d)) = d := by
  have hstratumClopen :
      IsClopen (PrimeSpectrum.dimensionStratum S d) :=
    isClopen_dimensionStratum_of_finiteType_cohenMacaulay (k := k) (S := S) d
  obtain ⟨x, hxC⟩ := C.2.1.1
  let s : Set (PrimeSpectrum S) :=
    Subtype.val '' (C : Set (PrimeSpectrum.dimensionStratum S d))
  have hs_irred : IsIrreducible s := by
    -- The image of a subtype component is still irreducible in the ambient spectrum.
    refine ⟨?_, C.2.1.2.image Subtype.val continuous_subtype_val.continuousOn⟩
    exact ⟨(x : PrimeSpectrum S), ⟨x, hxC, rfl⟩⟩
  obtain ⟨Zset, hZcomp, hs_subset⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible s hs_irred
  let Z : irreducibleComponents (PrimeSpectrum S) := ⟨Zset, hZcomp⟩
  have hxZ : (x : PrimeSpectrum S) ∈ (Z : Set (PrimeSpectrum S)) := by
    exact hs_subset ⟨x, hxC, rfl⟩
  have hZsubset :
      (Z : Set (PrimeSpectrum S)) ⊆ PrimeSpectrum.dimensionStratum S d :=
    irreducibleComponent_subset_dimensionStratum_of_mem
      (k := k) (S := S) Z hxZ x.2
  let Zsub : Set (PrimeSpectrum.dimensionStratum S d) :=
    Subtype.val ⁻¹' (Z : Set (PrimeSpectrum S))
  have hIncl :
      IsOpenEmbedding (Subtype.val : PrimeSpectrum.dimensionStratum S d → PrimeSpectrum S) :=
    hstratumClopen.2.isOpenEmbedding_subtypeVal
  have hZsub_comp :
      Zsub ∈ irreducibleComponents (PrimeSpectrum.dimensionStratum S d) := by
    -- Pull the ambient component back along the open embedding of the stratum.
    have hmeet :
        (((Z : Set (PrimeSpectrum S)) ∩
            Set.range (Subtype.val :
              PrimeSpectrum.dimensionStratum S d → PrimeSpectrum S))).Nonempty := by
      exact ⟨(x : PrimeSpectrum S), hxZ, ⟨x, rfl⟩⟩
    simpa [Zsub] using preimage_mem_irreducibleComponents Z.2 hIncl hmeet
  have hC_subset_Zsub : (C : Set (PrimeSpectrum.dimensionStratum S d)) ⊆ Zsub := by
    intro y hyC
    change (y : PrimeSpectrum S) ∈ (Z : Set (PrimeSpectrum S))
    exact hs_subset ⟨y, hyC, rfl⟩
  have hZsub_subset_C : Zsub ⊆ (C : Set (PrimeSpectrum.dimensionStratum S d)) := by
    -- Maximality of `Zsub` in the stratum forces it back inside the original subtype component.
    exact C.2.2 hZsub_comp.1 hC_subset_Zsub
  have hCeqZsub :
      (C : Set (PrimeSpectrum.dimensionStratum S d)) = Zsub :=
    Set.Subset.antisymm hC_subset_Zsub hZsub_subset_C
  have hhomeo :
      topologicalKrullDim Zsub = topologicalKrullDim (Z : Set (PrimeSpectrum S)) := by
    let eZ : Zsub ≃ₜ (Z : Set (PrimeSpectrum S)) :=
      hIncl.isEmbedding.homeomorphOfSubsetRange fun y hy ↦
        ⟨⟨y, hZsubset hy⟩, rfl⟩
    -- The pulled-back subtype component and its ambient owner are homeomorphic.
    simpa [eZ] using IsHomeomorph.topologicalKrullDim_eq eZ eZ.isHomeomorph
  -- Replace the subtype component by the ambient component that contains its image.
  calc
    topologicalKrullDim (C : Set (PrimeSpectrum.dimensionStratum S d)) =
        topologicalKrullDim Zsub := by
      rw [hCeqZsub]
    _ = topologicalKrullDim (Z : Set (PrimeSpectrum S)) := hhomeo
    _ = d :=
      topologicalKrullDim_irreducibleComponent_eq_of_mem_dimensionStratum
        (k := k) (S := S) Z hxZ x.2

-- Proof sketch: every irreducible component of the clopen stratum inherits the same local
-- dimension value `d`, so the stratum is equidimensional; if the stratum is nonempty, its common
-- topological Krull dimension is exactly `d`.
/-- Every nonempty dimension-`d` stratum of `Spec(S)` is equidimensional. -/
theorem equidimensionalSpace_dimensionStratum_of_finiteType_cohenMacaulay {d : ℕ}
    (_hd : (PrimeSpectrum.dimensionStratum S d).Nonempty) :
    EquidimensionalSpace (PrimeSpectrum.dimensionStratum S d) := by
  -- Once each subtype component has the shared dimension `d`, equidimensionality is formal.
  refine ⟨?_⟩
  intro C D
  calc
    topologicalKrullDim C = d :=
      @topologicalKrullDim_subtypeComponent_dimensionStratum_eq
        k S inferInstance inferInstance inferInstance inferInstance inferInstance d C
    _ = topologicalKrullDim D :=
      (@topologicalKrullDim_subtypeComponent_dimensionStratum_eq
        k S inferInstance inferInstance inferInstance inferInstance inferInstance d D).symm

omit k [Field k] in
/-- Helper for Chap10 Lemma 10 114 7: passing to an open subspace does not change the local
topological Krull dimension at a point. -/
-- TODO: Replace the broken ad hoc subset-range transport with the stable two-chart pattern from
-- `Chap05.Lemma_5_18_5`, comparing the open subspace neighborhood with its ambient trace.
private theorem topologicalKrullDimAt_subtype_eq_of_isOpen
    {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U) (x : U) :
    topologicalKrullDimAt x = topologicalKrullDimAt (x : X) := by
  apply le_antisymm
  · rcases exists_openNhdsOf_topologicalKrullDimAt_eq (x : X) with ⟨W, hW⟩
    let V : OpenNhdsOf x :=
      ⟨⟨Subtype.val ⁻¹' (W : Set X), W.isOpen.preimage continuous_subtype_val⟩, W.mem⟩
    let e₂ : V ≃ₜ (((U ∩ (W : Set X)) : Set X)) :=
      (Homeomorph.setCongr <| by
          ext y
          constructor
          · intro hy
            exact ⟨y.2, hy⟩
          · intro hy
            exact hy.2).trans
        (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange fun y hy ↦
          ⟨⟨y, hy.1⟩, rfl⟩)
    let e₁ : { y : W | (y : X) ∈ U } ≃ₜ (((U ∩ (W : Set X)) : Set X)) :=
      (Homeomorph.setCongr <| by
          ext y
          constructor
          · intro hy
            exact ⟨hy, y.2⟩
          · intro hy
            exact hy.1).trans
        (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange fun y hy ↦
          ⟨⟨y, hy.2⟩, rfl⟩)
    have hsubspace :
        topologicalKrullDim { y : W | (y : X) ∈ U } ≤ topologicalKrullDim W :=
      topologicalKrullDim_subspace_le W { y : W | (y : X) ∈ U }
    have heq₁ :
        topologicalKrullDim (((U ∩ (W : Set X)) : Set X)) =
          topologicalKrullDim { y : W | (y : X) ∈ U } := by
      -- Compare the ambient intersection with the corresponding subspace of the neighborhood `W`.
      simpa [e₁] using (IsHomeomorph.topologicalKrullDim_eq e₁ e₁.isHomeomorph).symm
    have heq₂ :
        topologicalKrullDim V = topologicalKrullDim (((U ∩ (W : Set X)) : Set X)) := by
      -- The preimage neighborhood inside `U` is homeomorphic to the ambient trace `U ∩ W`.
      simpa [e₂] using IsHomeomorph.topologicalKrullDim_eq e₂ e₂.isHomeomorph
    calc
      topologicalKrullDimAt x ≤ topologicalKrullDim V := topologicalKrullDimAt_le x V
      _ = topologicalKrullDim (((U ∩ (W : Set X)) : Set X)) := heq₂
      _ = topologicalKrullDim { y : W | (y : X) ∈ U } := heq₁
      _ ≤ topologicalKrullDim W := hsubspace
      _ = topologicalKrullDimAt (x : X) := hW.symm
  · rcases exists_openNhdsOf_topologicalKrullDimAt_eq x with ⟨V, hV⟩
    let W : OpenNhdsOf (x : X) :=
      ⟨⟨Subtype.val '' (V : Set U), hU.isOpenEmbedding_subtypeVal.isOpenMap _ V.isOpen⟩,
        ⟨x, V.mem, rfl⟩⟩
    let hImage : V ≃ₜ Subtype.val '' (V : Set U) :=
      (hU.isOpenEmbedding_subtypeVal.isEmbedding).homeomorphImage (V : Set U)
    have hdim : topologicalKrullDim W = topologicalKrullDim V := by
      -- Push the realizing neighborhood in `U` forward to an ambient neighborhood of the same
      -- topological Krull dimension.
      simpa [W, hImage] using
        (IsHomeomorph.topologicalKrullDim_eq hImage hImage.isHomeomorph).symm
    calc
      topologicalKrullDimAt (x : X) ≤ topologicalKrullDim W := topologicalKrullDimAt_le (x : X) W
      _ = topologicalKrullDim V := hdim
      _ = topologicalKrullDimAt x := hV.symm

omit k [Field k] in
/-- Helper for Chap10 Lemma 10 114 7: local topological Krull dimension is invariant under a
homeomorphism. -/
private theorem topologicalKrullDimAt_homeomorph_eq
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt (e x) = topologicalKrullDimAt x := by
  apply le_antisymm
  · rcases exists_openNhdsOf_topologicalKrullDimAt_eq x with ⟨U, hU⟩
    let V : OpenNhdsOf (e x) :=
      ⟨⟨e '' (U : Set X), e.isOpenMap _ U.isOpen⟩, ⟨x, U.mem, rfl⟩⟩
    let hEmbedding : IsEmbedding e := e.isEmbedding
    let hImage : U ≃ₜ e '' (U : Set X) := hEmbedding.homeomorphImage (U : Set X)
    have hdim :
        topologicalKrullDim V = topologicalKrullDim U := by
      -- Compare the chosen neighborhoods via the homeomorphism onto its image.
      simpa [V, hImage] using (IsHomeomorph.topologicalKrullDim_eq hImage hImage.isHomeomorph).symm
    calc
      topologicalKrullDimAt (e x) ≤ topologicalKrullDim V :=
        topologicalKrullDimAt_le (e x) V
      _ = topologicalKrullDim U := hdim
      _ = topologicalKrullDimAt x := hU.symm
  · rcases exists_openNhdsOf_topologicalKrullDimAt_eq (e x) with ⟨V, hV⟩
    let U : OpenNhdsOf x :=
      ⟨⟨e.symm '' (V : Set Y), e.symm.isOpenMap _ V.isOpen⟩,
        ⟨e x, V.mem, e.symm_apply_apply x⟩⟩
    let hEmbedding : IsEmbedding e.symm := e.symm.isEmbedding
    let hImage : V ≃ₜ e.symm '' (V : Set Y) := hEmbedding.homeomorphImage (V : Set Y)
    have hdim :
        topologicalKrullDim U = topologicalKrullDim V := by
      -- Apply the same image comparison to the inverse homeomorphism.
      simpa [U, hImage] using (IsHomeomorph.topologicalKrullDim_eq hImage hImage.isHomeomorph).symm
    calc
      topologicalKrullDimAt x ≤ topologicalKrullDim U :=
        topologicalKrullDimAt_le x U
      _ = topologicalKrullDim V := hdim
      _ = topologicalKrullDimAt (e x) := hV.symm

/-- Helper for Chap10 Lemma 10 114 7: a nonempty dimension stratum has topological Krull
dimension equal to its index once its subtype components have that common dimension. -/
-- TODO: Use equidimensionality of the stratum and the local-dimension invariance for open
-- subspaces to compare the stratum dimension with any ambient point it contains.
private theorem topologicalKrullDim_dimensionStratum_eq_of_nonempty {d : ℕ}
    (hd : (PrimeSpectrum.dimensionStratum S d).Nonempty) :
    topologicalKrullDim (PrimeSpectrum.dimensionStratum S d) = d := by
  have hstratumOpen :
      IsOpen (PrimeSpectrum.dimensionStratum S d) :=
    (isClopen_dimensionStratum_of_finiteType_cohenMacaulay (k := k) (S := S) d).2
  have hlocal :
      ∀ x : PrimeSpectrum.dimensionStratum S d, topologicalKrullDimAt x = d := by
    intro x
    -- Every point of the stratum has ambient local dimension `d`, and openness lets us transport
    -- that value back to the subspace.
    calc
      topologicalKrullDimAt x =
          topologicalKrullDimAt ((x : PrimeSpectrum.dimensionStratum S d) : PrimeSpectrum S) :=
        topologicalKrullDimAt_subtype_eq_of_isOpen hstratumOpen x
      _ = d := (PrimeSpectrum.mem_dimensionStratum S (x : PrimeSpectrum S) d).mp x.2
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
  refine le_antisymm ?_ ?_
  · -- The upper bound is pointwise because the local dimension is constant on the whole stratum.
    refine iSup_le fun x ↦ ?_
    exact le_of_eq (hlocal x)
  · rcases hd with ⟨x, hx⟩
    let x' : PrimeSpectrum.dimensionStratum S d := ⟨x, hx⟩
    -- A chosen point of the nonempty stratum supplies the reverse inequality.
    exact le_iSup_of_le x' (le_of_eq (hlocal x').symm)

/-- Helper for Chap10 Lemma 10 114 7: finite type affine spectra over a field have natural-valued
global Krull dimension. -/
-- Route correction: this helper is blocked by a statement issue, not a missing proof. Lean
-- `CommRing` permits subsingleton rings, and then `ringKrullDim S = ⊥`, so the claimed
-- natural-valued conclusion is false without an added nontriviality hypothesis.
private theorem existsNatRingKrullDim_of_finiteTypeAlgebra [Nontrivial S] :
    ∃ n : ℕ, ringKrullDim S = n := by
  refine ⟨((ringKrullDim S).unbotD 0).toNat, ?_⟩
  have hbot : ringKrullDim S ≠ ⊥ := by
    obtain ⟨M, hM, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal S) bot_ne_top
    let m : MaximalSpectrum S := ⟨M, hM⟩
    obtain ⟨d, hd⟩ :=
      existsNatTopologicalKrullDimAtOfFiniteTypeCohenMacaulay (k := k) (S := S) m.toPrimeSpectrum
    have hle :
        (d : WithBot ℕ∞) ≤ ringKrullDim S := by
      let U : OpenNhdsOf m.toPrimeSpectrum := ⊤
      have hU : topologicalKrullDim U ≤ topologicalKrullDim (PrimeSpectrum S) := by
        simpa [U] using
          topologicalKrullDim_subspace_le (PrimeSpectrum S) (Set.univ : Set (PrimeSpectrum S))
      calc
        (d : WithBot ℕ∞) = topologicalKrullDimAt m.toPrimeSpectrum := hd.symm
        _ ≤ topologicalKrullDim (PrimeSpectrum S) := (topologicalKrullDimAt_le m.toPrimeSpectrum U).trans hU
        _ = ringKrullDim S := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim S
    intro hs
    have : (d : WithBot ℕ∞) ≤ (⊥ : WithBot ℕ∞) := by simpa [hs] using hle
    simpa using this
  have htop : ringKrullDim S ≠ ⊤ := by
    obtain ⟨n, hn⟩ := existsNatTopologicalKrullDimLeOfFiniteTypeAlgebra (k := k) (S := S)
    intro hs
    have : (⊤ : WithBot ℕ∞) ≤ n := by
      simpa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim S, hs] using hn
    have hnot : ¬ ((n : WithBot ℕ∞) = ⊤) := by
      intro h
      cases h
    exact hnot (by simpa using this)
  -- Repackage the finite Krull dimension of `S` as an actual natural number.
  cases hs : ringKrullDim S with
  | bot =>
      exact (hbot hs).elim
  | coe e =>
      have he_ne_top : e ≠ ⊤ := by
        intro he_top
        exact htop <| by simp [hs, he_top]
      simpa [hs] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat he_ne_top).symm

/-- Helper for Chap10 Lemma 10 114 7: if a quotient factor cuts out the dimension-`d` stratum,
then every maximal ideal of that quotient has height `d`. -/
-- TODO: Push a maximal ideal of `S ⧸ I` across the quotient-spectrum homeomorphism, rewrite the
-- resulting closed point into the stratum, and finish with the closed-point local-dimension
-- formula plus `IsLocalization.AtPrime.ringKrullDim_eq_height`.
private theorem height_eq_index_of_dimensionStratum_quotient
    (I : Ideal S) {d : ℕ}
    (hstratum : PrimeSpectrum.dimensionStratum S d = zeroLocus (I : Set S)) :
    ∀ m : MaximalSpectrum (S ⧸ I), m.asIdeal.height = (d : ℕ) := by
  intro m
  let hquot :
      PrimeSpectrum (S ⧸ I) ≃ₜ PrimeSpectrum.dimensionStratum S d :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).trans
      (Homeomorph.setCongr hstratum.symm)
  have hstratumOpen :
      IsOpen (PrimeSpectrum.dimensionStratum S d) :=
    (isClopen_dimensionStratum_of_finiteType_cohenMacaulay (k := k) (S := S) d).2
  have hlocal :
      topologicalKrullDimAt m.toPrimeSpectrum = d := by
    -- Transport the closed point of the quotient spectrum to the dimension stratum of `Spec(S)`.
    calc
      topologicalKrullDimAt m.toPrimeSpectrum =
          topologicalKrullDimAt (hquot m.toPrimeSpectrum) := by
        exact (topologicalKrullDimAt_homeomorph_eq hquot m.toPrimeSpectrum).symm
      _ =
          topologicalKrullDimAt
            (((hquot m.toPrimeSpectrum : PrimeSpectrum.dimensionStratum S d) :
              PrimeSpectrum S)) :=
        topologicalKrullDimAt_subtype_eq_of_isOpen hstratumOpen (hquot m.toPrimeSpectrum)
      _ = d := by
        exact
          (PrimeSpectrum.mem_dimensionStratum S
            ((hquot m.toPrimeSpectrum : PrimeSpectrum.dimensionStratum S d) :
              PrimeSpectrum S) d).mp
            (hquot m.toPrimeSpectrum).2
  have hclosed :
      topologicalKrullDimAt m.toPrimeSpectrum =
        ringKrullDim (Localization.AtPrime m.asIdeal) := by
    rw [topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over
      (k := k) (S := S ⧸ I) m.toPrimeSpectrum]
    letI : Subsingleton { n : MaximalSpectrum (S ⧸ I) // m.asIdeal ≤ n.asIdeal } := by
      refine ⟨fun a b ↦ Subtype.ext <| MaximalSpectrum.ext <| ?_⟩
      have ha : m.asIdeal = a.1.asIdeal :=
        Ideal.IsMaximal.eq_of_le m.isMaximal a.1.isMaximal.ne_top a.2
      have hb : m.asIdeal = b.1.asIdeal :=
        Ideal.IsMaximal.eq_of_le m.isMaximal b.1.isMaximal.ne_top b.2
      exact ha.symm.trans hb
    let e : { n : MaximalSpectrum (S ⧸ I) // m.asIdeal ≤ n.asIdeal } := ⟨m, le_rfl⟩
    simpa [e] using
      (ciInf_subsingleton e fun n ↦ ringKrullDim (Localization.AtPrime n.1.asIdeal))
  -- Closed points identify local topological dimension with the height of the corresponding
  -- maximal localization.
  have hheight :
      (m.asIdeal.height : WithBot ℕ∞) = d := by
    calc
      (m.asIdeal.height : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime m.asIdeal) := by
        exact (IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal
          (Localization.AtPrime m.asIdeal)).symm
      _ = d := hclosed.symm.trans hlocal
  exact_mod_cast hheight

/-- If the dimension-`d` stratum of `Spec(S)` is nonempty, then its topological Krull dimension
is `d`. -/
theorem topologicalKrullDim_dimensionStratum_of_finiteType_cohenMacaulay {d : ℕ}
    (hd : (PrimeSpectrum.dimensionStratum S d).Nonempty) :
    topologicalKrullDim (PrimeSpectrum.dimensionStratum S d) = d := by
  -- The remaining work is isolated in the reusable subtype-component dimension bridge.
  exact @topologicalKrullDim_dimensionStratum_eq_of_nonempty
    k S inferInstance inferInstance inferInstance inferInstance inferInstance d hd

-- Proof sketch: every point of `Spec(S)` lies in the unique stratum corresponding to its local
-- Krull dimension, and only finitely many local dimensions occur because `Spec(S)` has finitely
-- many irreducible components.
omit [CohenMacaulayRing S] in
/-- Only finitely many dimension strata of `Spec(S)` are nonempty. -/
theorem finite_nonempty_dimensionStrata_of_finiteType_cohenMacaulay :
    { d : ℕ | (PrimeSpectrum.dimensionStratum S d).Nonempty }.Finite := by
  -- The set-theoretic helper turns the finite global dimension bound into finiteness of fibers.
  have hfinite : ∃ n : ℕ, topologicalKrullDim (PrimeSpectrum S) ≤ n :=
    @existsNatTopologicalKrullDimLeOfFiniteTypeAlgebra k S inferInstance inferInstance
      inferInstance inferInstance
  obtain ⟨n, hbound⟩ := hfinite
  exact PrimeSpectrum.finite_nonempty_dimensionStrata_of_topologicalKrullDim_le S hbound

/-- The dimension strata cover `Spec(S)`. -/
theorem iUnion_dimensionStratum_of_finiteType_cohenMacaulay :
    (⋃ d : ℕ, PrimeSpectrum.dimensionStratum S d) = Set.univ := by
  -- The cover is exactly the assertion that every local dimension is a natural value.
  rw [PrimeSpectrum.iUnion_dimensionStratum_eq_univ_iff]
  intro x
  -- The local dimension formula reduces natural-valuedness to finite-dimensional local rings.
  exact @existsNatTopologicalKrullDimAtOfFiniteTypeCohenMacaulay
    k S inferInstance inferInstance inferInstance inferInstance inferInstance x

/-- Helper for Chap10 Lemma 10 114 7: the nonempty dimension strata come from a complete
orthogonal family of idempotents. -/
private theorem exists_completeOrthogonalIdempotents_dimensionStrata
    (D : Finset ℕ)
    (hD : ∀ d : ℕ, d ∈ D ↔ (PrimeSpectrum.dimensionStratum S d).Nonempty) :
    ∃ elem : D → S,
      CompleteOrthogonalIdempotents elem ∧
        ∀ d : D, PrimeSpectrum.dimensionStratum S (d : ℕ) =
          (PrimeSpectrum.basicOpen (elem d) : Set (PrimeSpectrum S)) := by
  let U : D → Clopens (PrimeSpectrum S) := fun d ↦
    Clopens.mk
      (PrimeSpectrum.dimensionStratum S (d : ℕ))
      (isClopen_dimensionStratum_of_finiteType_cohenMacaulay
        (k := k) (S := S) (d : ℕ))
  have hDisjoint :
      Pairwise fun i j : D ↦ Disjoint
        (U i : Set (PrimeSpectrum S)) (U j : Set (PrimeSpectrum S)) := by
    intro i j hij
    exact PrimeSpectrum.disjoint_dimensionStratum_of_ne (S := S) fun hEq ↦
      hij <| Subtype.ext hEq
  have hCover : (⋃ d : D, (U d : Set (PrimeSpectrum S))) = Set.univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have hxall : x ∈ ⋃ d : ℕ, PrimeSpectrum.dimensionStratum S d := by
        simpa [iUnion_dimensionStratum_of_finiteType_cohenMacaulay (k := k) (S := S)] using
          (Set.mem_univ x)
      obtain ⟨d, hxd⟩ := Set.mem_iUnion.1 hxall
      let dd : D := ⟨d, (hD d).2 ⟨x, hxd⟩⟩
      refine Set.mem_iUnion.2 ⟨dd, ?_⟩
      change x ∈ PrimeSpectrum.dimensionStratum S ((dd : D) : ℕ)
      simpa using hxd
  let idem : D → {e : S // IsIdempotentElem e} := fun d ↦
    PrimeSpectrum.isIdempotentElemEquivClopens.symm (U d)
  let elem : D → S := fun d ↦ (idem d).1
  have hbasicOpens : ∀ d : D, PrimeSpectrum.basicOpen (elem d) = (U d).toOpens := by
    intro d
    simpa [elem, idem] using
      PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm (U d)
  have hOrthogonal : OrthogonalIdempotents elem := by
    refine ⟨fun d ↦ (idem d).2, ?_⟩
    intro i j hij
    have hInfBot : (U i ⊓ U j : Clopens (PrimeSpectrum S)) = ⊥ := by
      apply Clopens.ext
      ext x
      simp only [Clopens.coe_inf, Set.mem_inter_iff, Clopens.coe_bot, Set.mem_empty_iff_false]
      constructor
      · intro hx
        exact (Set.disjoint_left.1 (hDisjoint hij)) hx.1 hx.2
      · intro hx
        cases hx
    have hZeroOpen : PrimeSpectrum.basicOpen (0 : S) = (⊥ : Clopens (PrimeSpectrum S)).toOpens := by
      ext x
      constructor
      · intro hx
        exact False.elim (by simpa [PrimeSpectrum.mem_basicOpen] using hx)
      · intro hx
        exact False.elim (by simpa using hx)
    have hEqOpen : PrimeSpectrum.basicOpen (elem i * elem j) = PrimeSpectrum.basicOpen (0 : S) := by
      calc
        PrimeSpectrum.basicOpen (elem i * elem j)
            = PrimeSpectrum.basicOpen (elem i) ⊓ PrimeSpectrum.basicOpen (elem j) :=
          PrimeSpectrum.basicOpen_mul _ _
        _ = (U i).toOpens ⊓ (U j).toOpens := by rw [hbasicOpens i, hbasicOpens j]
        _ = (⊥ : Clopens (PrimeSpectrum S)).toOpens := by
          change ((U i ⊓ U j : Clopens (PrimeSpectrum S)).toOpens =
            (⊥ : Clopens (PrimeSpectrum S)).toOpens)
          exact congrArg Clopens.toOpens hInfBot
        _ = PrimeSpectrum.basicOpen (0 : S) := hZeroOpen.symm
    exact PrimeSpectrum.basicOpen_injOn_isIdempotentElem
      ((idem i).2.mul (idem j).2) IsIdempotentElem.zero hEqOpen
  have hprodIdemFinset :
      ∀ s : Finset D, IsIdempotentElem (∏ d ∈ s, (1 - elem d)) := by
    intro s
    induction s using Finset.cons_induction with
    | empty =>
        simpa using (IsIdempotentElem.one : IsIdempotentElem (1 : S))
    | cons a s ha hs =>
        simpa [Finset.prod_insert ha] using ((idem a).2.one_sub).mul hs
  have hprodIdem : IsIdempotentElem (∏ d : D, (1 - elem d)) := by
    simpa using hprodIdemFinset Finset.univ
  have hUcomplbasic :
      ∀ d : D, PrimeSpectrum.basicOpen (1 - elem d) = ((U d)ᶜ).toOpens := by
    intro d
    have hComplIdem :
        PrimeSpectrum.isIdempotentElemEquivClopens.symm ((U d)ᶜ) =
          ⟨1 - elem d, (idem d).2.one_sub⟩ := by
      simpa [elem, idem] using
        (PrimeSpectrum.isIdempotentElemEquivClopens_symm_compl (U d))
    calc
      PrimeSpectrum.basicOpen (1 - elem d)
          = PrimeSpectrum.basicOpen
              (PrimeSpectrum.isIdempotentElemEquivClopens.symm ((U d)ᶜ)).1 := by
              rw [hComplIdem]
      _ = ((U d)ᶜ).toOpens :=
        PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm ((U d)ᶜ)
  have hprodZero : ∏ d : D, (1 - elem d) = 0 := by
    have hZeroOpen : PrimeSpectrum.basicOpen (0 : S) = (⊥ : Clopens (PrimeSpectrum S)).toOpens := by
      ext x
      constructor
      · intro hx
        exact False.elim (by simpa [PrimeSpectrum.mem_basicOpen] using hx)
      · intro hx
        exact False.elim (by simpa using hx)
    have hEqOpen : PrimeSpectrum.basicOpen (∏ d : D, (1 - elem d)) = PrimeSpectrum.basicOpen (0 : S) := by
      apply Opens.ext
      ext x
      constructor
      · intro hx
        have hxNoFactor : ∀ d : D, 1 - elem d ∉ x.asIdeal := by
          intro d hd
          apply hx
          have hprod_mem : (Finset.univ.prod fun d : D ↦ 1 - elem d) ∈ x.asIdeal := by
            have hd_mem : d ∈ (Finset.univ : Finset D) := by simp
            rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hd_mem]
            exact x.asIdeal.mul_mem_right _ hd
          exact hprod_mem
        have hxCover : x ∈ ⋃ d : D, (U d : Set (PrimeSpectrum S)) := by
          simpa [hCover] using (Set.mem_univ x)
        rcases Set.mem_iUnion.1 hxCover with ⟨d, hxd⟩
        have hxCompl : x ∈ (((U d)ᶜ : Clopens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) := by
          have hxBasic : x ∈ PrimeSpectrum.basicOpen (1 - elem d) := by
            change 1 - elem d ∉ x.asIdeal
            exact hxNoFactor d
          simpa [hUcomplbasic d] using hxBasic
        exact False.elim (hxCompl hxd)
      · intro hx
        exact False.elim (by simpa [PrimeSpectrum.mem_basicOpen] using hx)
    exact PrimeSpectrum.basicOpen_injOn_isIdempotentElem hprodIdem IsIdempotentElem.zero hEqOpen
  refine ⟨elem, CompleteOrthogonalIdempotents.of_prod_one_sub hOrthogonal hprodZero, ?_⟩
  intro d
  simpa [U] using
    congrArg (fun V : TopologicalSpace.Opens (PrimeSpectrum S) => (V : Set (PrimeSpectrum S)))
      (hbasicOpens d).symm

-- Proof sketch: apply the clopen stratification theorem to write `Spec(S)` as a finite disjoint
-- union of the nonempty `PrimeSpectrum.dimensionStratum S d`. Convert each clopen stratum to its
-- canonical idempotent, use the disjoint cover to obtain a complete orthogonal family, and then
-- apply the canonical product decomposition by quotienting with the ideals `⟨1 - e_d⟩`.
/-- Chap10 Lemma 10 114 7: equivalently, a finite type Cohen-Macaulay algebra over a field is a
product of quotient factors indexed by the occurring dimension strata, where the factor indexed by
`d` cuts out the dimension-`d` stratum and every maximal ideal of that factor has height `d`. -/
@[stacks 00OV]
theorem exists_product_decomposition_by_dimensionStrata_of_finiteType_cohenMacaulay :
    ∃ (D : Finset ℕ)
      (_ : ∀ d : ℕ, d ∈ D ↔ (PrimeSpectrum.dimensionStratum S d).Nonempty)
      (I : D → Ideal S)
      (_e : S ≃ₐ[k] ((d : D) → S ⧸ I d)),
      (∀ d : D,
        PrimeSpectrum.dimensionStratum S (d : ℕ) = zeroLocus (I d : Set S)) ∧
        ∀ d : D,
          ∀ m : MaximalSpectrum (S ⧸ I d), m.asIdeal.height = (d : ℕ) := by
  classical
  by_cases hS : Nontrivial S
  · letI : Nontrivial S := hS
    let hfiniteD :=
      finite_nonempty_dimensionStrata_of_finiteType_cohenMacaulay (k := k) (S := S)
    let D : Finset ℕ := hfiniteD.toFinset
    have hD : ∀ d : ℕ, d ∈ D ↔ (PrimeSpectrum.dimensionStratum S d).Nonempty := by
      intro d
      simpa [D] using hfiniteD.mem_toFinset d
    obtain ⟨elem, hComplete, hbasic⟩ :=
      exists_completeOrthogonalIdempotents_dimensionStrata (k := k) (S := S) D hD
    let I : D → Ideal S := fun d ↦ Ideal.span ({1 - elem d} : Set S)
    let eHom : S →ₐ[k] ((d : D) → S ⧸ I d) :=
      Pi.algHom k (fun d : D ↦ S ⧸ I d) fun d ↦ Ideal.Quotient.mkₐ k (I d)
    have hbij : Function.Bijective eHom := by
      simpa [eHom, I] using hComplete.bijective_pi
    let e : S ≃ₐ[k] ((d : D) → S ⧸ I d) := AlgEquiv.ofBijective eHom hbij
    have hstratum :
        ∀ d : D, PrimeSpectrum.dimensionStratum S (d : ℕ) = zeroLocus (I d : Set S) := by
      intro d
      calc
        PrimeSpectrum.dimensionStratum S (d : ℕ) =
            (PrimeSpectrum.basicOpen (elem d) : Set (PrimeSpectrum S)) :=
          hbasic d
        _ = zeroLocus (I d : Set S) := by
          rw [show I d = Ideal.span ({1 - elem d} : Set S) by rfl, zeroLocus_span]
          simpa using
            (PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem (elem d) (hComplete.idem d))
    have hheight :
        ∀ d : D, ∀ m : MaximalSpectrum (S ⧸ I d), m.asIdeal.height = (d : ℕ) := by
      intro d m
      -- Once the zero locus is identified with the dimension stratum, the height statement is
      -- exactly the quotient-side height formula already proved earlier.
      exact height_eq_index_of_dimensionStratum_quotient
        (k := k) (S := S) (I := I d) (d := (d : ℕ)) (hstratum d) m
    exact ⟨D, hD, I, e, hstratum, hheight⟩
  · letI : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    letI : IsEmpty (PrimeSpectrum S) := (PrimeSpectrum.isEmpty_iff_subsingleton).2 inferInstance
    let I : (∅ : Finset ℕ) → Ideal S := fun d ↦ nomatch d
    let e : S ≃ₐ[k] ((d : (∅ : Finset ℕ)) → S ⧸ I d) :=
      AlgEquiv.ofBijective
        (Pi.algHom k (fun d : (∅ : Finset ℕ) ↦ S ⧸ I d) fun d ↦ Ideal.Quotient.mkₐ k (I d))
        ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, by
          funext d
          nomatch d⟩⟩
    refine ⟨∅, ?_, I, e, ?_, ?_⟩
    · intro d
      constructor
      · intro hd
        exact False.elim (by simpa using hd)
      · rintro ⟨x, _hx⟩
        exact isEmptyElim x
    · intro d
      nomatch d
    · intro d m
      nomatch d

end
