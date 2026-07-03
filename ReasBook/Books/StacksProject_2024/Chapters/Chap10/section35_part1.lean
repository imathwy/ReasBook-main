import Mathlib
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.Extension.Generators
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_35_1 (from Chap10) -/
/-
Definition 10.35.1 is recalled canonically by `IsJacobsonRing R`: a commutative ring is Jacobson
if every radical ideal is the intersection of the maximal ideals containing it, equivalently if
every radical ideal equals its Jacobson radical.
-/
recall IsJacobsonRing

/- Companion recall: the defining radical-ideal formulation is the canonical equivalence
`isJacobsonRing_iff`. -/
recall isJacobsonRing_iff

/-! ### Lemma_10_35_2 (from Chap10) -/
universe u v

section

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/- Domain triage:
* primary domain: commutative algebra of finite type algebras and Jacobson rings;
* source-facing layer: the field-specialized Jacobson statement from the Stacks lemma;
* core/canonical owner: `IsJacobsonRing` with the transfer theorem
  `isJacobsonRing_of_finiteType`;
* bridge/view layer: the only specialization is the instance `Field k → IsJacobsonRing k`;
* primitive data vs. derived API: the `k`-algebra structure on `A` together with
  `[Algebra.FiniteType k A]` are the primitive inputs, while the Jacobson conclusion is exactly the
  derived owner-level theorem, so no parallel local wrapper is needed here.
-/
/- Lemma 10.35.2: any commutative algebra of finite type over a field is a Jacobson ring. This is
the field-specialized case of the canonical theorem `isJacobsonRing_of_finiteType`, with the
Jacobson hypothesis on `k` supplied by the instance `Field k`. -/
recall isJacobsonRing_of_finiteType

end

/-! ### Lemma_10_35_3 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]

/-- Lemma 10.35.3: if every prime ideal of `R` is the intersection of the maximal ideals
containing it, then `R` is a Jacobson ring. This is a thin source-faithful bridge to the
canonical owner criterion `isJacobsonRing_iff_sInf_maximal`. -/
theorem isJacobsonRing_of_prime_eq_sInf_maximals
    (h : ∀ P : Ideal R, P.IsPrime → P = sInf { J : Ideal R | P ≤ J ∧ J.IsMaximal }) :
    IsJacobsonRing R := by
  rw [isJacobsonRing_iff_sInf_maximal]
  intro P hP
  refine ⟨{ J : Ideal R | P ≤ J ∧ J.IsMaximal }, ?_, h P hP⟩
  intro J hJ
  exact Or.inl hJ.2

end

/-! ### Lemma_10_35_4 (from Chap10) -/
/- Lemma 10.35.4: a commutative ring `R` is Jacobson if and only if its prime spectrum
`PrimeSpectrum R` is a Jacobson topological space. This is exactly the canonical mathlib theorem
`PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace`. -/
recall PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace

/-! ### Lemma_10_35_5 (from Chap10) -/
universe u

open PrimeSpectrum TopologicalSpace
open scoped PrimeSpectrum

section

variable {R : Type u} [CommRing R]

/- Domain triage:
* primary domain: Jacobson-topological behavior of `Spec R` and its basic opens/localizations;
* source-facing layer: the two public theorems keep the Stacks formulation in terms of
  `V(p) ∩ D(f)`;
* core/canonical owners: `IsJacobsonRing R`, `JacobsonSpace (PrimeSpectrum R)`, the chapter
  homeomorphisms `primeSpectrum_quotient_homeomorph_zeroLocus` and
  `primeSpectrum_localizationAway_homeomorph_D`, and mathlib's
  `PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`;
* primitive data vs. derived API: the only public witnesses are the textbook `p` and `f`. The
  singleton-spectrum and localization-at-prime identifications stay derived from the owner
  abstractions rather than appearing as extra wrapper data in the theorem statements.
-/

/-- Helper for Lemma 10.35.5: a locally closed singleton in `Spec R` is realized as a basic open
inside its closure. -/
private lemma exists_basicOpen_inter_zeroLocus_eq_singleton_of_isLocallyClosed_singleton
    (p : PrimeSpectrum R) (hp : IsLocallyClosed ({p} : Set (PrimeSpectrum R))) :
    ∃ f : R, f ∉ p.asIdeal ∧ V(p.asIdeal) ∩ (D(f) : Set (PrimeSpectrum R)) = {p} := by
  -- Use the locally closed neighborhood criterion and then shrink to a basic open.
  have hNeighborhood :=
    ((isLocallyClosed_tfae ({p} : Set (PrimeSpectrum R))).out 0 3).mp hp
  obtain ⟨U, hpU, hUopen, hUsub⟩ := hNeighborhood p (by simp)
  obtain ⟨_, ⟨f, rfl⟩, hpDf, hDfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hUopen
  refine ⟨f, (mem_D f p).mp hpDf, ?_⟩
  ext x
  constructor
  · intro hx
    -- The chosen basic open lies in a neighborhood whose intersection with `closure {p}` is
    -- exactly `{p}`.
    have hxClosure : x ∈ closure ({p} : Set (PrimeSpectrum R)) := by
      simpa [PrimeSpectrum.closure_singleton] using hx.1
    have hxU : x ∈ U := hDfU hx.2
    have hxSingleton : x ∈ ({p} : Set (PrimeSpectrum R)) := hUsub ⟨hxU, hxClosure⟩
    simpa using hxSingleton
  · intro hx
    -- The point `p` belongs both to its closure and to the selected basic open.
    rcases Set.mem_singleton_iff.mp hx with rfl
    refine ⟨?_, hpDf⟩
    simpa [PrimeSpectrum.closure_singleton] using subset_closure (Set.mem_singleton p)

/-- Helper for Lemma 10.35.5: quotienting by `p` transports `V(p) ∩ D(f) = {p}` to a singleton
basic open in `Spec (R / p)`. -/
private lemma exists_quotient_basicOpen_eq_singleton_of_zeroLocus_inter_basicOpen_eq_singleton
    (p : PrimeSpectrum R) (f : R)
    (hp : V(p.asIdeal) ∩ (D(f) : Set (PrimeSpectrum R)) = {p}) :
    ∃ q : PrimeSpectrum (R ⧸ p.asIdeal),
      (D(Ideal.Quotient.mk p.asIdeal f) : Set (PrimeSpectrum (R ⧸ p.asIdeal))) = {q} := by
  let e := Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal
  have hpV : p ∈ V(p.asIdeal) := (mem_V p.asIdeal p).mpr subset_rfl
  let q : PrimeSpectrum (R ⧸ p.asIdeal) := e.symm ⟨p, hpV⟩
  refine ⟨q, ?_⟩
  ext x
  constructor
  · intro hx
    -- Transport the basic-open condition through the quotient homeomorphism.
    have hxImage : e x = ⟨p, hpV⟩ := by
      apply Subtype.ext
      have hxVD : (e x).1 ∈ V(p.asIdeal) ∩ (D(f) : Set (PrimeSpectrum R)) := by
        refine ⟨(e x).2, ?_⟩
        exact (mem_D f (PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal) x)).mpr <| by
          simpa [Ideal.mem_comap] using (mem_D (Ideal.Quotient.mk p.asIdeal f) x).mp hx
      have hxSingleton : (e x).1 ∈ ({p} : Set (PrimeSpectrum R)) := by
        rw [← hp]
        exact hxVD
      simpa using hxSingleton
    refine Set.mem_singleton_iff.mpr ?_
    exact e.injective (hxImage.trans (e.apply_symm_apply ⟨p, hpV⟩).symm)
  · intro hx
    -- The distinguished quotient point maps back to `p`, which lies in `D(f)`.
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have hpDf : p ∈ D(f) := by
      have hpVD : p ∈ V(p.asIdeal) ∩ (D(f) : Set (PrimeSpectrum R)) := by
        rw [hp]
        simp
      exact hpVD.2
    have hqDf : (e q).1 ∈ D(f) := by
      simpa [q] using hpDf
    refine (mem_D (Ideal.Quotient.mk p.asIdeal f) q).mpr ?_
    have hqComap : f ∉ Ideal.comap (Ideal.Quotient.mk p.asIdeal) q.asIdeal := by
      exact (mem_D f (PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal) q)).mp hqDf
    simpa [Ideal.mem_comap] using hqComap

/-- Helper for Lemma 10.35.5: after quotienting by `p`, localizing away from `f` produces a ring
whose prime spectrum has one point. -/
private lemma subsingleton_primeSpectrum_localizationAway_quotient_of_zeroLocus_inter_basicOpen_eq_singleton
    (p : PrimeSpectrum R) (f : R)
    (hp : V(p.asIdeal) ∩ (D(f) : Set (PrimeSpectrum R)) = {p}) :
    Subsingleton (PrimeSpectrum (Localization.Away (Ideal.Quotient.mk p.asIdeal f))) := by
  obtain ⟨q, hq⟩ :=
    exists_quotient_basicOpen_eq_singleton_of_zeroLocus_inter_basicOpen_eq_singleton p f hp
  let e := primeSpectrum_localizationAway_homeomorph_D (Ideal.Quotient.mk p.asIdeal f)
  have hsub :
      Subsingleton
        (D(Ideal.Quotient.mk p.asIdeal f) : Set (PrimeSpectrum (R ⧸ p.asIdeal))) := by
    rw [hq]
    refine ⟨fun x y ↦ ?_⟩
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp x.2).trans (Set.mem_singleton_iff.mp y.2).symm
  exact ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩

/-- Helper for Lemma 10.35.5: a finite family of primes strictly above `p` is simultaneously cut
out by one element outside `p`. -/
private lemma exists_not_mem_prime_mem_all_of_finite_subset_zeroLocus
    (p : PrimeSpectrum R) {S : Set (PrimeSpectrum R)} (hSfin : S.Finite)
    (hS : S ⊆ V(p.asIdeal)) (hpS : p ∉ S) :
    ∃ g : R, g ∉ p.asIdeal ∧ ∀ q ∈ S, g ∈ q.asIdeal := by
  classical
  let T : Finset (PrimeSpectrum R) := hSfin.toFinset
  have hprod :
      ∀ T : Finset (PrimeSpectrum R),
        (∀ q ∈ T, q ∈ V(p.asIdeal)) →
        (∀ q ∈ T, q ≠ p) →
        ∃ g : R, g ∉ p.asIdeal ∧ ∀ q ∈ T, g ∈ q.asIdeal := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _ _
        refine ⟨1, ?_, ?_⟩
        · simpa [Ideal.eq_top_iff_one] using p.isPrime.ne_top
        · intro q hq
          simpa using hq
    | @insert q T hqT ih =>
        intro hT hneq
        have hqV : q ∈ V(p.asIdeal) := hT q (by simp)
        have hT' : ∀ r ∈ T, r ∈ V(p.asIdeal) := by
          intro r hr
          exact hT r (by simp [hr])
        have hneq' : ∀ r ∈ T, r ≠ p := by
          intro r hr
          exact hneq r (by simp [hr])
        obtain ⟨g, hg_not_mem, hg_mem⟩ := ih hT' hneq'
        have hp_le_q : p.asIdeal ≤ q.asIdeal := (mem_V p.asIdeal q).mp hqV
        have hq_not_le : ¬ q.asIdeal ≤ p.asIdeal := by
          intro hq_le
          exact (hneq q (by simp)) (PrimeSpectrum.ext (le_antisymm hq_le hp_le_q))
        obtain ⟨a, haq_mem, hap_not_mem⟩ := Set.not_subset.mp hq_not_le
        refine ⟨a * g, ?_, ?_⟩
        · -- Primality of `p` keeps the product outside `p`.
          intro hag_mem
          exact ((p.isPrime.mul_mem_iff_mem_or_mem).mp hag_mem).elim hap_not_mem hg_not_mem
        · intro r hr
          by_cases hrq : r = q
          · subst r
            simpa [mul_comm] using (Ideal.mul_mem_left (I := q.asIdeal) g haq_mem)
          · exact Ideal.mul_mem_left (I := r.asIdeal) _ (hg_mem r ((Finset.mem_insert.mp hr).resolve_left hrq))
  obtain ⟨g, hg_not_mem, hg_mem⟩ := hprod T
    (by
      intro q hq
      exact hS ((Set.Finite.mem_toFinset (hs := hSfin)).mp hq))
    (by
      intro q hq hqp
      exact hpS ((Set.Finite.mem_toFinset (hs := hSfin)).mp (hqp ▸ hq)))
  refine ⟨g, hg_not_mem, ?_⟩
  intro q hq
  exact hg_mem q ((Set.Finite.mem_toFinset (hs := hSfin)).mpr hq)

-- Proof sketch: use Lemma `5.18.3` together with
-- `PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace` to obtain a nonclosed prime `p` whose
-- singleton is locally closed in `Spec R`. Express that singleton as `V(p) ∩ D(f)` via the
-- quotient and localization homeomorphisms from Lemmas `10.17.7` and `10.17.6`.
/-- Lemma 10.35.5 (1): if `R` is not Jacobson, then there exist a nonmaximal prime `p` and an
element `f` such that `V(p) ∩ D(f) = {p}`. -/
theorem exists_nonmaximal_prime_basicOpen_inter_zeroLocus_eq_singleton_of_not_isJacobsonRing
    (hR : ¬ IsJacobsonRing R) :
    ∃ (p : PrimeSpectrum R) (f : R),
      ¬ p.asIdeal.IsMaximal ∧
        V(p.asIdeal) ∩ (D(f) : Set (PrimeSpectrum R)) = {p} := by
  -- Turn non-Jacobsonness into a nonclosed point with locally closed singleton.
  have hSpec : ¬ JacobsonSpace (PrimeSpectrum R) := by
    rw [← PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace]
    exact hR
  obtain ⟨p, hp_nonclosed, hp_loc⟩ :=
    exists_nonclosed_point_with_locallyClosed_singleton_of_not_jacobsonSpace hSpec
  -- Realize that singleton as `V(p) ∩ D(f)`.
  obtain ⟨f, hf, hpf⟩ :=
    exists_basicOpen_inter_zeroLocus_eq_singleton_of_isLocallyClosed_singleton p hp_loc
  refine ⟨p, f, ?_, hpf⟩
  intro hpmax
  have hp_closed : p ∈ closedPoints (PrimeSpectrum R) := by
    simpa [closedPoints] using (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr hpmax
  exact hp_nonclosed hp_closed

-- Proof sketch: transport the singleton description of `V(p) ∩ D(f)` along the quotient and
-- localization spectrum homeomorphisms from Lemmas `10.17.7` and `10.17.6`, then apply
-- `PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton` to identify
-- `((R ⧸ p)_f)` with the local ring at the corresponding singleton point of its spectrum.
/-- Lemma 10.35.5 (2): if `V(p) ∩ D(f) = {p}`, then the localization `(R / p)_f` is a field. -/
theorem isField_localizationAway_quotient_of_zeroLocus_inter_basicOpen_eq_singleton
    (p : PrimeSpectrum R) (f : R)
    (hp :
      V(p.asIdeal) ∩ (D(f) : Set (PrimeSpectrum R)) = {p}) :
    IsField (Localization.Away (Ideal.Quotient.mk p.asIdeal f)) := by
  -- First identify the localization as a localization at a prime of the quotient, so it is a
  -- domain.
  obtain ⟨q, hq⟩ :=
    exists_quotient_basicOpen_eq_singleton_of_zeroLocus_inter_basicOpen_eq_singleton p f hp
  letI : IsLocalization.AtPrime
      (Localization.Away (Ideal.Quotient.mk p.asIdeal f)) q.asIdeal :=
    (PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton hq).mp inferInstance
  letI : IsDomain (Localization.Away (Ideal.Quotient.mk p.asIdeal f)) :=
    IsLocalization.isDomain_of_atPrime _ q.asIdeal
  -- The localization has a one-point prime spectrum, hence its spectrum is `T₁`.
  letI :=
    subsingleton_primeSpectrum_localizationAway_quotient_of_zeroLocus_inter_basicOpen_eq_singleton
      p f hp
  letI : T1Space (PrimeSpectrum (Localization.Away (Ideal.Quotient.mk p.asIdeal f))) :=
    ⟨fun x ↦ by
      have hsingleton : ({x} : Set (PrimeSpectrum (Localization.Away (Ideal.Quotient.mk p.asIdeal f)))) =
          Set.univ := by
        ext y
        simp [Subsingleton.elim y x]
      rw [hsingleton]
      exact isClosed_univ⟩
  exact
    (PrimeSpectrum.t1Space_iff_isField
      (R := Localization.Away (Ideal.Quotient.mk p.asIdeal f))).mp inferInstance

-- Proof sketch: in the Jacobson space `Spec R`, the locally closed subset `V(p) ∩ D(f)` has
-- dense closed points. If it were finite, it would be discrete by `JacobsonSpace.discreteTopology`,
-- so the point `p` would be closed in that subset and hence closed in `Spec R`, contradicting
-- `PrimeSpectrum.isClosed_singleton_iff_isMaximal`.
/-- Lemma 10.35.5 (3): if `R` is Jacobson, then for every nonmaximal prime `p` and every
`f ∉ p`, the locally closed subset `V(p) ∩ D(f)` is infinite. -/
theorem infinite_zeroLocus_inter_basicOpen_of_isJacobsonRing
    [IsJacobsonRing R] (p : PrimeSpectrum R) (f : R)
    (hp : ¬ p.asIdeal.IsMaximal) (hf : f ∉ p.asIdeal) :
    Set.Infinite (V(p.asIdeal) ∩ (D(f) : Set (PrimeSpectrum R))) := by
  classical
  -- Route correction: use the source-text finite-product separator, not the finite-discrete
  -- shortcut.
  by_contra hfinite
  let S : Set (PrimeSpectrum R) := V(p.asIdeal) ∩ (D(f) : Set (PrimeSpectrum R))
  have hSfinite : S.Finite := Set.not_infinite.mp hfinite
  have hpS : p ∈ S := by
    refine ⟨(mem_V p.asIdeal p).mpr subset_rfl, (mem_D f p).mpr hf⟩
  obtain ⟨g, hg_not_mem, hg_mem⟩ :=
    exists_not_mem_prime_mem_all_of_finite_subset_zeroLocus p (S := S \ ({p} : Set _))
      (hSfinite.subset Set.diff_subset) (by
        intro q hq
        exact hq.1.1) (by simp)
  have hsingleton : V(p.asIdeal) ∩ (D(f * g) : Set (PrimeSpectrum R)) = {p} := by
    ext q
    constructor
    · intro hq
      -- Any point of `V(p) ∩ D(fg)` already lies in `V(p) ∩ D(f)`, and if it were not `p` then
      -- the separator `g` would lie in its prime ideal.
      have hqfg : f * g ∉ q.asIdeal := (mem_D (f * g) q).mp hq.2
      have hqf : f ∉ q.asIdeal := by
        intro hfq
        exact hqfg (q.asIdeal.mul_mem_right g hfq)
      have hqS : q ∈ S := ⟨hq.1, (mem_D f q).mpr hqf⟩
      by_cases hqp : q = p
      · simpa [hqp]
      · have hqg : g ∈ q.asIdeal := hg_mem q ⟨hqS, by simpa [Set.mem_singleton_iff, hqp]⟩
        exact False.elim (hqfg (q.asIdeal.mul_mem_left f hqg))
    · intro hq
      have hqeq : q = p := Set.mem_singleton_iff.mp hq
      subst q
      refine ⟨(mem_V p.asIdeal p).mpr subset_rfl, (mem_D (f * g) p).mpr ?_⟩
      intro hfg
      exact ((p.isPrime.mul_mem_iff_mem_or_mem).mp hfg).elim hf hg_not_mem
  have hloc : IsLocallyClosed (V(p.asIdeal) ∩ (D(f * g) : Set (PrimeSpectrum R))) := by
    -- The set is locally closed because it is a closed set intersected with a basic open.
    exact (PrimeSpectrum.isClosed_zeroLocus (p.asIdeal : Set R)).isLocallyClosed.inter
      PrimeSpectrum.isOpen_basicOpen.isLocallyClosed
  have hnonempty : (V(p.asIdeal) ∩ (D(f * g) : Set (PrimeSpectrum R))).Nonempty := by
    refine ⟨p, ?_⟩
    rw [hsingleton]
    simp
  -- Jacobsonness now forces this singleton locally closed set to contain a closed point.
  obtain ⟨x, hx, hxclosed⟩ := nonempty_inter_closedPoints hnonempty hloc
  have hxp : x = p := by
    have hxSingleton : x ∈ ({p} : Set (PrimeSpectrum R)) := by
      rw [← hsingleton]
      exact hx
    exact Set.mem_singleton_iff.mp hxSingleton
  have hp_closed : p ∈ closedPoints (PrimeSpectrum R) := hxp ▸ hxclosed
  have hpmax : p.asIdeal.IsMaximal := by
    exact
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp
        (by simpa [closedPoints] using hp_closed)
  exact hp hpmax

end

/-! ### Lemma_10_35_6 (from Chap10) -/
universe u

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Ring.DimensionLEOne R] [Infinite (MaximalSpectrum R)]

/-- Helper for Lemma 10.35.6: a prime ideal in a dimension-one domain that contains a nonzero
element is minimal over the principal ideal generated by that element. -/
lemma prime_mem_minimalPrimes_span_singleton_of_ne_zero {P : Ideal R} (hP : P.IsPrime) {x : R}
    (hx : x ≠ 0) (hxP : x ∈ P) : P ∈ (Ideal.span ({x} : Set R)).minimalPrimes := by
  refine ⟨⟨hP, Ideal.span_le.2 (Set.singleton_subset_iff.mpr hxP)⟩, ?_⟩
  intro Q hQ hQP
  have hxQ : x ∈ Q := hQ.2 (Ideal.subset_span (by simp))
  have hQ_ne : Q ≠ ⊥ := by
    intro hQ_bot
    exact hx (by simpa [hQ_bot] using hxQ)
  have hQ_max : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ_ne hQ.1
  exact (hQ_max.eq_of_le hP.ne_top hQP).symm.le

/-- Helper for Lemma 10.35.6: every prime of `R / (x)` is minimal when `x` is nonzero in a
dimension-one domain. -/
lemma quotient_prime_isMin_of_ne_zero {x : R} (hx : x ≠ 0)
    (q : PrimeSpectrum (R ⧸ Ideal.span ({x} : Set R))) : IsMin q := by
  let I : Ideal R := Ideal.span ({x} : Set R)
  have hxmk : Ideal.Quotient.mk I x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hminimal :
      q.asIdeal.comap (Ideal.Quotient.mk I) ∈ I.minimalPrimes := by
    -- Pull the quotient prime back to `R`, where the dimension-one hypothesis applies.
    refine prime_mem_minimalPrimes_span_singleton_of_ne_zero (R := R)
      (P := q.asIdeal.comap (Ideal.Quotient.mk I)) (Ideal.comap_isPrime _ q.asIdeal) hx ?_
    simpa [Ideal.mem_comap, hxmk] using q.asIdeal.zero_mem
  rw [PrimeSpectrum.isMin_iff]
  rw [Ideal.minimalPrimes_eq_comap (R := R) (I := I)] at hminimal
  rcases hminimal with ⟨p, hp, hpq⟩
  have hp_eq : p = q.asIdeal :=
    Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hpq
  simpa [hp_eq] using hp

/-- Helper for Lemma 10.35.6: the closed subset `V(x)` is finite for every nonzero `x`. -/
lemma finite_zeroLocus_span_singleton_of_ne_zero {x : R} (hx : x ≠ 0) :
    (PrimeSpectrum.zeroLocus (R := R) ({x} : Set R)).Finite := by
  let I : Ideal R := Ideal.span ({x} : Set R)
  have hfinite_univ : (Set.univ : Set (PrimeSpectrum (R ⧸ I))).Finite := by
    -- On the quotient, every point is minimal, so the whole spectrum is finite.
    refine (PrimeSpectrum.finite_setOf_isMin (R := R ⧸ I)).subset ?_
    intro q hq
    simp only [Set.mem_setOf_eq]
    exact quotient_prime_isMin_of_ne_zero (R := R) (x := x) hx q
  letI : Finite (PrimeSpectrum (R ⧸ I)) := Finite.of_finite_univ hfinite_univ
  let e : PrimeSpectrum (R ⧸ I) ≃o PrimeSpectrum.zeroLocus (R := R) I :=
    Ideal.primeSpectrumQuotientOrderIsoZeroLocus I
  letI : Finite (PrimeSpectrum.zeroLocus (R := R) I) := Finite.of_injective e.symm e.symm.injective
  -- Replace the ideal-theoretic zero locus by the singleton form appearing in the statement.
  simpa [I, PrimeSpectrum.zeroLocus_span] using (Set.toFinite (PrimeSpectrum.zeroLocus (R := R) I))

/-- Helper for Lemma 10.35.6: a nonzero element is avoided by some maximal ideal when the maximal
spectrum is infinite. -/
lemma exists_maximalSpectrum_avoiding_ne_zero {x : R} (hx : x ≠ 0) :
    ∃ m : MaximalSpectrum R, x ∉ m.asIdeal := by
  let S : Set (MaximalSpectrum R) := {m | x ∈ m.asIdeal}
  have hzeroLocus : (PrimeSpectrum.zeroLocus (R := R) ({x} : Set R)).Finite :=
    finite_zeroLocus_span_singleton_of_ne_zero (R := R) hx
  letI : Fintype (PrimeSpectrum.zeroLocus (R := R) ({x} : Set R)) := hzeroLocus.fintype
  have hmem :
      ∀ m : S, MaximalSpectrum.toPrimeSpectrum m.1 ∈ PrimeSpectrum.zeroLocus (R := R) ({x} : Set R) :=
    by
      intro m
      rw [PrimeSpectrum.mem_zeroLocus]
      exact Set.singleton_subset_iff.mpr m.2
  let f : S → PrimeSpectrum.zeroLocus (R := R) ({x} : Set R) :=
    fun m ↦ ⟨MaximalSpectrum.toPrimeSpectrum m.1, hmem m⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact MaximalSpectrum.toPrimeSpectrum_injective (congrArg Subtype.val hab)
  letI : Finite S := Finite.of_injective f hf
  have hSfinite : S.Finite := Set.toFinite S
  obtain ⟨m, hm⟩ := hSfinite.infinite_compl.nonempty
  refine ⟨m, ?_⟩
  simpa [S] using hm

-- Proof sketch: by Lemma 10.35.4 it is enough to prove that `PrimeSpectrum R` is Jacobson. For a
-- nonzero element `x`, the closed subset `V(x)` identifies with `PrimeSpectrum (R ⧸ Ideal.span {x})`;
-- since `R` is Noetherian and every prime of the quotient is minimal by the dimension-one
-- hypothesis, this spectrum has finitely many irreducible components and hence finitely many
-- points. Therefore every nonzero prime ideal is the intersection of maximal ideals above it, so
-- `R` is Jacobson.
/-- Lemma 10.35.6: more generally, a Noetherian domain of dimension at most one with infinitely
many maximal ideals is a Jacobson ring. The owner abstraction for “every nonzero prime ideal is
maximal” is the canonical class `Ring.DimensionLEOne`; the textbook prime-ideal formulation is
kept below only as a bridge. -/
theorem isJacobsonRing_of_isNoetherianRing_of_dimensionLEOne_of_infinite_maximalSpectrum :
    IsJacobsonRing R := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hP0 : P = ⊥
  · subst hP0
    refine le_antisymm ?_ Ideal.le_jacobson
    intro x hxJ
    by_cases hx0 : x = 0
    · simpa [hx0]
    · obtain ⟨m, hmx⟩ := exists_maximalSpectrum_avoiding_ne_zero (R := R) hx0
      -- A nonzero element of the Jacobson radical would lie in every maximal ideal.
      have hxJ' :
          ∀ J : Ideal R, J ∈ {J : Ideal R | ⊥ ≤ J ∧ J.IsMaximal} → x ∈ J := by
        exact Ideal.mem_sInf.mp (by simpa [Ideal.jacobson] using hxJ)
      have hxm : x ∈ m.asIdeal := by
        exact hxJ' m.asIdeal ⟨bot_le, m.isMaximal⟩
      exact False.elim (hmx hxm)
  · -- Every nonzero prime ideal is already maximal in dimension one.
    letI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP0 hP
    simpa using (Ideal.jacobson_eq_self_of_isMaximal (I := P))

end

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Infinite (MaximalSpectrum R)]

/-- Lemma 10.35.6, source-faithful form: if every nonzero prime ideal of a Noetherian domain is
maximal and the maximal spectrum is infinite, then the ring is Jacobson. -/
theorem isJacobsonRing_of_isNoetherianRing_of_nonzero_prime_isMaximal_of_infinite_maximalSpectrum
    (hmax : ∀ ⦃P : Ideal R⦄, P ≠ ⊥ → P.IsPrime → P.IsMaximal) :
    IsJacobsonRing R := by
  letI : Ring.DimensionLEOne R := ⟨fun {_} hp hprime ↦ hmax hp hprime⟩
  exact isJacobsonRing_of_isNoetherianRing_of_dimensionLEOne_of_infinite_maximalSpectrum R

end

section

/-- Helper for Lemma 10.35.6: the ideal generated by a prime natural number is maximal in `ℤ`. -/
lemma ideal_span_natPrime_isMaximal (p : Nat.Primes) :
    (Ideal.span ({((p : ℕ) : ℤ)} : Set ℤ)).IsMaximal := by
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  infer_instance

/-- Helper for Lemma 10.35.6: distinct prime numbers define distinct maximal ideals of `ℤ`. -/
lemma infinite_maximalSpectrum_int : Infinite (MaximalSpectrum ℤ) := by
  let f : Nat.Primes → MaximalSpectrum ℤ := fun p ↦
    ⟨Ideal.span ({((p : ℕ) : ℤ)} : Set ℤ), ideal_span_natPrime_isMaximal p⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    have hspan :
        Ideal.span ({((p : ℕ) : ℤ)} : Set ℤ) = Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ) :=
      congrArg MaximalSpectrum.asIdeal hpq
    have hcard :
        Nat.card (ℤ ⧸ Ideal.span ({((p : ℕ) : ℤ)} : Set ℤ)) =
          Nat.card (ℤ ⧸ Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) :=
      congrArg (fun I : Ideal ℤ => Nat.card (ℤ ⧸ I)) hspan
    simpa [Int.card_ideal_quot] using hcard
  exact Infinite.of_injective f hf

-- Proof sketch: apply the general criterion above. The ring `ℤ` is a Noetherian domain of
-- dimension at most one, and its maximal ideals are generated by prime integers, giving infinitely
-- many maximal ideals.
/-- The ring of integers is a Jacobson ring. -/
instance : IsJacobsonRing ℤ := by
  letI : Infinite (MaximalSpectrum ℤ) := infinite_maximalSpectrum_int
  -- The general dimension-one criterion now applies directly to `ℤ`.
  exact isJacobsonRing_of_isNoetherianRing_of_dimensionLEOne_of_infinite_maximalSpectrum ℤ

end

/-! ### Example_10_35_7 (from Chap10) -/
universe u v

noncomputable section

/-
Domain triage:
* primary domain: Jacobson rings via away-localizations in commutative algebra;
* source-facing layer: the example asserts that a product of fields is Jacobson;
* core/canonical owners: `IsJacobsonRing` and mathlib's away-localization API;
* bridge/view used here: surjectivity of each canonical map `R → Localization.Away f`,
  obtained from an associated idempotent and the owner theorem
  `IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem`.
-/

section

variable {R : Type u} [CommRing R]

/-- If the canonical map to every localization away from a single element is surjective, then `R`
is a Jacobson ring. Equivalently, each away-localization is already a quotient of `R` through the
localization map. -/
theorem isJacobsonRing_of_localizationAway_surjective
    (h : ∀ f : R, Function.Surjective (algebraMap R (Localization.Away f))) :
    IsJacobsonRing R :=
  by
    rw [isJacobsonRing_iff_sInf_maximal]
    intro P hP
    refine ⟨{ J : Ideal R | P ≤ J ∧ J.IsMaximal }, ?_, ?_⟩
    · intro J hJ
      exact Or.inl hJ.2
    · refine le_antisymm (le_sInf fun J hJ ↦ hJ.1) ?_
      intro x hx
      by_contra hxP
      let φ : R →+* Localization.Away x := algebraMap R (Localization.Away x)
      have hdisj : Disjoint (Submonoid.powers x : Set R) (P : Set R) := by
        rw [Ideal.disjoint_powers_iff_notMem x hP.isRadical]
        exact hxP
      have hPmap : (Ideal.map φ P).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint
          (Submonoid.powers x) (Localization.Away x) P hP hdisj
      obtain ⟨M, hMmax, hPM⟩ := Ideal.exists_le_maximal (Ideal.map φ P) hPmap.ne_top
      letI := hMmax
      have hMcomapMax : (Ideal.comap φ M).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective φ (h x)
      have hPle : P ≤ Ideal.comap φ M := fun y hy ↦ hPM (Ideal.mem_map_of_mem _ hy)
      have hxM : x ∉ Ideal.comap φ M := by
        intro hxM
        exact hMmax.ne_top <|
          Ideal.eq_top_of_isUnit_mem _ hxM (IsLocalization.Away.algebraMap_isUnit x)
      exact hxM <| Ideal.mem_sInf.mp hx ⟨hPle, hMcomapMax⟩

end

section

variable {A : Type u} (k : A → Type v) [∀ a, Field (k a)]

open IsLocalization.Away

private def piFieldIdempotent (f : ∀ a, k a) : ∀ a, k a := fun a ↦
  letI := Classical.decEq (k a)
  if f a = 0 then 0 else 1

private theorem piFieldIdempotent_spec (f : ∀ a, k a) :
    IsIdempotentElem (piFieldIdempotent k f) := by
  classical
  ext a
  simp [piFieldIdempotent]

/-- The coordinatewise idempotent attached to `f` is associated to `f`. -/
-- Proof sketch: define the idempotent coordinatewise by testing whether the given coordinate is
-- zero, and define a unit coordinatewise by using `1` at zero coordinates and the original value
-- elsewhere. Then `f = u * e`, so `f` is associated to this idempotent `e`.
private theorem piFieldIdempotent_associated (f : ∀ a, k a) :
    Associated f (piFieldIdempotent k f) := by
  classical
  let u : ∀ a, k a := fun a ↦
    letI := Classical.decEq (k a)
    if f a = 0 then 1 else f a
  have hu : IsUnit u := by
    rw [Pi.isUnit_iff]
    intro a
    by_cases h : f a = 0
    · simp [u, h]
    · simp [u, h, isUnit_iff_ne_zero]
  have hf : f = u * piFieldIdempotent k f := by
    ext a
    by_cases h : f a = 0
    · simp [u, piFieldIdempotent, h]
    · simp [u, piFieldIdempotent, h]
  exact (Associated.of_eq hf).trans <|
    associated_unit_mul_left _ _ hu

/-- Example 10.35.7: if `k a` is a field for each `a : A`, then `∀ a, k a` is a Jacobson ring.
This strengthens the source statement, which also assumes `A` is infinite. -/
instance pi_isJacobsonRing : IsJacobsonRing ((a : A) → k a) :=
  isJacobsonRing_of_localizationAway_surjective fun f ↦ by
    let e := piFieldIdempotent k f
    have he : IsIdempotentElem e := piFieldIdempotent_spec k f
    have hfe : Associated f e := piFieldIdempotent_associated k f
    letI : IsLocalization.Away e (Localization.Away f) := of_associated hfe
    exact IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he

end

/-! ### Example_10_35_8 (from Chap10) -/
universe u

open Ideal IsLocalRing

section

variable {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]

/-- In a nonfield domain with finite maximal spectrum, the Jacobson radical is nonzero. -/
-- Proof sketch: enumerate the finitely many maximal ideals, show their product ideal is contained
-- in the Jacobson radical, and use that in a domain the product of finitely many nonzero ideals is
-- nonzero.
private theorem bot_lt_ringJacobson_of_finite_maximalSpectrum_of_not_isField
    (hR : ¬ IsField R) :
    (⊥ : Ideal R) < Ring.jacobson R := sorry

/-- Example 10.35.8: a domain with finitely many maximal ideals is not a Jacobson ring unless it
is a field. -/
-- Proof sketch: if `R` were Jacobson, then `⊥` would equal the infimum of the maximal ideals.
-- With only finitely many maximal ideals, this infimum contains the product of all maximal ideals,
-- and in a domain that product is nonzero when `R` is not a field, so `⊥` cannot be that
-- intersection.
theorem not_isJacobsonRing_of_finite_maximalSpectrum_of_not_isField
    (hR : ¬ IsField R) :
    ¬ IsJacobsonRing R := by
  intro hJacobson
  letI : IsJacobsonRing R := hJacobson
  have hradical :
      Ring.jacobson R = (⊥ : Ideal R) := by
    simpa [Ideal.jacobson_bot, Ideal.radical_bot_of_noZeroDivisors] using
      (Ideal.radical_eq_jacobson (⊥ : Ideal R)).symm
  have hlt := bot_lt_ringJacobson_of_finite_maximalSpectrum_of_not_isField hR
  rw [hradical] at hlt
  exact (lt_irrefl (⊥ : Ideal R)) hlt

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A local ring with a prime ideal distinct from its maximal ideal is not Jacobson. -/
-- Proof sketch: in a Jacobson local ring every prime ideal would equal its Jacobson radical, but
-- the Jacobson radical of any proper ideal in a local ring is the maximal ideal, forcing every
-- prime ideal to be maximal. A distinct prime ideal contradicts this.
theorem not_isJacobsonRing_of_isLocalRing_of_exists_prime_ne_maximalIdeal
    (hP : ∃ P : Ideal R, P.IsPrime ∧ P ≠ maximalIdeal R) :
    ¬ IsJacobsonRing R := by
  rintro hJacobson
  letI : IsJacobsonRing R := hJacobson
  rcases hP with ⟨P, hPprime, hPne⟩
  exact hPne <|
    calc
      P = P.jacobson := by
        simpa [hPprime.radical] using (Ideal.radical_eq_jacobson P)
      _ = maximalIdeal R := jacobson_eq_maximalIdeal P hPprime.ne_top

end

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A discrete valuation ring is not a Jacobson ring. -/
-- Proof sketch: a discrete valuation ring is local and not a field, so its maximal spectrum is a
-- singleton. Apply the finite-maximal-spectrum theorem to conclude that it cannot be Jacobson.
theorem IsDiscreteValuationRing.not_isJacobsonRing :
    ¬ IsJacobsonRing R :=
  not_isJacobsonRing_of_isLocalRing_of_exists_prime_ne_maximalIdeal
    ⟨⊥, Ideal.isPrime_bot, fun h ↦ IsDiscreteValuationRing.not_a_field R h.symm⟩

end

/-! ### Lemma_10_35_9 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.35.9: if `q` is a prime ideal of `S` lying over a maximal ideal `m` of `R` and the
residue field extension `κ(q) / κ(m)` is algebraic, then `q` is maximal. -/
-- Proof sketch: `S ⧸ q` is a domain and canonically an `(R ⧸ m)`-algebra because `q` lies over
-- `m`. The quotient map `S ⧸ q → κ(q)` is injective, so algebraicity of `κ(q) / κ(m)` together
-- with the canonical equivalence `R ⧸ m ≃ κ(m)` makes `S ⧸ q` algebraic, hence integral, over the
-- field `R ⧸ m`. Therefore `S ⧸ q` is a field, so `q` is maximal.
theorem isMaximal_of_liesOver_of_isAlgebraic_residueField
    (m : Ideal R) [m.IsMaximal] (q : Ideal S) [q.IsPrime] [q.LiesOver m]
    [Algebra.IsAlgebraic m.ResidueField q.ResidueField] :
    q.IsMaximal := by
  letI := Ideal.Quotient.field m
  letI : Algebra (R ⧸ m) (S ⧸ q) := Ideal.Quotient.algebraOfLiesOver q m
  letI : Algebra (R ⧸ m) q.ResidueField :=
    ((Ideal.ResidueField.map m q (algebraMap R S) (q.over_def m)).comp
      (algebraMap (R ⧸ m) m.ResidueField)).toAlgebra
  letI : IsScalarTower (R ⧸ m) (S ⧸ q) q.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.algebraMap_quotient_residueField_mk]
    change
      Ideal.ResidueField.map m q (algebraMap R S) (q.over_def m)
          (algebraMap (R ⧸ m) m.ResidueField (Ideal.Quotient.mk m x)) =
        algebraMap S q.ResidueField (algebraMap R S x)
    simp [Ideal.algebraMap_quotient_residueField_mk, Ideal.ResidueField.map_algebraMap]
  letI : IsScalarTower (R ⧸ m) m.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : Algebra.IsAlgebraic (R ⧸ m) q.ResidueField :=
    Algebra.IsAlgebraic.trans (R ⧸ m) m.ResidueField q.ResidueField
  let _ : Algebra.IsAlgebraic (R ⧸ m) (S ⧸ q) :=
    Algebra.IsAlgebraic.of_injective
      (IsScalarTower.toAlgHom (R ⧸ m) (S ⧸ q) q.ResidueField)
      q.injective_algebraMap_quotient_residueField
  exact Ideal.Quotient.maximal_of_isField q
    (isField_of_isIntegral_of_isField' (Field.toIsField (R ⧸ m)))

end

/-! ### Lemma_10_35_10 (from Chap10) -/
open Cardinal Polynomial

universe u v

section

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [Nontrivial V]

/-- Helper for Lemma 10.35.10: if every monic polynomial in `T` is invertible, then every nonzero
polynomial in `T` is invertible after normalizing by its leading coefficient. -/
lemma aeval_isUnit_of_forall_monic_aeval_isUnit
    (T : Module.End k V)
    (hmonic : ∀ P : k[X], P.Monic → IsUnit (aeval T P)) :
    ∀ P : k[X], P ≠ 0 → IsUnit (aeval T P) := by
  intro P hP
  -- Normalize by the leading coefficient so the monic hypothesis applies.
  have hmonicP : (P * C P.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hP
  have hunit_norm : IsUnit (aeval T (P * C P.leadingCoeff⁻¹)) := hmonic _ hmonicP
  have hcomm :
      Commute ((aeval T) P) ((algebraMap k (Module.End k V)) P.leadingCoeff⁻¹) :=
    (Algebra.commutes _ _).symm
  -- Strip off the invertible scalar factor on the right.
  have hunit_product :
      IsUnit (((aeval T) P) * ((algebraMap k (Module.End k V)) P.leadingCoeff⁻¹)) := by
    simpa [map_mul] using hunit_norm
  exact (hcomm.isUnit_mul_iff.mp hunit_product).1

/-- Helper for Lemma 10.35.10: chosen preimages of a fixed nonzero vector under the invertible maps
`aeval T (X - C a)` form a linearly independent family. -/
lemma linearIndependent_preimage_family_of_forall_aeval_isUnit
    (T : Module.End k V)
    (hunit : ∀ P : k[X], P ≠ 0 → IsUnit (aeval T P))
    {v : V} (hv : v ≠ 0) :
    LinearIndependent k fun a : k ↦
      (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((hunit (X - C a) (X_sub_C_ne_zero a)).unit)).symm v := by
  classical
  let w : k → V := fun a ↦
    (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((hunit (X - C a) (X_sub_C_ne_zero a)).unit)).symm v
  have hw : ∀ a : k, (aeval T (X - C a)) (w a) = v := by
    intro a
    -- Each `w a` is chosen to be a preimage of `v` under `aeval T (X - C a)`.
    change
      (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((hunit (X - C a) (X_sub_C_ne_zero a)).unit))
        ((LinearMap.GeneralLinearGroup.toLinearEquiv
          ((hunit (X - C a) (X_sub_C_ne_zero a)).unit)).symm v) = v
    exact LinearEquiv.apply_symm_apply _ _
  rw [linearIndependent_iff']
  intro s m hm i hi
  let q : k[X] := s.prod fun j ↦ X - C j
  let p : k[X] := s.sum fun j ↦ C (m j) * (s.erase j).prod fun x ↦ X - C x
  have hq_apply :
      ∀ j ∈ s, (aeval T q) (w j) = (aeval T ((s.erase j).prod fun x ↦ X - C x)) v := by
    intro j hj
    -- Factor the product polynomial into the `j`-term and the remaining factors.
    have hwj := congrArg
      (fun x : V ↦ (aeval T ((s.erase j).prod fun x ↦ X - C x)) x) (hw j)
    simpa [q, ← s.prod_erase_mul _ hj, aeval_mul, Module.End.mul_apply] using hwj
  have hm_apply : ∑ j ∈ s, m j • (aeval T q) (w j) = 0 := by
    -- Apply `aeval T q` to the assumed linear relation.
    simpa [w, map_sum, map_smul] using congrArg (fun x : V ↦ (aeval T q) x) hm
  have hp_apply : (aeval T p) v = 0 := by
    -- Repackage the transformed relation as a single polynomial evaluated at `T`.
    calc
      (aeval T p) v
          = ∑ j ∈ s, m j • (aeval T ((s.erase j).prod fun x ↦ X - C x)) v := by
              simp [p, map_sum, map_mul, aeval_C, Module.End.mul_apply]
      _ = ∑ j ∈ s, m j • (aeval T q) (w j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hq_apply j hj]
      _ = 0 := hm_apply
  have hp_zero : p = 0 := by
    by_cases hp : p = 0
    · exact hp
    · -- A nonzero `p` would make `aeval T p` invertible, forcing `v = 0`.
      have hinj : Function.Injective (aeval T p) :=
        (LinearMap.GeneralLinearGroup.toLinearEquiv ((hunit p hp).unit)).injective
      have hv_zero : v = 0 := hinj <| by simpa using hp_apply
      exact False.elim (hv hv_zero)
  have h_eval_zero : Polynomial.aeval i p = 0 := by
    -- Evaluate the zero polynomial at `i` to isolate the coefficient `m i`.
    simpa [hp_zero] using congrArg (Polynomial.aeval i) hp_zero
  have h_other :
      ∀ j ∈ s.erase i, m j * ((s.erase j).prod fun x ↦ i - x) = 0 := by
    intro j hj
    have hij : i ∈ s.erase j := Finset.mem_erase_of_ne_of_mem (Finset.ne_of_mem_erase hj).symm hi
    rw [← (s.erase j).prod_erase_mul (fun x ↦ i - x) hij]
    simp
  have h_eval_sum : ∑ j ∈ s, m j * ((s.erase j).prod fun x ↦ i - x) = 0 := by
    -- Expanding `aeval i p` turns the polynomial identity into a scalar relation.
    simpa [p, map_zero, map_sum, map_mul, aeval_X, aeval_C, Algebra.algebraMap_self_apply] using
      h_eval_zero
  have hmi :
      m i * ((s.erase i).prod fun x ↦ i - x) = 0 := by
    -- All other summands vanish because they retain the factor `i - i`.
    rw [← s.sum_erase_add (fun j ↦ m j * ((s.erase j).prod fun x ↦ i - x)) hi,
      Finset.sum_eq_zero h_other, zero_add] at h_eval_sum
    exact h_eval_sum
  -- The remaining product is nonzero because all roots are distinct.
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero
    (Finset.prod_ne_zero_iff.2 fun j hj ↦ sub_ne_zero.2 (Finset.ne_of_mem_erase hj).symm) hmi

/-- Helper for Lemma 10.35.10: if every nonzero polynomial in `T` is invertible, then the rank of
`V` is at least the cardinality of `k`. -/
lemma rank_ge_cardinal_of_forall_aeval_isUnit
    (T : Module.End k V)
    (hunit : ∀ P : k[X], P ≠ 0 → IsUnit (aeval T P)) :
    lift.{max u v} (#k) ≤ lift.{max u v} (Module.rank k V) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  -- A `k`-indexed linearly independent family forces the rank lower bound.
  simpa [← Cardinal.lift_umax] using
    (linearIndependent_preimage_family_of_forall_aeval_isUnit (T := T) hunit hv).cardinal_lift_le_rank

/-- Lemma 10.35.10 (Tag 00FT): if `V` is a nontrivial `k`-vector space whose dimension is
strictly smaller than the cardinality of `k`, then every endomorphism of `V` admits a monic
polynomial whose evaluation at that endomorphism is not a unit. -/
theorem exists_monic_polynomial_aeval_not_isUnit_of_rank_lt_cardinal
    (T : Module.End k V)
    (hV : lift.{max u v} (Module.rank k V) < lift.{max u v} (#k)) :
    ∃ P : k[X], P.Monic ∧ ¬ IsUnit (aeval T P) := by
  classical
  by_contra h
  push Not at h
  -- Route correction: the direct source proof uses a rank contradiction, not algebraicity.
  have hunit : ∀ P : k[X], P ≠ 0 → IsUnit (aeval T P) :=
    aeval_isUnit_of_forall_monic_aeval_isUnit (T := T) h
  have hrank : lift.{max u v} (#k) ≤ lift.{max u v} (Module.rank k V) :=
    rank_ge_cardinal_of_forall_aeval_isUnit (T := T) hunit
  exact not_lt_of_ge hrank hV

end

/-! ### Theorem_10_35_11 (from Chap10) -/
open Cardinal

universe u w

section

variable {k : Type u} {S : Type w}
variable [Field k] [CommRing S] [Algebra k S]

/- Domain triage:
* primary domain: residue-field algebraicity and Jacobson properties for small `k`-algebras;
* source-facing layer: the Stacks hypotheses stay in terms of a generating set `s` with
  `Algebra.adjoin k s = ⊤` and `#s < #k`;
* core/canonical owners: `Algebra.IsAlgebraic k m.ResidueField` and `IsJacobsonRing S`;
* bridge/view: this item upgrades the small-generation hypothesis to those owner predicates;
* primitive data vs. derived API: the only primitive source data are `s`, `hs`, and `hcard`,
  while residue-field algebraicity and the Jacobson condition remain theorem-level conclusions.
-/

/-- Helper for Theorem 10.35.11: the polynomial evaluation map on the chosen generators is
surjective once those generators adjoin the whole algebra. -/
lemma aeval_subtype_surjective_of_adjoin_eq_top
    (s : Set S) (hs : Algebra.adjoin k s = ⊤) :
    Function.Surjective (MvPolynomial.aeval ((↑) : s → S) : MvPolynomial s k →ₐ[k] S) := by
  -- Identify the evaluation map range with the subalgebra generated by `s`.
  rw [← AlgHom.range_eq_top]
  simpa [Algebra.adjoin_eq_range] using hs

/-- Helper for Theorem 10.35.11: for infinitely many generators, the residue field of a maximal
ideal has `k`-dimension strictly smaller than `#k`. -/
lemma lift_rank_residueField_lt_cardinal_of_infinite_generators
    (s : Set S) (hs : Algebra.adjoin k s = ⊤)
    (hcard : lift.{max u w} (#s) < lift.{max u w} (#k))
    (m : Ideal S) [m.IsMaximal] (hsinf : Set.Infinite s) :
    lift.{max u w} (Module.rank k m.ResidueField) < lift.{max u w} (#k) := by
  let ψ : MvPolynomial s k →ₐ[k] m.ResidueField :=
    (IsScalarTower.toAlgHom k S m.ResidueField).comp
      (MvPolynomial.aeval ((↑) : s → S))
  have hψ : Function.Surjective ψ := by
    -- Choose a polynomial preimage of the numerator in `S`, then descend to the residue field.
    intro y
    obtain ⟨x, rfl⟩ := Ideal.algebraMap_residueField_surjective m y
    obtain ⟨p, hp⟩ := aeval_subtype_surjective_of_adjoin_eq_top (k := k) s hs x
    refine ⟨p, ?_⟩
    simpa [ψ, hp] using congrArg (algebraMap S m.ResidueField) hp
  have hψlin : Function.Surjective ψ.toLinearMap := by
    simpa using hψ
  have hrank_le :
      lift.{max u w} (Module.rank k m.ResidueField) ≤
        lift.{w} (Module.rank k (MvPolynomial s k)) := by
    exact LinearMap.lift_rank_le_of_surjective (f := ψ.toLinearMap) hψlin
  have hpoly_rank :
      lift.{w} (Module.rank k (MvPolynomial s k)) ≤ lift.{max u w} (#s) := by
    letI : Infinite s := hsinf.to_subtype
    haveI : Nonempty s := Infinite.nonempty s
    -- Infinite-variable monomials have the same cardinality as the variable set itself.
    rw [MvPolynomial.rank_eq_lift, lift_lift, Cardinal.mk_finsupp_nat]
    exact le_of_eq <| by simpa using congrArg (lift.{max u w}) (max_eq_left (aleph0_le_mk s))
  -- Chain the surjective rank bound with the monomial-cardinality calculation.
  exact lt_of_le_of_lt (hrank_le.trans hpoly_rank) hcard

/-- Helper for Theorem 10.35.11: surjective algebra maps carry a generating set onto a generating
set of the target algebra. -/
lemma adjoin_image_eq_top_of_surjective
    (s : Set S) (hs : Algebra.adjoin k s = ⊤)
    {T : Type w} [CommRing T] [Algebra k T]
    (φ : S →ₐ[k] T) (hφ : Function.Surjective φ) :
    Algebra.adjoin k (φ '' s) = ⊤ := by
  -- Map the generating equality across `φ` and use surjectivity to identify the image with `⊤`.
  simpa [AlgHom.map_adjoin, (AlgHom.range_eq_top φ).2 hφ] using
    congrArg (Subalgebra.map φ) hs

/-- Helper for Theorem 10.35.11: the canonical quotient-plus-localization presentation already
surjects onto the localized quotient ring, so no hand-built `Option`-indexed evaluation map is
needed. -/
lemma quotient_localization_comp_generators_aeval_surjective
    (s : Set S) (hs : Algebra.adjoin k s = ⊤)
    (q : PrimeSpectrum S) (f : S) :
    let A : Type w := S ⧸ q.asIdeal
    let L : Type w := Localization.Away (Ideal.Quotient.mk q.asIdeal f)
    let sA : Set A := (Ideal.Quotient.mkₐ k q.asIdeal) '' s
    let hsA : Algebra.adjoin k sA = ⊤ :=
      adjoin_image_eq_top_of_surjective (k := k) (S := S) s hs
        (Ideal.Quotient.mkₐ k q.asIdeal) (Ideal.Quotient.mkₐ_surjective k q.asIdeal)
    let P : Algebra.Generators k A sA := Algebra.Generators.ofSet hsA
    let Q : Algebra.Generators A L Unit :=
      Algebra.Generators.localizationAway L (Ideal.Quotient.mk q.asIdeal f)
    Function.Surjective
      (MvPolynomial.aeval ((Q.comp P).val) : MvPolynomial (Unit ⊕ sA) k →ₐ[k] L) := by
  intro A L sA hsA P Q
  -- The composed generators come with a built-in section, hence the evaluation map is surjective.
  simpa using (Q.comp P).aeval_val_surjective

omit [Field k] [CommRing S] [Algebra k S] in
/-- Helper for Theorem 10.35.11: adjoining one localization generator to a set whose cardinality is
bounded by `#s` still keeps the resulting generator family smaller than `#k`. -/
lemma lift_cardinal_range_sum_generators_lt_cardinal
    {A : Type w} {T : Type w} (s : Set S) (φ : Unit ⊕ A → T)
    (hAcard : lift.{max u w} (#A) ≤ lift.{max u w} (#s))
    (hcard : lift.{max u w} (#s) < lift.{max u w} (#k))
    (hsinf : Set.Infinite s) :
    lift.{max u w} #(↑(Set.range φ)) < lift.{max u w} (#k) := by
  letI : Infinite s := hsinf.to_subtype
  have hrange0 : #(↑(Set.range φ)) ≤ #(Unit ⊕ A) := by
    refine Cardinal.mk_le_of_surjective (f := fun x : Unit ⊕ A => ⟨φ x, ⟨x, rfl⟩⟩) ?_
    intro y
    rcases y.2 with ⟨x, hx⟩
    refine ⟨x, Subtype.ext ?_⟩
    simpa using hx
  have hrange :
      lift.{max u w} #(↑(Set.range φ)) ≤ lift.{max u w} (#(Unit ⊕ A)) := by
    exact Cardinal.lift_le.mpr hrange0
  have hsAleph :
      ℵ₀ ≤ lift.{max u w} (#s) := by
    exact Cardinal.aleph0_le_lift.2 (aleph0_le_mk s)
  have hsum :
      lift.{max u w} (#(Unit ⊕ A)) ≤ lift.{max u w} (#s) := by
    rw [Cardinal.mk_sum, Cardinal.lift_add, Cardinal.lift_lift, Cardinal.lift_lift,
      Cardinal.mk_eq_one, Cardinal.lift_one]
    calc
      1 + lift.{max u w} (#A) ≤ 1 + lift.{max u w} (#s) := by
        simpa [add_comm] using add_le_add_left hAcard 1
      _ = lift.{max u w} (#s) := by
        rw [Cardinal.add_eq_right hsAleph (one_le_aleph0.trans hsAleph)]
  -- Chain the range bound through the `1 + #A = #s` cardinal estimate.
  exact lt_of_le_of_lt (hrange.trans hsum) hcard

/-- Helper for Theorem 10.35.11: the field `(S / q)_f` is generated over `k` by fewer than `#k`
elements when `s` is infinite and already generates `S`. -/
lemma exists_small_generating_set_localizationAway_quotient
    (s : Set S) (hs : Algebra.adjoin k s = ⊤)
    (hcard : lift.{max u w} (#s) < lift.{max u w} (#k))
    (q : PrimeSpectrum S) (f : S) (_hf : f ∉ q.asIdeal) (hsinf : Set.Infinite s) :
    ∃ t : Set (Localization.Away (Ideal.Quotient.mk q.asIdeal f)),
      Algebra.adjoin k t = ⊤ ∧
        lift.{max u w} (#t) < lift.{max u w} (#k) := by
  let A : Type w := S ⧸ q.asIdeal
  let L : Type w := Localization.Away (Ideal.Quotient.mk q.asIdeal f)
  let sA : Set A := (Ideal.Quotient.mkₐ k q.asIdeal) '' s
  have hsA : Algebra.adjoin k sA = ⊤ := by
    -- Pass the original generating set through the quotient map to generate `S / q`.
    exact
      adjoin_image_eq_top_of_surjective (k := k) (S := S) s hs
        (Ideal.Quotient.mkₐ k q.asIdeal) (Ideal.Quotient.mkₐ_surjective k q.asIdeal)
  let P : Algebra.Generators k A sA := Algebra.Generators.ofSet hsA
  let Q : Algebra.Generators A L Unit :=
    Algebra.Generators.localizationAway L (Ideal.Quotient.mk q.asIdeal f)
  let PQ : Algebra.Generators k L (Unit ⊕ sA) := Q.comp P
  refine ⟨Set.range PQ.val, ?_, ?_⟩
  · -- Route correction: use the canonical composed presentation instead of a manual `Option` map.
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (AlgHom.range_eq_top _).2 <|
      quotient_localization_comp_generators_aeval_surjective
      (k := k) (S := S) s hs q f
  · let ιsA : s → A := fun x ↦ Ideal.Quotient.mkₐ k q.asIdeal x.1
    have hsAcard :
        lift.{max u w} (#sA) ≤ lift.{max u w} (#s) := by
      -- The quotient-image generating set is indexed by the image of the original subtype `s`.
      simpa [sA, Set.image_eq_range, ιsA] using
        (Cardinal.mk_range_le_lift (f := ιsA))
    -- The extra localization inverse contributes only one additional generator.
    simpa [PQ] using
      lift_cardinal_range_sum_generators_lt_cardinal
        (k := k) (S := S) (A := sA) (T := L) s PQ.val hsAcard hcard hsinf

/-- Helper for Theorem 10.35.11: if the field `(S / q)_f` is algebraic over `k`, then so is the
residue field `κ(q)`. -/
lemma isAlgebraic_residueField_of_field_localizationAway_quotient
    (q : PrimeSpectrum S) (f : S) (hf : f ∉ q.asIdeal)
    {L : Type w} [Field L] [Algebra k L] [Algebra (S ⧸ q.asIdeal) L]
    [IsScalarTower k (S ⧸ q.asIdeal) L] [IsLocalization.Away (Ideal.Quotient.mk q.asIdeal f) L]
    [Algebra.IsAlgebraic k L] :
    Algebra.IsAlgebraic k q.asIdeal.ResidueField := by
  let A : Type w := S ⧸ q.asIdeal
  let y : A := Ideal.Quotient.mk q.asIdeal f
  let hy_ne_zero : y ≠ 0 := by
    intro hy
    exact hf <| Ideal.Quotient.eq_zero_iff_mem.mp <| by simpa [y] using hy
  have hnonzero :
      Submonoid.powers y ≤ nonZeroDivisors A := by
    intro z hz
    rcases hz with ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hy_ne_zero)
  have hA_alg : Algebra.IsAlgebraic k A :=
    Algebra.IsAlgebraic.of_injective
      (IsScalarTower.toAlgHom k A L)
      (IsLocalization.injective L hnonzero)
  let _ : Algebra.IsAlgebraic k A := hA_alg
  exact Algebra.IsAlgebraic.trans k A q.asIdeal.ResidueField

/-- Helper for Theorem 10.35.11: the residue field at the zero ideal of a field is just the field
itself, so algebraicity of that residue field transports back to the field. -/
lemma isAlgebraic_of_bot_residueField
    {L : Type w} [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k ((⊥ : Ideal L).ResidueField)] :
    Algebra.IsAlgebraic k L := by
  let eQuot :
      (L ⧸ (⊥ : Ideal L)) ≃ₐ[L] ((⊥ : Ideal L).ResidueField) :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom L (L ⧸ (⊥ : Ideal L)) ((⊥ : Ideal L).ResidueField))
      (Ideal.bijective_algebraMap_quotient_residueField (⊥ : Ideal L))
  let e :
      ((⊥ : Ideal L).ResidueField) ≃ₐ[k] L :=
    (eQuot.symm.trans (AlgEquiv.quotientBot L L)).restrictScalars k
  -- Replace the bottom residue field with `L` itself via the canonical quotient equivalence.
  exact e.isAlgebraic

/-- Helper for Theorem 10.35.11: over a field base, a prime ideal with algebraic residue field is
already maximal. -/
lemma isMaximal_of_isAlgebraic_residueField_over_field
    (q : Ideal S) [q.IsPrime] [Algebra.IsAlgebraic k q.ResidueField] :
    q.IsMaximal := by
  let _ : Algebra.IsAlgebraic k (S ⧸ q) :=
    Algebra.IsAlgebraic.of_injective
      (IsScalarTower.toAlgHom k (S ⧸ q) q.ResidueField)
      q.injective_algebraMap_quotient_residueField
  -- The quotient by `q` is an integral algebra over the field `k`, hence a field.
  exact Ideal.Quotient.maximal_of_isField q
    (isField_of_isIntegral_of_isField' (Field.toIsField k))

-- Proof sketch: replace `S` by the polynomial ring on the generating family and pass to the
-- quotient by the corresponding maximal ideal. The polynomial ring has `k`-dimension bounded by
-- the cardinality of the generating set, so Lemma `10.35.10` rules out a transcendental element in
-- the residue field, forcing `κ(m) / k` to be algebraic.
/-- Theorem 10.35.11 (1): if a `k`-algebra `S` is generated by fewer than `#k` elements, then for
every maximal ideal `m` of `S` the residue field extension `m.ResidueField / k` is algebraic. -/
theorem isAlgebraic_residueField_of_maximal_of_adjoin_eq_top_of_cardinalMk_lt
    (s : Set S) (hs : Algebra.adjoin k s = ⊤)
    (hcard : lift.{max u w} (#s) < lift.{max u w} (#k))
    (m : Ideal S) [m.IsMaximal] :
    Algebra.IsAlgebraic k m.ResidueField := by
  by_cases hsfin : Set.Finite s
  · -- In the finite case, apply Hilbert Nullstellensatz through finite type.
    have hfgTop : (⊤ : Subalgebra k S).FG := by
      refine ⟨hsfin.toFinset, ?_⟩
      simpa using hs
    letI : Algebra.FiniteType k S := ⟨hfgTop⟩
    have hfinite : Module.Finite k m.ResidueField :=
      finite_residueField_of_isMaximal_of_finiteType k m
    infer_instance
  · have hsinf : Set.Infinite s := by
      rw [Set.Infinite]
      exact hsfin
    -- Route correction: the infinite branch follows the source proof via a rank contradiction,
    -- not by trying to build algebraicity directly.
    have hrank :
        lift.{max u w} (Module.rank k m.ResidueField) < lift.{max u w} (#k) :=
      lift_rank_residueField_lt_cardinal_of_infinite_generators
        (k := k) (S := S) s hs hcard m hsinf
    by_contra halg
    have htrans_alg : Algebra.Transcendental k m.ResidueField := by
      simpa [Algebra.transcendental_iff_not_isAlgebraic] using halg
    obtain ⟨T, hT⟩ := Algebra.transcendental_def.mp htrans_alg
    let μT : Module.End k m.ResidueField := Algebra.lmul k m.ResidueField T
    obtain ⟨P, hPmonic, hPnotunit⟩ :=
      exists_monic_polynomial_aeval_not_isUnit_of_rank_lt_cardinal (T := μT) hrank
    have hTinj :
        Function.Injective (Polynomial.aeval T : Polynomial k →ₐ[k] m.ResidueField) :=
      (transcendental_iff_injective (R := k) (x := T)).mp hT
    have hPT_ne_zero : Polynomial.aeval T P ≠ 0 := by
      intro hPT_zero
      have hP_zero : P = 0 := hTinj <| by simpa using hPT_zero
      exact Polynomial.not_monic_zero (hP_zero ▸ hPmonic)
    have hPunit : IsUnit (Polynomial.aeval T P) :=
      isUnit_iff_ne_zero.mpr hPT_ne_zero
    have hμT_unit : IsUnit (Polynomial.aeval μT P) := by
      -- Evaluating at left multiplication by `T` is left multiplication by `P(T)`.
      rw [Polynomial.aeval_algHom_apply]
      exact (Algebra.lmul_isUnit_iff (R := k) (A := m.ResidueField)).2 hPunit
    exact hPnotunit hμT_unit

-- Proof sketch: if `S` were not Jacobson, Lemma `10.35.5` gives a nonmaximal prime `q` such that
-- a localization of `S ⧸ q` is a field. That localization is still generated by fewer than `#k`
-- elements, so the first part makes it algebraic over `k`; then Lemma `10.35.9` forces `q` to be
-- maximal, a contradiction.
/-- Theorem 10.35.11 (2): if a `k`-algebra `S` is generated by fewer than `#k` elements, then `S`
is a Jacobson ring. -/
theorem isJacobsonRing_of_adjoin_eq_top_of_cardinalMk_lt
    (s : Set S) (hs : Algebra.adjoin k s = ⊤)
    (hcard : lift.{max u w} (#s) < lift.{max u w} (#k))
    : IsJacobsonRing S := by
  by_cases hsfin : Set.Finite s
  · -- In the finite case, Jacobsonness is the finite-type Nullstellensatz.
    have hfgTop : (⊤ : Subalgebra k S).FG := by
      refine ⟨hsfin.toFinset, ?_⟩
      simpa using hs
    letI : Algebra.FiniteType k S := ⟨hfgTop⟩
    exact isJacobsonRing_of_finiteType (A := k) (B := S)
  · have hsinf : Set.Infinite s := by
      rw [Set.Infinite]
      exact hsfin
    by_contra hJacobson
    obtain ⟨q, f, hq_nonmax, hq_basicOpen⟩ :=
      exists_nonmaximal_prime_basicOpen_inter_zeroLocus_eq_singleton_of_not_isJacobsonRing
        (R := S) hJacobson
    have hf : f ∉ q.asIdeal := by
      -- The source obstruction keeps `q` inside the displayed basic open, so `f ∉ q`.
      have hq_mem :
          q ∈ PrimeSpectrum.zeroLocus (q.asIdeal : Set S) ∩
            (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum S)) := by
        rw [hq_basicOpen]
        simp
      exact (PrimeSpectrum.mem_basicOpen f q).mp hq_mem.2
    have hLfield : IsField (Localization.Away (Ideal.Quotient.mk q.asIdeal f)) := by
      -- The Jacobson obstruction localizes to a field by Lemma `10.35.5`.
      exact
        isField_localizationAway_quotient_of_zeroLocus_inter_basicOpen_eq_singleton
          (R := S) q f hq_basicOpen
    letI : Field (Localization.Away (Ideal.Quotient.mk q.asIdeal f)) := hLfield.toField
    obtain ⟨t, ht, htcard⟩ :
        ∃ t : Set (Localization.Away (Ideal.Quotient.mk q.asIdeal f)),
          Algebra.adjoin k t = ⊤ ∧
          lift.{max u w} (#t) < lift.{max u w} (#k) := by
      -- Route correction: follow the source `#s + 1` localization presentation exactly.
      exact
        exists_small_generating_set_localizationAway_quotient
          (k := k) (S := S) s hs hcard q f hf hsinf
    have hL_residue_alg :
        Algebra.IsAlgebraic k
          ((⊥ : Ideal (Localization.Away (Ideal.Quotient.mk q.asIdeal f))).ResidueField) :=
      letI :
          (⊥ : Ideal (Localization.Away (Ideal.Quotient.mk q.asIdeal f))).IsMaximal :=
        Ideal.bot_isMaximal
      isAlgebraic_residueField_of_maximal_of_adjoin_eq_top_of_cardinalMk_lt
        (k := k) (S := Localization.Away (Ideal.Quotient.mk q.asIdeal f)) t ht htcard
        (⊥ : Ideal (Localization.Away (Ideal.Quotient.mk q.asIdeal f)))
    let _ :
        Algebra.IsAlgebraic k
          ((⊥ : Ideal (Localization.Away (Ideal.Quotient.mk q.asIdeal f))).ResidueField) :=
      hL_residue_alg
    let _ : Algebra.IsAlgebraic k (Localization.Away (Ideal.Quotient.mk q.asIdeal f)) :=
      isAlgebraic_of_bot_residueField
        (k := k) (L := Localization.Away (Ideal.Quotient.mk q.asIdeal f))
    have hq_alg : Algebra.IsAlgebraic k q.asIdeal.ResidueField :=
      isAlgebraic_residueField_of_field_localizationAway_quotient
        (k := k) (S := S) q f hf
        (L := Localization.Away (Ideal.Quotient.mk q.asIdeal f))
    have hq_max : q.asIdeal.IsMaximal :=
      isMaximal_of_isAlgebraic_residueField_over_field (k := k) (S := S) q.asIdeal
    exact hq_nonmax hq_max

end

/-! ### Lemma_10_35_12 (from Chap10) -/
open Cardinal
open Algebra.TensorProduct
open scoped TensorProduct

universe u v w

section

variable {k : Type u} {S : Type v} {K : Type w}
variable [Field k] [CommRing S] [Algebra k S] [Field K] [Algebra k K]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (includeRight : S →ₐ[k] S_K)

private theorem adjoin_range_includeRight_eq_top :
    Algebra.adjoin K (Set.range iSK) = ⊤ := by
  simpa [Set.image_univ] using
    adjoin_one_tmul_image_eq_top (Set.univ : Set S) (Algebra.adjoin_univ k S)

private theorem lift_mk_range_includeRight_lt
    (hcard :
      Cardinal.lift.{max w v, v} #S <
        Cardinal.lift.{max w v, w} #K) :
    Cardinal.lift.{max v w, max v w}
        #(Set.range iSK) <
      Cardinal.lift.{max v w, w} #K := by
  have hle :
      Cardinal.lift.{v, max v w}
          #(Set.range iSK) ≤
        Cardinal.lift.{max v w, v} #S := by
    exact Cardinal.mk_range_le_lift
  have hsmall :
      Cardinal.lift.{v, max v w}
          #(Set.range iSK) <
        Cardinal.lift.{max v w, w} #K := by
    exact lt_of_le_of_lt hle <| by simpa [max_comm] using hcard
  rw [Cardinal.lift_id'.{v, w}] at hsmall
  simpa [Cardinal.lift_id] using hsmall

/-- Lemma 10.35.12 (1): if `K/k` is a field extension with `#S < #K`, then for every maximal ideal
`m` of the scalar extension `K ⊗[k] S`, the residue field `m.ResidueField` is algebraic over
`K`. -/
theorem isAlgebraic_residueField_of_maximal_scalarExtension_of_cardinalMk_lt
    (_hcard :
      Cardinal.lift.{max w v, v} #S <
        Cardinal.lift.{max w v, w} #K)
    (m : Ideal S_K) [m.IsMaximal] :
    Algebra.IsAlgebraic K m.ResidueField := by
  simpa using
    isAlgebraic_residueField_of_maximal_of_adjoin_eq_top_of_cardinalMk_lt m

/-- Lemma 10.35.12 (2): if `K/k` is a field extension with `#S < #K`, then the scalar extension
`K ⊗[k] S` is a Jacobson ring. -/
theorem isJacobsonRing_scalarExtension_of_cardinalMk_lt
    (_hcard :
      Cardinal.lift.{max w v, v} #S <
        Cardinal.lift.{max w v, w} #K) :
    IsJacobsonRing S_K := by
  simpa using
    isJacobsonRing_of_adjoin_eq_top_of_cardinalMk_lt

end
