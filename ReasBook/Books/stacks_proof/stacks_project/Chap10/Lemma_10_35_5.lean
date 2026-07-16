import Mathlib
import stacks_proof.stacks_project.Chap05.Lemma_5_18_3
import stacks_proof.stacks_project.Chap10.Definition_10_17_1
import stacks_proof.stacks_project.Chap10.Lemma_10_17_6
import stacks_proof.stacks_project.Chap10.Lemma_10_17_7
import stacks_proof.stacks_project.Chap10.Lemma_10_35_4

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 034J]
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
@[stacks 034J]
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
@[stacks 034J]
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
