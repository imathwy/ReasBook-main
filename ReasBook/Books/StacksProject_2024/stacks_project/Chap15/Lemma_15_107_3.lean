import Mathlib
import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap10.Lemma_10_156_2
import StacksProject_2024.Chap15.Definition_15_107_1
import StacksProject_2024.Chap15.Lemma_15_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct Unibranch
open Algebra.TensorProduct
open IsLocalRing

universe u

noncomputable section

section

variable (A Ah : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

local notation "A′" => unibranchNormalization A
local notation "A′h" => A′ ⊗[A] Ah

/-
Domain-style sampling:
- primary domain: local commutative algebra of unibranch local rings, henselizations, and minimal
  prime ideals;
- sampled owner declarations of the same kind:
  `IsUnibranch`,
  `IsHenselizationOf`,
  `henselizationMap_faithfullyFlat`,
  `unibranchNormalizationTensorHenselization_bijOn_minimalPrimes`;
- best owner abstraction: `IsUnibranch` is the core owner, while the chosen henselization `Ah` and
  its minimal-prime set form the bridge/view used to restate the source criterion;
- primitive data: the local ring `A` and the chosen henselization `Ah`;
- derived API: the unique-minimal-prime characterization on `Ah`.

Source/core/bridge triage:
- `source-facing`: the equivalence below;
- `core/canonical`: `IsUnibranch`, `IsHenselizationOf`, `minimalPrimes`;
- `bridge/view`: the chosen henselization `Ah`.
-/

/-- Helper for Lemma 15.107.3: a bijection between two sets transports the property of having a
unique element. -/
lemma existsUnique_mem_iff_existsUnique_mem_of_bijOn
    {α β : Type u} {s : Set α} {t : Set β} {f : α → β}
    (hbij : Set.BijOn f s t) :
    (∃! x, x ∈ s) ↔ ∃! y, y ∈ t := by
  classical
  constructor
  · rintro ⟨x, hx, hx_unique⟩
    refine ⟨f x, hbij.mapsTo hx, ?_⟩
    intro y hy
    rcases hbij.surjOn hy with ⟨z, hz, rfl⟩
    -- Pull the target point back through the bijection and use uniqueness on the source set.
    simp [hx_unique z hz]
  · rintro ⟨y, hy, hy_unique⟩
    rcases hbij.surjOn hy with ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    intro z hz
    have hfz : f z = y := hy_unique (f z) (hbij.mapsTo hz)
    -- Source uniqueness follows from injectivity of the bijection on the source set.
    exact hbij.injOn hz hx <| by
      calc
        f z = y := hfz
        _ = f x := hxy.symm

/-- Helper for Lemma 15.107.3: surjectivity on a subset transports the property of having a
unique element to the target subset. -/
lemma existsUnique_mem_of_surjOn
    {α β : Type u} {s : Set α} {t : Set β} {f : α → β}
    (hmap : Set.MapsTo f s t) (hsurj : Set.SurjOn f s t) (huniq : ∃! x, x ∈ s) :
    ∃! y, y ∈ t := by
  rcases huniq with ⟨x, hx, hx_unique⟩
  refine ⟨f x, hmap hx, ?_⟩
  intro y hy
  rcases hsurj hy with ⟨z, hz, rfl⟩
  -- Pull a target witness back to the unique source witness and then push forward again.
  simpa using congrArg f (hx_unique z hz)

/-- Helper for Lemma 15.107.3: under a faithfully flat algebra map, minimal primes contract to
minimal primes. -/
lemma comap_mem_minimalPrimes_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hff : (algebraMap R S).FaithfullyFlat) {Q : Ideal S}
    (hQ : Q ∈ minimalPrimes S) :
    Ideal.comap (algebraMap R S) Q ∈ minimalPrimes R := by
  -- Flatness gives going down, so a strictly smaller contracted prime would lift upstairs.
  have hflat : (algebraMap R S).Flat := hff.flat
  let _ : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  have hcomapPrime : (Ideal.comap (algebraMap R S) Q).IsPrime := by
    let _ : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
    exact Ideal.comap_isPrime (algebraMap R S) Q
  refine ⟨⟨hcomapPrime, bot_le⟩, ?_⟩
  intro J hJ hJ_le
  by_cases hQJ : Ideal.comap (algebraMap R S) Q = J
  · exact hQJ.le
  · let _ : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
    let _ : J.IsPrime := hJ.1
    let _ : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
    let _ : Q.LiesOver (Ideal.comap (algebraMap R S) Q) := ⟨rfl⟩
    have hJ_lt_Q : J < Ideal.comap (algebraMap R S) Q :=
      lt_of_le_of_ne hJ_le (Ne.symm hQJ)
    -- Going down produces the forbidden smaller prime below `Q`.
    obtain ⟨Q', hQ'_lt, hQ'_prime, _⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt (R := R) (S := S) (Q := Q) hJ_lt_Q
    have hQ_le_Q' : Q ≤ Q' :=
      hQ.2 ⟨hQ'_prime, bot_le⟩ hQ'_lt.le
    exact (hQ'_lt.not_ge hQ_le_Q').elim

/-- Helper for Lemma 15.107.3: contraction along a faithfully flat algebra map is surjective on
minimal primes. -/
lemma surjOn_minimalPrimes_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hff : (algebraMap R S).FaithfullyFlat) :
    Set.SurjOn (Ideal.comap (algebraMap R S)) (minimalPrimes S) (minimalPrimes R) := by
  intro q hq
  -- Injectivity plus minimal-prime lifting produces a prime upstairs over `q`.
  have hinj : Function.Injective (algebraMap R S) := hff.injective
  have hker : RingHom.ker (algebraMap R S) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot (algebraMap R S)).mp hinj
  have hqker : q ∈ (RingHom.ker (algebraMap R S)).minimalPrimes := by
    refine ⟨⟨Ideal.minimalPrimes_isPrime hq, ?_⟩, ?_⟩
    · simpa [hker]
    · intro I hI hIq
      exact hq.2 ⟨hI.1, by simpa [hker] using hI.2⟩ hIq
  obtain ⟨Q, hQ, hQq⟩ :=
    Ideal.exists_minimalPrimes_comap_eq (algebraMap R S) q hqker
  exact ⟨Q, hQ, hQq⟩

omit [IsLocalRing A] in
/-- Helper for Lemma 15.107.3: in a unibranch local ring, the nilradical is the unique minimal
prime. -/
lemma minimalPrimes_eq_singleton_nilradical_of_isUnibranch [IsUnibranch A] :
    minimalPrimes A = {nilradical A} := by
  letI : (nilradical A).IsPrime := by
    -- The reduction of a unibranch ring is a domain, so quotienting by the nilradical is prime.
    simpa [unibranchReduction] using
      (Ideal.Quotient.isDomain_iff_prime (R := A) (I := nilradical A)).mp inferInstance
  -- Once the nilradical is prime, it is the unique minimal prime of `A`.
  simpa [minimalPrimes, nilradical] using
    (show (nilradical A).minimalPrimes = {nilradical A} from
      Ideal.minimalPrimes_eq_subsingleton_self)

omit [IsLocalRing A] in
/-- Helper for Lemma 15.107.3: a unique minimal prime must equal the nilradical. -/
lemma minimalPrimes_eq_singleton_nilradical_of_existsUnique_minimalPrime
    (huniq : ∃! p : Ideal A, p ∈ minimalPrimes A) :
    minimalPrimes A = {nilradical A} := by
  rcases huniq with ⟨p, hp, hp_unique⟩
  have hsingle : minimalPrimes A = {p} := by
    ext q
    constructor
    · intro hq
      simpa using hp_unique q hq
    · intro hq
      rcases Set.mem_singleton_iff.mp hq with rfl
      exact hp
  have hsInf : sInf (minimalPrimes A) = nilradical A := by
    rw [minimalPrimes, nilradical]
    exact Ideal.sInf_minimalPrimes
  have hnil : nilradical A = p := by
    -- The nilradical is the infimum of all minimal primes, so a singleton minimal-prime set
    -- identifies it with that unique prime.
    rw [← hsInf, hsingle, sInf_singleton]
  -- Rewriting by the singleton description finishes the comparison with the nilradical.
  rw [hsingle, hnil]

/-- Helper for Lemma 15.107.3: a commutative ring has a unique minimal prime exactly when its
reduction is a domain. -/
lemma existsUnique_minimalPrime_iff_isDomain_reduction
    {R : Type u} [CommRing R] :
    (∃! p : Ideal R, p ∈ minimalPrimes R) ↔ IsDomain (R ⧸ nilradical R) := by
  constructor
  · intro huniq
    rcases huniq with ⟨q, hq, hq_unique⟩
    have hsingle : minimalPrimes R = {q} := by
      ext J
      constructor
      · intro hJ
        simpa [hq_unique J hJ]
      · intro hJ
        rcases Set.mem_singleton_iff.mp hJ with rfl
        exact hq
    have hsInf : sInf (minimalPrimes R) = nilradical R := by
      rw [minimalPrimes, nilradical]
      exact Ideal.sInf_minimalPrimes
    have hnil : nilradical R = q := by
      -- A singleton minimal-prime set identifies the nilradical with that prime.
      rw [← hsInf, hsingle, sInf_singleton]
    let _ : (nilradical R).IsPrime := by
      simpa [hnil] using (show q.IsPrime from Ideal.minimalPrimes_isPrime hq)
    -- Once the nilradical is prime, the reduced quotient is a domain.
    exact Ideal.Quotient.isDomain (nilradical R)
  · intro hdom
    let _ : (nilradical R).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime (R := R) (I := nilradical R)).mp hdom
    have hsingle : minimalPrimes R = {nilradical R} := by
      -- A prime nilradical is automatically the unique minimal prime.
      simpa [minimalPrimes, nilradical] using
        (show (nilradical R).minimalPrimes = {nilradical R} from
          Ideal.minimalPrimes_eq_subsingleton_self)
    refine ⟨nilradical R, ?_, ?_⟩
    · rw [hsingle]
      simp
    · intro p hp
      rw [hsingle] at hp
      simpa using hp

/-- Helper for Lemma 15.107.3: a unique minimal prime becomes a unique maximal ideal once each
minimal prime lies under a unique maximal ideal and each maximal ideal contains a unique minimal
prime. -/
lemma existsUnique_maximalIdeal_of_existsUnique_minimalPrime
    {R : Type u} [CommRing R]
    (hmin : ∃! p : Ideal R, p ∈ minimalPrimes R)
    (hmax_of_min :
      ∀ {p : Ideal R}, p ∈ minimalPrimes R → ∃! m : Ideal R, m.IsMaximal ∧ p ≤ m)
    (hmin_of_max :
      ∀ {m : Ideal R}, m.IsMaximal → ∃! p : Ideal R, p ∈ minimalPrimes R ∧ p ≤ m) :
    ∃! m : Ideal R, m.IsMaximal := by
  rcases hmin with ⟨p, hp, hp_unique⟩
  rcases hmax_of_min hp with ⟨m, hm, hm_unique⟩
  refine ⟨m, hm.1, ?_⟩
  intro n hn
  rcases hmin_of_max hn with ⟨q, hq, hq_unique⟩
  have hq_eq_p : q = p := hp_unique q hq.1
  have hp_le_n : p ≤ n := by
    simpa [hq_eq_p] using hq.2
  -- Every maximal ideal contains the same unique minimal prime, so the chosen maximal ideal is
  -- the only one.
  exact hm_unique n ⟨hn, hp_le_n⟩

/-- Helper for Lemma 15.107.3: a unique maximal ideal becomes a unique minimal prime once each
minimal prime lies under a unique maximal ideal and each maximal ideal contains a unique minimal
prime. -/
lemma existsUnique_minimalPrime_of_existsUnique_maximalIdeal
    {R : Type u} [CommRing R]
    (hmax : ∃! m : Ideal R, m.IsMaximal)
    (_hmax_of_min :
      ∀ {p : Ideal R}, p ∈ minimalPrimes R → ∃! m : Ideal R, m.IsMaximal ∧ p ≤ m)
    (hmin_of_max :
      ∀ {m : Ideal R}, m.IsMaximal → ∃! p : Ideal R, p ∈ minimalPrimes R ∧ p ≤ m) :
    ∃! p : Ideal R, p ∈ minimalPrimes R := by
  rcases hmax with ⟨m, hm, hm_unique⟩
  rcases hmin_of_max hm with ⟨p, hp, hp_unique⟩
  refine ⟨p, hp.1, ?_⟩
  intro q hq
  have hq_ne_top : q ≠ ⊤ := (Ideal.minimalPrimes_isPrime hq).ne_top
  obtain ⟨n, hn, hq_le_n⟩ := Ideal.exists_le_maximal q hq_ne_top
  have hn_eq_m : n = m := hm_unique n hn
  rcases hmin_of_max hn with ⟨p', hp', hp'_unique⟩
  have hp_le_n : p ≤ n := by
    simpa [hn_eq_m] using hp.2
  have hq_eq_p' : q = p' := hp'_unique q ⟨hq, hq_le_n⟩
  have hp_eq_p' : p = p' := hp'_unique p ⟨hp.1, hp_le_n⟩
  -- Compare both minimal primes inside the same maximal ideal `n`.
  calc
    q = p' := hq_eq_p'
    _ = p := hp_eq_p'.symm

/-- Helper for Lemma 15.107.3: a henselization with a unique minimal prime forces the base local
ring to have a unique minimal prime as well. -/
lemma existsUnique_minimalPrime_of_henselization
    (huniq : ∃! p : Ideal Ah, p ∈ minimalPrimes Ah) :
    ∃! p : Ideal A, p ∈ minimalPrimes A := by
  have hmap :
      Set.MapsTo (Ideal.comap (algebraMap A Ah)) (minimalPrimes Ah) (minimalPrimes A) := by
    intro Q hQ
    exact comap_mem_minimalPrimes_of_faithfullyFlat
      (henselizationMap_faithfullyFlat (R := A) (Rh := Ah)) hQ
  let hsurj :
      Set.SurjOn (Ideal.comap (algebraMap A Ah)) (minimalPrimes Ah) (minimalPrimes A) :=
    surjOn_minimalPrimes_of_faithfullyFlat
      (R := A) (S := Ah) (henselizationMap_faithfullyFlat (R := A) (Rh := Ah))
  -- Contract the unique minimal prime of the henselization along the faithfully flat map.
  exact existsUnique_mem_of_surjOn hmap hsurj huniq

-- Proof sketch: follow the source comparison route through Lemma `15.107.2`.
-- When `A` is unibranch, the reduced normalization `A′` is local, hence `A′ ⊗[A] A^h` is local by
-- the maximal-ideal bijection from `15.107.2 (1)`. Clauses `(3)` and `(4)` then convert unique
-- maximal ideal on `A′ ⊗[A] A^h` into unique minimal prime there, and clause `(2)` transports that
-- uniqueness to `A^h`. Conversely, a unique minimal prime of `A^h` first descends to a unique
-- minimal prime of `A`; on the normalization tensor product, clause `(2)` lifts the uniqueness,
-- clauses `(3)` and `(4)` turn it into a unique maximal ideal, and clause `(1)` transports that
-- back to the reduced normalization `A′`, which is therefore local.
/-- Lemma 15.107.3: for a local ring `A` and a chosen henselization `Ah` of `A`, the ring `A` is
unibranch if and only if `Ah` has a unique minimal prime ideal. -/
theorem isUnibranch_iff_existsUnique_minimalPrime_henselization :
    IsUnibranch A ↔ ∃! p : Ideal Ah, p ∈ minimalPrimes Ah := by
  -- The intended proof factors through Lemma `15.107.2`, whose current work file does not yet
  -- compile. We therefore isolate the remaining dependency at this target theorem.
  sorry

end
