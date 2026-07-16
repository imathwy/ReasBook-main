import stacks_proof.stacks_project.Chap10.Definition_10_63_1
import stacks_proof.stacks_project.Chap10.Lemma_10_62_2
import stacks_proof.stacks_project.Chap10.Lemma_10_63_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum RelSeries Submodule

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (s : PrimeCyclicFiltration R M)

/-
Domain triage:
- primary domain: commutative algebra of associated primes and prime-cyclic filtrations;
- source-facing owner: `associatedPrimesOfModule R M`;
- filtration owner: `s.primeFactors`;
- canonical Noetherian owner: mathlib's `associatedPrimes R M`;
- layer of this file: `bridge/view`, first from associated-prime points to the intrinsic filtration
  owner `s.primeFactors`, then from that owner statement to a chosen indexing `p`.
-/

/-- Helper for Lemma 10.63.4: prime factors already present in a filtration remain present after
adjoining one more prime-quotient step at the end. -/
lemma PrimeCyclicFiltration.primeFactors_subset_snoc
    {N : Submodule R M} (hrel : s.last.IsQuotientEquivQuotientPrime N) :
    s.primeFactors ⊆ PrimeCyclicFiltration.primeFactors (s.snoc N hrel) := by
  intro 𝔭 h𝔭
  rcases h𝔭 with ⟨i, hi⟩
  rcases hi with ⟨e⟩
  have hsucc : (s.snoc N hrel) (i.castSucc.succ) = s i.succ := by
    simpa using RelSeries.snoc_cast_castSucc s N hrel i.succ
  have hprev : (s.snoc N hrel) (i.castSucc.castSucc) = s i.castSucc := by
    simpa using RelSeries.snoc_cast_castSucc s N hrel i.castSucc
  let eNum : (s.snoc N hrel) (i.castSucc.succ) ≃ₗ[R] s i.succ :=
    LinearEquiv.ofEq _ _ hsucc
  have hmap :
      (((s.snoc N hrel) (i.castSucc.castSucc)).submoduleOf ((s.snoc N hrel) (i.castSucc.succ))).map
        (eNum : ((s.snoc N hrel) (i.castSucc.succ) →ₗ[R] s i.succ)) =
      (s i.castSucc).submoduleOf (s i.succ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [eNum, hsucc, hprev] using hy
    · intro hx
      refine ⟨eNum.symm x, ?_, ?_⟩
      · simpa [eNum, hsucc, hprev] using hx
      · simpa using eNum.apply_symm_apply x
  refine ⟨i.castSucc, ?_⟩
  -- The earlier successive quotients are unchanged under `snoc`, so the old witness survives.
  exact ⟨(Submodule.Quotient.equiv _ _ eNum hmap).trans e⟩

/-- Helper for Lemma 10.63.4: the prime quotient used in the final `snoc` step is itself one of
the prime factors of the extended filtration. -/
lemma PrimeCyclicFiltration.mem_primeFactors_snoc_last
    {N : Submodule R M} {𝔭 : PrimeSpectrum R}
    (hle : s.last ≤ N)
    (h𝔭 : Nonempty ((↥N ⧸ s.last.submoduleOf N) ≃ₗ[R] R ⧸ 𝔭.asIdeal)) :
    𝔭 ∈ PrimeCyclicFiltration.primeFactors (s.snoc N ⟨hle, 𝔭, h𝔭⟩) := by
  have hstep : Nonempty ((↥N ⧸ s.last.submoduleOf N) ≃ₗ[R] R ⧸ 𝔭.asIdeal) := h𝔭
  rcases hstep with ⟨e⟩
  have hlast : (s.snoc N ⟨hle, 𝔭, h𝔭⟩).last = N := by
    simp
  have hprev : (s.snoc N ⟨hle, 𝔭, h𝔭⟩) (Fin.last s.length).castSucc = s.last := by
    simpa using RelSeries.snoc_cast_castSucc s N ⟨hle, 𝔭, h𝔭⟩ (Fin.last s.length)
  let eNum : (s.snoc N ⟨hle, 𝔭, h𝔭⟩).last ≃ₗ[R] N :=
    LinearEquiv.ofEq _ _ hlast
  have hmap :
      (((s.snoc N ⟨hle, 𝔭, h𝔭⟩) (Fin.last s.length).castSucc).submoduleOf
          ((s.snoc N ⟨hle, 𝔭, h𝔭⟩).last)).map
        (eNum : ((s.snoc N ⟨hle, 𝔭, h𝔭⟩).last →ₗ[R] N)) =
      s.last.submoduleOf N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [eNum, hlast, hprev] using hy
    · intro hx
      refine ⟨eNum.symm x, ?_, ?_⟩
      · simpa [eNum, hlast, hprev] using hx
      · simpa using eNum.apply_symm_apply x
  refine ⟨Fin.last s.length, ?_⟩
  -- The last successive quotient of the extended series is exactly the new prime quotient.
  exact ⟨(Submodule.Quotient.equiv _ _ eNum hmap).trans e⟩

/-- Helper for Lemma 10.63.4: the textbook associated primes of the prime quotient `R ⧸ q` form
the singleton `{q.asIdeal}`. -/
lemma associatedPrimesOfModule_quotient_prime_eq_singleton (q : PrimeSpectrum R) :
    associatedPrimesOfModule R (R ⧸ q.asIdeal) = {q.asIdeal} := by
  ext I
  constructor
  · intro hI
    rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hI
    rcases hI with ⟨hprime, x, rfl⟩
    have hx_ne : x ≠ 0 := by
      intro hx
      have htop : Ideal.torsionOf R (R ⧸ q.asIdeal) x = ⊤ := by
        simpa [hx] using (Ideal.torsionOf_eq_top_iff (R := R) x).2 hx
      exact hprime.ne_top (by simpa [htop])
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha_not_mem : a ∉ q.asIdeal := by
      intro ha
      exact hx_ne ((Ideal.Quotient.eq_zero_iff_mem).2 ha)
    simp only [Set.mem_singleton_iff]
    apply Ideal.ext
    intro r
    constructor
    · intro hr
      rw [Ideal.mem_torsionOf_iff] at hr
      have hmul : r * a ∈ q.asIdeal := by
        change Ideal.Quotient.mk q.asIdeal (r * a) = 0 at hr
        exact (Ideal.Quotient.eq_zero_iff_mem).1 hr
      exact q.isPrime.mem_or_mem hmul |>.resolve_right ha_not_mem
    · intro hr
      rw [Ideal.mem_torsionOf_iff]
      change Ideal.Quotient.mk q.asIdeal (r * a) = 0
      exact (Ideal.Quotient.eq_zero_iff_mem).2 <| by
        simpa [mul_comm] using q.asIdeal.mul_mem_left a hr
  · intro hI
    rw [Set.mem_singleton_iff] at hI
    subst I
    rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf]
    refine ⟨q.isPrime, (1 : R ⧸ q.asIdeal), ?_⟩
    apply Ideal.ext
    intro r
    constructor
    · intro hr
      rw [Ideal.mem_torsionOf_iff]
      change Ideal.Quotient.mk q.asIdeal (r * 1) = 0
      simpa using (Ideal.Quotient.eq_zero_iff_mem).2 hr
    · intro hr
      rw [Ideal.mem_torsionOf_iff] at hr
      change Ideal.Quotient.mk q.asIdeal (r * 1) = 0 at hr
      simpa using (Ideal.Quotient.eq_zero_iff_mem).1 hr

/-- Helper for Lemma 10.63.4: if a prime-cyclic filtration starts at `0`, then every textbook
associated prime of its final stage comes from one of its prime factors. -/
lemma associatedPrimesOfLast_subset_image_primeFactors_of_prime_quotient_filtration
    (hs₀ : s.head = ⊥) :
    associatedPrimesOfModule R s.last ⊆ PrimeSpectrum.asIdeal '' s.primeFactors := by
  -- We follow the source proof by peeling off the last quotient and recursing on the shorter
  -- filtration.
  revert hs₀
  induction s using RelSeries.inductionOn' with
  | singleton N =>
      intro hs₀ I hI
      have hN : N = ⊥ := hs₀
      subst N
      have hI' : I ∈ associatedPrimesOfModule R (⊥ : Submodule R M) := by
        simpa using hI
      rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hI'
      rcases hI' with ⟨hprime, m, hm⟩
      have hm_zero : m = 0 := Subsingleton.elim _ _
      have htop : Ideal.torsionOf R (⊥ : Submodule R M) m = ⊤ :=
        (Ideal.torsionOf_eq_top_iff (R := R) m).2 hm_zero
      have : I = ⊤ := by simpa [hm, htop]
      exact (hprime.ne_top this).elim
  | snoc s N hrel ih =>
      rcases hrel with ⟨hle, q, hq⟩
      intro hs₀ I hI
      rw [RelSeries.last_snoc] at hI
      have hI_N : I ∈ associatedPrimesOfModule R N := hI
      have hsubmodule :
          associatedPrimesOfModule R (s.last.submoduleOf N) = associatedPrimesOfModule R s.last := by
        simpa using
          (LinearEquiv.associatedPrimesOfModule_eq
            (R := R) (M := s.last.submoduleOf N) (M' := s.last)
            (Submodule.submoduleOfEquivOfLe hle))
      have hsubset :
          associatedPrimesOfModule R N ⊆
            associatedPrimesOfModule R (s.last.submoduleOf N) ∪
              associatedPrimesOfModule R (N ⧸ s.last.submoduleOf N) :=
        associatedPrimesOfModule.subset_union_of_exact
          (f := Submodule.subtype (s.last.submoduleOf N)) (g := (s.last.submoduleOf N).mkQ)
          (Submodule.injective_subtype _) (LinearMap.exact_subtype_mkQ _)
      have hI' := hsubset hI_N
      rcases hI' with hI' | hI'
      · -- Associated primes already coming from the penultimate stage remain prime factors after
        -- adding the last quotient.
        have hI_last : I ∈ associatedPrimesOfModule R s.last := by
          rw [← hsubmodule]
          exact hI'
        rcases ih hs₀ hI_last with ⟨𝔭, h𝔭, rfl⟩
        exact ⟨𝔭, PrimeCyclicFiltration.primeFactors_subset_snoc (s := s) ⟨hle, q, hq⟩ h𝔭, rfl⟩
      · -- The quotient term contributes only the last prime factor, since it is isomorphic to
        -- `R ⧸ q`.
        have hquot :
            associatedPrimesOfModule R (N ⧸ s.last.submoduleOf N) = {q.asIdeal} := by
          rcases hq with ⟨e⟩
          rw [LinearEquiv.associatedPrimesOfModule_eq
            (R := R) (M := N ⧸ s.last.submoduleOf N) (M' := R ⧸ q.asIdeal) e]
          exact associatedPrimesOfModule_quotient_prime_eq_singleton (R := R) q
        rw [hquot, Set.mem_singleton_iff] at hI'
        exact ⟨q, PrimeCyclicFiltration.mem_primeFactors_snoc_last (s := s) hle hq, hI'.symm⟩

/-- Owner-form companion to Lemma 10.63.4: the associated prime points of `M` lie among the prime
factors occurring in the given prime-cyclic filtration. -/
theorem associatedPrimePointsOfModule_subset_primeFactors_of_prime_quotient_filtration
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    :
    asIdeal ⁻¹' associatedPrimesOfModule R M ⊆
      s.primeFactors := by
  have hlast :
      associatedPrimesOfModule R s.last ⊆ PrimeSpectrum.asIdeal '' s.primeFactors :=
    associatedPrimesOfLast_subset_image_primeFactors_of_prime_quotient_filtration
      (R := R) (M := M) s hs₀
  have htop :
      associatedPrimesOfModule R s.last = associatedPrimesOfModule R M := by
    rw [hs_top]
    simpa using
      (LinearEquiv.associatedPrimesOfModule_eq
        (R := R) (M := (⊤ : Submodule R M)) (M' := M) Submodule.topEquiv)
  intro 𝔭 h𝔭
  have h𝔭_mem : 𝔭.asIdeal ∈ associatedPrimesOfModule R M := by
    simpa using h𝔭
  have h𝔭_last : 𝔭.asIdeal ∈ associatedPrimesOfModule R s.last := by
    rw [htop]
    exact h𝔭_mem
  rcases hlast h𝔭_last with ⟨q, hq, hq_eq⟩
  have : q = 𝔭 := PrimeSpectrum.ext hq_eq
  simpa [this] using hq

variable (p : Fin s.length → PrimeSpectrum R)

/-- Lemma 10.63.4: if `M` admits a finite filtration by submodules whose successive quotients are
isomorphic to quotients `R ⧸ p i` by prime ideals, then every textbook-associated prime of `M`
comes from one of the prime points occurring in that filtration. This ideal-valued form is the
image of the prime-spectrum owner statement under `PrimeSpectrum.asIdeal`. -/
-- Proof sketch: induct on the length of the relation series. For the last step, apply
-- the source-facing associated-prime description to the last short exact sequence
-- `0 → s.eraseLast.last → s.last → quotient → 0`; identify the associated primes of the quotient
-- with the singleton `{(p i).asIdeal}` using the chosen quotient isomorphism and the cyclic
-- description of
-- `Ass(R ⧸ p)`, then use the induction hypothesis on the truncated filtration.
@[stacks 00LB]
theorem associatedPrimesOfModule_subset_range_of_prime_quotient_filtration
    (hp : ∀ i,
      Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    : associatedPrimesOfModule R M ⊆ asIdeal '' Set.range p := by
  have hsubset :
      asIdeal ⁻¹' associatedPrimesOfModule R M ⊆ Set.range p := by
    simpa [s.primeFactors_eq_range p hp] using
      associatedPrimePointsOfModule_subset_primeFactors_of_prime_quotient_filtration s hs₀ hs_top
  intro I hI
  have hpoint :
      (⟨I, hI.1⟩ : PrimeSpectrum R) ∈ asIdeal ⁻¹' associatedPrimesOfModule R M := by
    simpa
  rcases hsubset hpoint with ⟨i, hi⟩
  refine ⟨p i, ⟨⟨i, rfl⟩, ?_⟩⟩
  exact congrArg asIdeal hi

/-- In the Noetherian setting, Lemma 10.63.4 can be restated using the canonical mathlib set
`associatedPrimes R M`. -/
theorem associatedPrimes_subset_range_of_prime_quotient_filtration [IsNoetherianRing R]
    (hp : ∀ i,
      Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    : associatedPrimes R M ⊆ asIdeal '' Set.range p := by
  simpa [associatedPrimesOfModule_eq_associatedPrimes R M] using
    associatedPrimesOfModule_subset_range_of_prime_quotient_filtration s p hp hs₀ hs_top

end
