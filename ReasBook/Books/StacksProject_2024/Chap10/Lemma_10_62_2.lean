import Mathlib.RingTheory.Support
import StacksProject_2024.Chap10.Lemma_10_62_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum RelSeries

section SupportAndDimensionOfModules

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace PrimeCyclicFiltration

/-- The `i`-th successive quotient in a prime-cyclic filtration. -/
abbrev successiveQuotient (s : PrimeCyclicFiltration R M) (i : Fin s.length) :=
  (s i.succ) ⧸ (s i.castSucc).submoduleOf (s i.succ)

/-- The prime points occurring as successive prime-quotient factors of a finite prime-cyclic
filtration. This is derived from the owner relation `PrimeCyclicFiltration R M`, not from an
auxiliary chosen enumeration. -/
def primeFactors (s : PrimeCyclicFiltration R M) : Set (PrimeSpectrum R) :=
  { 𝔭 | ∃ i : Fin s.length,
      Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ 𝔭.asIdeal) }

end PrimeCyclicFiltration

/-- Helper for Lemma 10.62.2: any module linearly equivalent to a prime quotient has support equal
to the corresponding closed subset of `Spec R`. -/
lemma support_eq_zeroLocus_of_nonempty_linearEquiv_quotient
    {Q : Type v} [AddCommGroup Q] [Module R Q] {𝔭 : PrimeSpectrum R}
    (hQ : Nonempty (Q ≃ₗ[R] R ⧸ 𝔭.asIdeal)) :
    Module.support R Q = zeroLocus 𝔭.asIdeal := by
  rcases hQ with ⟨e⟩
  haveI : Module.Finite R Q := Module.Finite.equiv e.symm
  -- Transport support across the linear equivalence and then identify the quotient annihilator.
  rw [LinearEquiv.support_eq e]
  simpa [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

/-- Helper for Lemma 10.62.2: a module linearly equivalent to both `R ⧸ 𝔭` and `R ⧸ 𝔮`
determines the same prime point. -/
lemma primeSpectrum_eq_of_nonempty_linearEquiv_quotients
    {Q : Type v} [AddCommGroup Q] [Module R Q] {𝔭 𝔮 : PrimeSpectrum R}
    (h𝔭 : Nonempty (Q ≃ₗ[R] R ⧸ 𝔭.asIdeal))
    (h𝔮 : Nonempty (Q ≃ₗ[R] R ⧸ 𝔮.asIdeal)) :
    𝔭 = 𝔮 := by
  rcases h𝔭 with ⟨e⟩
  rcases h𝔮 with ⟨f⟩
  -- Compare the two prime points through the annihilator of the common module.
  apply PrimeSpectrum.ext
  calc
    𝔭.asIdeal = Module.annihilator R (R ⧸ 𝔭.asIdeal) := by
      simp [Ideal.annihilator_quotient]
    _ = Module.annihilator R Q := by
      symm
      simpa using (LinearEquiv.annihilator_eq e)
    _ = Module.annihilator R (R ⧸ 𝔮.asIdeal) := by
      simpa using (LinearEquiv.annihilator_eq f)
    _ = 𝔮.asIdeal := by
      simp [Ideal.annihilator_quotient]

variable (s : PrimeCyclicFiltration R M)

/-- Helper for Lemma 10.62.2: adjoining one more quotient step at the end of a filtration leaves
the earlier successive quotients unchanged up to linear equivalence. -/
lemma PrimeCyclicFiltration.successiveQuotient_snoc_castSucc_equiv
    {N : Submodule R M} (hrel : s.last.IsQuotientEquivQuotientPrime N) (i : Fin s.length) :
    Nonempty
      (PrimeCyclicFiltration.successiveQuotient (s := s.snoc N hrel) i.castSucc ≃ₗ[R]
        PrimeCyclicFiltration.successiveQuotient (s := s) i) := by
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
    -- Identify the transported penultimate stage with the original submodule.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [eNum, hsucc, hprev] using hy
    · intro hx
      refine ⟨eNum.symm x, ?_, ?_⟩
      · simpa [eNum, hsucc, hprev] using hx
      · simpa using eNum.apply_symm_apply x
  exact ⟨Submodule.Quotient.equiv _ _ eNum hmap⟩

/-- Helper for Lemma 10.62.2: the final successive quotient of a `snoc` filtration is the new
quotient `N / s.last`. -/
lemma PrimeCyclicFiltration.successiveQuotient_snoc_last_equiv
    {N : Submodule R M} {𝔭 : PrimeSpectrum R}
    (hle : s.last ≤ N)
    (h𝔭 : Nonempty ((↥N ⧸ s.last.submoduleOf N) ≃ₗ[R] R ⧸ 𝔭.asIdeal)) :
    Nonempty
      (PrimeCyclicFiltration.successiveQuotient (s := s.snoc N ⟨hle, 𝔭, h𝔭⟩) (Fin.last s.length) ≃ₗ[R]
        (↥N ⧸ s.last.submoduleOf N)) := by
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
    -- Transport the penultimate stage along the identification of the last term with `N`.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [eNum, hlast, hprev] using hy
    · intro hx
      refine ⟨eNum.symm x, ?_, ?_⟩
      · simpa [eNum, hlast, hprev] using hx
      · simpa using eNum.apply_symm_apply x
  exact ⟨Submodule.Quotient.equiv _ _ eNum hmap⟩

/-- Helper for Lemma 10.62.2: a prime-cyclic filtration starting at `0` admits an enumeration of
its successive prime factors whose zero loci cover the support of the last stage. -/
lemma PrimeCyclicFiltration.exists_enumeration_support_last_eq_iUnion_zeroLocus
    (hs₀ : s.head = ⊥) :
    ∃ p : Fin s.length → PrimeSpectrum R,
      (∀ i : Fin s.length,
        Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal)) ∧
      Module.support R s.last = ⋃ i, zeroLocus (p i).asIdeal := by
  revert hs₀
  induction s using RelSeries.inductionOn' with
  | singleton N =>
      intro hs₀
      have hN : N = ⊥ := hs₀
      subst hN
      refine ⟨Fin.elim0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · -- The base filtration has no successive quotients, so both sides are empty.
        simpa using (Module.support_eq_empty (R := R) (M := (⊥ : Submodule R M)))
  | snoc s N hrel ih =>
      rcases hrel with ⟨hle, 𝔭, h𝔭⟩
      intro hs₀
      rcases ih hs₀ with ⟨p, hp, hsupport⟩
      refine ⟨Fin.snoc p 𝔭, ?_, ?_⟩
      · intro i
        -- Split the extended index into the old part and the final new quotient.
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · have hquot : Nonempty ((↥N ⧸ s.last.submoduleOf N) ≃ₗ[R] R ⧸ 𝔭.asIdeal) := h𝔭
          have hlastQuot :=
            PrimeCyclicFiltration.successiveQuotient_snoc_last_equiv
              (s := s) (N := N) hle hquot
          have hlast :
              Nonempty
                (PrimeCyclicFiltration.successiveQuotient
                    (s := s.snoc N ⟨hle, 𝔭, h𝔭⟩) (Fin.last s.length) ≃ₗ[R]
                  R ⧸ 𝔭.asIdeal) := by
            rcases hlastQuot with ⟨e₀⟩
            rcases hquot with ⟨e⟩
            exact ⟨e₀.trans e⟩
          rw [Fin.snoc_last]
          exact hlast
        · have hcast :=
            PrimeCyclicFiltration.successiveQuotient_snoc_castSucc_equiv
              (s := s) (N := N) ⟨hle, 𝔭, h𝔭⟩ j
          have hold :
              Nonempty
                (PrimeCyclicFiltration.successiveQuotient
                    (s := s.snoc N ⟨hle, 𝔭, h𝔭⟩) j.castSucc ≃ₗ[R]
                  R ⧸ (p j).asIdeal) := by
            rcases hcast with ⟨e₀⟩
            rcases hp j with ⟨e⟩
            exact ⟨e₀.trans e⟩
          rw [Fin.snoc_castSucc]
          exact hold
      · have hsupport_exact :
            Module.support R N =
              Module.support R (s.last.submoduleOf N) ∪
                Module.support R (N ⧸ s.last.submoduleOf N) := by
          -- The new last stage sits in the canonical short exact sequence
          -- `0 → s.last → N → N / s.last → 0`.
          exact Module.support_of_exact
            (LinearMap.exact_subtype_mkQ _)
            (Submodule.injective_subtype _)
            (Submodule.mkQ_surjective _)
        have hsupport_prev :
            Module.support R (s.last.submoduleOf N) = Module.support R s.last := by
          -- Transport the support of the embedded penultimate stage back to `s.last`.
          simpa using
            (LinearEquiv.support_eq
              (Submodule.submoduleOfEquivOfLe hle))
        have hsupport_quot :
            Module.support R (N ⧸ s.last.submoduleOf N) = zeroLocus 𝔭.asIdeal := by
          -- Rewrite the new prime quotient as the closed subset `V(𝔭)`.
          exact support_eq_zeroLocus_of_nonempty_linearEquiv_quotient (R := R) h𝔭
        -- Combine the old support formula with the support decomposition for the final step.
        calc
          Module.support R (s.snoc N ⟨hle, 𝔭, h𝔭⟩).last = Module.support R N := by
            rw [RelSeries.last_snoc]
          _ =
              Module.support R (s.last.submoduleOf N) ∪
                Module.support R (N ⧸ s.last.submoduleOf N) := hsupport_exact
          _ = Module.support R s.last ∪ zeroLocus 𝔭.asIdeal := by
            rw [hsupport_prev, hsupport_quot]
          _ = (⋃ i, zeroLocus (p i).asIdeal) ∪ zeroLocus 𝔭.asIdeal := by
            rw [hsupport]
          _ =
              ⋃ i,
                zeroLocus
                  ((((Fin.snoc p 𝔭 : Fin (s.length + 1) → PrimeSpectrum R) i).asIdeal) : Set R) := by
            ext 𝔮
            simp [Fin.exists_iff_castSucc, or_comm]

-- Proof sketch: induct on the length of the filtration. For each successive quotient, use
-- a chosen representative of the nonempty family of quotient isomorphisms to identify its
-- support with `Supp (R ⧸ pᵢ)`, rewrite that support as `V(pᵢ)` via `Module.support_eq_zeroLocus`,
-- and combine the stages using `Module.support_of_exact`.
/-- Lemma 10.62.2: for a finite prime cyclic filtration `s` of `M`, the support of `M` is the
union of the closed sets `V(𝔭)` as `𝔭` ranges over the prime points occurring in `s`. -/
theorem support_eq_iUnion_zeroLocus_of_prime_cyclic_filtration
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤) :
    Module.support R M = ⋃ 𝔭 : s.primeFactors, zeroLocus 𝔭.1.asIdeal := by
  obtain ⟨p, hp, hsupport⟩ :=
    PrimeCyclicFiltration.exists_enumeration_support_last_eq_iUnion_zeroLocus
      (R := R) (M := M) s hs₀
  have hrange : s.primeFactors = Set.range p := by
    ext 𝔭
    constructor
    · rintro ⟨i, hi⟩
      have hprime :
          𝔭 = p i :=
        primeSpectrum_eq_of_nonempty_linearEquiv_quotients
          (R := R) (Q := s.successiveQuotient i) hi (hp i)
      exact ⟨i, hprime.symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, hp i⟩
  have hsupport_top : Module.support R s.last = Module.support R M := by
    -- Replace the last stage of the filtration with the ambient module via `s.last = ⊤`.
    rw [hs_top]
    simpa using
      (LinearEquiv.support_eq (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M))
  -- First compute the support from the chosen enumeration, then rewrite the indexing set intrinsically.
  calc
    Module.support R M = Module.support R s.last := by
      symm
      exact hsupport_top
    _ = ⋃ i, zeroLocus (p i).asIdeal := hsupport
    _ = ⋃ 𝔭 : Set.range p, zeroLocus 𝔭.1.asIdeal := by
      ext 𝔮
      simp [Set.mem_range]
    _ = ⋃ 𝔭 : s.primeFactors, zeroLocus 𝔭.1.asIdeal := by
      rw [hrange]

/-- The prime points occurring as successive quotients in a finite prime cyclic filtration of `M`
form a subset of `Module.support R M`. This is the invariant owner-form of the textbook statement
“every prime appearing in the filtration lies in the support.” -/
theorem primeFactors_subset_support_of_prime_cyclic_filtration
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤) :
    s.primeFactors ⊆ Module.support R M := by
  intro 𝔭 h𝔭
  rw [support_eq_iUnion_zeroLocus_of_prime_cyclic_filtration (R := R) (M := M) s hs₀ hs_top]
  -- Choose the indexed zero locus corresponding to `𝔭` itself.
  refine Set.mem_iUnion.2 ?_
  refine ⟨⟨𝔭, h𝔭⟩, ?_⟩
  exact (PrimeSpectrum.mem_zeroLocus 𝔭 𝔭.asIdeal).2 le_rfl

variable (p : Fin s.length → PrimeSpectrum R)

/-- A chosen enumeration of the prime-quotient factors of `s` recovers the intrinsic owner set
`s.primeFactors`. This is a bridge from a presentation by indices to the filtration itself. -/
theorem PrimeCyclicFiltration.primeFactors_eq_range
    (hp : ∀ i : Fin s.length,
      Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal)) :
    s.primeFactors = Set.range p := by
  ext 𝔭
  constructor
  · rintro ⟨i, hi⟩
    -- Compare the intrinsic witness for index `i` with the chosen presentation `p i`.
    have hprime :
        𝔭 = p i :=
      primeSpectrum_eq_of_nonempty_linearEquiv_quotients
        (R := R) (Q := s.successiveQuotient i) hi (hp i)
    exact ⟨i, hprime.symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, hp i⟩

end SupportAndDimensionOfModules
