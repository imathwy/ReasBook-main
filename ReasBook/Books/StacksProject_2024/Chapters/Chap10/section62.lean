import Mathlib
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Support
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_62_1 (from Chap10) -/
universe u v

open Submodule

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: prime-quotient filtrations of finite modules over a Noetherian ring;
- `core/canonical`: `RelSeries` over the relation `Submodule.IsQuotientEquivQuotientPrime`;
- `bridge/view`: the chapter shorthand `PrimeCyclicFiltration R M`, retained because it is the
  stable vocabulary used by the immediate Chapter 10 downstream API;
- primitive data: only the relation series itself, with prime factors and successive quotients as
  derived API in later files.
-/

/-- Chapter-shared shorthand for the canonical `RelSeries` owner whose successive quotients are
prime quotients `R ⧸ p`. -/
abbrev PrimeCyclicFiltration :=
  RelSeries {(N₁, N₂) : Submodule R M × Submodule R M |
    IsQuotientEquivQuotientPrime N₁ N₂}

end

/- Lemma 10.62.1: if `R` is Noetherian and `M` is a finite `R`-module, then there exists a finite
filtration `0 = M₀ ≤ M₁ ≤ ... ≤ Mₙ = M` such that each successive quotient `Mᵢ₊₁ / Mᵢ` is
linearly isomorphic to `R ⧸ pᵢ` for some prime ideal `pᵢ` of `R`. This is exactly the canonical
mathlib theorem `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime`. -/
recall IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime

/-! ### Lemma_10_62_2 (from Chap10) -/
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

/-! ### Lemma_10_62_3 (from Chap10) -/
open IsLocalRing PrimeSpectrum

universe u v

section SupportAndDimensionOfModules

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: use the owner support-annihilator criterion from Lemma `10.62.4`. If
-- `Module.support R M = {closedPoint R}`, then `Module.support R M ⊆ V(maximalIdeal R)`, so some
-- power of `maximalIdeal R` annihilates `M`; Lemma `10.52.8` turns that into finite length.
-- Conversely, finite length gives such a power by Lemma `10.52.4`, hence the same support
-- inclusion via Lemma `10.62.4`. The local closed point lies in the support of a nontrivial
-- module, so the inclusion is an equality.
/-- Lemma 10.62.3: for a nonzero finite module over a Noetherian local ring, the support is the
singleton consisting of the closed point of `Spec R` if and only if the module has finite length
over `R`. -/
theorem support_eq_singleton_closedPoint_iff_isFiniteLength [Nontrivial M] :
    Module.support R M = ({closedPoint R} : Set (PrimeSpectrum R)) ↔ IsFiniteLength R M := by
  have hclosed :
      ({closedPoint R} : Set (PrimeSpectrum R)) = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
    simp [PrimeSpectrum.zeroLocus_eq_singleton, IsLocalRing.closedPoint]
  have hsupport :
      Module.support R M ⊆ PrimeSpectrum.zeroLocus (maximalIdeal R) ↔ IsFiniteLength R M := by
    rw [← Module.exists_pow_smul_top_eq_bot_iff_support_subset_zeroLocus
      (maximalIdeal R) (Ideal.fg_of_isNoetherianRing (maximalIdeal R))]
    constructor
    · rintro ⟨n, hn⟩
      exact isFiniteLength_of_pow_smul_eq_bot (maximalIdeal R)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) hn
    · exact exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength
  constructor
  · intro hsupp
    have hsubset : Module.support R M ⊆ PrimeSpectrum.zeroLocus (maximalIdeal R) := by
      rw [hsupp, hclosed]
    exact hsupport.mp hsubset
  · intro hM
    exact Set.Subset.antisymm (by simpa [hclosed] using hsupport.mpr hM) <|
      Set.singleton_subset_iff.mpr <| IsLocalRing.closedPoint_mem_support R M

end SupportAndDimensionOfModules

/-! ### Lemma_10_62_4 (from Chap10) -/
universe u v

section

open PrimeSpectrum

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Module

-- Proof sketch: rewrite `support R M` as `zeroLocus (annihilator R M)` via
-- `support_eq_zeroLocus`; then `zeroLocus_subset_zeroLocus_iff` identifies the support inclusion
-- with `I ≤ (annihilator R M).radical`. Since `I` is finitely generated, this is equivalent to the
-- existence of `n` such that `I ^ n ≤ annihilator R M`; `Submodule.le_annihilator_iff` then
-- condition as the textbook criterion `(I ^ n) • (⊤ : Submodule R M) = ⊥`.
/-- Lemma 10.62.4, owner-facing form: for a finite module `M` and a finitely generated ideal `I`,
support of `M` is contained in `V(I)` if and only if some power of `I` is contained in the
annihilator of `M`. -/
theorem exists_pow_le_annihilator_iff_support_subset_zeroLocus
    (I : Ideal R) (hI : I.FG) :
    (∃ n : ℕ, I ^ n ≤ annihilator R M) ↔ support R M ⊆ zeroLocus I := by
  rw [support_eq_zeroLocus, zeroLocus_subset_zeroLocus_iff]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
        rw [pow_zero] at hn
        have htop : annihilator R M = ⊤ := by
          simpa [Ideal.one_eq_top] using hn
        simp [htop, Ideal.radical_top]
    | succ n =>
        calc
          I ≤ (I ^ (n + 1)).radical := by
            simpa [I.radical_pow n.succ_ne_zero] using (Ideal.le_radical : I ≤ I.radical)
          _ ≤ (annihilator R M).radical := Ideal.radical_mono hn
  · intro h
    exact Ideal.exists_pow_le_of_le_radical_of_fg h hI

/-- Lemma 10.62.4, textbook form: the same support criterion expressed by the vanishing condition
`(I ^ n) • (⊤ : Submodule R M) = ⊥`. -/
theorem exists_pow_smul_top_eq_bot_iff_support_subset_zeroLocus
    (I : Ideal R) (hI : I.FG) :
    (∃ n : ℕ, (I ^ n) • (⊤ : Submodule R M) = ⊥) ↔ support R M ⊆ zeroLocus I := by
  rw [← exists_pow_le_annihilator_iff_support_subset_zeroLocus I hI]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by
      simpa [Submodule.annihilator_top] using
        (Submodule.le_annihilator_iff.mpr hn : I ^ n ≤ (⊤ : Submodule R M).annihilator)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa [Submodule.annihilator_top] using
      (Submodule.le_annihilator_iff.mp <| by
        simpa [Submodule.annihilator_top] using
          (hn : I ^ n ≤ annihilator R M) : I ^ n • (⊤ : Submodule R M) = ⊥)⟩

end Module

end

/-! ### Lemma_10_62_5 (from Chap10) -/
universe u v

open PrimeSpectrum

section SupportAndDimensionOfModules

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

variable (s : PrimeCyclicFiltration R M)

-- Proof sketch: use Lemma 10.62.2 to identify `Module.support R M` with the union of the zero
-- loci of the prime ideals appearing as successive prime-quotient factors of `s`. A prime point is
-- minimal in that union exactly when it is minimal among those prime factors.
/-- Lemma 10.62.5: a prime point of `Spec R` is minimal among the prime factors occurring in a
finite prime-cyclic filtration of `M` from `0` to `M` if and only if it is a minimal element of
`Module.support R M`. -/
theorem minimal_primeFactor_iff_minimal_support_of_prime_cyclic_filtration
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    (𝔭 : PrimeSpectrum R) :
    Minimal (· ∈ s.primeFactors) 𝔭 ↔
      Minimal (· ∈ Module.support R M) 𝔭 := by
  have hsupport :=
    support_eq_iUnion_zeroLocus_of_prime_cyclic_filtration s hs₀ hs_top
  have hprimeFactors :=
    primeFactors_subset_support_of_prime_cyclic_filtration s hs₀ hs_top
  constructor
  · intro h𝔭
    refine ⟨hprimeFactors h𝔭.1, ?_⟩
    intro q hq hq𝔭
    rw [hsupport] at hq
    rcases Set.mem_iUnion.1 hq with ⟨r, hrq⟩
    have hrq' : r.1 ≤ q := by
      simpa using (mem_zeroLocus q (r.1.asIdeal : Set R)).1 hrq
    exact (h𝔭.2 r.2 (hrq'.trans hq𝔭)).trans hrq'
  · intro h𝔭
    have h𝔭_support : 𝔭 ∈ Module.support R M := h𝔭.1
    rw [hsupport] at h𝔭_support
    rcases Set.mem_iUnion.1 h𝔭_support with ⟨r, hr𝔭⟩
    have hr𝔭' : r.1 ≤ 𝔭 := by
      simpa using (mem_zeroLocus 𝔭 (r.1.asIdeal : Set R)).1 hr𝔭
    have h𝔭r : 𝔭 ≤ r.1 := h𝔭.2
      (hprimeFactors r.2) hr𝔭'
    have h𝔭_eq : 𝔭 = r.1 := le_antisymm h𝔭r hr𝔭'
    refine ⟨h𝔭_eq ▸ r.2, ?_⟩
    intro q hq hq𝔭
    exact h𝔭.2 (hprimeFactors hq) hq𝔭

end SupportAndDimensionOfModules

/-! ### Lemma_10_62_6 (from Chap10) -/
universe u v

open CategoryTheory
open CategoryTheory.ShortComplex
open IsLocalRing
open scoped Ideal

private theorem cast_hilbertSamuelPolynomialDegree_eq_supportDim_of_prime_quotient
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : PrimeSpectrum R) :
    Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R (R ⧸ p.asIdeal)) =
      Module.supportDim R (R ⧸ p.asIdeal) := by
  let S := R ⧸ p.asIdeal
  letI : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective
  have hsurj : Function.Surjective (algebraMap R S) := by
    simpa [S, Ideal.Quotient.algebraMap_eq] using
      (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk p.asIdeal))
  have hmap :
      Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S := by
    exact IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) hsurj
  have hchi :
      ∀ n : ℕ,
        χ_(maximalIdeal R) S n =
          χ_(maximalIdeal S) S n := by
    intro n
    simp only [Ideal.hilbertSamuelChi]
    let J : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R ^ (n + 1))
    have hJ :
        (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R S)) = J.restrictScalars R := by
      simp [J, Ideal.smul_top_eq_map, Ideal.map_pow]
    calc
      Module.length R (S ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R S))) =
          Module.length R (S ⧸ J.restrictScalars R) := by
            rw [hJ]
      _ = Module.length R (S ⧸ J) := by
            exact LinearEquiv.length_eq (Submodule.Quotient.restrictScalarsEquiv R J)
      _ = Module.length S (S ⧸ J) := by
            rw [Module.length_eq_of_surjective hsurj]
      _ = Module.length S (S ⧸ (maximalIdeal S ^ (n + 1) : Ideal S)) := by
            have hJ' : J = maximalIdeal S ^ (n + 1) := by
              change
                Ideal.map (algebraMap R S) (maximalIdeal R ^ (n + 1)) =
                  maximalIdeal S ^ (n + 1)
              rw [Ideal.map_pow, hmap]
            rw [hJ']
      _ = Module.length S (S ⧸ (maximalIdeal S ^ (n + 1) • (⊤ : Submodule S S))) := by
            rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hdeg :
      hilbertSamuelPolynomialDegree R S = hilbertSamuelPolynomialDegree S S := by
    let P := hilbertSamuelChiPolynomial S S
    have hP :
        ∀ᶠ n : ℕ in Filter.atTop,
          P.eval (n : ℚ) = ((χ_(maximalIdeal S) S n).toNat : ℚ) :=
        hilbertSamuelChiPolynomial_eventuallyEq S S
    have hPR :
        ∀ᶠ n : ℕ in Filter.atTop,
          P.eval (n : ℚ) = ((χ_(maximalIdeal R) S n).toNat : ℚ) := by
      filter_upwards [hP] with n hn
      simpa [hchi n] using hn
    rw [hilbertSamuelPolynomialDegree_eq_degree R S hPR, hilbertSamuelPolynomialDegree]
  have hbot : ringKrullDim S ≠ ⊥ := by
    exact ringKrullDim_ne_bot
  have htop : ringKrullDim S ≠ ⊤ := by
    exact ringKrullDim_ne_top
  let d : ℕ := ((ringKrullDim S).unbot hbot).toNat
  have hdim : ringKrullDim S = d := by
    have hneTop : (ringKrullDim S).unbot hbot ≠ ⊤ := by
      intro h
      exact htop (by
        simpa [WithBot.coe_unbot] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) h)
    have hdim' : ((ringKrullDim S).unbot hbot : WithBot ℕ∞) = d := by
      simpa [d] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
    calc
      ringKrullDim S = (ringKrullDim S).unbot hbot := by
        exact (WithBot.coe_unbot (ringKrullDim S) hbot).symm
      _ = d := hdim'
  have htfae :
      List.TFAE [ringKrullDim S = d, hilbertSamuelPolynomialDegree S S = d, _] :=
    local_noetherian_ring_dimension_tfae d
  have hdegS : hilbertSamuelPolynomialDegree S S = d :=
    (htfae.out 0 1).mp hdim
  calc
    Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R S) =
        Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree S S) := by
          rw [hdeg]
    _ = ringKrullDim S := by
          simp [hdegS, hdim]
    _ = Module.supportDim R S := by
          simpa [S] using (Module.supportDim_quotient_eq_ringKrullDim p.asIdeal).symm

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Source/core/bridge triage:
-- * source-facing: Lemma 10.62.6 identifies the textbook invariant `d(M)` with the Krull
--   dimension of `Supp(M)`;
-- * core/canonical: the owner abstractions are `hilbertSamuelPolynomialDegree` and
--   `Module.supportDim`;
-- * bridge/view: the proof reduces to prime quotients via the Noetherian filtration induction, then
--   compares the quotient-ring Hilbert-Samuel degree with `ringKrullDim` using
--   `local_noetherian_ring_dimension_tfae`.
-- Proof sketch: use a finite prime-cyclic filtration of `M` from Lemma 10.62.1. Lemma 10.59.10
-- expresses `d(M)` as the maximum of the degrees of the cyclic factors `R ⧸ 𝔭ᵢ`, and Proposition
-- 10.60.9 identifies each such degree with `ringKrullDim (R ⧸ 𝔭ᵢ)`, hence with the dimension of
-- the closed set `V(𝔭ᵢ)`. Lemma 10.62.5 identifies the minimal primes of `Supp(M)` with the
-- minimal primes occurring in the filtration, so the maximum is exactly the Krull dimension of the
-- support.
/-- Lemma 10.62.6: if `R` is a Noetherian local ring and `M` is a finite `R`-module, then the
invariant `d(M)` from Definition 10.59.8 equals the Krull dimension of `Supp(M)`, written
canonically via the lifted owner map `Nat.castOrderEmbedding.withBotMap`. -/
theorem hilbertSamuelPolynomialDegree_eq_supportDim :
    Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R M) =
      Module.supportDim R M := by
  classical
  induction ‹Module.Finite R M› using
      IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
      simpa using (Module.supportDim_eq_bot_of_subsingleton R N).symm
  | quotient N q e =>
      calc
        Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N) =
            Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R (R ⧸ q.asIdeal)) := by
              rw [hilbertSamuelPolynomialDegree_eq_of_linearEquiv R N e]
        _ = Module.supportDim R (R ⧸ q.asIdeal) :=
            cast_hilbertSamuelPolynomialDegree_eq_supportDim_of_prime_quotient q
        _ = Module.supportDim R N := by
              rw [Module.supportDim_eq_of_equiv e]
  | exact N₁ N₂ N₃ f g hf hg hfg hN₁ hN₃ =>
      let S : ShortComplex (ModuleCat.{v} R) := moduleCatMk f g hfg.linearMap_comp_eq_zero
      let _ : Module.Finite R S.X₁ := by
        change Module.Finite R N₁
        infer_instance
      let _ : Module.Finite R S.X₂ := by
        change Module.Finite R N₂
        infer_instance
      let _ : Module.Finite R S.X₃ := by
        change Module.Finite R N₃
        infer_instance
      have hS : S.ShortExact := by
        refine
          { exact := (ShortExact.moduleCat_exact_iff_function_exact S).2 hfg
            mono_f := (ModuleCat.mono_iff_injective _).2 hf
            epi_g := (ModuleCat.epi_iff_surjective _).2 hg }
      have hdeg0 :
          hilbertSamuelPolynomialDegree R N₂ =
            max (hilbertSamuelPolynomialDegree R N₁) (hilbertSamuelPolynomialDegree R N₃) := by
        simpa [S] using hilbertSamuelPolynomialDegree_eq_max_of_shortExact hS
      have hdegS :
          Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N₂) =
            max (Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N₁) : WithBot ℕ∞)
              (Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N₃)) := by
        simpa using
          congrArg (fun x : WithBot ℕ ↦ (Nat.castOrderEmbedding.withBotMap x : WithBot ℕ∞)) hdeg0
      have hsupS :
          Module.supportDim R N₂ =
            max (Module.supportDim R N₁ : WithBot ℕ∞) (Module.supportDim R N₃) := by
        simpa [S] using supportDim_eq_max_of_shortExact hS
      calc
        Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N₂) =
            max (Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N₁) : WithBot ℕ∞)
              (Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N₃)) := hdegS
        _ = max (Module.supportDim R N₁ : WithBot ℕ∞) (Module.supportDim R N₃) := by
              rw [hN₁, hN₃]
        _ = Module.supportDim R N₂ := by
              exact hsupS.symm

end

/-! ### Lemma_10_62_7 (from Chap10) -/
universe u v

open CategoryTheory
open CategoryTheory.ShortComplex

private theorem moduleSupport_isUpperSet
    {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    IsUpperSet (Module.support R M) := by
  intro p q hpq hp
  exact Module.mem_support_mono hpq hp

private theorem krullDim_union_eq_max_of_isUpperSet
    {α : Type*} [Preorder α] {s t : Set α} (hs : IsUpperSet s) (ht : IsUpperSet t) :
    Order.krullDim ↑(s ∪ t) = max (Order.krullDim ↑s) (Order.krullDim ↑t) := by
  refine le_antisymm ?_ (max_le_iff.mpr ⟨?_, ?_⟩)
  · rw [Order.krullDim, iSup_le_iff]
    intro p
    by_cases hp : (p.head : α) ∈ s
    · let q : LTSeries s :=
        LTSeries.mk p.length
          (fun i ↦ ⟨(p i : α), hs (show (p.head : α) ≤ (p i : α) from p.head_le i) hp⟩)
          (fun i j hij ↦ p.strictMono hij)
      exact (Order.LTSeries.length_le_krullDim q).trans (le_max_left _ _)
    · have hp' : (p.head : α) ∈ t := by
        rcases p.head.2 with hp' | hp'
        · exact (hp hp').elim
        · exact hp'
      let q : LTSeries t :=
        LTSeries.mk p.length
          (fun i ↦ ⟨(p i : α), ht (show (p.head : α) ≤ (p i : α) from p.head_le i) hp'⟩)
          (fun i j hij ↦ p.strictMono hij)
      exact (Order.LTSeries.length_le_krullDim q).trans (le_max_right _ _)
  · exact Order.krullDim_le_of_strictMono
      (fun x : s ↦ (⟨(x : α), Or.inl x.2⟩ : ↑(s ∪ t)))
      (fun _ _ h ↦ h)
  · exact Order.krullDim_le_of_strictMono
      (fun x : t ↦ (⟨(x : α), Or.inr x.2⟩ : ↑(s ∪ t)))
      (fun _ _ h ↦ h)

-- Proof sketch: `Module.support_of_exact` rewrites the support of the middle term as the union of
-- the supports of the two end terms. Each module support is an upper set in the specialization
-- order on `Spec R`, so any prime chain in that union is already contained in whichever support
-- contains its head. The Krull dimension of the union is therefore the maximum of the two support
-- dimensions.
/-
Source/core/bridge triage:
* source-facing: Lemma 10.62.7 is the short-exact-sequence dimension formula from the text.
* core/canonical: the owner abstractions are `Module.support` and `Module.supportDim`.
* bridge/view: exactness identifies the middle support with a union, and support monotonicity
  upgrades the set-theoretic union formula to the owner invariant `Module.supportDim`.
-/
/-- Lemma 10.62.7: for a short exact sequence `0 → M' → M → M'' → 0` of `R`-modules, the support
dimension of the middle term is the maximum of the support dimensions of the two end terms. -/
theorem supportDim_eq_max_of_shortExact
    {R : Type u} [CommRing R]
    {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) :
    Module.supportDim R S.X₂ =
      max (Module.supportDim R S.X₁) (Module.supportDim R S.X₃) := by
  have hExact : Function.Exact S.f.hom S.g.hom :=
    (ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hsupp :
      Module.support R S.X₂ = Module.support R S.X₁ ∪ Module.support R S.X₃ :=
    Module.support_of_exact hExact hS.moduleCat_injective_f hS.moduleCat_surjective_g
  rw [Module.supportDim, Module.supportDim, Module.supportDim, hsupp]
  exact
    krullDim_union_eq_max_of_isUpperSet
      (moduleSupport_isUpperSet S.X₁)
      (moduleSupport_isUpperSet S.X₃)
