import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct
open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

local notation "f" => algebraMap R S

/- Layering for this item:
* source-facing: the TFAE characterizing surjectivity of `Spec S → Spec R` in terms of
  contraction formulas for extended ideals, plus its stability under arbitrary base change;
* core/canonical owner: `PrimeSpectrum.comap (algebraMap R S)` together with the ideal
  operations `Ideal.map`, `Ideal.comap`, and `Ideal.radical`;
* bridge/view: Lemma `10.18.6`, `PrimeSpectrum.mem_range_comap_iff`,
  `PrimeSpectrum.nontrivial_iff_mem_rangeComap`, `Ideal.comap_radical`, and
  `Ideal.radical_eq_sInf`, which translate between the owner map on spectra and the textbook
  contraction criteria.
-/

/-- Helper for Lemma 10.30.3: mapping an ideal or first replacing it by its radical gives the
same radical after extension to `S`. -/
-- The only content is the radical bookkeeping bridge used to pass between the arbitrary-ideal
-- clause and the radical-ideal clause of the source proof.
lemma radical_map_eq_radical_map_radical (I : Ideal R) :
    (I.map f).radical = (I.radical.map f).radical := by
  apply le_antisymm
  · -- Monotonicity of `map` and `radical` gives the easy inclusion.
    exact Ideal.radical_mono (Ideal.map_mono Ideal.le_radical)
  · -- The reverse inclusion is exactly `map_radical_le`, upgraded through radicality.
    exact (Ideal.radical_isRadical _).radical_le_iff.mpr (Ideal.map_radical_le f)

/-- Helper for Lemma 10.30.3: if every extended prime contracts back to itself, then the same
contraction formula holds for every radical ideal. -/
-- This packages the source-proof step that recovers a radical ideal as the intersection of the
-- primes containing it and checks membership prime-by-prime.
lemma prime_contraction_implies_radical_ideal_contraction
    (hprime : ∀ p : PrimeSpectrum R, (p.asIdeal.map f).comap f = p.asIdeal) :
    ∀ I : Ideal R, I.IsRadical → (I.map f).comap f = I := by
  intro I hI
  apply le_antisymm
  · intro x hx
    -- Rewrite membership in the radical ideal as membership in every prime above it.
    rw [← hI.radical, Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro P hP
    have hx_map : algebraMap R S x ∈ I.map f := by
      simpa [Ideal.mem_comap] using hx
    have hx_prime_map : algebraMap R S x ∈ Ideal.map f P :=
      (Ideal.map_mono hP.1) hx_map
    have hx_prime_comap : x ∈ (Ideal.map f P).comap f := by
      simpa [Ideal.mem_comap] using hx_prime_map
    have hP_contract : (Ideal.map f P).comap f = P := hprime ⟨P, hP.2⟩
    simpa [hP_contract] using hx_prime_comap
  · -- Extension followed by contraction always contains the original ideal.
    exact Ideal.le_comap_map

/-- Helper for Lemma 10.30.3: surjectivity of `Spec S → Spec R` is equivalent to the prime-wise
contraction formula `φ⁻¹(pS) = p` for every prime `p`. -/
-- This is the pointwise owner-level image criterion rewritten as a global surjectivity statement.
lemma surjective_iff_forall_prime_contraction :
    Function.Surjective (comap f) ↔
      ∀ p : PrimeSpectrum R, (p.asIdeal.map f).comap f = p.asIdeal := by
  constructor
  · intro hsurj p
    exact (PrimeSpectrum.mem_range_comap_iff f).mp (hsurj p)
  · intro hprime p
    exact (PrimeSpectrum.mem_range_comap_iff f).mpr (hprime p)

/-- Lemma 10.30.3: for a ring map `R → S`, the following are equivalent: `Spec S → Spec R` is
surjective, contraction of `√(IS)` is `√I` for every ideal `I`, contraction of `IS` is `I` for
every radical ideal `I`, and contraction of `pS` is `p` for every prime `p` of `R`. -/
-- Proof sketch: the owner object is the canonical spectral map `comap f : Spec S → Spec R`.
-- Use `Ideal.comap_radical` to identify the radical clause with the radical-ideal clause,
-- `Ideal.radical_eq_sInf` to recover a radical ideal as the intersection of primes containing it,
-- and `mem_range_comap_iff` together with Lemma 10.18.6 to identify surjectivity of `comap f`
-- with the prime-ideal contraction condition.
@[stacks 00FI]
theorem specComap_surjective_tfae :
    List.TFAE
      [ Function.Surjective (comap f),
        ∀ I : Ideal R,
          ((I.map f).radical).comap f = I.radical,
        ∀ I : Ideal R, I.IsRadical → (I.map f).comap f = I,
        ∀ p : PrimeSpectrum R, (p.asIdeal.map f).comap f = p.asIdeal ] := by
  tfae_have 2 ↔ 3 := by
    constructor
    · intro h I hI
      -- Rewrite the radical clause through `comap_radical`, then use radicality of `I`.
      have hrad : ((I.map f).comap f).radical = I := by
        simpa [Ideal.comap_radical, hI.radical] using h I
      exact le_antisymm
        ((hI.radical_le_iff).mp (le_of_eq hrad))
        Ideal.le_comap_map
    · intro h I
      -- Apply the radical-ideal clause to `I.radical` and transport it back to `I`.
      calc
        ((I.map f).radical).comap f = (((I.radical).map f).radical).comap f := by
          rw [radical_map_eq_radical_map_radical]
        _ = (((I.radical).map f).comap f).radical := by
          rw [Ideal.comap_radical]
        _ = I.radical := by
          rw [h I.radical (Ideal.radical_isRadical _), Ideal.radical_idem]
  tfae_have 3 → 4 := by
    intro h p
    -- A prime ideal is radical, so the radical-ideal contraction formula applies directly.
    simpa using h p.asIdeal p.isPrime.isRadical
  tfae_have 4 → 3 := by
    intro h
    -- This is the source-proof intersection-of-primes step, packaged as a reusable helper.
    exact prime_contraction_implies_radical_ideal_contraction h
  tfae_have 1 ↔ 4 := by
    -- Surjectivity is exactly the pointwise image criterion on prime ideals.
    exact surjective_iff_forall_prime_contraction
  tfae_finish

section BaseChange

variable {R' : Type w} [CommRing R'] [Algebra R R']

/-- Helper for Lemma 10.30.3: nontriviality of a fiber ring is preserved after arbitrary base
change along `R → R'`. -/
-- The source proof identifies the new fiber with scalar extension of the old fiber from
-- `κ(p)` to `κ(p')`, and scalar extension over a field preserves nontriviality because the
-- canonical `includeRight` map is injective.
lemma baseChange_fiber_nontrivial (p' : PrimeSpectrum R') :
    Nontrivial ((p'.asIdeal.under R).Fiber S) →
      Nontrivial (p'.asIdeal.Fiber (R' ⊗[R] S)) := by
  intro hfiber
  let p : Ideal R := p'.asIdeal.under R
  let e :
      p'.asIdeal.Fiber (R' ⊗[R] S) ≃ₐ[p'.asIdeal.ResidueField]
        p'.asIdeal.ResidueField ⊗[p.ResidueField] (p.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  have hcod :
      Nontrivial (p'.asIdeal.ResidueField ⊗[p.ResidueField] (p.Fiber S)) := by
    -- Scalar extension is injective on the fiber ring because residue-field extensions are
    -- injective and tensoring over a field is flat.
    let j :
        p.Fiber S →ₐ[p.ResidueField]
          p'.asIdeal.ResidueField ⊗[p.ResidueField] (p.Fiber S) :=
      Algebra.TensorProduct.includeRight
    have hj : Function.Injective j :=
      Algebra.TensorProduct.includeRight_injective
        (A := p'.asIdeal.ResidueField) (B := p.Fiber S)
        (ha := RingHom.injective (algebraMap p.ResidueField p'.asIdeal.ResidueField))
    let _ : Nontrivial (p.Fiber S) := hfiber
    exact hj.nontrivial
  let _ : Nontrivial (p'.asIdeal.ResidueField ⊗[p.ResidueField] (p.Fiber S)) := hcod
  exact RingHom.domain_nontrivial e.toRingHom

/-- If `Spec S → Spec R` is surjective, then every base change `Spec (R' ⊗[R] S) → Spec R'` is
also surjective. The corresponding contraction formulas for the base-changed map then follow from
`specComap_surjective_tfae`. -/
-- Proof sketch: for `p' : Spec R'` lying over `p : Spec R`, apply Lemma 10.18.6 to reduce
-- surjectivity of `Spec (R' ⊗[R] S) → Spec R'` to nontriviality of the fiber ring over `p'`.
-- Identify that fiber with `(S ⊗[R] κ(p)) ⊗[κ(p)] κ(p')`, which is nontrivial because the first
-- factor is nontrivial by the surjectivity hypothesis and the second map is an extension of
-- fields.
theorem specComap_surjective_stable_under_baseChange
    (h : Function.Surjective (comap f)) :
    Function.Surjective (comap (algebraMap R' (R' ⊗[R] S))) := by
  intro p'
  let p : PrimeSpectrum R := comap (algebraMap R R') p'
  have hp_mem : p ∈ Set.range (comap f) := h p
  have hp_fiber : Nontrivial (p.asIdeal.Fiber S) := by
    exact (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mpr hp_mem
  have hp'_fiber : Nontrivial ((p'.asIdeal.under R).Fiber S) := by
    simpa [p, PrimeSpectrum.comap_asIdeal] using hp_fiber
  have hbase_fiber : Nontrivial (p'.asIdeal.Fiber (R' ⊗[R] S)) :=
    baseChange_fiber_nontrivial (R := R) (S := S) p' hp'_fiber
  exact (PrimeSpectrum.nontrivial_iff_mem_rangeComap p').mp hbase_fiber

end BaseChange

end
