import LinearRepresentations_Serre_1977.Chap11.Proposition_11_11_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe v

noncomputable section

open Representation
open scoped Representation SubgroupInduction TensorProduct
open scoped TensorCharacterRing

/- Domain-style sampling pass:
* primary domain: indexed prime ideals in LinearRepresentations_Serre_1977's tensor character ring `A ⊗R(G)` and the
  induction ideal owner `ℐ H`;
* sampled owner declarations in this domain:
  `tensorCharacterRingInductionIdeal`,
  `tensorCharacterRingZeroPrimeIdeal`,
  `IsTensorCharacterRingRegularPrime`,
  `tensorCharacterRingRegularPrime_spec`;
* best owner abstraction: `IsTensorCharacterRingRegularPrime A G p M c`, whose second component is
  exactly the regular-prime induction-ideal criterion used in the exercise.

Primitive data vs. derived API:
* primitive data: the owner objects `ℐ H`, `P0 A c`, and `Pm M c`, together with the canonical
  regular-prime owner predicate `IsTensorCharacterRingRegularPrime A G p M c`;
* derived API: the containment criteria for `ℐ H` inside those indexed primes, especially the
  regular-prime half already exported by `tensorCharacterRingRegularPrime_spec`.

Source/core/bridge triage:
* source-facing: the zero-prime containment criterion from the exercise;
* core/canonical: the Chapter `11` owners `tensorCharacterRingInductionIdeal`,
  `tensorCharacterRingZeroPrimeIdeal`, `IsTensorCharacterRingRegularPrime`, and
  `tensorCharacterRingRegularPrime`;
* bridge/view: no new bridge is introduced here. The regular-prime half is recall-only because the
  exact owner theorem already exists upstream.
-/

section ZeroPrime

variable {G : Type} [Group G]
variable {A : Type v} [CommRing A]
variable [Finite G] [Algebra A ℂ]

local instance : Fintype G := Fintype.ofFinite G
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Exercise 11-11.4-7: membership of a subgroup-induction generator in the zero prime
indexed by the class of `x` is equivalent to vanishing of the induced class function at `x`. -/
private lemma induction_generator_mem_zero_class_prime_iff
    (H : Subgroup G) (x : G) (χ : R(H)) :
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
      (H.characterRingInduction χ)) ∈ (P0 A (ConjClasses.mk x)).asIdeal ↔
      ((H.characterRingInduction χ : R(G)) : G → ℂ) x = 0 := by
  -- Reduce kernel membership in `P₀,[x]` to ordinary evaluation of the induced class function.
  change (((tensorCharacterRingToSubalgebra A G)
      ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G)))
        (H.characterRingInduction χ)) :
        characterRingScalarExtensionSubalgebra A G) : G → ℂ) x = 0 ↔ _
  simp [tensorCharacterRingToSubalgebra, Subgroup.characterRingInduction_apply]

/-- Helper for Exercise 11-11.4-7: if the conjugacy class of `x` misses `H`, then every class
function induced from `H` vanishes at `x`. -/
private lemma induced_value_eq_zero_of_disjoint_conjclass
    (H : Subgroup G) (x : G)
    (hdisj : ((H : Set G) ∩ (ConjClasses.mk x).carrier) = ∅) (χ : R(H)) :
    ((H.characterRingInduction χ : R(G)) : G → ℂ) x = 0 := by
  classical
  -- Expand the induced character and show every summand is forced to vanish.
  rw [Subgroup.characterRingInduction_apply]
  change ((Nat.card H : ℂ)⁻¹) *
      (∑ s : G,
        if hsg : s⁻¹ * x * s ∈ H then
          χ ⟨s⁻¹ * x * s, hsg⟩
        else 0) = 0
  have hsum :
      (∑ s : G,
        if hsg : s⁻¹ * x * s ∈ H then
          χ ⟨s⁻¹ * x * s, hsg⟩
        else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro s _
    by_cases hs : s⁻¹ * x * s ∈ H
    · -- A nonzero summand would exhibit an element of `H` inside the conjugacy class of `x`.
      have hsconj : s * (s⁻¹ * x * s) * s⁻¹ = x := by
        group
      have hcarrier : s⁻¹ * x * s ∈ (ConjClasses.mk x).carrier := by
        refine ConjClasses.mem_carrier_iff_mk_eq.mpr ?_
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.2 ⟨s, hsconj⟩)
      have hempty : False := by
        have hmem : s⁻¹ * x * s ∈ ((H : Set G) ∩ (ConjClasses.mk x).carrier) := ⟨hs, hcarrier⟩
        simp [hdisj] at hmem
      suffices χ ⟨s⁻¹ * x * s, hs⟩ = 0 by
        simpa [hs] using this
      exact False.elim hempty
    · simp [hs]
  rw [hsum, mul_zero]

/-- Helper for Exercise 11-11.4-7: when `x ∈ H`, the trivial induction generator has nonzero
value at `x`. -/
private lemma trivial_induced_value_ne_zero_of_mem_subgroup
    (H : Subgroup G) (x : G) (hx : x ∈ H) :
    ((H.characterRingInduction (1 : R(H)) : R(G)) : G → ℂ) x ≠ 0 := by
  -- For the trivial character, the identity element of `G` already contributes a nonzero summand.
  rw [Subgroup.characterRingInduction_apply, Subgroup.inducedClassFunction]
  simpa using (show ∃ s : G, s⁻¹ * x * s ∈ H by
    refine ⟨1, ?_⟩
    simpa using hx)

-- Proof sketch: use the evaluation description of `P₀,c`; an induced character vanishes on `c`
-- exactly when no element of `H` lies in that conjugacy class.
/-- Exercise 11-11.4-7 (1): the ideal `I_H` generated by induction from `H` is contained in
`P₀,c` exactly when `H` does not meet the conjugacy class `c`. -/
theorem subgroup_induction_ideal_le_zero_class_prime_iff_inter_eq_empty
    (H : Subgroup G) (c : ConjClasses G) :
    ℐ H ≤ (P0 A c).asIdeal ↔
      ((H : Set G) ∩ c.carrier) = ∅ := by
  constructor
  · intro hcontain
    -- If `I_H` were contained in `P₀,c`, then the trivial induction generator would vanish on
    -- every element of `H ∩ c`, contradicting the explicit nonvanishing witness.
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    intro x hx
    rcases hx with ⟨hxH, hxc⟩
    have hrange :
        Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
          (H.characterRingInduction (1 : R(H))) ∈
          Set.range fun χ : R(H) ↦
            Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
              (H.characterRingInduction χ) := ⟨1, rfl⟩
    have hgen_mem :
        Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
          (H.characterRingInduction (1 : R(H))) ∈ ℐ H := by
      exact Ideal.subset_span hrange
    have hprime_mem :
        Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
          (H.characterRingInduction (1 : R(H))) ∈ (P0 A (ConjClasses.mk x)).asIdeal := by
      have hmem_c :
          Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
            (H.characterRingInduction (1 : R(H))) ∈ (P0 A c).asIdeal :=
        hcontain hgen_mem
      have hmk : ConjClasses.mk x = c := ConjClasses.mem_carrier_iff_mk_eq.mp hxc
      simpa [hmk] using hmem_c
    have hzero :=
      (induction_generator_mem_zero_class_prime_iff (A := A) H x (1 : R(H))).mp hprime_mem
    exact (trivial_induced_value_ne_zero_of_mem_subgroup H x hxH) hzero
  · intro hdisj
    -- Containment in `P₀,c` is checked on the induction generators spanning `I_H`.
    rw [tensorCharacterRingInductionIdeal, Ideal.span_le]
    intro ξ hξ
    rcases hξ with ⟨χ, rfl⟩
    obtain ⟨x, hmk⟩ := ConjClasses.mk_surjective c
    have hdisj_x : ((H : Set G) ∩ (ConjClasses.mk x).carrier) = ∅ := by
      simpa [hmk] using hdisj
    have hmem_x :
        Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
          (H.characterRingInduction χ) ∈ (P0 A (ConjClasses.mk x)).asIdeal :=
      (induction_generator_mem_zero_class_prime_iff (A := A) H x χ).2
        (induced_value_eq_zero_of_disjoint_conjclass H x hdisj_x χ)
    simpa [hmk] using hmem_x

end ZeroPrime

section ResidualPrime

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [IsDomain A] [Ring.HasFiniteQuotients A]
variable [Algebra A ℂ]

/- Exercise 11-11.4-7 (2): the regular-prime containment criterion is already the second
component of the owner theorem `tensorCharacterRingRegularPrime_spec`, so this exercise should be
presented by direct recall of that canonical result rather than by a duplicate wrapper theorem. -/
recall tensorCharacterRingRegularPrime_spec

end ResidualPrime
