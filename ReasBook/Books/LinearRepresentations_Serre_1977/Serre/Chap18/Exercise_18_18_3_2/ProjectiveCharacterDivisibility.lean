import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Serre.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Serre.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopePairing

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section ProjectiveCharacterCriterion

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
-- Serre's Chapter 18 modular system uses a *complete* DVR `A`; the projective scalar-extension
-- owner `projectiveCharacterScalarExtension` requires adic completeness of the maximal ideal.
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [CharZero K]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

/-
Domain-style sampling for Exercise `18-18.3-2`:
* primary domain: modular representation theory of finite groups, combining the projective
  scalar-extension owner `projectiveGrothendieckScalarExtensionHom A K`, the Chapter `16`
  Grothendieck-character owner `finiteRepGrothendieckCharacter`, the Chapter `12`
  scalar-extension owner `A ⊗R[K](G)`, and the Cartan owners `cartanCokernel` and
  `cartanMatrix`;
* relevant owner declarations inspected in this domain:
  `projectiveGrothendieckScalarExtensionHom`,
  `finiteRepGrothendieckCharacter`,
  `characterRingOverFieldAlgebraScalarExtension`,
  `cartanCokernel`,
  `cartanMatrix`.

Layer triage:
* source-facing: the projective-character span inside `A ⊗R[K](G)` and the invariant-factor
  formulas indexed by `p`-regular conjugacy-class representatives;
* core/canonical: the owner declarations
  `projectiveGrothendieckScalarExtensionHom A K`, `finiteRepGrothendieckCharacter K G`,
  `A ⊗R[K](G)`, `cartanCokernel`, and `cartanMatrix`;
* bridge/view: the codomain restriction from `R₀[K](G)` to `A ⊗R[K](G)` obtained from
  `finiteRepGrothendieckCharacter K G` and the canonical inclusion `R[K](G) ⊆ A ⊗R[K](G)`.

Ordinary-character regime check:
* the source-facing span in part `(1)` lives in the characteristic-zero ordinary-character setting
  used nearby in Chapter `18`;
* its primitive definition inside `A ⊗R[K](G)` needs only `[CharZero K]`, but the membership
  criterion below must stay in the standard large-field regime
  `[HasEnoughRootsOfUnity K (Monoid.exponent G)]`, matching the Chapter `16` image criterion and
  neighboring Theorem `18-18.3-1`.
-/
local notation "k" => IsLocalRing.ResidueField A
local notation "e" => (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G))
local instance instFintypeGProjectiveCharacterDivisibility : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 18-18.3-2: Serre's full indicator should first be written as an explicit
combination of the projective-envelope restrictions before passing to the scaled indicator by a
unit rescaling. -/
theorem full_regular_indicator_eq_sum_projectiveEnvelope_restriction
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (c : PRegularConjClass G p) :
    let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
    full_regular_indicator (p := p) (A := A) (K := K) (G := G) c =
      ∑ i,
        (FDRep.modularCharacterOnPRegularConjClass (p := p) (π i) liftA
          (inversePRegularConjClass (p := p) c)) •
          regularRestriction (p := p)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀) := by
  -- Route correction: package Serre's reverse direction as an exact equality first, so the image
  -- theorem below becomes a formal `Submodule.sum_mem` corollary instead of another membership
  -- loop.
  classical
  dsimp
  ext c'
  let hliftA : Function.Injective (primeToPRoot_canonicalLift (p := p) (A := A)) :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A)
      (primeToPRoot_canonicalLift (p := p) (A := A)) hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  have hsum_repr :=
    congrFun
      (bA.sum_repr
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')))
      (inversePRegularConjClass (p := p) c)
  simp only [Finset.sum_apply, Pi.mul_apply, Algebra.smul_def]
  have hvalue (i : ι) :
      regularRestriction (p := p)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀) c' =
        algebraMap A K
          ((ConjClasses.centralizerPPart p c'.1 : A) *
            bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i) := by
    simpa [bA, inversePRegularConjClass_involutive, ConjClasses.centralizerPPart_inv] using
      (projectiveEnvelope_regularRestriction_value_eq_centralizerPPart_mul_repr_inv
        (p := p) (A := A) (K := K) (G := G)
        (hω := hω)
        (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
        (P := P) (hP_envelope := hP_envelope) i
        (inversePRegularConjClass (p := p) c'))
  simp_rw [hvalue]
  have hcoeff :
      ∑ i,
          (bA i (inversePRegularConjClass (p := p) c)) *
            ((ConjClasses.centralizerPPart p c'.1 : A) *
              bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i) =
        (ConjClasses.centralizerPPart p c'.1 : A) *
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c'))
            (inversePRegularConjClass (p := p) c) := by
    calc
      ∑ i,
          (bA i (inversePRegularConjClass (p := p) c)) *
            ((ConjClasses.centralizerPPart p c'.1 : A) *
              bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i)
          =
        ∑ i,
          (ConjClasses.centralizerPPart p c'.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i *
              bA i (inversePRegularConjClass (p := p) c)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
      _ =
        (ConjClasses.centralizerPPart p c'.1 : A) *
          ∑ i,
            bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i *
              bA i (inversePRegularConjClass (p := p) c) := by
            rw [Finset.mul_sum]
      _ =
        (ConjClasses.centralizerPPart p c'.1 : A) *
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c'))
            (inversePRegularConjClass (p := p) c) := by
            congr 1
            simpa [bA, Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc] using hsum_repr
  symm
  calc
    ∑ i,
        (algebraMap A (PRegularConjClass G p → K))
            (FDRep.modularCharacterOnPRegularConjClass (p := p) (π i)
              (primeToPRoot_canonicalLift (p := p) (A := A))
              (inversePRegularConjClass (p := p) c)) c' *
          algebraMap A K
            ((ConjClasses.centralizerPPart p c'.1 : A) *
              bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i)
        =
      ∑ i,
        algebraMap A K (bA i (inversePRegularConjClass (p := p) c)) *
          algebraMap A K
            ((ConjClasses.centralizerPPart p c'.1 : A) *
              bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [bA]
    _ =
      ∑ i,
        algebraMap A K
          ((bA i (inversePRegularConjClass (p := p) c)) *
            ((ConjClasses.centralizerPPart p c'.1 : A) *
              bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [map_mul]
    _ =
      algebraMap A K
        (∑ i,
          (bA i (inversePRegularConjClass (p := p) c)) *
            ((ConjClasses.centralizerPPart p c'.1 : A) *
              bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i)) := by
          simp [map_sum]
    _ = algebraMap A K
        ((ConjClasses.centralizerPPart p c'.1 : A) *
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c'))
            (inversePRegularConjClass (p := p) c)) := by
          rw [hcoeff]
  by_cases hcc' : c' = c
  · subst c'
    have hcard :
        ConjClasses.centralizerCard c.1 =
          ConjClasses.centralizerPPart p c.1 *
            ordCompl[p] (ConjClasses.centralizerCard c.1) :=
      ConjClasses.centralizerCard_eq_centralizerPPart_mul_ordCompl
        (p := p) (G := G) c.1
    calc
      algebraMap A K
          ((ConjClasses.centralizerPPart p c.1 : A) *
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) c))
              (inversePRegularConjClass (p := p) c))
          =
        algebraMap A K
          ((ConjClasses.centralizerPPart p c.1 : A) *
            (ordCompl[p]
              (ConjClasses.centralizerCard
                (inversePRegularConjClass (p := p) c : PRegularConjClass G p).1) : A)) := by
              simp [primeToP_regular_indicator]
      _ = algebraMap A K (ConjClasses.centralizerCard c.1 : A) := by
            simpa [map_mul, ConjClasses.centralizerCard_inv] using
              congrArg (fun n : ℕ => algebraMap A K (n : A)) hcard.symm
      _ = full_regular_indicator (p := p) (A := A) (K := K) (G := G) c c := by
            simp [full_regular_indicator]
  · have hcc'_inv :
        inversePRegularConjClass (p := p) c' ≠ inversePRegularConjClass (p := p) c := by
      intro hInv
      exact hcc' (by
        simpa [inversePRegularConjClass_involutive] using
          congrArg (inversePRegularConjClass (p := p)) hInv)
    simp [full_regular_indicator, primeToP_regular_indicator, hcc', hcc'_inv]

/-- Helper for Exercise 18-18.3-2: each projective-character generator already lies in the
projective-character span by construction. -/
theorem projectiveCharacterScalarExtension_mem_projectiveCharacterSubmodule
    (x : P₀[k](G)) :
    projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x ∈
      projectiveCharacterSubmodule (A := A) (K := K) (G := G) := by
  -- The span owner is generated exactly by the range of `projectiveCharacterScalarExtension`.
  exact Submodule.subset_span ⟨x, rfl⟩

/-- Helper for Exercise 18-18.3-2: the regular restriction of each projective-character generator
lies in the mapped projective-character span. -/
theorem regularRestriction_projectiveCharacter_mem_projectiveCharacter_map
    (x : P₀[k](G)) :
    regularRestriction (p := p)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x) ∈
      Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
  -- Use the generator itself as the witness in the mapped span.
  refine Submodule.mem_map.2 ?_
  refine
    ⟨projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x,
      projectiveCharacterScalarExtension_mem_projectiveCharacterSubmodule
        (A := A) (K := K) (G := G) x, rfl⟩

/-- Helper for Exercise 18-18.3-2: Serre's full indicator should first be written as an explicit
combination of the projective-envelope restrictions before passing to the scaled indicator by a
unit rescaling. -/
theorem full_regular_indicator_mem_projectiveCharacter_map
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (c : PRegularConjClass G p) :
    full_regular_indicator (p := p) (A := A) (K := K) (G := G) c ∈
      Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
  classical
  have hfamilies :
      ∃ (ι : Type (u + 1)) (_ : Fintype ι) (π : ι → FDRep k G),
        PairwiseNonisomorphic π ∧
          IsCompleteIrreducibleFamily π ∧
          ∃ P : ι → FiniteProjectiveGroupAlgebraModule k G,
            ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope :=
    exists_complete_simple_family_with_projective_envelopes
  rcases hfamilies with
    ⟨ι, _, π, hπ_pairwise, hπ_complete, P, hP_envelope⟩
  -- Route correction: once the exact full-indicator expansion is available, this is only span
  -- bookkeeping inside the mapped projective-character submodule.
  rw [full_regular_indicator_eq_sum_projectiveEnvelope_restriction
    (p := p) (A := A) (K := K) (G := G)
    (hω := hω)
    (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
    (P := P) (hP_envelope := hP_envelope) c]
  refine Submodule.sum_mem _ ?_
  intro i hi
  exact Submodule.smul_mem _ _
    (regularRestriction_projectiveCharacter_mem_projectiveCharacter_map
      (p := p) (A := A) (K := K) (G := G) [P i]ₚ₀)

/-- Helper for Exercise 18-18.3-2: each scaled regular indicator should be realized as the
regular restriction of an explicit `A`-linear combination of projective-envelope characters. -/
theorem scaled_regular_indicator_mem_projectiveCharacter_map
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (c : PRegularConjClass G p) :
    scaled_regular_indicator (p := p) (A := A) (K := K) c ∈
      Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
  refine
    scaled_regular_indicator_mem_of_full_regular_indicator_mem
      (p := p) (A := A) (K := K) (G := G) c ?_
  exact full_regular_indicator_mem_projectiveCharacter_map
    (p := p) (A := A) (K := K) (G := G) hω c

/-- Helper for Exercise 18-18.3-2: after restricting to `PRegularConjClass G p`, the projective
character span maps exactly onto the coordinatewise divisibility lattice. -/
theorem projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule :
    (∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s)) →
    Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  intro hω
  apply le_antisymm
  · -- Route correction: reduce the forward inclusion to the generator case of the projective span.
    rw [projectiveCharacterSubmodule, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
    exact
      regularRestriction_projectiveCharacter_mem_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) hω y
  · -- Route correction: reduce the reverse inclusion to Serre's scaled point-mass generators.
    rw [regularValueDivisibilitySubmodule_eq_span_scaled_regular_indicator
      (p := p) (A := A) (K := K) (G := G)]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    exact
      scaled_regular_indicator_mem_projectiveCharacter_map
        (p := p) (A := A) (K := K) (G := G) hω c

/-- Helper for Exercise 18-18.3-2: after restricting to `PRegularConjClass G p`, the projective
character span is controlled entirely by the regular-value divisibility condition once the
`p`-singular vanishing half is fixed. -/
theorem mem_projectiveCharacterSubmodule_iff_regularRestriction_mem_of_zero_on_pSingular
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (Φ : A ⊗R[K](G))
    (hzero : ∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) :
    Φ ∈ projectiveCharacterSubmodule ↔
      regularRestriction (p := p) Φ ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hΦ
    -- Push a projective character through the regular-restriction map and rewrite the image using
    -- the already identified diagonal lattice.
    have hmap :
        regularRestriction (p := p) Φ ∈
          Submodule.map
            (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
            (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
      exact Submodule.mem_map.2 ⟨Φ, hΦ, rfl⟩
    simpa [projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G) hω] using hmap
  · intro hreg
    -- Pick a projective character with the same regular restriction, then use the zero-extension
    -- formula to show it coincides with `Φ` on all of `G`.
    have hmap :
        regularRestriction (p := p) Φ ∈
          Submodule.map
            (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
            (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
      simpa [projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) hω] using hreg
    rcases Submodule.mem_map.1 hmap with ⟨Ψ, hΨ, hΨreg⟩
    have hzeroΨ :
        ∀ g : G, ¬ IsPRegular p g → (Ψ : G → K) g = 0 :=
      projectiveCharacterSubmodule_zero_on_pSingular (p := p) (A := A) (K := K) (G := G) hΨ
    have hΦext :=
      (regular_restriction_zero_extension_iff (p := p) (A := A) (K := K) (G := G) Φ).1 hzero
    have hΨext :=
      (regular_restriction_zero_extension_iff (p := p) (A := A) (K := K) (G := G) Ψ).1 hzeroΨ
    have hEq : Φ = Ψ := by
      apply Subtype.ext
      funext g
      rw [hΦext g, hΨext g]
      by_cases hg : IsPRegular p g
      · rw [dif_pos hg, dif_pos hg]
        have hregEq :=
          congrFun hΨreg (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩)
        simpa [regularRestrictionLinearMap] using hregEq.symm
      · simp [hg]
    simpa [hEq] using hΨ

/-- Helper for Exercise 18-18.3-2: after restricting to `PRegularConjClass G p`, the projective
character span should identify with the coordinatewise divisibility lattice. -/
theorem mem_projectiveCharacterSubmodule_iff_zero_off_pRegular_and_regularRestriction_mem
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (Φ : A ⊗R[K](G)) :
    Φ ∈ projectiveCharacterSubmodule ↔
      (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
        regularRestriction (p := p) Φ ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hΦ
    refine ⟨?_, ?_⟩
    · exact projectiveCharacterSubmodule_zero_on_pSingular
        (p := p) (A := A) (K := K) (G := G) hΦ
    · exact
        (mem_projectiveCharacterSubmodule_iff_regularRestriction_mem_of_zero_on_pSingular
          (p := p) (A := A) (K := K) (G := G) hω Φ
          (projectiveCharacterSubmodule_zero_on_pSingular
            (p := p) (A := A) (K := K) (G := G) hΦ)).1 hΦ
  · rintro ⟨hzero, hreg⟩
    exact
      (mem_projectiveCharacterSubmodule_iff_regularRestriction_mem_of_zero_on_pSingular
        (p := p) (A := A) (K := K) (G := G) hω Φ hzero).2 hreg
end ProjectiveCharacterCriterion

end Representation
