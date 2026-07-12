import Mathlib
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PrimeToPRootLift

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
local instance instFintypeGProjectiveEnvelopePairing : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 18-18.3-2: after transporting the canonical `A`-valued Brauer basis
through `algebraMap A K`, Serre's projective-envelope pairing with its `j`-th basis vector is the
Kronecker delta. This is the source-faithful bridge from the Exercise `18.4` basis to the
characteristic-zero orthogonality relation. -/
theorem projectiveEnvelope_pairing_primeToP_indicator_eq_basis_repr
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i j : ι) :
    let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
    let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
    let bA :=
      exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
        (p := p) (A := A) liftA hliftA
        (residue_primeToPRoot_canonicalLift (p := p) (A := A))
        π hπ_pairwise hπ_complete
    (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            (if hs : IsPRegular p s then
              algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
            else 0) =
      if i = j then (1 : K) else 0 := by
  classical
  intro liftA hliftA bA
  let liftK : PrimeToPRoot p k →* Kˣ :=
    (Units.map (algebraMap A K).toMonoidHom).comp
      (primeToPRoot_unitsLift (p := p) (A := A))
  have hbA_apply :
      (fun c : PRegularConjClass G p => algebraMap A K (bA j c)) =
        FDRep.modularCharacterOnPRegularConjClass (p := p) (π j)
          (PrimeToPRoot.toFieldLift liftK) := by
    -- Transport the canonical `A`-valued Exercise `18.4` basis vector to the `K`-valued Brauer
    -- character used by Serre's orthogonality formula: postcomposing with `algebraMap A K`
    -- commutes with the descended Brauer character (naturality in the coefficient ring), and the
    -- field-valued lift `toFieldLift liftK` is exactly `algebraMap A K` applied to the canonical
    -- `A`-valued lift.
    funext c
    rw [show bA j c =
          FDRep.modularCharacterOnPRegularConjClass (p := p) (π j) liftA c from
        congrFun
            (exercise_18_18_2_9_irreducible_modular_characters_basis_apply_dvr
            (p := p) (A := A) liftA hliftA
            (residue_primeToPRoot_canonicalLift (p := p) (A := A))
            π hπ_pairwise hπ_complete j) c]
    exact
      congrFun
        (modularCharacterOnPRegularConjClass_comp_lift_local
          (σ := (algebraMap A K))
          (lift := (Units.coeHom A).comp (primeToPRoot_unitsLift (p := p) (A := A)))
          (E := π j)) c
  have hsum :
      ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            (if hs : IsPRegular p s then
              algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
            else 0) =
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            FDRep.modularCharacterZeroExtension (π j) (PrimeToPRoot.toFieldLift liftK) s := by
    -- Rewrite the transported basis vector as the zero extension of the corresponding modular
    -- character, so the pairing can be collapsed by `projectiveEnvelope_regular_pairing_eq_delta`.
    refine Finset.sum_congr rfl ?_
    intro s hs
    by_cases hsp : IsPRegular p s
    · -- The common `s⁻¹`-regular factor matches; reduce the second factor through `hbA_apply`.
      have hval := congrFun hbA_apply (PRegularConjClass.ofSubtype (G := G) p ⟨s, hsp⟩)
      rw [FDRep.modularCharacterOnPRegularConjClass_ofSubtype] at hval
      refine congrArg₂ (· * ·) rfl ?_
      rw [dif_pos hsp, FDRep.modularCharacterZeroExtension, dif_pos hsp]
      exact hval
    · simp [FDRep.modularCharacterZeroExtension, hsp]
  rw [hsum]
  -- Now apply the already-proved projective-envelope/Brauer orthogonality relation.
  have hredK : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((liftK x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k) := by
    intro x
    refine ⟨((primeToPRoot_unitsLift (p := p) (A := A) x : Aˣ) : A), ?_, ?_⟩
    · simp [liftK]
    · exact residue_primeToPRoot_unitLift (p := p) (A := A) x
  simpa [liftK] using
    (projectiveEnvelope_regular_pairing_eq_delta
      (p := p) (A := A) (K := K) (G := G)
      (lift := liftK) (hred := hredK) (hω := hω) (π := π) (hπ_pairwise := hπ_pairwise)
      (hπ_complete := hπ_complete) (P := P) (hP_envelope := hP_envelope) i j)

/-- Helper for Exercise 18-18.3-2: the regular restriction of each projective-character generator
already satisfies Serre's coordinatewise divisibility condition. -/
theorem projectiveEnvelope_regularRestriction_value_eq_centralizerPPart_mul_repr_inv
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i : ι) (c : PRegularConjClass G p) :
    let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
    let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
    let bA :=
      exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
        (p := p) (A := A) liftA hliftA
        (residue_primeToPRoot_canonicalLift (p := p) (A := A))
        π hπ_pairwise hπ_complete
    regularRestriction (p := p)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
        (inversePRegularConjClass (p := p) c) =
      algebraMap A K
        ((ConjClasses.centralizerPPart p c.1 : A) *
          ((bA.repr
            (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i)) := by
  classical
  dsimp
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  have hpair_eq :
      (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
          regularRestriction (p := p)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
            (inversePRegularConjClass (p := p) c) =
        algebraMap A K
          ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i) := by
    have hindicator :
        ∀ s : G,
          (if hs : IsPRegular p s then
            algebraMap A K
              ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
          else 0) =
            ∑ j,
              algebraMap A K
                  ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                (if hs : IsPRegular p s then
                  algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                else 0) := by
      intro s
      by_cases hs : IsPRegular p s
      · have hsum :=
          primeToP_regular_indicator_apply_eq_sum_basis_repr
            (p := p) (A := A) (G := G)
            (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
            c (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
        -- Expand Serre's prime-to-`p` indicator in the canonical `A`-valued Brauer basis, then
        -- transport the resulting coefficient formula through `algebraMap A K`.
        rw [dif_pos hs]
        calc
          algebraMap A K
              ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
            =
              algebraMap A K
                (∑ j,
                  (bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c) j) *
                    bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)) := by
                  simpa [bA] using congrArg (fun x : A ↦ algebraMap A K x) hsum
          _ =
              ∑ j,
                algebraMap A K
                    ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                  algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)) := by
                  simp [map_sum, map_mul]
          _ =
              ∑ j,
                algebraMap A K
                    ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                  (if hs' : IsPRegular p s then
                    algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs'⟩))
                  else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  simp [hs]
      · simp [hs]
    have h_expand :
        (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              (if hs : IsPRegular p (s⁻¹) then
                regularRestriction (p := p)
                  (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                  (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
              else 0) *
                (if hs : IsPRegular p s then
                  algebraMap A K
                    ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                      (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                else 0) =
          algebraMap A K
            ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i) := by
      -- Replace Serre's prime-to-`p` indicator by its canonical Brauer-basis expansion, then
      -- collapse each basis pairing by the previous Kronecker-delta helper.
      calc
        (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              (if hs : IsPRegular p (s⁻¹) then
                regularRestriction (p := p)
                  (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                  (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
              else 0) *
                (if hs : IsPRegular p s then
                  algebraMap A K
                    ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                      (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                else 0)
          =
            (Fintype.card G : K)⁻¹ *
              ∑ s : G,
                (if hs : IsPRegular p (s⁻¹) then
                  regularRestriction (p := p)
                    (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                    (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
                else 0) *
                  ∑ j,
                    algebraMap A K
                        ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                      (if hs : IsPRegular p s then
                        algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                      else 0) := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro s hs
                rw [hindicator s]
        _ =
            (Fintype.card G : K)⁻¹ *
              ∑ j,
                ∑ s : G,
                  algebraMap A K
                      ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                    ((if hs : IsPRegular p (s⁻¹) then
                      regularRestriction (p := p)
                        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                        (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
                    else 0) *
                      (if hs : IsPRegular p s then
                        algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                      else 0)) := by
                congr 1
                simp_rw [Finset.mul_sum]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl ?_
                intro j hj
                refine Finset.sum_congr rfl ?_
                intro s hs
                ring
        _ =
            ∑ j,
              algebraMap A K
                  ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                ((Fintype.card G : K)⁻¹ *
                  ∑ s : G,
                    (if hs : IsPRegular p (s⁻¹) then
                      regularRestriction (p := p)
                        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                        (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
                    else 0) *
                      (if hs : IsPRegular p s then
                        algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                      else 0)) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [← Finset.mul_sum]
                ring
        _ =
            ∑ j,
              algebraMap A K
                  ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                (if i = j then (1 : K) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                congr 1
                simpa [bA] using
                  (projectiveEnvelope_pairing_primeToP_indicator_eq_basis_repr
                    (p := p) (A := A) (K := K) (G := G)
                    (hω := hω)
                    (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
                    (P := P) (hP_envelope := hP_envelope) i j)
        _ =
            algebraMap A K
              ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i) := by
                simpa using
                  Finsupp.total_apply_single
                    (bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i
    calc
      (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
          regularRestriction (p := p)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
            (inversePRegularConjClass (p := p) c)
        =
          (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              (if hs : IsPRegular p (s⁻¹) then
                regularRestriction (p := p)
                  (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                  (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
              else 0) *
                (if hs : IsPRegular p s then
                  algebraMap A K
                    ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                      (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                else 0) := by
            -- This is the source class-sum computation that isolates the inverse-class value.
            symm
            exact
              projectiveEnvelope_pairing_primeToP_indicator_eq_inverse_regularRestriction
                (p := p) (A := A) (K := K) (G := G) (i := P i) c
      _ =
          algebraMap A K
            ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i) := h_expand
  have hppart_ne :=
    algebraMap_centralizerPPart_ne_zero (p := p) (A := A) (K := K) (G := G) c
  -- Clear the invertible denominator `ConjClasses.centralizerPPart p c.1` to recover Serre's
  -- divisibility statement itself, using `hpair_eq` directly.
  calc
    regularRestriction (p := p)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
          (inversePRegularConjClass (p := p) c)
      =
        algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) *
          ((algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
            regularRestriction (p := p)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
              (inversePRegularConjClass (p := p) c)) := by
          field_simp
    _ =
        algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) *
          algebraMap A K
            ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i) := by
          rw [hpair_eq]
    _ =
        algebraMap A K
          ((ConjClasses.centralizerPPart p c.1 : A) *
            ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i)) := by
          rw [← map_mul]

/-- Helper for Exercise 18-18.3-2: the regular restriction of each projective-character generator
already satisfies Serre's coordinatewise divisibility condition. -/
theorem regularRestriction_projectiveCharacter_mem_regularValueDivisibilitySubmodule
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (x : P₀[k](G)) :
    regularRestriction (p := p)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x) ∈
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
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
  -- Route correction: first reduce the arbitrary projective class to the canonical
  -- projective-envelope basis used by Serre, then isolate the source orthogonality calculation on
  -- those generators.
  refine
    regularRestriction_projectiveCharacter_mem_of_projectiveEnvelope_generators
      (p := p) (A := A) (K := K) (G := G) (π := π)
      hπ_pairwise hπ_complete (P := P) hP_envelope ?_ x
  intro i
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  have hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  refine
    (mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G)
      (regularRestriction (p := p)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀))).2 ?_
  intro c
  refine
    ⟨(bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c))) i, ?_⟩
  simpa [liftA, hliftA, bA, mul_comm, inversePRegularConjClass_involutive,
    ConjClasses.centralizerPPart_inv] using
    (projectiveEnvelope_regularRestriction_value_eq_centralizerPPart_mul_repr_inv
      (p := p) (A := A) (K := K) (G := G)
      (hω := hω)
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (P := P) (hP_envelope := hP_envelope) i
      (inversePRegularConjClass (p := p) c))

end ProjectiveCharacterCriterion

end Representation
