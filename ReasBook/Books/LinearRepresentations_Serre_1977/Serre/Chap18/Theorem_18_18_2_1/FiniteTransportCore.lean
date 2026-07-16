import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Serre.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.RegularConjClassCore
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.MixedCharacterOwner

noncomputable section

universe u x

open CategoryTheory

namespace Representation

section

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p] [Fact p.Prime]
variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

/-- Helper for Theorem 18-18.2-1: dividing a finite-support Brauer relation by a chosen nonzero
supported coefficient preserves the vanishing relation and normalizes that distinguished
coefficient to `1`. This is the exact algebraic prefix of Serre's denominator-normalization step
before any mixed-character model is introduced. -/
theorem normalized_supported_brauer_relation_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (E : ι → FDRep k G)
    (s : Finset ι)
    (a : ι → K)
    (hsum :
      (Finset.sum s
          fun j ↦ a j •
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E j)
              (PrimeToPRoot.toFieldLift lift)) =
        (0 : PRegularConjClass G p → K))
    {i : ι} (hi : i ∈ s)
    (hai : a i ≠ 0) :
    ∃ aNorm : ι → K,
      (∀ j, aNorm j = a j / a i) ∧
      (Finset.sum s
          fun j ↦ aNorm j •
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E j)
              (PrimeToPRoot.toFieldLift lift)) =
        (0 : PRegularConjClass G p → K) ∧
      aNorm i = 1 := by
  refine ⟨fun j ↦ a j / a i, ?_, ?_, ?_⟩
  · -- The normalized coefficients are defined by dividing every supported coefficient by `a i`.
    intro j
    rfl
  · -- Scale the original vanishing relation by `(a i)⁻¹`; commutativity of the field then
    -- rewrites the coefficients into the normalized form.
    ext c
    have hpoint := congrFun hsum c
    have hscaled : (a i)⁻¹ * ((Finset.sum s fun j ↦ a j •
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E j)
          (PrimeToPRoot.toFieldLift lift)) c) =
        (a i)⁻¹ * 0 :=
      congrArg (fun x : K ↦ (a i)⁻¹ * x) hpoint
    simpa [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm] using hscaled
  · -- The chosen supported coefficient becomes exactly `1` after normalization.
    simp [hai]

/-- Helper for Theorem 18-18.2-1: after normalizing a supported Brauer relation at one nonzero
coefficient, only finitely many coefficients and Brauer values remain. This is the finite table
that the mixed-character realization should transport. -/
theorem finite_normalized_brauer_relation_data_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (E : ι → FDRep k G)
    (s : Finset ι)
    (aNorm : ι → K) :
    Set.Finite (Set.range fun j : s ↦ aNorm j.1) ∧
      Set.Finite
        (Set.range fun q : s × PRegularConjClass G p ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E q.1.1)
            (PrimeToPRoot.toFieldLift lift) q.2) := by
  classical
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  refine ⟨?_, ?_⟩
  · -- The normalized coefficients are indexed by the finite support `s`.
    exact Set.finite_range fun j : s ↦ aNorm j.1
  · -- The Brauer-character values are indexed by the same finite support and the finite owner
    -- `PRegularConjClass G p`.
    exact
      Set.finite_range fun q : s × PRegularConjClass G p ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E q.1.1)
          (PrimeToPRoot.toFieldLift lift) q.2

/-- Helper for Theorem 18-18.2-1: Serre part `(b)` only has to transport the finitely many values
taken by a regular class function on the finite owner `PRegularConjClass G p`. -/
theorem finite_regularClassFunction_transport_values_local
    (f : PRegularConjClass G p → K) :
    Set.Finite (Set.range f) := by
  classical
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  -- The owner `PRegularConjClass G p` is finite because `G` is finite, so `f` has finite image.
  exact Set.finite_range f

/-- Helper for Theorem 18-18.2-1: in Serre part `(b)`, a complete irreducible family contributes
only finitely many Brauer-character values on the finite owner `PRegularConjClass G p`. -/
theorem finite_complete_family_brauer_values_local
    [NeZero (Nat.card G : k)]
    (lift : PrimeToPRoot p k →* Kˣ)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Set.Finite
      (Set.range fun q : ι × PRegularConjClass G p ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E q.1)
          (PrimeToPRoot.toFieldLift lift) q.2) := by
  let _ := hE_pairwise
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index E hE_complete hE_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  -- Both the index family and the regular-class owner are finite, so the combined Brauer table
  -- has finite image.
  exact
    Set.finite_range fun q : ι × PRegularConjClass G p ↦
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E q.1)
        (PrimeToPRoot.toFieldLift lift) q.2

/-- Helper for Theorem 18-18.2-1: postcomposing the chosen prime-to-`p` root lift with a ring
homomorphism postcomposes the descended Brauer character pointwise on `PRegularConjClass G p`. -/
theorem modularCharacterOnPRegularConjClass_comp_lift_local
    {A : Type x} [CommSemiring A]
    {B : Type x} [CommSemiring B]
    (σ : A →+* B)
    (lift : PrimeToPRoot p k →* A)
    (E : FDRep k G) :
    (fun c ↦ σ (FDRep.modularCharacterOnPRegularConjClass (p := p) E lift c)) =
      FDRep.modularCharacterOnPRegularConjClass (p := p) E (fun x ↦ σ (lift x)) := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- Evaluate both descended Brauer characters on the same regular representative and commute the
  -- coefficient-ring map through the defining multiset sum once.
  rw [← hs, FDRep.modularCharacterOnPRegularConjClass_ofSubtype,
    FDRep.modularCharacterOnPRegularConjClass_ofSubtype]
  simp [Representation.modularCharacter, Function.comp, map_multiset_sum]

/-- Helper for Theorem 18-18.2-1: if the characteristic parameter of the source field is nonzero,
then it is prime. This is the arithmetic gate needed before freezing Serre's mixed-character
transport at a Witt-vector owner. -/
theorem fact_prime_of_charP_ne_zero_local
    (hp0 : p ≠ 0) :
    Fact p.Prime := by
  let _hp0 := hp0
  -- Route correction: the Witt-owner branch only needs the standard characteristic arithmetic,
  -- so we package mathlib's prime-characteristic fact instead of keeping a local placeholder.
  infer_instance

/-- Helper for Theorem 18-18.2-1: in the positive-character branch, the theorem-local support file
already supplies Serre's fixed mixed-character owner `W(k)` together with its residue-field
identification back to `k`. -/
theorem exists_fixed_witt_owner_of_charP_ne_zero_local
    (hp0 : p ≠ 0) :
    ∃ (A0 : Type u) (_ : CommRing A0) (_ : Fact p.Prime) (_ : IsLocalRing A0)
      (_ : IsDomain A0) (_ : IsDiscreteValuationRing A0)
      (K0 : Type u) (_ : Field K0) (_ : Algebra A0 K0) (_ : IsFractionRing A0 K0)
      (_ : CharZero K0) (_e0 : IsLocalRing.ResidueField A0 ≃+* k), True := by
  let _ := fact_prime_of_charP_ne_zero_local (p := p) hp0
  -- Freeze Serre's mixed-character route at the theorem-local Witt-vector owner from the support
  -- file; all later transport data is meant to live over this fixed DVR.
  simpa using mixed_character_owner_with_residue_equiv_local (p := p) (k := k)

/-- Helper for Theorem 18-18.2-1: once Serre freezes part `(a)` at the Witt-vector owner `W(k)`,
the prime-to-`p` roots already have the canonical Teichmuller lift, and reducing by the constant
coefficient map recovers the original root in `k`. This removes owner-selection noise from the
remaining finite realization step. -/
theorem exists_witt_vector_primeToPRoot_lift_with_reduction_local :
    ∃ lift0 : PrimeToPRoot p k →* WittVector p k,
      ∃ red0 : WittVector p k →+* k,
        ∀ x : PrimeToPRoot p k, red0 (lift0 x) = ((x : kˣ) : k) := by
  let valLift : PrimeToPRoot p k →* k :=
    { toFun := fun x ↦ ((x : kˣ) : k)
      map_one' := by simp
      map_mul' := by
        intro x y
        simp }
  refine ⟨(WittVector.teichmuller p).comp valLift, WittVector.constantCoeff, ?_⟩
  intro x
  -- The Teichmuller lift is a right inverse to the constant coefficient map on Witt vectors.
  simp [valLift]

end

end Representation
