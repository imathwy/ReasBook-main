import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Serre.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.RegularConjClassCore
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.RegularClassFunctionSpanBridge
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.BrauerRelationSeparator
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.MixedCharacterOwner
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.FiniteTransportCore

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

/-- Helper for Theorem 18-18.2-1: the fixed Witt-vector lift of prime-to-`p` roots is already
injective, because reducing by `constantCoeff` recovers the original root in `k`. This isolates
the exact owner-level injectivity needed before passing from `W(k)` to its fraction field. -/
private theorem witt_vector_primeToPRoot_lift_injective_local
    (lift0 : PrimeToPRoot p k →* WittVector p k)
    (red0 : WittVector p k →+* k)
    (hred0 : ∀ x : PrimeToPRoot p k, red0 (lift0 x) = ((x : kˣ) : k)) :
    Function.Injective lift0 := by
  intro x y hxy
  -- Reduce the Witt-vector equality to the residue field, where the chosen lift is the identity
  -- on the underlying prime-to-`p` roots.
  apply Subtype.ext
  apply Units.val_injective
  simpa [hred0 x, hred0 y] using congrArg red0 hxy

/-- Helper for Theorem 18-18.2-1: the fixed Witt-vector lift induces an injective units-valued
lift into `Frac(W(k))`. This is the canonical mixed-character lift that both Serre part `(a)` and
part `(b)` are meant to use after freezing the owner at `W(k)`. -/
private theorem exists_fractionRing_witt_primeToPRoot_units_lift_local :
    ∃ liftFrac : PrimeToPRoot p k →* (FractionRing (WittVector p k))ˣ,
      Function.Injective liftFrac := by
  obtain ⟨lift0, red0, hred0⟩ :=
    exists_witt_vector_primeToPRoot_lift_with_reduction_local (p := p) (k := k)
  let liftField : PrimeToPRoot p k →* FractionRing (WittVector p k) :=
    ((algebraMap (WittVector p k) (FractionRing (WittVector p k))).toMonoidHom).comp lift0
  have hlift0 : Function.Injective lift0 :=
    witt_vector_primeToPRoot_lift_injective_local lift0 red0 hred0
  have hliftField : Function.Injective liftField := by
    intro x y hxy
    apply hlift0
    exact (IsFractionRing.injective (WittVector p k) (FractionRing (WittVector p k))) hxy
  -- Package the field-valued fraction-field lift as a units-valued lift, which is the form
  -- consumed by `PrimeToPRoot.toFieldLift` in the later span and row-comparison lemmas.
  refine ⟨unitsLift_of_fieldLift (p := p) (k := k) liftField, ?_⟩
  exact unitsLift_of_fieldLift_injective (p := p) (k := k) liftField hliftField

/-- Helper for Theorem 18-18.2-1: applying a coefficient-ring map to a finite Brauer relation
preserves the pointwise zero relation on `PRegularConjClass G p`. This isolates the rowwise
transport rewrite used before and after the mixed-character owner change. -/
private theorem zero_brauer_relation_map_local
    {A : Type u} [CommSemiring A]
    {B : Type u} [CommSemiring B]
    (σ : A →+* B)
    (lift : PrimeToPRoot p k →* A)
    (E : ι → FDRep k G)
    (s : Finset ι)
    (a : ι → A)
    (hsum :
      (Finset.sum s
          fun j ↦ a j •
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E j) lift) =
        (0 : PRegularConjClass G p → A)) :
    (Finset.sum s
        fun j ↦ σ (a j) •
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E j) (fun x ↦ σ (lift x))) =
      (0 : PRegularConjClass G p → B) := by
  -- Apply `σ` pointwise to the vanished finite relation, then rewrite each Brauer row through
  -- the coefficient-map comparison from `FiniteTransportCore`.
  ext c
  have hpoint := congrFun hsum c
  have hmap :
      σ
          ((Finset.sum s
              fun j ↦ a j •
                FDRep.modularCharacterOnPRegularConjClass (p := p) (E j) lift) c) =
        σ 0 :=
    congrArg σ hpoint
  have hrow :
      ∀ j,
        σ (FDRep.modularCharacterOnPRegularConjClass (p := p) (E j) lift c) =
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E j) (fun x ↦ σ (lift x)) c := by
    intro j
    simpa using congrFun
      (modularCharacterOnPRegularConjClass_comp_lift_local
        (p := p) (k := k) (G := G) σ lift (E j)) c
  simpa [Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hrow] using hmap

/-- Helper for Theorem 18-18.2-1: Serre's zero-extension on `PRegularConjClass G p` commutes with
postcomposing the values by a field homomorphism. This packages the finite-table rewrite needed in
part `(b)` before comparing upstairs and downstairs regular class functions. -/
private theorem regularClassFunctionExtension_map_local
    {A : Type u} [Field A]
    {B : Type u} [Field B]
    (σ : A →+* B)
    (f : PRegularConjClass G p → A) :
    (fun g ↦ σ (regularClassFunctionExtension (G := G) (p := p) f g)) =
      regularClassFunctionExtension (G := G) (p := p) (fun c ↦ σ (f c)) := by
  -- Serre's extension is defined by the same regular/non-regular case split both before and
  -- after postcomposition by `σ`, so a direct branchwise comparison is enough.
  funext g
  by_cases hg : IsPRegular p g
  · rw [regularClassFunctionExtension, regularClassFunctionExtension, dif_pos hg, dif_pos hg]
  · simp [regularClassFunctionExtension, hg]

/-- Helper for Theorem 18-18.2-1: once the normalized Brauer relation has been realized over the
fixed Witt owner, Serre part `(a)` reduces it by `constantCoeff`, applies the public separator on
the chosen simple factor, and reaches the contradiction `0 = 1`. -/
theorem supported_normalized_brauer_relation_contradiction_over_residue_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    (s : Finset ι)
    (aNorm : ι → K)
    (hsumNorm :
      (Finset.sum s
          fun j ↦ aNorm j •
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E j)
              (PrimeToPRoot.toFieldLift lift)) =
        (0 : PRegularConjClass G p → K))
    {i : ι} (hi : i ∈ s)
    (haNorm_i : aNorm i = 1) :
    False := by
  have hlin :
      LinearIndependent K
        (fun j ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E j)
            (PrimeToPRoot.toFieldLift lift)) := by
    -- Route correction: use the already-packaged linear independence theorem on
    -- `PRegularConjClass G p` instead of rebuilding Serre part `(a)` through an internal
    -- mixed-character realization.
    exact
      linearIndependent_irreducibleModularCharacters_of_pairwiseNonisomorphic
        (p := p) (k := k) (K := K)
        lift hlift E hE_simple hE_pairwise
  rw [linearIndependent_iff'] at hlin
  have hi_zero : aNorm i = 0 := hlin s aNorm hsumNorm i hi
  -- The normalized coefficient cannot be both `0` and `1`.
  have h01 : (0 : K) = 1 := by
    simpa [hi_zero] using haNorm_i
  exact zero_ne_one h01

theorem finite_regular_and_brauer_table_span_transfer_over_witt_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (f : PRegularConjClass G p → K) :
    f ∈ Submodule.span K
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) := by
  let b :=
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (p := p) (k := k) (K := K)
      lift hlift E hE_pairwise hE_complete
  have hspan :
      Submodule.span K
        (Set.range fun i ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
            (PrimeToPRoot.toFieldLift lift)) =
        ⊤ := by
    -- The canonical Brauer-character basis already spans the whole function space.
    have hb :
        (⇑b : ι → (PRegularConjClass G p → K)) =
          fun i ↦
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
              (PrimeToPRoot.toFieldLift lift) := by
      funext i
      exact
        irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply
          (p := p) (k := k) (K := K) lift hlift E hE_pairwise hE_complete i
    rw [← hb]
    exact b.span_eq
  -- Rewrite the span to `⊤`, where membership is immediate.
  rw [hspan]
  exact Submodule.mem_top

end

end Representation
