import Mathlib
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.RegularConjClassCore
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.RegularClassFunctionSpanBridge
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.MixedCharacterOwner
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.FiniteTransportCore
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.FiniteMixedCharacteristicRealization

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

local notation "Lexp" => CyclotomicField (Monoid.exponent G) ℚ

local instance : NumberField Lexp := inferInstance

local instance : IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
  CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)

/-- Helper for Theorem 18-18.2-1: a family is linearly independent once every finite-support
relation among its vectors forces each supported coefficient to vanish. -/
private theorem linearIndependent_of_supported_coefficient_vanishes_local
    {V : Type*} [AddCommGroup V] [Module K V]
    (v : ι → V)
    (hvanish :
      ∀ (s : Finset ι) (a : ι → K),
        (Finset.sum s fun j ↦ a j • v j) = 0 →
        ∀ ⦃i : ι⦄, i ∈ s → a i = 0) :
    LinearIndependent K v := by
  -- Repackage the finite-support vanishing criterion through the standard `Finset` formulation of
  -- linear independence.
  rw [linearIndependent_iff']
  intro s a hsum i hi
  exact hvanish s a hsum hi

/-- Helper for Theorem 18-18.2-1: in every characteristic-zero coefficient field, the order of the
finite group `G` stays nonzero. This is the Maschke-side arithmetic input needed when freezing
LinearRepresentations_Serre_1977 part `(b)` over an algebraically closed characteristic-zero owner. -/
private theorem nat_card_ne_zero_of_charZero_local
    {L : Type*} [Field L] [CharZero L] :
    (Nat.card G : L) ≠ 0 := by
  -- Positive group cardinality survives in every characteristic-zero field.
  exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'

/-- Helper for Theorem 18-18.2-1: at the full cyclotomic owner `Lexp`, the fixing subgroup of the
top intermediate field maps to the trivial subgroup of exponent units. This records the exact
cyclotomic arithmetic simplification that would feed the final owner step in part `(b)`. -/
private theorem top_cyclotomic_fixing_subgroup_maps_to_bot_local :
    (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).mapSubgroup
        ((⊤ : IntermediateField ℚ Lexp).fixingSubgroup) =
      (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := by
  -- The top cyclotomic field has trivial fixing subgroup, so its image is also trivial.
  rw [IntermediateField.fixingSubgroup_top]
  simpa using OrderIso.map_bot
    (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).mapSubgroup

/-- Helper for Theorem 18-18.2-1: after normalizing one supported coefficient, LinearRepresentations_Serre_1977 part `(a)`
reduces coefficient vanishing to the imported mixed-character contradiction. -/
private theorem supported_coefficient_zero_after_transport_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    (s : Finset ι)
    (a : ι → K)
    (hsum :
      (Finset.sum s
          fun j ↦ a j •
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E j)
              (PrimeToPRoot.toFieldLift lift)) =
        (0 : PRegularConjClass G p → K))
    {i : ι} (hi : i ∈ s) :
    a i = 0 := by
  by_contra hai
  -- Route correction: normalize the chosen coefficient locally, then hand the source-faithful
  -- mixed-character contradiction to the theorem-local support module.
  obtain ⟨aNorm, _haNorm_def, hsumNorm, haNorm_i⟩ :=
    normalized_supported_brauer_relation_local
      (p := p) (k := k) (K := K) (G := G) lift E s a hsum hi hai
  exact
    supported_normalized_brauer_relation_contradiction_over_residue_local
      (p := p) (k := k) (K := K) (G := G)
      lift hlift E hE_simple hE_pairwise s aNorm hsumNorm hi haNorm_i

/-- Helper for Theorem 18-18.2-1: LinearRepresentations_Serre_1977 part `(b)` now reduces directly to the canonical
finite-table transport theorem from the theorem-local support files. -/
private theorem regularClassFunction_mem_span_after_mixed_character_transport_local
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
  -- Route correction: the remaining source-faithful work for part `(b)` is already packaged in
  -- the imported finite transport theorem, so this file only keeps the outer span wrapper.
  exact
    finite_regular_and_brauer_table_span_transfer_over_witt_local
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete f

/-- Helper for Theorem 18-18.2-1: every `K`-valued function on `PRegularConjClass G p` already
lies in the span of the Brauer characters of a complete irreducible family. This is the explicit
one-function form of LinearRepresentations_Serre_1977 part `(b)` used before packaging the full `span = ⊤` statement. -/
theorem regularClassFunction_mem_span_irreducibleModularCharacters_of_complete_family
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
  -- Route correction: keep LinearRepresentations_Serre_1977 part `(b)` at the wrapper level as a one-function span statement,
  -- and let the theorem-local mixed-character transport module supply the only remaining heavy
  -- owner-change step.
  exact
    regularClassFunction_mem_span_after_mixed_character_transport_local
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete f

/-- Helper for Theorem 18-18.2-1: in the field-valued setting, pairwise nonisomorphic simple
modules have linearly independent Brauer characters on `PRegularConjClass G p`. -/
theorem linearIndependent_irreducibleModularCharacters_of_pairwiseNonisomorphic
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E) :
    LinearIndependent K
      (fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) := by
  -- LinearRepresentations_Serre_1977 part `(a)` reduces to vanishing of every supported coefficient in a finite relation.
  refine
    linearIndependent_of_supported_coefficient_vanishes_local
      (K := K)
      (v := fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) ?_
  intro s a hsum i hi
  exact
    supported_coefficient_zero_after_transport_local
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_simple hE_pairwise s a hsum hi

/-- Helper for Theorem 18-18.2-1: in the field-valued setting, the Brauer characters of a
complete irreducible family span the whole function space on `PRegularConjClass G p`. -/
theorem span_irreducibleModularCharacters_eq_top_of_complete_family
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Submodule.span K
        (Set.range fun i ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
            (PrimeToPRoot.toFieldLift lift)) =
      ⊤ := by
  -- LinearRepresentations_Serre_1977 part `(b)` is the statement that every regular class function already lies in the
  -- Brauer-character span.
  apply top_unique
  intro f _
  exact
    regularClassFunction_mem_span_irreducibleModularCharacters_of_complete_family
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete f

/-- Helper for Theorem 18-18.2-1: once LinearRepresentations_Serre_1977 parts `(a)` and `(b)` are available in the
field-valued setting, the Brauer-character family is a basis of the full function space. -/
private theorem brauer_character_linearIndependent_and_span_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    LinearIndependent K
        (fun i ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
            (PrimeToPRoot.toFieldLift lift)) ∧
      Submodule.span K
          (Set.range fun i ↦
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
              (PrimeToPRoot.toFieldLift lift)) =
        ⊤ := by
  -- Record LinearRepresentations_Serre_1977 parts `(a)` and `(b)` together as the stable proof skeleton used by the final
  -- basis construction.
  constructor
  · exact
      linearIndependent_irreducibleModularCharacters_of_pairwiseNonisomorphic
        (p := p) (k := k) (K := K) (G := G) lift hlift E hE_complete.isSimple hE_pairwise
  · exact
      span_irreducibleModularCharacters_eq_top_of_complete_family
        (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete

/-- Helper for Theorem 18-18.2-1: once LinearRepresentations_Serre_1977 parts `(a)` and `(b)` are available in the
field-valued setting, the Brauer-character family is a basis of the full function space. -/
private theorem basis_of_linearIndependent_and_span_eq_top_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Module.Basis ι K (PRegularConjClass G p → K) := by
  obtain ⟨hlin, hspan⟩ :=
    brauer_character_linearIndependent_and_span_local
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete
  -- Assemble the basis directly from the linearly independent Brauer rows and their span.
  refine
    Module.Basis.mk
      hlin
      ?_
  -- The spanning statement from LinearRepresentations_Serre_1977 part `(b)` is exactly the second basis axiom.
  exact hspan.ge

/-- Theorem 18-18.2-1: for a complete pairwise nonisomorphic family of simple finite-dimensional
`k[G]`-representations, the corresponding Brauer characters form a `K`-basis of the
`K`-vector space of `K`-valued functions on the `p`-regular conjugacy classes of `G`, viewed
through an injective multiplicative lift of the prime-to-`p` roots of unity into the field `K`. -/
def irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Module.Basis ι K (PRegularConjClass G p → K) :=
  -- Reduce the theorem statement to the already-isolated linear independence and spanning parts.
  basis_of_linearIndependent_and_span_eq_top_local
    (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete

@[simp]
theorem irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
        lift hlift E hE_pairwise hE_complete i =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
        (PrimeToPRoot.toFieldLift lift) := by
  -- Unfold the basis construction and read off the indexed basis vector.
  rw [irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions]
  simp

/-- Helper for Theorem 18-18.2-1: every regular class function has a canonical finite expansion
in the Brauer-character basis returned by the theorem. This packages the basis coordinates as the
finite witness that later span arguments can reuse without reopening the basis construction. -/
theorem exists_finite_brauer_character_expansion_of_complete_family
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (f : PRegularConjClass G p → K) :
    ∃ c : ι →₀ K,
      (Finset.sum c.support fun i ↦ c i •
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) = f := by
  let b :=
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete
  refine ⟨b.repr f, ?_⟩
  -- Expand `f` in the theorem's basis, then rewrite each basis vector back to the matching
  -- Brauer character.
  simpa [b, irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply] using
    b.sum_repr f

end

end Representation
