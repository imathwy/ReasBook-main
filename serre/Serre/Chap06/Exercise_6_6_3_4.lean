import Mathlib
import Serre.Chap02.Corollary_2_2_4_3
import Serre.Chap06.Proposition_6_6_3_1
import Serre.Chap06.Proposition_6_6_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra Representation
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {k G : Type u} [Field k] [IsAlgClosed k]
variable {ι : Type v} [Group G] [Finite G] [Invertible (Nat.card G : k)]
variable (π : ι → Rep k G)
variable [∀ i, FiniteDimensional k (π i)]

-- Source/core/bridge triage:
-- * source-facing: the exercise says that every `k`-algebra map from the center of `k[G]` to `k`
--   is the central character of one irreducible constituent in a complete family.
-- * core/canonical: the chapter owner `ω[ρ] = centralCharacter ρ` from
--   Proposition `6-6.3-1`, together with the owner equivalence
--   `centralCharacterFamilyAlgEquiv` from Proposition `6-6.3-2`.
-- * bridge/view: the scalar-action reformulation comes afterward from
--   `asAlgebraHom_center_eq_centralCharacter_smul_id`.
-- Proof sketch: Proposition `centralCharacterFamilyAlgEquiv` identifies the center of `k[G]`
-- with the product algebra `ι → k`. The completeness and pairwise-nonisomorphism hypotheses make
-- `ι` finite, so `AlgHom.eq_piEvalAlgHom` says that any algebra map `(ι → k) →ₐ[k] k` is
-- evaluation at some index `i`. Transporting back along the equivalence identifies `η` with the
-- central character `ω[(π i).ρ]`.
/-- For a complete pairwise nonisomorphic irreducible family, every `k`-algebra homomorphism from
the center of `k[G]` to `k` is the central character of one member of the family. -/
theorem exists_centralCharacter_of_pairwise_complete_irreducible_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (η : Subalgebra.center k (k[G]) →ₐ[k] k) :
    ∃ i,
      let _ : (π i).ρ.IsIrreducible :=
        IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
      ω[(π i).ρ] = η := by
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  obtain ⟨i, hi⟩ := (η.comp e.symm.toAlgHom).eq_piEvalAlgHom
  refine ⟨i, ?_⟩
  letI : (π i).ρ.IsIrreducible := IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  ext u
  -- Evaluate the algebra-map identity on the image of `u` under the central-character equivalence.
  have hu : η u = (e u) i := by
    simpa using congrArg (fun f : (ι → k) →ₐ[k] k ↦ f (e u)) hi
  simpa [e] using hu.symm

-- Proof sketch: first identify `η` with `ω[(π i).ρ]` via the previous theorem, then use
-- Proposition `asAlgebraHom_center_eq_centralCharacter_smul_id` to translate equality of central
-- characters into the scalar-action formula.
/-- Scalar-action reformulation of
`exists_centralCharacter_of_pairwise_complete_irreducible_family`. -/
theorem exists_centralCharacter_action_of_pairwise_complete_irreducible_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (η : Subalgebra.center k (k[G]) →ₐ[k] k) :
    ∃ i,
      ∀ u : Subalgebra.center k (k[G]),
        (π i).ρ.asAlgebraHom u = η u • LinearMap.id := by
  obtain ⟨i, hi⟩ :=
    exists_centralCharacter_of_pairwise_complete_irreducible_family π hπ_pairwise hπ_complete η
  refine ⟨i, ?_⟩
  letI : (π i).ρ.IsIrreducible := IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  have hi' : ω[(π i).ρ] = η := hi
  intro u
  have hiu : ω[(π i).ρ] u = η u := by
    simpa using congrArg (fun f : Subalgebra.center k (k[G]) →ₐ[k] k ↦ f u) hi'
  rw [← hiu]
  exact asAlgebraHom_center_eq_centralCharacter_smul_id (π i).ρ u

/-- Helper for Exercise 6-6.3-4: isomorphism of the underlying representations defines the
quotient relation used to choose one representative from each isomorphism class. -/
private abbrev representationIsoSetoid : Setoid ι :=
  { r := fun i j ↦ Nonempty ((π i).ρ.Equiv (π j).ρ)
    iseqv :=
      ⟨fun i ↦ ⟨Representation.Equiv.refl ((π i).ρ)⟩,
        fun {i j} hij ↦ by
          rcases hij with ⟨e⟩
          exact ⟨e.symm⟩,
        fun {i j l} hij hjl ↦ by
          rcases hij with ⟨eij⟩
          rcases hjl with ⟨ejl⟩
          exact ⟨eij.trans ejl⟩⟩ }

/-- Helper for Exercise 6-6.3-4: choose a concrete representative for each isomorphism class in
the complete family. -/
private abbrev quotientRepresentativeFamily :
    Quotient (representationIsoSetoid (π := π)) → Rep k G :=
  fun q ↦ π (Quotient.out q)

/-- Helper for Exercise 6-6.3-4: different quotient classes cannot label isomorphic chosen
representatives. -/
private theorem quotientRepresentativeFamily_pairwiseNonisomorphic :
    PairwiseNonisomorphic (quotientRepresentativeFamily (π := π)) := by
  -- Distinct quotient classes would coincide if their chosen representatives were isomorphic.
  intro q q' hqq' hIso
  rcases hIso with ⟨e⟩
  have hrel :
      Nonempty ((π (Quotient.out q)).ρ.Equiv (π (Quotient.out q')).ρ) := by
    simpa [quotientRepresentativeFamily] using
      (show
          Nonempty
            (((quotientRepresentativeFamily (π := π) q).ρ).Equiv
              ((quotientRepresentativeFamily (π := π) q').ρ)) from
        ⟨Representation.equivOfIso e⟩)
  have hclasses :
      (⟦Quotient.out q⟧ : Quotient (representationIsoSetoid (π := π))) =
        (⟦Quotient.out q'⟧ : Quotient (representationIsoSetoid (π := π))) :=
    Quotient.sound hrel
  apply hqq'
  calc
    q = (⟦Quotient.out q⟧ : Quotient (representationIsoSetoid (π := π))) :=
      (Quotient.out_eq q).symm
    _ = (⟦Quotient.out q'⟧ : Quotient (representationIsoSetoid (π := π))) := hclasses
    _ = q' := Quotient.out_eq q'

/-- Helper for Exercise 6-6.3-4: the chosen representative of the class of `i` remains equivalent
to the original representation indexed by `i`. -/
private theorem quotientRepresentativeFamily_equiv_original (i : ι) :
    Nonempty
      (((quotientRepresentativeFamily (π := π)
            (⟦i⟧ : Quotient (representationIsoSetoid (π := π)))).ρ).Equiv
        (π i).ρ) := by
  -- `Quotient.out` picks a representative of the class `⟦i⟧`, so it is equivalent to `i`.
  simpa [quotientRepresentativeFamily] using
    (Quotient.exact
      (Quotient.out_eq (⟦i⟧ : Quotient (representationIsoSetoid (π := π)))))

/-- Helper for Exercise 6-6.3-4: the quotient representative family is still complete and
irreducible after passing to one representative per isomorphism class. -/
private theorem quotientRepresentativeFamily_complete
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    IsCompleteIrreducibleFamily
      (fun q ↦ FDRep.of ((quotientRepresentativeFamily (π := π) q).ρ)) := by
  refine
    { isSimple := ?_
      exists_iso := ?_ }
  · intro q
    -- Each chosen representative is literally one member of the original complete family.
    simpa [quotientRepresentativeFamily] using hπ_complete.isSimple (Quotient.out q)
  · intro τ hτ
    -- First use completeness of the original family, then move the witness to its quotient class.
    obtain ⟨i, hi⟩ := hπ_complete.exists_iso τ hτ
    refine ⟨(⟦i⟧ : Quotient (representationIsoSetoid (π := π))), ?_⟩
    have hout :
        Nonempty
          (((quotientRepresentativeFamily (π := π)
                (⟦i⟧ : Quotient (representationIsoSetoid (π := π)))).ρ).Equiv
            (π i).ρ) :=
      quotientRepresentativeFamily_equiv_original (π := π) i
    rcases hout with ⟨hout⟩
    rcases hi with ⟨hi⟩
    simpa [quotientRepresentativeFamily] using ⟨hi.trans hout.toFDRepIso.symm⟩

-- Proof sketch: first replace the complete family by a complete pairwise nonisomorphic
-- representative subfamily; then apply
-- `exists_centralCharacter_of_pairwise_complete_irreducible_family` and transport the resulting
-- central-character identity back along the chosen isomorphism into the original family.
/-- Exercise 6-6.3-4: for a complete family of irreducible finite-dimensional representations of a
finite group over an algebraically closed field in which `|G|` is invertible, every `k`-algebra
homomorphism from the center of `k[G]` to `k` is the central character of one member of the
family. -/
theorem exists_centralCharacter_of_complete_irreducible_family
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (η : Subalgebra.center k (k[G]) →ₐ[k] k) :
    ∃ i,
      let _ : (π i).ρ.IsIrreducible :=
        IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
      ω[(π i).ρ] = η := by
  classical
  let πq := quotientRepresentativeFamily (π := π)
  letI : ∀ q, FiniteDimensional k (πq q) :=
    fun q ↦ by
      simpa [πq, quotientRepresentativeFamily] using
        (inferInstance : FiniteDimensional k (π (Quotient.out q)))
  have hπq_pairwise : PairwiseNonisomorphic πq :=
    quotientRepresentativeFamily_pairwiseNonisomorphic (π := π)
  have hπq_complete :
      IsCompleteIrreducibleFamily (fun q ↦ FDRep.of (πq q).ρ) := by
    -- The quotient family keeps exactly one representative from each original isomorphism class.
    simpa [πq] using quotientRepresentativeFamily_complete (π := π) hπ_complete
  -- Apply the pairwise theorem to the quotient family and return its chosen original index.
  obtain ⟨q, hq⟩ :=
    exists_centralCharacter_of_pairwise_complete_irreducible_family
      (π := πq) hπq_pairwise hπq_complete η
  refine ⟨Quotient.out q, ?_⟩
  simpa [πq, quotientRepresentativeFamily] using hq

-- Proof sketch: use the central-character form of Exercise `6-6.3-4`, then translate it to the
-- scalar-action statement via Proposition `asAlgebraHom_center_eq_centralCharacter_smul_id`.
/-- Scalar-action reformulation of
`exists_centralCharacter_of_complete_irreducible_family`. -/
theorem exists_centralCharacter_action_of_complete_irreducible_family
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (η : Subalgebra.center k (k[G]) →ₐ[k] k) :
    ∃ i,
      ∀ u : Subalgebra.center k (k[G]),
        (π i).ρ.asAlgebraHom u = η u • LinearMap.id := by
  obtain ⟨i, hi⟩ := exists_centralCharacter_of_complete_irreducible_family π hπ_complete η
  refine ⟨i, ?_⟩
  letI : (π i).ρ.IsIrreducible := IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  have hi' : ω[(π i).ρ] = η := hi
  intro u
  have hiu : ω[(π i).ρ] u = η u := by
    simpa using congrArg (fun f : Subalgebra.center k (k[G]) →ₐ[k] k ↦ f u) hi'
  rw [← hiu]
  exact asAlgebraHom_center_eq_centralCharacter_smul_id (π i).ρ u

end

end Representation
