import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.RepresentationTheory.ExternalTensor
import LinearRepresentations_Serre_1977.FiniteToFintype

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

set_option linter.unnecessarySimpa false

open CategoryTheory
open MonoidHom (fst snd)
open scoped BigOperators TensorProduct

universe u v v' w w'

noncomputable local instance instDecidableEqOfFinite (α : Type*) [Finite α] : DecidableEq α :=
  Classical.decEq α

namespace Representation

end Representation

namespace CategoryTheory

section

variable {C : Type u} [Category C]
variable {ι : Type v}

/-- Helper for Theorem 3-3.2-1: a family is pairwise nonisomorphic when distinct indices cannot
label isomorphic objects. -/
abbrev PairwiseNonisomorphic (X : ι → C) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → ¬ Nonempty (X i ≅ X j)

end

end CategoryTheory

namespace Representation

section

variable {R : Type u} [Ring R]
variable {G : Type u} [Monoid G]
variable {ι : Type v}

/-- Helper for Theorem 3-3.2-1: a complete irreducible family in `FDRep` consists of simple
objects and contains a representative of every simple object up to isomorphism. -/
class IsCompleteIrreducibleFamily (π : ι → FDRep R G) : Prop where
  isSimple (i : ι) : Simple (π i)
  exists_iso (τ : FDRep R G) (_hτ : Simple τ) : ∃ i, Nonempty (τ ≅ π i)

attribute [instance] IsCompleteIrreducibleFamily.isSimple

namespace IsCompleteIrreducibleFamily

section

variable {K : Type u} [Field K]
variable {G : Type u} [Monoid G]

/-- Helper for Theorem 3-3.2-1: completeness for the `FDRep` owner also covers irreducible
representations after rebundling them as finite-dimensional objects. -/
theorem exists_iso_of_representation (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K G W) (hτ : τ.IsIrreducible) :
    ∃ i, Nonempty (FDRep.of τ ≅ π i) := by
  -- Move the irreducible representation into the canonical owner before applying completeness.
  letI : Representation.IsIrreducible τ := hτ
  letI : Representation.IsIrreducible ((FDRep.of τ).ρ) := by
    simpa using hτ
  letI : Simple (FDRep.of τ) := FDRep.simple_of_isIrreducible (FDRep.of τ)
  exact hπ_complete.exists_iso (FDRep.of τ) (FDRep.simple_of_isIrreducible (FDRep.of τ))

end

end IsCompleteIrreducibleFamily

section

variable {G : Type u} [Monoid G]
variable {K : Type v} [CommSemiring K]
variable {ι : Type w}
variable {M : ι → Type v'} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module K (M i)]
variable {W : Type w'} [AddCommMonoid W] [Module K W]

/-- Helper for Theorem 3-3.2-1: intertwining maps from a direct sum are exactly families of
intertwining maps from each summand. -/
private noncomputable def directSumIntertwiningMapEquivPi
    (π : ∀ i, Representation K G (M i)) (τ : Representation K G W) :
    (directSum π).IntertwiningMap τ ≃ₗ[K] ∀ i, (π i).IntertwiningMap τ :=
  let _ : DecidableEq ι := Classical.decEq ι
  { toFun := fun F i ↦
      ((F.toLinearMap.comp
          (DirectSum.lof K ι M i)).intertwiningMap_of_isIntertwiningMap
        (π i) τ fun g x ↦ by
          simpa [Representation.directSum] using
            congr($(F.isIntertwining' g) (DirectSum.lof K ι M i x)))
    invFun := fun f ↦
      { toLinearMap := DirectSum.toModule K ι W fun i ↦ (f i).toLinearMap
        isIntertwining' := by
          intro g
          apply DirectSum.linearMap_ext
          intro i
          ext x
          simp [Representation.directSum, Representation.IntertwiningMap.isIntertwining] }
    left_inv := by
      intro F
      apply IntertwiningMap.ext
      apply DirectSum.linearMap_ext
      intro i
      ext x
      change
        (DirectSum.toModule K ι W
          (fun j ↦ F.toLinearMap.comp (DirectSum.lof K ι M j)))
          (DirectSum.lof K ι M i x) =
        F (DirectSum.lof K ι M i x)
      simp
    right_inv := by
      intro f
      funext i
      apply IntertwiningMap.ext
      ext x
      change
        (DirectSum.toModule K ι W fun j ↦ (f j).toLinearMap)
          (DirectSum.lof K ι M i x) =
        (f i) x
      simp
    map_add' := by
      intro F H
      funext i
      apply IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a F
      funext i
      apply IntertwiningMap.ext
      ext x
      rfl }

end

section

variable {G : Type u} [Monoid G]
variable {K : Type v} [CommSemiring K]
variable {V : Type v'} [AddCommMonoid V] [Module K V]
variable {W : Type w} [AddCommMonoid W] [Module K W]
variable {U : Type w'} [AddCommMonoid U] [Module K U]

namespace Equiv

/-- Helper for Theorem 3-3.2-1: precomposing with a representation equivalence identifies
intertwining spaces with the same codomain. -/
private noncomputable def intertwiningMapCongrLeft
    {ρ : Representation K G V} {σ : Representation K G W}
    (e : ρ.Equiv σ) (τ : Representation K G U) :
    σ.IntertwiningMap τ ≃ₗ[K] ρ.IntertwiningMap τ :=
  { toFun := fun f ↦ f.comp e.toIntertwiningMap
    invFun := fun f ↦ f.comp e.symm.toIntertwiningMap
    left_inv := by
      intro f
      apply IntertwiningMap.ext
      ext x
      simp
    right_inv := by
      intro f
      apply IntertwiningMap.ext
      ext x
      simp
    map_add' := by
      intro f g
      apply IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a f
      apply IntertwiningMap.ext
      ext x
      rfl }

end Equiv

end

section

variable {G : Type u} [Monoid G]
variable {K : Type v} [Field K]
variable {V : Type v'} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]
variable {ι : Type w'} [Fintype ι]

/-- Helper for Theorem 3-3.2-1: count the indices whose summand isomorphic to a fixed target by
the corresponding indicator sum. -/
private theorem nat_card_isomorphic_summands_eq_sum_ite
    (ρ : Representation K G V) (σ : ι → Subrepresentation ρ)
    (τ : Representation K G W) :
    by
      classical
      exact Nat.card { i // Nonempty (((σ i).toRepresentation).Equiv τ) } =
        ∑ i, if Nonempty (((σ i).toRepresentation).Equiv τ) then 1 else 0 := by
  classical
  -- Rewrite the subtype cardinality as a filter on `Finset.univ`.
  rw [Nat.card_eq_fintype_card,
    Fintype.card_of_subtype
      (Finset.univ.filter fun i ↦ Nonempty (((σ i).toRepresentation).Equiv τ))]
  · rw [Finset.card_filter]
  · intro i
    simp

end

section

variable {G : Type u} [Monoid G]
variable {K : Type v} [Field K] [IsAlgClosed K]
variable {V : Type v'} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {ι : Type w'} [Finite ι]

section

omit [FiniteDimensional K V]

/-- Helper for Theorem 3-3.2-1: Schur's lemma makes the intertwining space between irreducible
representations one-dimensional exactly in the isomorphic case, and zero-dimensional otherwise. -/
theorem finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible
    (ρ : Representation K G V) (hρ : ρ.IsIrreducible)
    (τ : Representation K G W) (hτ : τ.IsIrreducible) :
    by
      classical
      exact Module.finrank K (ρ.IntertwiningMap τ) = if Nonempty (ρ.Equiv τ) then 1 else 0 := by
  classical
  letI : ρ.IsIrreducible := hρ
  letI : τ.IsIrreducible := hτ
  by_cases hρτ : Nonempty (ρ.Equiv τ)
  · rcases hρτ with ⟨e⟩
    have hρτ : Nonempty (ρ.Equiv τ) := ⟨e⟩
    -- Transport to the self-case and then apply Schur's lemma.
    calc
      Module.finrank K (ρ.IntertwiningMap τ) =
          Module.finrank K (τ.IntertwiningMap τ) := by
            symm
            exact (Representation.Equiv.intertwiningMapCongrLeft e τ).finrank_eq
      _ = 1 := IsIrreducible.finrank_intertwiningMap_self τ
      _ = if Nonempty (ρ.Equiv τ) then 1 else 0 := by simp [hρτ]
  · letI : IsEmpty (ρ.Equiv τ) := not_nonempty_iff.mp hρτ
    letI : Subsingleton (ρ.IntertwiningMap τ) := inferInstance
    -- In the nonisomorphic case, all intertwiners vanish.
    calc
      Module.finrank K (ρ.IntertwiningMap τ) = 0 := Module.finrank_zero_of_subsingleton
      _ = if Nonempty (ρ.Equiv τ) then 1 else 0 := by simp [hρτ]

end

omit [IsAlgClosed K] in
/-- Helper for Theorem 3-3.2-1: an internal direct-sum decomposition turns the intertwining-space
dimension against `τ` into the sum of the corresponding dimensions on the summands. -/
private theorem finrank_intertwiningMap_eq_sum_of_isInternal
    (ρ : Representation K G V) (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (τ : Representation K G W) [Fintype ι] :
    Module.finrank K (ρ.IntertwiningMap τ) =
      ∑ i, Module.finrank K (((σ i).toRepresentation).IntertwiningMap τ) := by
  classical
  let ℳ : ι → Submodule K V := fun i ↦ (σ i).toSubmodule
  let π : ∀ i, Representation K G (ℳ i) := fun i ↦ (σ i).toRepresentation
  letI := DirectSum.IsInternal.chooseDecomposition ℳ hinternal
  let decompositionEquiv : (directSum π).Equiv ρ :=
    Representation.Equiv.mk
      (DirectSum.decomposeLinearEquiv ℳ).symm
      (fun g ↦ by
        ext i x
        simp [Representation.directSum, π]
        rfl)
  have hpi :
      Module.finrank K (∀ i, (π i).IntertwiningMap τ) =
        ∑ i, Module.finrank K (((σ i).toRepresentation).IntertwiningMap τ) := by
    have hpi' :
        Module.finrank K (∀ i, (π i).IntertwiningMap τ) =
          ∑ i, Module.finrank K ((π i).IntertwiningMap τ) := by
      rw [Module.finrank_pi_fintype]
    simpa [π] using hpi'
  -- Replace `ρ` by the equivalent direct sum and then use the direct-sum universal property.
  calc
    Module.finrank K (ρ.IntertwiningMap τ)
      = Module.finrank K ((directSum π).IntertwiningMap τ) := by
          exact
            (Representation.Equiv.intertwiningMapCongrLeft decompositionEquiv τ).finrank_eq
    _ = Module.finrank K (∀ i, (π i).IntertwiningMap τ) := by
          exact (directSumIntertwiningMapEquivPi π τ).finrank_eq
    _ = ∑ i, Module.finrank K (((σ i).toRepresentation).IntertwiningMap τ) := hpi

omit [FiniteDimensional K V] in
/-- Helper for Theorem 3-3.2-1: an irreducible summand contributes `1` exactly when it is
isomorphic to the target irreducible representation, and `0` otherwise. -/
private theorem finrank_intertwiningMap_irreducible_summand_eq_ite
    {U : Type w'} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (ρ : Representation K G V) (σ : Subrepresentation ρ)
    (hσ : σ.toRepresentation.IsIrreducible)
    (τ : Representation K G U) (hτ : τ.IsIrreducible) :
    by
      classical
      exact Module.finrank K (σ.toRepresentation.IntertwiningMap τ) =
        if Nonempty (σ.toRepresentation.Equiv τ) then 1 else 0 := by
  letI : σ.toRepresentation.IsIrreducible := hσ
  simpa using
    finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible σ.toRepresentation hσ τ hτ

/-- Helper for Theorem 3-3.2-1: the multiplicity of an irreducible summand in an internal
decomposition equals the dimension of the corresponding intertwining space. -/
theorem card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
    (ρ : Representation K G V) (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (τ : Representation K G W) (hτ : τ.IsIrreducible) :
    Nat.card { i // Nonempty (((σ i).toRepresentation).Equiv τ) } =
      Module.finrank K (ρ.IntertwiningMap τ) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hfactor :
      ∀ i, Module.finrank K (((σ i).toRepresentation).IntertwiningMap τ) =
        if Nonempty (((σ i).toRepresentation).Equiv τ) then 1 else 0 := by
    intro i
    simpa using finrank_intertwiningMap_irreducible_summand_eq_ite
      ρ (σ i) (hσ i) τ hτ
  calc
    Nat.card { i // Nonempty (((σ i).toRepresentation).Equiv τ) } =
        ∑ i, if Nonempty (((σ i).toRepresentation).Equiv τ) then 1 else 0 := by
          exact nat_card_isomorphic_summands_eq_sum_ite ρ σ τ
    _ = ∑ i, Module.finrank K (((σ i).toRepresentation).IntertwiningMap τ) := by
          congr with i
          symm
          exact hfactor i
    _ = Module.finrank K (ρ.IntertwiningMap τ) := by
          symm
          exact finrank_intertwiningMap_eq_sum_of_isInternal ρ σ hinternal τ

end

section

variable {G : Type u} [Group G] [Finite G]
variable {ι : Type v} [Finite ι]
variable {K : Type u} [Field K] [IsAlgClosed K] [NeZero (Nat.card G : K)]
variable (π : ι → FDRep K G)

private abbrev IsIrreducibleLeftRegularSummand
    (σ : Subrepresentation (leftRegular K G)) : Prop :=
  let _ : AddCommGroup σ.toSubmodule := inferInstance
  Representation.IsIrreducible (σ.toRepresentation)

omit [Finite G] [IsAlgClosed K] [NeZero (Nat.card G : K)] in
/-- Helper for Theorem 3-3.2-1: an irreducible summand in an internal decomposition of the left
regular representation has nontrivial carrier. -/
private theorem summand_toSubmodule_ne_bot_of_isIrreducible
    (σ : Subrepresentation (leftRegular K G))
    (hσ : IsIrreducibleLeftRegularSummand σ) :
    σ.toSubmodule ≠ ⊥ := by
  -- Irreducibility rules out the zero representation, so the carrier submodule cannot vanish.
  intro hbot
  letI : AddCommGroup σ.toSubmodule := inferInstance
  letI : Representation.IsIrreducible (σ.toRepresentation) := by
    simpa [IsIrreducibleLeftRegularSummand] using hσ
  letI : Subsingleton σ.toSubmodule := by
    rw [hbot]
    infer_instance
  have hbot_top :
      (⊥ : Subrepresentation σ.toRepresentation).toSubmodule =
        (⊤ : Subrepresentation σ.toRepresentation).toSubmodule := by
    -- In a subsingleton carrier, membership in `⊥` and `⊤` is identical.
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact bot_ne_top <| Subrepresentation.toSubmodule_injective hbot_top

omit [IsAlgClosed K] [NeZero (Nat.card G : K)] in
/-- Helper for Theorem 3-3.2-1: an internal irreducible decomposition of the left regular
representation has finite index type. -/
private theorem finite_index_of_internal_irreducible_leftRegular_decomposition
    (σ : ι → Subrepresentation (leftRegular K G))
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, IsIrreducibleLeftRegularSummand (σ i)) :
    Finite ι := by
  classical
  have hfinite_support : Set.Finite { i | (σ i).toSubmodule ≠ ⊥ } :=
    Submodule.finite_ne_bot_of_iSupIndep hinternal.submodule_iSupIndep
  have huniv : { i | (σ i).toSubmodule ≠ ⊥ } = Set.univ := by
    -- Every index contributes a nonzero irreducible summand.
    ext i
    simp [summand_toSubmodule_ne_bot_of_isIrreducible (σ i) (hσ i)]
  exact Finite.of_finite_univ <| by
    convert hfinite_support using 1
    simp [huniv]

omit [Finite G] [IsAlgClosed K] [NeZero (Nat.card G : K)] in
/-- Helper for Theorem 3-3.2-1: intertwining maps from the left regular representation to an
irreducible representation have dimension equal to that representation's degree. -/
private theorem leftRegular_intertwining_finrank_eq_degree
    {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K G W) :
    Module.finrank K ((leftRegular K G).IntertwiningMap τ) = Module.finrank K W := by
  -- The universal property of `leftRegular` identifies intertwiners with vectors.
  simpa using (leftRegularMapEquiv τ).finrank_eq

omit [NeZero (Nat.card G : K)] in
/-- Helper for Theorem 3-3.2-1: in an internal irreducible decomposition of the left regular
representation, the multiplicity of a fixed irreducible summand equals its degree. -/
theorem leftRegular_irreducible_multiplicity_eq_finrank
    {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (σ : ι → Subrepresentation (leftRegular K G))
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, IsIrreducibleLeftRegularSummand (σ i))
    (τ : Representation K G W)
    (hτ : τ.IsIrreducible) :
    Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv τ) } = Module.finrank K W := by
  classical
  letI : τ.IsIrreducible := hτ
  letI : Finite ι :=
    finite_index_of_internal_irreducible_leftRegular_decomposition σ hinternal hσ
  let _ : ∀ i, AddCommGroup (σ i).toSubmodule := fun i ↦ inferInstance
  have hσ' : ∀ i, (σ i).toRepresentation.IsIrreducible := by
    intro i
    simpa [IsIrreducibleLeftRegularSummand] using hσ i
  -- First compute the multiplicity by the Chapter 2 owner theorem, then convert intertwiners to
  -- vectors using the left-regular universal property.
  calc
    Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv τ) } =
        Module.finrank K ((leftRegular K G).IntertwiningMap τ) := by
          exact
            card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
              (leftRegular K G) σ hinternal hσ' τ hτ
    _ = Module.finrank K W := leftRegular_intertwining_finrank_eq_degree τ

omit [Finite G] [IsAlgClosed K] [NeZero (Nat.card G : K)] in
/-- Helper for Theorem 3-3.2-1: an `FDRep` isomorphism yields an equivalence of the underlying
representations. -/
private theorem fdrep_iso_nonempty_to_rep_equiv_nonempty
    {A B : FDRep K G} (h : Nonempty (A ≅ B)) :
    Nonempty (Representation.Equiv A.ρ B.ρ) := by
  -- Forget the owner-level isomorphism and read it as an equivalence of representations.
  rcases h with ⟨e⟩
  exact ⟨Representation.equivOfIso ((forget₂ (FDRep K G) (Rep K G)).mapIso e)⟩

/-- Helper for Theorem 3-3.2-1: a finite complete pairwise nonisomorphic irreducible family has
square-degree sum equal to the group order. -/
theorem sum_sq_degree_eq_card_of_complete_irreducible_family
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_pairwise : PairwiseNonisomorphic π) :
    ∑ i : ι, Module.finrank K (π i) ^ 2 = Nat.card G := by
  classical
  obtain ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type v) (_ : Fintype κ) (σ : κ → Subrepresentation (leftRegular K G)),
        iSupIndep (fun j ↦ (σ j).toSubmodule) ∧
          (⨆ j, (σ j).toSubmodule) = ⊤ ∧
          ∀ j, IsIrreducibleLeftRegularSummand (σ j) := by
    obtain ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr_raw⟩ :=
      exists_isInternal_irreducible_subrepresentations (leftRegular K G)
    refine ⟨κ, hκ, σ, hσ_indep, hσ_top, ?_⟩
    intro j
    let _ : AddCommGroup (σ j).toSubmodule := inferInstance
    simpa [IsIrreducibleLeftRegularSummand] using hσ_irr_raw j
  letI : Fintype κ := hκ
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let S : ι → Finset κ :=
    fun i ↦ Finset.univ.filter fun j ↦
      Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ))
  let covered : Finset κ := Finset.univ.biUnion S
  let dimσ : κ → Nat := fun j ↦ Module.finrank K (σ j).toSubmodule
  have hS_disjoint : Pairwise fun i i' ↦ Disjoint (S i) (S i') := by
    -- Distinct irreducible classes cannot share a summand of the regular representation.
    intro i i' hii
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨e'⟩
    have hiso : Nonempty (π i ≅ π i') := by
      refine ⟨?_⟩
      simpa using (e.symm.trans e').toFDRepIso
    exact hπ_pairwise hii hiso
  have hS_card (i : ι) : (S i).card = Module.finrank K (π i) := by
    -- Corollary 2-2.4-2 computes the multiplicity of `π i` in the regular representation.
    have hπi_simple : Simple (π i) := hπ_complete.isSimple i
    letI : Simple (π i) := hπi_simple
    have hπi_irreducible : Representation.IsIrreducible ((π i).ρ) :=
      FDRep.isIrreducible_of_simple (π i)
    letI : Representation.IsIrreducible ((π i).ρ) := hπi_irreducible
    have hcard :
        Fintype.card
            { j // Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ)) } =
          (S i).card := by
      rw [show S i = Finset.univ.filter
          (fun j ↦ Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ))) by rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter
          (fun j ↦ Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ))))]
      · intro j
        simp
    have hmult :
        Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) } =
          Module.finrank K (π i) := by
      exact
        (leftRegular_irreducible_multiplicity_eq_finrank
          σ hinternal hσ_irr (π i).ρ hπi_irreducible :
            Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) } =
              Module.finrank K (π i))
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using hmult
  have hS_sum (i : ι) : Finset.sum (S i) dimσ = Module.finrank K (π i) ^ 2 := by
    -- Inside one isomorphism class, every summand has the same degree as `π i`.
    calc
      Finset.sum (S i) dimσ = Finset.sum (S i) (fun _j ↦ Module.finrank K (π i)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        exact e.toLinearEquiv.finrank_eq
      _ = (S i).card * Module.finrank K (π i) := by simp
      _ = Module.finrank K (π i) ^ 2 := by
            rw [hS_card, pow_two]
  have hcovered_raw : Finset.sum covered dimσ = ∑ i : ι, Finset.sum (S i) dimσ := by
    rw [show covered = Finset.univ.biUnion S from rfl]
    exact Finset.sum_biUnion fun i _ i' _ hii ↦ hS_disjoint hii
  have hcovered_univ : covered = Finset.univ := by
    -- Completeness ensures every irreducible summand appears in the family.
    apply Finset.ext
    intro j
    constructor
    · intro hj
      simp
    · intro hj
      let _ : AddCommGroup (σ j).toSubmodule := inferInstance
      have hτ_irreducible : Representation.IsIrreducible (σ j).toRepresentation := by
        simpa [IsIrreducibleLeftRegularSummand] using hσ_irr j
      letI : Representation.IsIrreducible (σ j).toRepresentation := hτ_irreducible
      have hi :
          ∃ i, Nonempty (FDRep.of (σ j).toRepresentation ≅ π i) := by
        exact
          IsCompleteIrreducibleFamily.exists_iso_of_representation
            π hπ_complete (σ j).toRepresentation hτ_irreducible
      rcases hi with ⟨i, hi⟩
      refine Finset.mem_biUnion.mpr ⟨i, by simp, ?_⟩
      exact Finset.mem_filter.mpr ⟨by simp, fdrep_iso_nonempty_to_rep_equiv_nonempty hi⟩
  have hcovered_sum : Finset.sum covered dimσ = ∑ i : ι, Module.finrank K (π i) ^ 2 := by
    calc
      Finset.sum covered dimσ = ∑ i : ι, Finset.sum (S i) dimσ := hcovered_raw
      _ = ∑ i : ι, Module.finrank K (π i) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ ↦ hS_sum i
  have htotal_eq_card : ∑ j : κ, dimσ j = Nat.card G := by
    -- Summing the dimensions of an internal decomposition recovers the regular representation.
    letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
    letI : ∀ j : κ, Module.Free K (σ j).toSubmodule := fun j ↦
      Module.Free.of_divisionRing K (σ j).toSubmodule
    let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
    calc
      ∑ j : κ, dimσ j = Module.finrank K (G →₀ K) := by
        symm
        calc
          Module.finrank K (G →₀ K)
              = Module.finrank K (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
                  exact e.finrank_eq.symm
          _ = ∑ j : κ, dimσ j := by
                simpa [dimσ] using
                  (Module.finrank_directSum fun j ↦ (σ j).toSubmodule)
      _ = Nat.card G := by
            let _ : Fintype G := Fintype.ofFinite G
            rw [Nat.card_eq_fintype_card]
            exact Module.finrank_finsupp_self K
  calc
    ∑ i : ι, Module.finrank K (π i) ^ 2 = Finset.sum covered dimσ := by
      symm
      calc
        Finset.sum covered dimσ = ∑ i : ι, Finset.sum (S i) dimσ := hcovered_raw
        _ = ∑ i : ι, Module.finrank K (π i) ^ 2 := by
              refine Finset.sum_congr rfl fun i _ ↦ hS_sum i
    _ = ∑ j : κ, dimσ j := by
          simpa [hcovered_univ]
    _ = Nat.card G := htotal_eq_card

/-- Helper for Theorem 3-3.2-1: in the finite-index setting, the square-degree criterion implies
completeness of a pairwise nonisomorphic simple family. -/
theorem isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card
    (hπ_simple : ∀ i, Simple (π i))
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_sum : ∑ i : ι, Module.finrank K (π i) ^ 2 = Nat.card G) :
    IsCompleteIrreducibleFamily π := by
  classical
  obtain ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type v) (_ : Fintype κ) (σ : κ → Subrepresentation (leftRegular K G)),
        iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
          (⨆ i, (σ i).toSubmodule) = ⊤ ∧
          ∀ i, IsIrreducibleLeftRegularSummand (σ i) := by
    obtain ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr_raw⟩ :=
      exists_isInternal_irreducible_subrepresentations (leftRegular K G)
    refine ⟨κ, hκ, σ, hσ_indep, hσ_top, ?_⟩
    intro i
    let _ : AddCommGroup (σ i).toSubmodule := inferInstance
    simpa [IsIrreducibleLeftRegularSummand] using hσ_irr_raw i
  letI : Fintype κ := hκ
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let S : ι → Finset κ :=
    fun i ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π i).ρ)
  let covered : Finset κ := Finset.univ.biUnion S
  let dimσ : κ → Nat := fun j ↦ Module.finrank K (σ j).toSubmodule
  have hS_disjoint : Pairwise fun i i' ↦ Disjoint (S i) (S i') := by
    -- Distinct indices cannot represent the same irreducible summand class.
    intro i i' hii
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨e'⟩
    exact hπ_pairwise hii <| ⟨(e.symm.trans e').toFDRepIso⟩
  have hmult (i : ι) :
      Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) } =
        Module.finrank K (π i) := by
    have hπ_irreducible : Representation.IsIrreducible ((π i).ρ) := by
      letI : Simple (π i) := hπ_simple i
      exact FDRep.isIrreducible_of_simple (π i)
    exact
      (leftRegular_irreducible_multiplicity_eq_finrank
        σ hinternal hσ_irr (π i).ρ hπ_irreducible :
          Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) } =
            Module.finrank K (π i))
  have hS_card (i : ι) : (S i).card = Module.finrank K (π i) := by
    have hcard :
        Fintype.card { j // Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) } = (S i).card := by
      rw [show S i =
            Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) by rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π i).ρ))]
      · intro j
        simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using hmult i
  have hS_sum (i : ι) : Finset.sum (S i) dimσ = Module.finrank K (π i) ^ 2 := by
    -- Each summand in one class contributes the same degree.
    calc
      Finset.sum (S i) dimσ = Finset.sum (S i) (fun _j ↦ Module.finrank K (π i)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        exact e.toLinearEquiv.finrank_eq
      _ = (S i).card * Module.finrank K (π i) := by simp
      _ = Module.finrank K (π i) ^ 2 := by
            rw [hS_card, pow_two]
  have hcovered_raw : Finset.sum covered dimσ = ∑ i : ι, Finset.sum (S i) dimσ := by
    rw [show covered = Finset.univ.biUnion S from rfl]
    exact Finset.sum_biUnion fun i _ i' _ hii ↦ hS_disjoint hii
  have hcovered_sum : Finset.sum covered dimσ = ∑ i : ι, Module.finrank K (π i) ^ 2 := by
    calc
      Finset.sum covered dimσ = ∑ i : ι, Finset.sum (S i) dimσ := hcovered_raw
      _ = ∑ i : ι, Module.finrank K (π i) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ ↦ hS_sum i
  have hcovered_eq_card : Finset.sum covered dimσ = Nat.card G := by
    calc
      Finset.sum covered dimσ = ∑ i : ι, Module.finrank K (π i) ^ 2 := hcovered_sum
      _ = Nat.card G := hπ_sum
  have htotal_eq_card : ∑ j : κ, dimσ j = Nat.card G := by
    -- The full internal decomposition still has total degree `|G|`.
    letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
    letI : ∀ j : κ, Module.Free K (σ j).toSubmodule := fun j ↦
      Module.Free.of_divisionRing K (σ j).toSubmodule
    let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
    calc
      ∑ j : κ, dimσ j = Module.finrank K (G →₀ K) := by
        symm
        calc
          Module.finrank K (G →₀ K)
              = Module.finrank K (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
                  exact e.finrank_eq.symm
          _ = ∑ j : κ, dimσ j := by
                simpa [dimσ] using
                  (Module.finrank_directSum fun j ↦ (σ j).toSubmodule)
      _ = Nat.card G := by
            let _ : Fintype G := Fintype.ofFinite G
            have hfinrankFinsupp : Module.finrank K (G →₀ K) = Fintype.card G := by
              exact
                (show Module.finrank K (G →₀ K) = Fintype.card G from
                  Module.finrank_finsupp_self K)
            rw [Nat.card_eq_fintype_card]
            exact hfinrankFinsupp
  refine
    { isSimple := hπ_simple
      exists_iso := ?_ }
  intro τ hτ
  letI : Simple τ := hτ
  letI : Nontrivial τ := by
    by_contra hτ
    letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp hτ
    have hzero : (𝟙 τ : τ ⟶ τ) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    exact CategoryTheory.id_nonzero τ hzero
  let τρ := τ.ρ
  have hτρ_irreducible : Representation.IsIrreducible τρ := by
    exact FDRep.isIrreducible_of_simple τ
  letI : Representation.IsIrreducible τρ := hτρ_irreducible
  have hτ_pos : 0 < Module.finrank K τ := Module.finrank_pos
  have hτ_mult :
      Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } = Module.finrank K τ := by
    exact
      (leftRegular_irreducible_multiplicity_eq_finrank
        σ hinternal hσ_irr τρ hτρ_irreducible :
          Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } =
            Module.finrank K τ)
  have hτ_count_pos : 0 < Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } := by
    rw [hτ_mult]
    exact hτ_pos
  obtain ⟨⟨j, hjτ⟩⟩ := (Nat.card_pos_iff.mp hτ_count_pos).1
  have hj_mem : j ∈ covered := by
    by_contra hj_not_mem
    have hτ_term : dimσ j = Module.finrank K τ := by
      rcases hjτ with ⟨e⟩
      exact e.toLinearEquiv.finrank_eq
    have hcomp_pos : 0 < Finset.sum (Finset.univ \ covered) dimσ := by
      have hj_mem_compl : j ∈ Finset.univ \ covered := by
        simp [hj_not_mem]
      have hsingle : dimσ j ≤ Finset.sum (Finset.univ \ covered) dimσ := by
        simpa using
          (Finset.single_le_sum (fun x hx ↦ Nat.zero_le (dimσ x)) hj_mem_compl :
            dimσ j ≤ Finset.sum (Finset.univ \ covered) dimσ)
      exact lt_of_lt_of_le (by simpa [hτ_term] using hτ_pos) hsingle
    have hlt : Finset.sum covered dimσ < ∑ j : κ, dimσ j := by
      rw [← Finset.sum_add_sum_compl covered dimσ]
      exact Nat.lt_add_of_pos_right hcomp_pos
    have hcontra : Nat.card G < Nat.card G := by
      calc
        Nat.card G = Finset.sum covered dimσ := hcovered_eq_card.symm
        _ < ∑ j : κ, dimσ j := hlt
        _ = Nat.card G := htotal_eq_card
    exact Nat.lt_irrefl _ hcontra
  rcases Finset.mem_biUnion.mp hj_mem with ⟨i, _, hij⟩
  rcases (Finset.mem_filter.mp hij).2 with ⟨e⟩
  rcases hjτ with ⟨eτ⟩
  exact ⟨i, ⟨(eτ.symm.trans e).toFDRepIso⟩⟩

/-- A finite pairwise nonisomorphic simple family is complete exactly when the sum of the squares
of its degrees is the group order. This is the canonical owner theorem for the square-degree
criterion used in Remark 2-2.4-4. -/
theorem complete_irreducible_family_iff_sum_sq_degree_eq_card
    (hπ_simple : ∀ i, Simple (π i))
    (hπ_pairwise : PairwiseNonisomorphic π) :
    IsCompleteIrreducibleFamily π ↔
      ∑ i : ι, Module.finrank K (π i) ^ 2 = Nat.card G := by
  constructor
  · intro hπ_complete
    exact sum_sq_degree_eq_card_of_complete_irreducible_family π hπ_complete hπ_pairwise
  · intro hπ_sum
    exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card π hπ_simple hπ_pairwise hπ_sum

end

end

end Representation

namespace FDRep

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G₁ : Type u} [Group G₁] [Finite G₁]
variable {G₂ : Type u} [Group G₂] [Finite G₂]
variable [NeZero (Nat.card G₁ : k)] [NeZero (Nat.card G₂ : k)]

open Representation
open Representation.FDRep
open scoped Representation.ExternalTensor

noncomputable local instance fintypeG₁ : Fintype G₁ := Fintype.ofFinite G₁
noncomputable local instance fintypeG₂ : Fintype G₂ := Fintype.ofFinite G₂

local instance neZero_card_prod : NeZero (Nat.card (G₁ × G₂) : k) := by
  refine ⟨?_⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Nat.cast_mul]
  exact mul_ne_zero
    (by simpa [Nat.card_eq_fintype_card] using (NeZero.ne (Nat.card G₁ : k)))
    (by simpa [Nat.card_eq_fintype_card] using (NeZero.ne (Nat.card G₂ : k)))

noncomputable local instance invertibleCardG₁ : Invertible (Fintype.card G₁ : k) := by
  exact invertibleOfNonzero <| by
    simpa [Nat.card_eq_fintype_card] using (NeZero.ne (Nat.card G₁ : k))

noncomputable local instance invertibleCardG₂ : Invertible (Fintype.card G₂ : k) := by
  exact invertibleOfNonzero <| by
    simpa [Nat.card_eq_fintype_card] using (NeZero.ne (Nat.card G₂ : k))

noncomputable local instance invertibleCardProd : Invertible (Fintype.card (G₁ × G₂) : k) := by
  exact invertibleOfNonzero <| by
    simpa [Nat.card_eq_fintype_card] using (NeZero.ne (Nat.card (G₁ × G₂) : k))

section

omit [IsAlgClosed k]

/-- Helper for Theorem 3-3.2-1: the normalized character pairing of two external tensor products
over `G₁ × G₂` factors into the product of the normalized pairings on the two factors. -/
lemma externalTensor_scalarProduct_eq_mul
    (A₁ B₁ : FDRep k G₁) (A₂ B₂ : FDRep k G₂) :
    ⅟ (Fintype.card (G₁ × G₂) : k) •
      ∑ g : G₁ × G₂,
        (FDRep.of (A₁.ρ ⊠ A₂.ρ)).character g *
          (FDRep.of (B₁.ρ ⊠ B₂.ρ)).character g⁻¹
      =
        (⅟ (Fintype.card G₁ : k) • ∑ g₁ : G₁, A₁.character g₁ * B₁.character g₁⁻¹) *
          (⅟ (Fintype.card G₂ : k) • ∑ g₂ : G₂, A₂.character g₂ * B₂.character g₂⁻¹) := by
  -- Expand the product-group sum into iterated sums and separate the two tensor factors.
  have hsum :
      (∑ g : G₁ × G₂,
        (FDRep.of (A₁.ρ ⊠ A₂.ρ)).character g *
          (FDRep.of (B₁.ρ ⊠ B₂.ρ)).character g⁻¹)
        =
        (∑ g₁ : G₁, A₁.character g₁ * B₁.character g₁⁻¹) *
          (∑ g₂ : G₂, A₂.character g₂ * B₂.character g₂⁻¹) := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ g₁ : G₁, ∑ g₂ : G₂,
          (FDRep.of (A₁.ρ ⊠ A₂.ρ)).character (g₁, g₂) *
            (FDRep.of (B₁.ρ ⊠ B₂.ρ)).character (g₁, g₂)⁻¹
          =
            ∑ g₁ : G₁, ∑ g₂ : G₂,
              (A₁.character g₁ * B₁.character g₁⁻¹) *
                (A₂.character g₂ * B₂.character g₂⁻¹) := by
              refine Finset.sum_congr rfl fun g₁ _ ↦ ?_
              refine Finset.sum_congr rfl fun g₂ _ ↦ ?_
              have hA :
                  (FDRep.of (A₁.ρ ⊠ A₂.ρ)).character (g₁, g₂) =
                    A₁.character g₁ * A₂.character g₂ := by
                simpa [FDRep.character, Representation.character] using
                  congrFun
                    (Representation.char_tensor
                      (A₁.ρ.comp (fst G₁ G₂))
                      (A₂.ρ.comp (snd G₁ G₂)))
                    (g₁, g₂)
              have hB :
                  (FDRep.of (B₁.ρ ⊠ B₂.ρ)).character ((g₁, g₂)⁻¹) =
                    B₁.character g₁⁻¹ * B₂.character g₂⁻¹ := by
                simpa [FDRep.character, Representation.character, Prod.fst_inv, Prod.snd_inv] using
                  congrFun
                    (Representation.char_tensor
                      (B₁.ρ.comp (fst G₁ G₂))
                      (B₂.ρ.comp (snd G₁ G₂)))
                    ((g₁, g₂)⁻¹)
              rw [hA, hB]
              ring
      _ =
          ∑ g₁ : G₁,
            (A₁.character g₁ * B₁.character g₁⁻¹) *
              ∑ g₂ : G₂, A₂.character g₂ * B₂.character g₂⁻¹ := by
            refine Finset.sum_congr rfl fun g₁ _ ↦ ?_
            rw [Finset.mul_sum]
      _ =
          (∑ g₁ : G₁, A₁.character g₁ * B₁.character g₁⁻¹) *
            (∑ g₂ : G₂, A₂.character g₂ * B₂.character g₂⁻¹) := by
            rw [Finset.sum_mul]
  -- Then rewrite the normalizing factor `|G₁ × G₂|⁻¹` as the product of the two factors.
  rw [hsum, smul_eq_mul, smul_eq_mul, smul_eq_mul, invOf_eq_inv, invOf_eq_inv, invOf_eq_inv,
    Fintype.card_prod, Nat.cast_mul]
  ring

end

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: if the normalized character pairing on the first factor vanishes,
then the normalized pairing of the external tensor products also vanishes. -/
private lemma externalTensor_scalarProduct_eq_zero_of_left
    (A₁ B₁ : FDRep k G₁) (A₂ B₂ : FDRep k G₂)
    (hleft :
      ⅟(Fintype.card G₁ : k) •
        ∑ g₁ : G₁, A₁.character g₁ * B₁.character g₁⁻¹
        = (0 : k)) :
    ⅟(Fintype.card (G₁ × G₂) : k) •
      ∑ g : G₁ × G₂,
        (FDRep.of (A₁.ρ ⊠ A₂.ρ)).character g *
          (FDRep.of (B₁.ρ ⊠ B₂.ρ)).character g⁻¹
      = (0 : k) := by
  -- Factor the product-group pairing and use the vanishing first factor.
  rw [externalTensor_scalarProduct_eq_mul, hleft, zero_mul]

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: if the normalized character pairing on the second factor vanishes,
then the normalized pairing of the external tensor products also vanishes. -/
private lemma externalTensor_scalarProduct_eq_zero_of_right
    (A₁ B₁ : FDRep k G₁) (A₂ B₂ : FDRep k G₂)
    (hright :
      ⅟(Fintype.card G₂ : k) •
        ∑ g₂ : G₂, A₂.character g₂ * B₂.character g₂⁻¹
        = (0 : k)) :
    ⅟(Fintype.card (G₁ × G₂) : k) •
      ∑ g : G₁ × G₂,
        (FDRep.of (A₁.ρ ⊠ A₂.ρ)).character g *
          (FDRep.of (B₁.ρ ⊠ B₂.ρ)).character g⁻¹
      = (0 : k) := by
  -- Factor the product-group pairing and use the vanishing second factor.
  rw [externalTensor_scalarProduct_eq_mul, hright, mul_zero]

section

omit [IsAlgClosed k] [Finite G₁] [Finite G₂] [NeZero (Nat.card G₁ : k)]
  [NeZero (Nat.card G₂ : k)]

/-- Helper for Theorem 3-3.2-1: the degree of an external tensor product is the product of the
degrees of the two factors. -/
lemma externalTensor_finrank (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) :
    Module.finrank k (FDRep.of (W₁.ρ ⊠ W₂.ρ)) = Module.finrank k W₁ * Module.finrank k W₂ := by
  -- The external tensor product is the usual tensor product on the underlying vector spaces.
  change Module.finrank k (W₁ ⊗[k] W₂) = Module.finrank k W₁ * Module.finrank k W₂
  exact Module.finrank_tensorProduct

end

/-- Helper for Theorem 3-3.2-1: every finite group under the Maschke hypotheses admits a complete
pairwise nonisomorphic family of simple finite-dimensional representations. -/
theorem exists_complete_pairwise_nonisomorphic_simple_family
    {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)] :
    ∃ (ι : Type u) (_ : Fintype ι) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (leftRegular k G)
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j l} hij hjl ↦ by
            rcases hij with ⟨eij⟩
            rcases hjl with ⟨ejl⟩
            exact ⟨eij.trans ejl⟩⟩ }
  let ι : Type u := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : ι)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep k G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot label isomorphic representatives.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses :
        (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep k G) (Rep k G)).mapIso e)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_simple (q : ι) : Simple (π q) := by
    -- Each quotient representative remains irreducible, hence simple in `FDRep`.
    letI : Representation.IsIrreducible ((π q).ρ) := by
      simpa [π] using hσ_irr (Quotient.out q)
    exact simple_of_isIrreducible (π q)
  let S : ι → Finset κ :=
    fun q ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ)
  let dimσ : κ → Nat := fun j ↦ Module.finrank k (σ j).toSubmodule
  have hS_disjoint : Pairwise fun q q' ↦ Disjoint (S q) (S q') := by
    -- A summand cannot lie in two different isomorphism classes.
    intro q q' hqq'
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨eqj⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨eqj'⟩
    exact hπ_pairwise hqq' <| ⟨(eqj.symm.trans eqj').toFDRepIso⟩
  have hS_card (q : ι) : (S q).card = Module.finrank k (π q) := by
    -- Multiplicity of one isomorphism class in the regular representation equals its degree.
    have hmult :
        Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } =
          Module.finrank k (π q) := by
      have hπq_irreducible : Representation.IsIrreducible ((π q).ρ) :=
        isIrreducible_of_simple (π q)
      exact
        (leftRegular_irreducible_multiplicity_eq_finrank
          σ hinternal hσ_irr (π q).ρ hπq_irreducible :
            Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } =
              Module.finrank k (π q))
    have hcard :
        Fintype.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } = (S q).card := by
      rw [show S q = Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) by
        rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ))]
      intro j
      simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using hmult
  have hS_sum (q : ι) : Finset.sum (S q) dimσ = Module.finrank k (π q) ^ 2 := by
    -- Every summand in the same isomorphism class has the same degree.
    calc
      Finset.sum (S q) dimσ = Finset.sum (S q) (fun _j ↦ Module.finrank k (π q)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        exact e.toLinearEquiv.finrank_eq
      _ = (S q).card * Module.finrank k (π q) := by
            simp
      _ = Module.finrank k (π q) ^ 2 := by
            rw [hS_card, pow_two]
  have hcover :
      Finset.univ.biUnion S = (Finset.univ : Finset κ) := by
    -- Each irreducible summand belongs to the class determined by its own quotient image.
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      have hj_mem : j ∈ S (⟦j⟧ : ι) := by
        refine Finset.mem_filter.mpr ?_
        constructor
        · simp
        · rcases Quotient.exact (Quotient.out_eq (⟦j⟧ : ι)) with ⟨e⟩
          exact ⟨e.symm⟩
      exact Finset.mem_biUnion.mpr ⟨(⟦j⟧ : ι), Finset.mem_univ _, hj_mem⟩
  have htotal_eq_card : Finset.sum (Finset.univ : Finset κ) dimσ = Nat.card G := by
    -- Summing the dimensions of the internal decomposition recovers the dimension of `leftRegular`.
    letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
    letI : ∀ j : κ, Module.Free k (σ j).toSubmodule := fun j ↦
      Module.Free.of_divisionRing k (σ j).toSubmodule
    let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
    calc
      Finset.sum (Finset.univ : Finset κ) dimσ = Module.finrank k (G →₀ k) := by
        symm
        calc
          Module.finrank k (G →₀ k) =
              Module.finrank k (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
                exact e.finrank_eq.symm
          _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
                simpa [dimσ] using
                  (Module.finrank_directSum :
                    Module.finrank k (DirectSum κ fun j ↦ (σ j).toSubmodule) =
                      Finset.sum (Finset.univ : Finset κ)
                        (fun j ↦ Module.finrank k ((σ j).toSubmodule)))
      _ = Nat.card G := by
            rw [Nat.card_eq_fintype_card]
            exact Module.finrank_finsupp_self k
  have hπ_sum : ∑ q : ι, Module.finrank k (π q) ^ 2 = Nat.card G := by
    -- The quotient classes partition the summands, so the square-degree sum is `|G|`.
    calc
      ∑ q : ι, Module.finrank k (π q) ^ 2 = ∑ q : ι, Finset.sum (S q) dimσ := by
        refine Finset.sum_congr rfl fun q _ ↦ (hS_sum q).symm
      _ = Finset.sum (Finset.univ.biUnion S) dimσ := by
            symm
            exact Finset.sum_biUnion fun q _ q' _ hqq' ↦ hS_disjoint hqq'
      _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
            rw [hcover]
      _ = Nat.card G := htotal_eq_card
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    -- The Chapter 2 criterion promotes the square-degree identity to completeness.
    exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card π hπ_simple hπ_pairwise hπ_sum
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Theorem 3-3.2-1: the product family of two complete irreducible families has
total square degree equal to the order of the product group. -/
lemma externalTensor_sum_sq_degree_eq_card
    {ι₁ : Type u} {ι₂ : Type u} [Finite ι₁] [Finite ι₂]
    (π₁ : ι₁ → FDRep k G₁) (π₂ : ι₂ → FDRep k G₂)
    (hπ₁_pairwise : PairwiseNonisomorphic π₁)
    (hπ₂_pairwise : PairwiseNonisomorphic π₂)
    (hπ₁_complete : IsCompleteIrreducibleFamily π₁)
    (hπ₂_complete : IsCompleteIrreducibleFamily π₂) :
    ∑ p : ι₁ × ι₂, Module.finrank k (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ)) ^ 2 =
      Nat.card (G₁ × G₂) := by
  classical
  let _ : Fintype ι₁ := Fintype.ofFinite ι₁
  let _ : Fintype ι₂ := Fintype.ofFinite ι₂
  -- Rewrite each degree through the tensor-product finrank formula and separate the double sum.
  rw [Fintype.sum_prod_type]
  calc
    ∑ i : ι₁, ∑ j : ι₂,
        Module.finrank k (FDRep.of ((π₁ i).ρ ⊠ (π₂ j).ρ)) ^ 2
      =
        ∑ i : ι₁, ∑ j : ι₂,
          (Module.finrank k (π₁ i) ^ 2) * (Module.finrank k (π₂ j) ^ 2) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [externalTensor_finrank, mul_pow]
    _ =
        ∑ i : ι₁,
          (Module.finrank k (π₁ i) ^ 2) * ∑ j : ι₂, Module.finrank k (π₂ j) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [Finset.mul_sum]
    _ =
        (∑ i : ι₁, Module.finrank k (π₁ i) ^ 2) *
          ∑ j : ι₂, Module.finrank k (π₂ j) ^ 2 := by
            rw [Finset.sum_mul]
    _ = Nat.card G₁ * Nat.card G₂ := by
          have hsum1 :
              ∑ i : ι₁, Module.finrank k (π₁ i) ^ 2 = Nat.card G₁ := by
            simpa using
              (sum_sq_degree_eq_card_of_complete_irreducible_family π₁ hπ₁_complete
                hπ₁_pairwise)
          have hsum2 :
              ∑ j : ι₂, Module.finrank k (π₂ j) ^ 2 = Nat.card G₂ := by
            simpa using
              (sum_sq_degree_eq_card_of_complete_irreducible_family π₂ hπ₂_complete
                hπ₂_pairwise)
          rw [hsum1, hsum2]
    _ = Nat.card (G₁ × G₂) := by
          simp [Nat.card_eq_fintype_card, Fintype.card_prod]

-- Proof sketch: identify the character of the product-group tensor representation with the product
-- of the characters of the two factors, then apply the character-norm criterion for irreducibility
-- together with multiplicativity of the normalized character inner product.
section

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: a simple finite-dimensional representation contains a nonzero
vector, because the identity morphism is nonzero. -/
private lemma exists_ne_zero_vec
    {G : Type u} [Group G]
    (W : FDRep k G) [Simple W] :
    ∃ v : W, v ≠ 0 := by
  -- Otherwise every vector would vanish, forcing the identity morphism to be zero.
  by_contra h
  apply CategoryTheory.id_nonzero W
  ext v
  by_contra hv
  exact h ⟨v, hv⟩

/-- Helper for Theorem 3-3.2-1: fix a nonzero vector in a simple representation for later scalar
extraction on its endomorphism ring. -/
private noncomputable def chosenVector
    {G : Type u} [Group G]
    (W : FDRep k G) [Simple W] : W :=
  Classical.choose (exists_ne_zero_vec W)

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: the chosen vector in a simple representation is nonzero. -/
private lemma chosenVector_ne_zero
    {G : Type u} [Group G]
    (W : FDRep k G) [Simple W] :
    chosenVector W ≠ 0 :=
  Classical.choose_spec (exists_ne_zero_vec W)

/-- Helper for Theorem 3-3.2-1: choose a dual vector that evaluates to `1` on the chosen nonzero
vector. -/
private noncomputable def chosenDual
    {G : Type u} [Group G]
    (W : FDRep k G) [Simple W] : Module.Dual k W :=
  Classical.choose (Module.Projective.exists_dual_eq_one k (chosenVector_ne_zero W))

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: the chosen dual vector evaluates to `1` on the chosen vector. -/
private lemma chosenDual_apply
    {G : Type u} [Group G]
    (W : FDRep k G) [Simple W] :
    chosenDual W (chosenVector W) = 1 :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one k (chosenVector_ne_zero W))

/-- Helper for Theorem 3-3.2-1: extract the scalar of an endomorphism of a simple object by
evaluating it on a fixed nonzero vector and the chosen dual vector. -/
private noncomputable def scalarOfSimpleEnd
    {G : Type u} [Group G]
    (W : FDRep k G) [Simple W] :
    (W ⟶ W) →ₗ[k] k where
  toFun f := chosenDual W (f (chosenVector W))
  map_add' f g := by
    -- The chosen dual vector is linear, so it reads off coefficients additively.
    change chosenDual W (f (chosenVector W) + g (chosenVector W)) = _
    exact map_add (chosenDual W) _ _
  map_smul' a f := by
    -- The same evaluation is compatible with scalar multiplication.
    change chosenDual W (a • f (chosenVector W)) = _
    simp [smul_eq_mul]

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: the scalar extracted from the identity endomorphism is `1`. -/
private lemma scalarOfSimpleEnd_id
    {G : Type u} [Group G]
    (W : FDRep k G) [Simple W] :
    scalarOfSimpleEnd W (𝟙 W) = 1 := by
  -- The chosen dual vector was normalized exactly for this identity computation.
  simp [scalarOfSimpleEnd, chosenDual_apply]

/-- Helper for Theorem 3-3.2-1: every endomorphism of a simple object is the extracted scalar
multiple of the identity. -/
private lemma scalarOfSimpleEnd_smul_id
    {G : Type u} [Group G]
    (W : FDRep k G) [Simple W] (f : W ⟶ W) :
    scalarOfSimpleEnd W f • 𝟙 W = f := by
  -- Use the rank-one endomorphism space to write `f = c • 𝟙`, then identify `c` by evaluation.
  have hfinrank : Module.finrank k (W ⟶ W) = 1 := by
    let hIso : Nonempty (W ≅ W) := ⟨Iso.refl W⟩
    simpa [hIso] using (FDRep.finrank_hom_simple_simple W W)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 W) (CategoryTheory.id_nonzero W)).mp
    hfinrank f
  have hscalar : scalarOfSimpleEnd W f = c := by
    rw [← hc]
    simp [scalarOfSimpleEnd_id]
  simpa [hscalar] using hc

/-- Helper for Theorem 3-3.2-1: move from `FDRep` endomorphisms of the external tensor product to
intertwining maps of the underlying product-group representation. -/
private noncomputable def externalTensor_end_intertwining_equiv
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) :
    ((FDRep.of (W₁.ρ ⊠ W₂.ρ)) ⟶ (FDRep.of (W₁.ρ ⊠ W₂.ρ))) ≃ₗ[k]
      Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ) := by
  let X : Rep k (G₁ × G₂) :=
    (forget₂ (FDRep k (G₁ × G₂)) (Rep k (G₁ × G₂))).obj (FDRep.of (W₁.ρ ⊠ W₂.ρ))
  -- First forget from `FDRep` to `Rep`, then use the standard `Rep`-to-intertwiner equivalence.
  exact
    ((FDRep.forget₂HomLinearEquiv (FDRep.of (W₁.ρ ⊠ W₂.ρ)) (FDRep.of (W₁.ρ ⊠ W₂.ρ))).symm).trans
      (Rep.homLinearEquiv X X)

/-- Helper for Theorem 3-3.2-1: forgetting an `FDRep` endomorphism to the underlying
representation intertwiner is a linear equivalence. -/
private noncomputable def end_intertwining_equiv
    {G : Type u} [Group G]
    (W : FDRep k G) :
    (W ⟶ W) ≃ₗ[k] Representation.IntertwiningMap W.ρ W.ρ :=
  let X : Rep k G := (forget₂ (FDRep k G) (Rep k G)).obj W
  ((FDRep.forget₂HomLinearEquiv W W).symm).trans (Rep.homLinearEquiv X X)

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: the raw intertwiner recovered from an `FDRep` morphism acts by the
same underlying linear map. -/
private lemma end_intertwining_equiv_apply
    {G : Type u} [Group G]
    (W : FDRep k G) (f : W ⟶ W) (v : W) :
    end_intertwining_equiv W f v = f v := by
  rfl

/-- Helper for Theorem 3-3.2-1: Schur's scalar on a raw intertwiner is read off on vectors by the
same scalar multiple formula. -/
private lemma intertwining_apply_eq_scalar_smul
    {G : Type u} [Group G]
    (W : FDRep k G) [Simple W] (φ : Representation.IntertwiningMap W.ρ W.ρ) (w : W) :
    φ w = scalarOfSimpleEnd W ((end_intertwining_equiv W).symm φ) • w := by
  -- Convert to an `FDRep` endomorphism and then apply the rank-one Schur formula there.
  let f : W ⟶ W := (end_intertwining_equiv W).symm φ
  have hscalar := congrArg (fun g : W ⟶ W ↦ g w) (scalarOfSimpleEnd_smul_id W f)
  simp [f] at hscalar
  exact hscalar.symm

/-- Helper for Theorem 3-3.2-1: the `i`-th coefficient of a tensor with respect to a basis in the
first factor. -/
private noncomputable def basis_tensor_coeff
    {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι k V) (i : ι) :
    V ⊗[k] W →ₗ[k] W :=
  (TensorProduct.lift.equiv (RingHom.id k) V W W)
    (LinearMap.smulRight (b.coord i) (LinearMap.id : W →ₗ[k] W))

omit [IsAlgClosed k] in
omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: on pure tensors, `basis_tensor_coeff` returns the expected basis
coordinate in the first factor times the second factor. -/
private lemma basis_tensor_coeff_tmul
    {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι k V) (i : ι) (v : V) (w : W) :
    basis_tensor_coeff b i (v ⊗ₜ[k] w) = (b.coord i v) • w := by
  simp [basis_tensor_coeff, TensorProduct.lift.equiv_apply]

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: taking a first-factor coefficient commutes with linear maps on the
second tensor factor. -/
private lemma basis_tensor_coeff_map_right
    {V W W' : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup W'] [Module k W'] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k V) (i : ι) (g : W →ₗ[k] W') (x : V ⊗[k] W) :
    basis_tensor_coeff b i ((TensorProduct.map (LinearMap.id) g) x) =
      g (basis_tensor_coeff b i x) := by
  -- Reduce to pure tensors and compute directly.
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul v w =>
      simp [basis_tensor_coeff_tmul]
  | add x y hx hy =>
      simp [hx, hy]

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: decomposing a tensor against a basis in the first factor recovers
the original tensor from its first-factor coefficients. -/
private lemma sum_basis_tmul_basis_tensor_coeff
    {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι k V) (x : V ⊗[k] W) :
    ∑ i, b i ⊗ₜ[k] basis_tensor_coeff b i x = x := by
  -- Expand by tensor induction, then use `Basis.sum_repr` on the first factor.
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul v w =>
      calc
        ∑ i, b i ⊗ₜ[k] basis_tensor_coeff b i (v ⊗ₜ[k] w) =
            ∑ i, (b.coord i v) • (b i ⊗ₜ[k] w) := by
              simp [basis_tensor_coeff_tmul, TensorProduct.tmul_smul]
        _ = (∑ i, (b.coord i v) • b i) ⊗ₜ[k] w := by
              symm
              exact TensorProduct.sum_tmul _ _ _
        _ = v ⊗ₜ[k] w := by
              exact congrArg (fun u : V ↦ u ⊗ₜ[k] w) (b.sum_repr v)
  | add x y hx hy =>
      simp_rw [LinearMap.map_add, TensorProduct.tmul_add]
      rw [Finset.sum_add_distrib, hx, hy]

/-- Helper for Theorem 3-3.2-1: extract the `(i,j)` coefficient endomorphism of the second factor
from a product-group intertwiner by fixing the `j`-th basis vector in the first factor and reading
off the `i`-th coefficient after applying the intertwiner. -/
private noncomputable def externalTensor_basis_coefficient_end
    {ι : Type*} [Fintype ι] (W₁ : FDRep k G₁) (W₂ : FDRep k G₂)
    (b : Module.Basis ι k W₁)
    (T : Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ))
    (i j : ι) : W₂ →ₗ[k] W₂ :=
  ((basis_tensor_coeff b i).comp T.toLinearMap).comp ((TensorProduct.mk k W₁ W₂) (b j))

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: each extracted coefficient map commutes with the `G₂`-action, so
it is an endomorphism of the simple second factor. -/
private lemma externalTensor_basis_coefficient_end_isIntertwining
    {ι : Type*} [Fintype ι] (W₁ : FDRep k G₁) (W₂ : FDRep k G₂)
    (b : Module.Basis ι k W₁)
    (T : Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ))
    (i j : ι) (g₂ : G₂) (w : W₂) :
    externalTensor_basis_coefficient_end W₁ W₂ b T i j (W₂.ρ g₂ w) =
      W₂.ρ g₂ (externalTensor_basis_coefficient_end W₁ W₂ b T i j w) := by
  -- Specialize the product intertwining relation at `(1, g₂)` so only the second factor moves.
  have hT :
      T (b j ⊗ₜ[k] W₂.ρ g₂ w) =
        (TensorProduct.map (LinearMap.id) (W₂.ρ g₂)) (T (b j ⊗ₜ[k] w)) := by
    simpa [Representation.tprod_apply] using
      congrArg (fun F : W₁ ⊗[k] W₂ →ₗ[k] W₁ ⊗[k] W₂ ↦ F (b j ⊗ₜ[k] w))
        (T.isIntertwining' (1, g₂))
  have hcoeff := congrArg (basis_tensor_coeff b i) hT
  rw [basis_tensor_coeff_map_right b i (W₂.ρ g₂)] at hcoeff
  simpa [externalTensor_basis_coefficient_end] using hcoeff

/-- Helper for Theorem 3-3.2-1: bundle the extracted coefficient map as a `G₂`-endomorphism. -/
private noncomputable def externalTensor_basis_coefficient_intertwining
    {ι : Type*} [Fintype ι] (W₁ : FDRep k G₁) (W₂ : FDRep k G₂)
    (b : Module.Basis ι k W₁)
    (T : Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ))
    (i j : ι) :
    Representation.IntertwiningMap W₂.ρ W₂.ρ :=
  (externalTensor_basis_coefficient_end W₁ W₂ b T i j).intertwiningMap_of_isIntertwiningMap
    W₂.ρ W₂.ρ (externalTensor_basis_coefficient_end_isIntertwining W₁ W₂ b T i j)

/-- Helper for Theorem 3-3.2-1: rebuild the left-factor linear map from the scalars of the
coefficient endomorphisms obtained from a product intertwiner. -/
private noncomputable def recoveredLeftLinear
    {ι : Type*} [Fintype ι] (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) [Simple W₂]
    (b : Module.Basis ι k W₁)
    (T : Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ)) :
    W₁ →ₗ[k] W₁ :=
  b.constr k (fun j ↦
    ∑ i, scalarOfSimpleEnd W₂
      ((end_intertwining_equiv W₂).symm
        (externalTensor_basis_coefficient_intertwining W₁ W₂ b T i j)) • b i)

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: the recovered left map is defined on the chosen basis by the Schur
scalars of the coefficient endomorphisms. -/
private lemma recoveredLeftLinear_basis
    {ι : Type*} [Fintype ι] (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) [Simple W₂]
    (b : Module.Basis ι k W₁)
    (T : Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ)) (j : ι) :
    recoveredLeftLinear W₁ W₂ b T (b j) =
      ∑ i, scalarOfSimpleEnd W₂
        ((end_intertwining_equiv W₂).symm
          (externalTensor_basis_coefficient_intertwining W₁ W₂ b T i j)) • b i := by
  rw [recoveredLeftLinear, Module.Basis.constr_basis]

/-- Helper for Theorem 3-3.2-1: on a basis tensor `b j ⊗ w`, the product intertwiner is exactly
the recovered left map tensored with the identity on the second factor. -/
private lemma apply_eq_tensor_recovered_on_basis
    {ι : Type*} [Fintype ι] (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) [Simple W₂]
    (b : Module.Basis ι k W₁)
    (T : Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ)) (j : ι) (w : W₂) :
    T (b j ⊗ₜ[k] w) = recoveredLeftLinear W₁ W₂ b T (b j) ⊗ₜ[k] w := by
  -- Reconstruct from first-factor coefficients, then collapse each coefficient by Schur.
  calc
    T (b j ⊗ₜ[k] w) =
        ∑ i, b i ⊗ₜ[k] externalTensor_basis_coefficient_end W₁ W₂ b T i j w := by
          symm
          simpa [externalTensor_basis_coefficient_end] using
            sum_basis_tmul_basis_tensor_coeff b (T (b j ⊗ₜ[k] w))
    _ =
        ∑ i, b i ⊗ₜ[k]
          (scalarOfSimpleEnd W₂
            ((end_intertwining_equiv W₂).symm
              (externalTensor_basis_coefficient_intertwining W₁ W₂ b T i j)) • w) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hscalar :=
            intertwining_apply_eq_scalar_smul W₂
              (externalTensor_basis_coefficient_intertwining W₁ W₂ b T i j) w
          exact congrArg (fun u : W₂ ↦ b i ⊗ₜ[k] u) (by
            simpa [externalTensor_basis_coefficient_intertwining] using hscalar)
    _ =
        ∑ i, scalarOfSimpleEnd W₂
          ((end_intertwining_equiv W₂).symm
            (externalTensor_basis_coefficient_intertwining W₁ W₂ b T i j)) •
          (b i ⊗ₜ[k] w) := by
          simp_rw [TensorProduct.tmul_smul]
    _ = recoveredLeftLinear W₁ W₂ b T (b j) ⊗ₜ[k] w := by
          rw [recoveredLeftLinear_basis]
          symm
          exact TensorProduct.sum_tmul _ _ _

/-- Helper for Theorem 3-3.2-1: after reconstruction on basis vectors, linearity upgrades the
identity `T = f ⊗ id` to all pure tensors. -/
private lemma apply_eq_tensor_recovered
    {ι : Type*} [Fintype ι] (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) [Simple W₂]
    (b : Module.Basis ι k W₁)
    (T : Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ)) (v : W₁) (w : W₂) :
    T (v ⊗ₜ[k] w) = recoveredLeftLinear W₁ W₂ b T v ⊗ₜ[k] w := by
  -- Expand `v` in the chosen basis and apply the basis-vector reconstruction termwise.
  rw [← b.sum_repr v]
  rw [TensorProduct.sum_tmul, map_sum, map_sum, TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← TensorProduct.smul_tmul', map_smul, LinearMap.map_smul,
    apply_eq_tensor_recovered_on_basis W₁ W₂ b T i w, TensorProduct.smul_tmul']

/-- Helper for Theorem 3-3.2-1: evaluate a tensor against the chosen dual vector on the second
factor. -/
private noncomputable def secondTensorEvaluator
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) [Simple W₂] :
    W₁ ⊗[k] W₂ →ₗ[k] W₁ :=
  (TensorProduct.lift.equiv (RingHom.id k) W₁ W₂ W₁)
    (LinearMap.smulRightₗ (chosenDual W₂))

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: the second-factor evaluator sends `v ⊗ w` to
`chosenDual(w) • v`. -/
private lemma secondTensorEvaluator_tmul
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) [Simple W₂] (v : W₁) (w : W₂) :
    secondTensorEvaluator W₁ W₂ (v ⊗ₜ[k] w) =
      chosenDual W₂ w • v := by
  simp [secondTensorEvaluator, TensorProduct.lift.equiv_apply]

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: evaluating against the second factor commutes with linear maps on
the first tensor factor. -/
private lemma secondTensorEvaluator_map_left
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) [Simple W₂]
    (f : W₁ →ₗ[k] W₁) (x : W₁ ⊗[k] W₂) :
    secondTensorEvaluator W₁ W₂ ((TensorProduct.map f (LinearMap.id)) x) =
      f (secondTensorEvaluator W₁ W₂ x) := by
  -- Again reduce to pure tensors and compute.
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul v w =>
      simp [secondTensorEvaluator_tmul]
  | add x y hx hy =>
      simp [hx, hy]

/-- Helper for Theorem 3-3.2-1: the recovered left map commutes with the `G₁`-action because
`T = f ⊗ id` and one can cancel the second tensor factor using the chosen dual vector. -/
private lemma recoveredLeftLinear_isIntertwining
    {ι : Type*} [Fintype ι] (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) [Simple W₂]
    (b : Module.Basis ι k W₁)
    (T : Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ)) (g₁ : G₁) (v : W₁) :
    recoveredLeftLinear W₁ W₂ b T (W₁.ρ g₁ v) =
      W₁.ρ g₁ (recoveredLeftLinear W₁ W₂ b T v) := by
  -- Compare the two ways of moving `(g₁, 1)` across `T`, then evaluate on the second factor.
  have hT :
      T (W₁.ρ g₁ v ⊗ₜ[k] chosenVector W₂) =
        (TensorProduct.map (W₁.ρ g₁) (LinearMap.id))
          (T (v ⊗ₜ[k] chosenVector W₂)) := by
    simpa [Representation.tprod_apply] using
      congrArg (fun F : W₁ ⊗[k] W₂ →ₗ[k] W₁ ⊗[k] W₂ ↦ F (v ⊗ₜ[k] chosenVector W₂))
        (T.isIntertwining' (g₁, 1))
  have hrecovered_left :
      T (W₁.ρ g₁ v ⊗ₜ[k] chosenVector W₂) =
        recoveredLeftLinear W₁ W₂ b T (W₁.ρ g₁ v) ⊗ₜ[k]
          chosenVector W₂ := by
    simpa using
      apply_eq_tensor_recovered W₁ W₂ b T (W₁.ρ g₁ v) (chosenVector W₂)
  have hrecovered_right :
      T (v ⊗ₜ[k] chosenVector W₂) =
        recoveredLeftLinear W₁ W₂ b T v ⊗ₜ[k] chosenVector W₂ := by
    simpa using
      apply_eq_tensor_recovered W₁ W₂ b T v (chosenVector W₂)
  rw [hrecovered_left, hrecovered_right] at hT
  have hEval := congrArg (secondTensorEvaluator W₁ W₂) hT
  simpa [secondTensorEvaluator_tmul, secondTensorEvaluator_map_left, chosenDual_apply,
    one_smul] using hEval

/-- Helper for Theorem 3-3.2-1: the recovered left linear map is an actual `G₁`-endomorphism. -/
private noncomputable def recoveredLeftIntertwining
    {ι : Type*} [Fintype ι] (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) [Simple W₂]
    (b : Module.Basis ι k W₁)
    (T : Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ)) :
    Representation.IntertwiningMap W₁.ρ W₁.ρ :=
  (recoveredLeftLinear W₁ W₂ b T).intertwiningMap_of_isIntertwiningMap
    W₁.ρ W₁.ρ (recoveredLeftLinear_isIntertwining W₁ W₂ b T)

/-- Helper for Theorem 3-3.2-1: rebundle the recovered left intertwiner as an `FDRep`
endomorphism. -/
private noncomputable def recoveredLeftEnd
    {ι : Type*} [Fintype ι] (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) [Simple W₂]
    (b : Module.Basis ι k W₁)
    (T : Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ)) :
    W₁ ⟶ W₁ :=
  (end_intertwining_equiv W₁).symm
    (recoveredLeftIntertwining W₁ W₂ b T)

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: the inverse of `externalTensor_end_intertwining_equiv` has the
same underlying linear map on tensors. -/
private lemma externalTensor_end_intertwining_equiv_apply
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂)
    (F : ((FDRep.of (W₁.ρ ⊠ W₂.ρ)) ⟶ (FDRep.of (W₁.ρ ⊠ W₂.ρ)))) (x : W₁ ⊗[k] W₂) :
    externalTensor_end_intertwining_equiv W₁ W₂ F x = F x := by
  rfl

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: the inverse of `externalTensor_end_intertwining_equiv` has the
same underlying linear map on tensors. -/
private lemma externalTensor_end_intertwining_equiv_symm_apply
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂)
    (T : Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ)) (x : W₁ ⊗[k] W₂) :
    (externalTensor_end_intertwining_equiv W₁ W₂).symm T x = T x := by
  rfl

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: a raw `G₁`-endomorphism gives a product-group intertwiner on the
first tensor factor. -/
private lemma fstRawEnd_isIntertwining
    (W₁ : FDRep k G₁) (f : Representation.IntertwiningMap W₁.ρ W₁.ρ)
    (g : G₁ × G₂) (v : W₁) :
    f ((W₁.ρ.comp (fst G₁ G₂)) g v) = (W₁.ρ.comp (fst G₁ G₂)) g (f v) := by
  simpa using congrArg (fun F : W₁ →ₗ[k] W₁ ↦ F v) (f.isIntertwining' g.1)

/-- Helper for Theorem 3-3.2-1: transport a `G₁`-endomorphism to the product-group representation
by letting it act on the first factor only. -/
private noncomputable def fstRawEnd
    (W₁ : FDRep k G₁) (_W₂ : FDRep k G₂)
    (f : Representation.IntertwiningMap W₁.ρ W₁.ρ) :
    Representation.IntertwiningMap (W₁.ρ.comp (fst G₁ G₂)) (W₁.ρ.comp (fst G₁ G₂)) :=
  f.toLinearMap.intertwiningMap_of_isIntertwiningMap
    (W₁.ρ.comp (fst G₁ G₂)) (W₁.ρ.comp (fst G₁ G₂)) (fstRawEnd_isIntertwining W₁ f)

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: on vectors, the transported first-factor endomorphism is just the
original underlying linear map. -/
private lemma fstRawEnd_apply
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂)
    (f : Representation.IntertwiningMap W₁.ρ W₁.ρ) (v : W₁) :
    fstRawEnd W₁ W₂ f v = f v := by
  rfl

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: `fstRawEnd` is additive. -/
private lemma fstRawEnd_add
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂)
    (f g : Representation.IntertwiningMap W₁.ρ W₁.ρ) :
    fstRawEnd W₁ W₂ (f + g) =
      fstRawEnd W₁ W₂ f +
        fstRawEnd W₁ W₂ g := by
  ext v
  simp [fstRawEnd]

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: `fstRawEnd` respects scalar multiplication. -/
private lemma fstRawEnd_smul
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) (a : k)
    (f : Representation.IntertwiningMap W₁.ρ W₁.ρ) :
    fstRawEnd W₁ W₂ (a • f) =
      a • fstRawEnd W₁ W₂ f := by
  ext v
  simp [fstRawEnd]

/-- Helper for Theorem 3-3.2-1: the first-factor transport is linear on endomorphisms. -/
private noncomputable def fstRawEndLinear
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) :
    Representation.IntertwiningMap W₁.ρ W₁.ρ →ₗ[k]
      Representation.IntertwiningMap (W₁.ρ.comp (fst G₁ G₂)) (W₁.ρ.comp (fst G₁ G₂)) where
  toFun := fstRawEnd W₁ W₂
  map_add' := fstRawEnd_add W₁ W₂
  map_smul' := fstRawEnd_smul W₁ W₂

/-- Helper for Theorem 3-3.2-1: tensoring with the identity on the second factor is linear on
first-factor intertwiners. -/
private noncomputable def tensorRightIdLinear
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) :
    Representation.IntertwiningMap (W₁.ρ.comp (fst G₁ G₂)) (W₁.ρ.comp (fst G₁ G₂)) →ₗ[k]
      Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ) where
  toFun := fun f ↦ f.tensor (Representation.IntertwiningMap.id (W₂.ρ.comp (snd G₁ G₂)))
  map_add' := fun f g ↦ Representation.IntertwiningMap.tensor_add_left f g _
  map_smul' := fun a f ↦ Representation.IntertwiningMap.tensor_smul_left a f _

/-- Helper for Theorem 3-3.2-1: the easy direction `f ↦ f ⊗ id` is a linear map on raw
intertwiners. -/
private noncomputable def leftEndToExternalTensorRawLinear
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) :
    Representation.IntertwiningMap W₁.ρ W₁.ρ →ₗ[k]
      Representation.IntertwiningMap (W₁.ρ ⊠ W₂.ρ) (W₁.ρ ⊠ W₂.ρ) :=
  (tensorRightIdLinear W₁ W₂).comp (fstRawEndLinear W₁ W₂)

/-- Helper for Theorem 3-3.2-1: the easy tensoring construction is linear on `FDRep`
endomorphisms. -/
private noncomputable def leftEndToExternalTensorLinear
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) :
    (W₁ ⟶ W₁) →ₗ[k] ((FDRep.of (W₁.ρ ⊠ W₂.ρ)) ⟶ (FDRep.of (W₁.ρ ⊠ W₂.ρ))) :=
  (externalTensor_end_intertwining_equiv W₁ W₂).symm.toLinearMap.comp
    ((leftEndToExternalTensorRawLinear W₁ W₂).comp
      (end_intertwining_equiv W₁).toLinearMap)

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: on pure tensors, the easy tensoring map acts by `f` on the first
factor and by the identity on the second. -/
private lemma leftEndToExternalTensorLinear_apply
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) (f : W₁ ⟶ W₁) (v : W₁) (w : W₂) :
    leftEndToExternalTensorLinear W₁ W₂ f (v ⊗ₜ[k] w) = f v ⊗ₜ[k] w := by
  -- Pass to the raw intertwiner side, where all constructions are definitionally transparent.
  have hraw :
      externalTensor_end_intertwining_equiv W₁ W₂
          (leftEndToExternalTensorLinear W₁ W₂ f) (v ⊗ₜ[k] w) =
        f v ⊗ₜ[k] w := by
    simp [leftEndToExternalTensorLinear, leftEndToExternalTensorRawLinear, tensorRightIdLinear,
      fstRawEndLinear, fstRawEnd_apply, end_intertwining_equiv_apply]
  simpa [externalTensor_end_intertwining_equiv_apply] using hraw

omit [IsAlgClosed k] in
/-- Helper for Theorem 3-3.2-1: the second-factor evaluator detects whether `f ⊗ id` is zero, so
the easy tensoring map is injective. -/
private lemma leftEndToExternalTensorLinear_injective
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) [Simple W₂] :
    Function.Injective (leftEndToExternalTensorLinear W₁ W₂) := by
  intro f g hfg
  ext v
  have htensor : f v ⊗ₜ[k] chosenVector W₂ = g v ⊗ₜ[k] chosenVector W₂ := by
    simpa [leftEndToExternalTensorLinear_apply] using congrArg
      (fun h : ((FDRep.of (W₁.ρ ⊠ W₂.ρ)) ⟶ (FDRep.of (W₁.ρ ⊠ W₂.ρ))) ↦
        h (v ⊗ₜ[k] chosenVector W₂)) hfg
  have hEval := congrArg (secondTensorEvaluator W₁ W₂) htensor
  simpa [secondTensorEvaluator_tmul, chosenDual_apply, one_smul] using hEval

/-- Helper for Theorem 3-3.2-1: every product-group intertwiner is in the image of the easy
tensoring map, with preimage given by the recovered left endomorphism. -/
private lemma leftEndToExternalTensorLinear_surjective
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) [Simple W₂] :
    Function.Surjective (leftEndToExternalTensorLinear W₁ W₂) := by
  let b : Module.Basis (Fin (Module.finrank k W₁)) k W₁ := Module.finBasis k W₁
  intro F
  refine ⟨recoveredLeftEnd W₁ W₂ b
      ((externalTensor_end_intertwining_equiv W₁ W₂) F), ?_⟩
  apply (externalTensor_end_intertwining_equiv W₁ W₂).injective
  -- After forgetting to raw intertwiners, both sides agree on every pure tensor.
  ext v w
  simpa [leftEndToExternalTensorLinear, leftEndToExternalTensorRawLinear, tensorRightIdLinear,
    fstRawEndLinear, fstRawEnd_apply, end_intertwining_equiv_apply, recoveredLeftEnd,
    recoveredLeftIntertwining] using
      (apply_eq_tensor_recovered W₁ W₂ b
        ((externalTensor_end_intertwining_equiv W₁ W₂) F) v w).symm

/-- Helper for Theorem 3-3.2-1: once one identifies product-group endomorphisms of
`W₁ ⊠ W₂` with endomorphisms of `W₁`, Schur's lemma finishes the simplicity proof. -/
noncomputable def externalTensor_end_linearEquiv
    (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) (hW₂ : Simple W₂) :
    ((FDRep.of (W₁.ρ ⊠ W₂.ρ)) ⟶ (FDRep.of (W₁.ρ ⊠ W₂.ρ))) ≃ₗ[k] (W₁ ⟶ W₁) := by
  -- Route correction: build the easy map `f ↦ f ⊗ id` and prove it is bijective by reconstructing
  -- any product intertwiner from its first-factor basis coefficients.
  letI : Simple W₂ := hW₂
  exact
    (LinearEquiv.ofBijective
      (leftEndToExternalTensorLinear W₁ W₂)
      ⟨leftEndToExternalTensorLinear_injective W₁ W₂,
        leftEndToExternalTensorLinear_surjective W₁ W₂⟩).symm

/-- Helper for Theorem 3-3.2-1: the product-group endomorphism space has dimension `1` once the
first factor is simple and the second-factor endomorphisms have already been eliminated by
`externalTensor_end_linearEquiv`. -/
private lemma externalTensor_end_rank_one_of_simple
    (W₁ : FDRep k G₁) (hW₁ : Simple W₁) (W₂ : FDRep k G₂) (hW₂ : Simple W₂) :
    Module.finrank k ((FDRep.of (W₁.ρ ⊠ W₂.ρ)) ⟶ (FDRep.of (W₁.ρ ⊠ W₂.ρ))) = 1 := by
  -- Route correction: abandon the monoid-algebra detour and compute the endomorphism rank
  -- through the already constructed linear equivalence with `End_G(W₁)`.
  letI : Simple W₁ := hW₁
  have hW₁_end_rank :
      Module.finrank k (W₁ ⟶ W₁) = 1 := by
    let hIso : Nonempty (W₁ ≅ W₁) := ⟨Iso.refl W₁⟩
    simpa [hIso] using (FDRep.finrank_hom_simple_simple W₁ W₁)
  calc
    Module.finrank k ((FDRep.of (W₁.ρ ⊠ W₂.ρ)) ⟶ (FDRep.of (W₁.ρ ⊠ W₂.ρ))) =
        Module.finrank k (W₁ ⟶ W₁) := by
          exact (externalTensor_end_linearEquiv W₁ W₂ hW₂).finrank_eq
    _ = 1 := hW₁_end_rank

/-- Theorem 3-3.2-1 (1): if `ρ₁` and `ρ₂` are irreducible finite-dimensional representations of
`G₁` and `G₂` over an algebraically closed field, then their external tensor product is a simple
representation of `G₁ × G₂`. -/
theorem externalTensor_simple
    (W₁ : FDRep k G₁) (hW₁ : Simple W₁) (W₂ : FDRep k G₂) (hW₂ : Simple W₂) :
    Simple (FDRep.of (W₁.ρ ⊠ W₂.ρ)) := by
  -- Convert the tensor-product endomorphism space to the first factor, then apply Schur's
  -- rank-one criterion in the owner `FDRep`.
  letI : Fintype G₁ := Fintype.ofFinite G₁
  letI : Fintype G₂ := Fintype.ofFinite G₂
  letI : Fintype (G₁ × G₂) := instFintypeProd G₁ G₂
  letI : Finite (G₁ × G₂) := Finite.of_fintype (G₁ × G₂)
  letI : Invertible (Fintype.card (G₁ × G₂) : k) := invertibleCardProd
  letI : NeZero (Nat.card (G₁ × G₂) : k) := by
    simpa [Nat.card_eq_fintype_card] using
      (show NeZero (Fintype.card (G₁ × G₂) : k) from inferInstance)
  exact
    (FDRep.simple_iff_end_is_rank_one (G := G₁ × G₂) (k := k) (FDRep.of (W₁.ρ ⊠ W₂.ρ))).2
      (externalTensor_end_rank_one_of_simple W₁ hW₁ W₂ hW₂)

end

/-- Helper for Theorem 3-3.2-1: each term in the external-tensor product family coming from
complete irreducible families is simple. -/
private lemma externalTensor_family_simple_of_complete_families
    {ι₁ : Type u} {ι₂ : Type u} [Finite ι₁] [Finite ι₂]
    (π₁ : ι₁ → FDRep k G₁) (π₂ : ι₂ → FDRep k G₂)
    (hπ₁_complete : IsCompleteIrreducibleFamily π₁)
    (hπ₂_complete : IsCompleteIrreducibleFamily π₂)
    (p : ι₁ × ι₂) :
    Simple (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ)) := by
  -- Completeness supplies simplicity of the two coordinates, so part (i) applies termwise.
  letI : Simple (π₁ p.1) := hπ₁_complete.isSimple p.1
  letI : Simple (π₂ p.2) := hπ₂_complete.isSimple p.2
  let h₁ : Simple (π₁ p.1) := hπ₁_complete.isSimple p.1
  let h₂ : Simple (π₂ p.2) := hπ₂_complete.isSimple p.2
  have hsimple : Simple (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ)) := by
    exact externalTensor_simple (π₁ p.1) h₁ (π₂ p.2) h₂
  exact hsimple

/-- Helper for Theorem 3-3.2-1: an isomorphism between two terms in the external-tensor family
forces their product-group character pairing to equal `1`. -/
private lemma externalTensor_scalarProduct_eq_one_of_iso
    {ι₁ : Type u} {ι₂ : Type u} [Finite ι₁] [Finite ι₂]
    (π₁ : ι₁ → FDRep k G₁) (π₂ : ι₂ → FDRep k G₂)
    (hπ₁_complete : IsCompleteIrreducibleFamily π₁)
    (hπ₂_complete : IsCompleteIrreducibleFamily π₂)
    {p q : ι₁ × ι₂}
    (hIso :
      Nonempty (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ) ≅
        FDRep.of ((π₁ q.1).ρ ⊠ (π₂ q.2).ρ))) :
    ⅟ (Fintype.card (G₁ × G₂) : k) •
      ∑ g : G₁ × G₂,
        (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ)).character g *
          (FDRep.of ((π₁ q.1).ρ ⊠ (π₂ q.2).ρ)).character g⁻¹
      = (1 : k) := by
  -- Completeness gives simplicity of both tensor factors, so orthonormality applies directly.
  letI : Simple (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ)) := by
    simpa using
      externalTensor_family_simple_of_complete_families π₁ π₂ hπ₁_complete
        hπ₂_complete p
  letI : Simple (FDRep.of ((π₁ q.1).ρ ⊠ (π₂ q.2).ρ)) := by
    simpa using
      externalTensor_family_simple_of_complete_families π₁ π₂ hπ₁_complete
        hπ₂_complete q
  -- An isomorphism between simple representations forces the normalized pairing to be `1`.
  simpa [hIso] using
    (FDRep.char_orthonormal (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ))
      (FDRep.of ((π₁ q.1).ρ ⊠ (π₂ q.2).ρ)))

/-- Helper for Theorem 3-3.2-1: an isomorphism between two terms in the external-tensor family
forces equality of their first coordinates. -/
private lemma externalTensor_first_eq_of_iso
    {ι₁ : Type u} {ι₂ : Type u} [Finite ι₁] [Finite ι₂]
    (π₁ : ι₁ → FDRep k G₁) (π₂ : ι₂ → FDRep k G₂)
    (hπ₁_pairwise : PairwiseNonisomorphic π₁)
    (hπ₁_complete : IsCompleteIrreducibleFamily π₁)
    (hπ₂_complete : IsCompleteIrreducibleFamily π₂)
    {p q : ι₁ × ι₂}
    (hIso :
      Nonempty (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ) ≅
        FDRep.of ((π₁ q.1).ρ ⊠ (π₂ q.2).ρ))) :
    p.1 = q.1 := by
  by_contra hp1
  letI : Simple (π₁ p.1) := hπ₁_complete.isSimple p.1
  letI : Simple (π₁ q.1) := hπ₁_complete.isSimple q.1
  letI : Simple (π₂ p.2) := hπ₂_complete.isSimple p.2
  letI : Simple (π₂ q.2) := hπ₂_complete.isSimple q.2
  have hpair :
      ⅟ (Fintype.card (G₁ × G₂) : k) •
        ∑ g : G₁ × G₂,
          (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ)).character g *
            (FDRep.of ((π₁ q.1).ρ ⊠ (π₂ q.2).ρ)).character g⁻¹
        = (1 : k) := by
    -- Reduce the product-family isomorphism to the standard character orthonormality statement.
    exact
      externalTensor_scalarProduct_eq_one_of_iso π₁ π₂ hπ₁_complete hπ₂_complete hIso
  have hleft :
      ⅟ (Fintype.card G₁ : k) •
        ∑ g₁ : G₁, (π₁ p.1).character g₁ * (π₁ q.1).character g₁⁻¹
        = (0 : k) := by
    -- Distinct first coordinates force orthogonality on the `G₁` factor.
    simpa [hπ₁_pairwise hp1] using (FDRep.char_orthonormal (π₁ p.1) (π₁ q.1))
  have hpair_zero :
      ⅟ (Fintype.card (G₁ × G₂) : k) •
        ∑ g : G₁ × G₂,
          (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ)).character g *
            (FDRep.of ((π₁ q.1).ρ ⊠ (π₂ q.2).ρ)).character g⁻¹
        = (0 : k) := by
    -- The vanishing of the first-factor pairing propagates to the product pairing.
    simpa using
      externalTensor_scalarProduct_eq_zero_of_left
        (π₁ p.1) (π₁ q.1) (π₂ p.2) (π₂ q.2) hleft
  exact zero_ne_one <| by rw [← hpair_zero, hpair]

/-- Helper for Theorem 3-3.2-1: an isomorphism between two terms in the external-tensor family
forces equality of their second coordinates. -/
private lemma externalTensor_second_eq_of_iso
    {ι₁ : Type u} {ι₂ : Type u} [Finite ι₁] [Finite ι₂]
    (π₁ : ι₁ → FDRep k G₁) (π₂ : ι₂ → FDRep k G₂)
    (hπ₂_pairwise : PairwiseNonisomorphic π₂)
    (hπ₁_complete : IsCompleteIrreducibleFamily π₁)
    (hπ₂_complete : IsCompleteIrreducibleFamily π₂)
    {p q : ι₁ × ι₂}
    (hIso :
      Nonempty (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ) ≅
        FDRep.of ((π₁ q.1).ρ ⊠ (π₂ q.2).ρ))) :
    p.2 = q.2 := by
  by_contra hp2
  letI : Simple (π₁ p.1) := hπ₁_complete.isSimple p.1
  letI : Simple (π₁ q.1) := hπ₁_complete.isSimple q.1
  letI : Simple (π₂ p.2) := hπ₂_complete.isSimple p.2
  letI : Simple (π₂ q.2) := hπ₂_complete.isSimple q.2
  have hpair :
      ⅟ (Fintype.card (G₁ × G₂) : k) •
        ∑ g : G₁ × G₂,
          (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ)).character g *
            (FDRep.of ((π₁ q.1).ρ ⊠ (π₂ q.2).ρ)).character g⁻¹
        = (1 : k) := by
    -- The same character-pairing normalization applies on the product group.
    exact
      externalTensor_scalarProduct_eq_one_of_iso π₁ π₂ hπ₁_complete hπ₂_complete hIso
  have hright :
      ⅟ (Fintype.card G₂ : k) •
        ∑ g₂ : G₂, (π₂ p.2).character g₂ * (π₂ q.2).character g₂⁻¹
        = (0 : k) := by
    -- Distinct second coordinates force orthogonality on the `G₂` factor.
    simpa [hπ₂_pairwise hp2] using (FDRep.char_orthonormal (π₂ p.2) (π₂ q.2))
  have hpair_zero :
      ⅟ (Fintype.card (G₁ × G₂) : k) •
        ∑ g : G₁ × G₂,
          (FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ)).character g *
            (FDRep.of ((π₁ q.1).ρ ⊠ (π₂ q.2).ρ)).character g⁻¹
        = (0 : k) := by
    -- The symmetric factorization argument gives the desired contradiction.
    simpa using
      externalTensor_scalarProduct_eq_zero_of_right
        (π₁ p.1) (π₁ q.1) (π₂ p.2) (π₂ q.2) hright
  exact zero_ne_one <| by rw [← hpair_zero, hpair]

/-- Helper for Theorem 3-3.2-1: complete pairwise nonisomorphic families on the two factors give a
complete pairwise nonisomorphic family of external tensor products on the product group. -/
lemma externalTensor_complete_family_of_complete_families
    {ι₁ : Type u} {ι₂ : Type u} [Finite ι₁] [Finite ι₂]
    (π₁ : ι₁ → FDRep k G₁) (π₂ : ι₂ → FDRep k G₂)
    (hπ₁_pairwise : PairwiseNonisomorphic π₁)
    (hπ₂_pairwise : PairwiseNonisomorphic π₂)
    (hπ₁_complete : IsCompleteIrreducibleFamily π₁)
    (hπ₂_complete : IsCompleteIrreducibleFamily π₂) :
    PairwiseNonisomorphic (fun p : ι₁ × ι₂ ↦ FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ)) ∧
      IsCompleteIrreducibleFamily
        (fun p : ι₁ × ι₂ ↦ FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ)) := by
  classical
  let _ : Fintype ι₁ := Fintype.ofFinite ι₁
  let _ : Fintype ι₂ := Fintype.ofFinite ι₂
  let _ : Fintype (ι₁ × ι₂) := Fintype.ofFinite (ι₁ × ι₂)
  let piTensor : ι₁ × ι₂ → FDRep k (G₁ × G₂) :=
    fun p ↦ FDRep.of ((π₁ p.1).ρ ⊠ (π₂ p.2).ρ)
  have hpiTensor_simple (p : ι₁ × ι₂) : Simple (piTensor p) := by
    -- Package the termwise simplicity of the product family into a reusable helper lemma.
    simpa [piTensor] using
      externalTensor_family_simple_of_complete_families π₁ π₂ hπ₁_complete
        hπ₂_complete p
  have hpiTensor_pairwise : PairwiseNonisomorphic piTensor := by
    intro p q hpq hIso
    -- Each coordinate equality is now handled by a dedicated orthogonality lemma.
    have hp1 : p.1 = q.1 :=
      externalTensor_first_eq_of_iso π₁ π₂ hπ₁_pairwise hπ₁_complete
        hπ₂_complete hIso
    have hp2 : p.2 = q.2 :=
      externalTensor_second_eq_of_iso π₁ π₂ hπ₂_pairwise hπ₁_complete
        hπ₂_complete hIso
    exact hpq <| Prod.ext hp1 hp2
  have hpiTensor_sum :
      ∑ p : ι₁ × ι₂, Module.finrank k (piTensor p) ^ 2 = Nat.card (G₁ × G₂) := by
    -- The total square degree of the product family is the product of the two source totals.
    let s : Finset (ι₁ × ι₂) := @Finset.univ (ι₁ × ι₂) (instFintypeProd ι₁ ι₂)
    have huniv : (@Finset.univ (ι₁ × ι₂) inferInstance) = s := by
      ext p
      simp [s]
    calc
      ∑ p : ι₁ × ι₂, Module.finrank k (piTensor p) ^ 2
        = Finset.sum s fun p ↦ Module.finrank k (piTensor p) ^ 2 := by
            rw [← huniv]
      _ = Nat.card (G₁ × G₂) := by
            simpa [piTensor, s] using
              externalTensor_sum_sq_degree_eq_card π₁ π₂ hπ₁_pairwise hπ₂_pairwise
                hπ₁_complete hπ₂_complete
  have hpiTensor_complete : IsCompleteIrreducibleFamily piTensor := by
    exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card
      piTensor hpiTensor_simple hpiTensor_pairwise hpiTensor_sum
  exact ⟨hpiTensor_pairwise, hpiTensor_complete⟩

-- Proof sketch: use the orthogonality relations for irreducible characters on `G₁` and `G₂` to
-- show that the characters of the tensor products coming from the two factors span the class
-- functions on `G₁ × G₂`; then an irreducible representation of the product group must be
-- isomorphic to one of these tensor products.
/-- Theorem 3-3.2-1 (2): every irreducible finite-dimensional representation of `G₁ × G₂` over an
algebraically closed field whose characteristic does not divide `|G₁|` or `|G₂|` is isomorphic to
the external tensor product of irreducible finite-dimensional representations of `G₁` and `G₂`. -/
theorem exists_iso_externalTensor_of_simple
    (X : FDRep k (G₁ × G₂)) (hX : Simple X) :
    ∃ (W₁ : FDRep k G₁) (W₂ : FDRep k G₂) (_ : X ≅ FDRep.of (W₁.ρ ⊠ W₂.ρ)),
      Simple W₁ ∧ Simple W₂ := by
  classical
  letI : Simple X := hX
  obtain ⟨ι₁, _, π₁, hπ₁_pairwise, hπ₁_complete⟩ :=
    (show ∃ (ι : Type u) (_ : Fintype ι) (π : ι → FDRep k G₁),
        PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π from
      exists_complete_pairwise_nonisomorphic_simple_family)
  obtain ⟨ι₂, _, π₂, hπ₂_pairwise, hπ₂_complete⟩ :=
    (show ∃ (ι : Type u) (_ : Fintype ι) (π : ι → FDRep k G₂),
        PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π from
      exists_complete_pairwise_nonisomorphic_simple_family)
  obtain ⟨_, hpiTensor_complete⟩ :=
    externalTensor_complete_family_of_complete_families π₁ π₂ hπ₁_pairwise hπ₂_pairwise
      hπ₁_complete hπ₂_complete
  -- The product family is complete, so the given simple representation must be one of its terms.
  obtain ⟨p, hp⟩ := hpiTensor_complete.exists_iso X hX
  rcases hp with ⟨e⟩
  exact ⟨π₁ p.1, π₂ p.2, e, hπ₁_complete.isSimple p.1, hπ₂_complete.isSimple p.2⟩

end

end FDRep
