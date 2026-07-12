import Mathlib
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2

/-!
# Field-general sum of squares of irreducible degrees, under an explicit splitting hypothesis

This scratch file reproves
`Representation.sum_sq_degree_eq_card_of_complete_irreducible_family`
WITHOUT `[IsAlgClosed K]`, replacing algebraic closedness by the explicit splitting hypothesis
`hsplit : ∀ i, Module.finrank K ((π i).ρ.IntertwiningMap (π i).ρ) = 1`
(each simple has one-dimensional self-intertwiner space; i.e. `K` is a splitting field).

All helper lemmas below are field-general reproductions of the private helpers in
`Serre/Chap03/Theorem_3_3_2_1.lean`. The only place algebraic closedness entered the original
proof was through `IsIrreducible.finrank_intertwiningMap_self` (Schur over an algebraically closed
field). Here that fact is supplied locally as a hypothesis on the relevant target representation.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators TensorProduct

universe u v v' w w'

namespace Representation

namespace SumSqSplit

noncomputable local instance instDecidableEqOfFinite (α : Type*) [Finite α] : DecidableEq α :=
  Classical.decEq α

/-! ### Field-general intertwining-space helpers (reproduced from `Theorem_3_3_2_1`) -/

section

variable {G : Type u} [Monoid G]
variable {K : Type v} [CommSemiring K]
variable {M : ι → Type v'} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module K (M i)]
variable {W : Type w'} [AddCommMonoid W] [Module K W]

/-- Intertwining maps from a direct sum are exactly families of intertwining maps from each
summand. (Field-general; reproduced from `Theorem_3_3_2_1`.) -/
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

/-- Precomposing with a representation equivalence identifies intertwining spaces with the same
codomain. (Field-general; reproduced from `Theorem_3_3_2_1`.) -/
private noncomputable def equivIntertwiningMapCongrLeft
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

end

section

variable {G : Type u} [Monoid G]
variable {K : Type v} [Field K]
variable {V : Type v'} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]
variable {ι : Type w'} [Fintype ι]

/-- Count the indices whose summand is isomorphic to a fixed target by the corresponding indicator
sum. (Field-general; reproduced from `Theorem_3_3_2_1`.) -/
private theorem nat_card_isomorphic_summands_eq_sum_ite
    (ρ : Representation K G V) (σ : ι → Subrepresentation ρ)
    (τ : Representation K G W) :
    by
      classical
      exact Nat.card { i // Nonempty (((σ i).toRepresentation).Equiv τ) } =
        ∑ i, if Nonempty (((σ i).toRepresentation).Equiv τ) then 1 else 0 := by
  classical
  rw [Nat.card_eq_fintype_card,
    Fintype.card_of_subtype
      (Finset.univ.filter fun i ↦ Nonempty (((σ i).toRepresentation).Equiv τ))]
  · rw [Finset.card_filter]
  · intro i
    simp

end

section

variable {G : Type u} [Monoid G]
variable {K : Type v} [Field K]
variable {V : Type v'} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {ι : Type w'} [Finite ι]

section

omit [FiniteDimensional K V]

/-- Schur's lemma plus an explicit splitting hypothesis on the target make the intertwining space
between two irreducible representations one-dimensional exactly in the isomorphic case, and
zero-dimensional otherwise.

This is the field-general replacement for
`finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible`: instead of `[IsAlgClosed K]` we require
`hself : Module.finrank K (τ.IntertwiningMap τ) = 1`, which over an algebraically closed field is
`IsIrreducible.finrank_intertwiningMap_self`. -/
private theorem finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible_of_split
    (ρ : Representation K G V) (hρ : ρ.IsIrreducible)
    (τ : Representation K G W) (hτ : τ.IsIrreducible)
    (hself : Module.finrank K (τ.IntertwiningMap τ) = 1) :
    by
      classical
      exact Module.finrank K (ρ.IntertwiningMap τ) = if Nonempty (ρ.Equiv τ) then 1 else 0 := by
  classical
  letI : ρ.IsIrreducible := hρ
  letI : τ.IsIrreducible := hτ
  by_cases hρτ : Nonempty (ρ.Equiv τ)
  · rcases hρτ with ⟨e⟩
    have hρτ : Nonempty (ρ.Equiv τ) := ⟨e⟩
    -- Transport to the self-case and then use the splitting hypothesis.
    calc
      Module.finrank K (ρ.IntertwiningMap τ) =
          Module.finrank K (τ.IntertwiningMap τ) := by
            symm
            exact (equivIntertwiningMapCongrLeft e τ).finrank_eq
      _ = 1 := hself
      _ = if Nonempty (ρ.Equiv τ) then 1 else 0 := by simp [hρτ]
  · letI : IsEmpty (ρ.Equiv τ) := not_nonempty_iff.mp hρτ
    letI : Subsingleton (ρ.IntertwiningMap τ) := inferInstance
    -- In the nonisomorphic case, all intertwiners vanish (Schur over any field).
    calc
      Module.finrank K (ρ.IntertwiningMap τ) = 0 := Module.finrank_zero_of_subsingleton
      _ = if Nonempty (ρ.Equiv τ) then 1 else 0 := by simp [hρτ]

end

/-- An internal direct-sum decomposition turns the intertwining-space dimension against `τ` into the
sum of the corresponding dimensions on the summands. (Field-general; reproduced from
`Theorem_3_3_2_1`.) -/
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
  calc
    Module.finrank K (ρ.IntertwiningMap τ)
      = Module.finrank K ((directSum π).IntertwiningMap τ) := by
          exact
            (equivIntertwiningMapCongrLeft decompositionEquiv τ).finrank_eq
    _ = Module.finrank K (∀ i, (π i).IntertwiningMap τ) := by
          exact (directSumIntertwiningMapEquivPi π τ).finrank_eq
    _ = ∑ i, Module.finrank K (((σ i).toRepresentation).IntertwiningMap τ) := hpi

section

omit [FiniteDimensional K V]

/-- An irreducible summand contributes `1` exactly when it is isomorphic to the (split) target
irreducible representation, and `0` otherwise. -/
private theorem finrank_intertwiningMap_irreducible_summand_eq_ite_of_split
    {U : Type w'} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (ρ : Representation K G V) (σ : Subrepresentation ρ)
    (hσ : σ.toRepresentation.IsIrreducible)
    (τ : Representation K G U) (hτ : τ.IsIrreducible)
    (hself : Module.finrank K (τ.IntertwiningMap τ) = 1) :
    by
      classical
      exact Module.finrank K (σ.toRepresentation.IntertwiningMap τ) =
        if Nonempty (σ.toRepresentation.Equiv τ) then 1 else 0 := by
  letI : σ.toRepresentation.IsIrreducible := hσ
  simpa using
    finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible_of_split
      σ.toRepresentation hσ τ hτ hself

end

/-- The multiplicity of a (split) irreducible summand in an internal decomposition equals the
dimension of the corresponding intertwining space. -/
private theorem card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap_of_split
    (ρ : Representation K G V) (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (τ : Representation K G W) (hτ : τ.IsIrreducible)
    (hself : Module.finrank K (τ.IntertwiningMap τ) = 1) :
    Nat.card { i // Nonempty (((σ i).toRepresentation).Equiv τ) } =
      Module.finrank K (ρ.IntertwiningMap τ) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hfactor :
      ∀ i, Module.finrank K (((σ i).toRepresentation).IntertwiningMap τ) =
        if Nonempty (((σ i).toRepresentation).Equiv τ) then 1 else 0 := by
    intro i
    simpa using finrank_intertwiningMap_irreducible_summand_eq_ite_of_split
      ρ (σ i) (hσ i) τ hτ hself
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

/-! ### Left-regular multiplicity helpers (field-general) -/

section

variable {G : Type u} [Group G] [Finite G]
variable {ι : Type v} [Finite ι]
variable {K : Type u} [Field K] [NeZero (Nat.card G : K)]

private abbrev IsIrreducibleLeftRegularSummand
    (σ : Subrepresentation (leftRegular K G)) : Prop :=
  let _ : AddCommGroup σ.toSubmodule := inferInstance
  Representation.IsIrreducible (σ.toRepresentation)

omit [Finite G] [NeZero (Nat.card G : K)] in
/-- An irreducible summand in an internal decomposition of the left regular representation has
nontrivial carrier. -/
private theorem summand_toSubmodule_ne_bot_of_isIrreducible
    (σ : Subrepresentation (leftRegular K G))
    (hσ : IsIrreducibleLeftRegularSummand σ) :
    σ.toSubmodule ≠ ⊥ := by
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
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact bot_ne_top <| Subrepresentation.toSubmodule_injective hbot_top

omit [NeZero (Nat.card G : K)] in
/-- An internal irreducible decomposition of the left regular representation has finite index
type. -/
private theorem finite_index_of_internal_irreducible_leftRegular_decomposition
    (σ : ι → Subrepresentation (leftRegular K G))
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, IsIrreducibleLeftRegularSummand (σ i)) :
    Finite ι := by
  classical
  have hfinite_support : Set.Finite { i | (σ i).toSubmodule ≠ ⊥ } :=
    Submodule.finite_ne_bot_of_iSupIndep hinternal.submodule_iSupIndep
  have huniv : { i | (σ i).toSubmodule ≠ ⊥ } = Set.univ := by
    ext i
    simp [summand_toSubmodule_ne_bot_of_isIrreducible (σ i) (hσ i)]
  exact Finite.of_finite_univ <| by
    convert hfinite_support using 1
    simp [huniv]

omit [Finite G] [NeZero (Nat.card G : K)] in
/-- Intertwining maps from the left regular representation to an irreducible representation have
dimension equal to that representation's degree. -/
private theorem leftRegular_intertwining_finrank_eq_degree
    {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K G W) :
    Module.finrank K ((leftRegular K G).IntertwiningMap τ) = Module.finrank K W := by
  simpa using (leftRegularMapEquiv τ).finrank_eq

omit [NeZero (Nat.card G : K)] in
/-- In an internal irreducible decomposition of the left regular representation, the multiplicity of
a fixed (split) irreducible summand equals its degree. -/
private theorem leftRegular_irreducible_multiplicity_eq_finrank_of_split
    {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (σ : ι → Subrepresentation (leftRegular K G))
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, IsIrreducibleLeftRegularSummand (σ i))
    (τ : Representation K G W)
    (hτ : τ.IsIrreducible)
    (hself : Module.finrank K (τ.IntertwiningMap τ) = 1) :
    Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv τ) } = Module.finrank K W := by
  classical
  letI : τ.IsIrreducible := hτ
  letI : Finite ι :=
    finite_index_of_internal_irreducible_leftRegular_decomposition σ hinternal hσ
  let _ : ∀ i, AddCommGroup (σ i).toSubmodule := fun i ↦ inferInstance
  have hσ' : ∀ i, (σ i).toRepresentation.IsIrreducible := by
    intro i
    simpa [IsIrreducibleLeftRegularSummand] using hσ i
  calc
    Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv τ) } =
        Module.finrank K ((leftRegular K G).IntertwiningMap τ) := by
          exact
            card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap_of_split
              (leftRegular K G) σ hinternal hσ' τ hτ hself
    _ = Module.finrank K W := leftRegular_intertwining_finrank_eq_degree τ

omit [Finite G] [NeZero (Nat.card G : K)] in
/-- An `FDRep` isomorphism yields an equivalence of the underlying representations. -/
private theorem fdrep_iso_nonempty_to_rep_equiv_nonempty
    {A B : FDRep K G} (h : Nonempty (A ≅ B)) :
    Nonempty (Representation.Equiv A.ρ B.ρ) := by
  rcases h with ⟨e⟩
  exact ⟨Representation.equivOfIso ((forget₂ (FDRep K G) (Rep K G)).mapIso e)⟩

omit [NeZero (Nat.card G : K)] in
/-- An irreducible representation `τ` of positive degree occurs as a summand in any internal
irreducible decomposition of the left regular representation. Field-general (Schur's lemma over any
field, via `Representation.IsIrreducible.bijective_or_eq_zero`): we do **not** need `τ` to split.

The total intertwining dimension `Hom(leftRegular, τ) ≅ τ` is positive, and it splits as the sum of
the per-summand intertwining dimensions; positivity of the sum forces a nonzero intertwiner
`σ j → τ`, which Schur upgrades to an isomorphism. -/
private theorem exists_summand_equiv_of_isIrreducible
    {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (σ : ι → Subrepresentation (leftRegular K G))
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, IsIrreducibleLeftRegularSummand (σ i))
    (τ : Representation K G W)
    (hτ : τ.IsIrreducible)
    (hτ_pos : 0 < Module.finrank K W) :
    0 < Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv τ) } := by
  classical
  letI : τ.IsIrreducible := hτ
  letI : Finite ι :=
    finite_index_of_internal_irreducible_leftRegular_decomposition σ hinternal hσ
  letI : Fintype ι := Fintype.ofFinite ι
  let _ : ∀ i, AddCommGroup (σ i).toSubmodule := fun i ↦ inferInstance
  have hσ' : ∀ i, (σ i).toRepresentation.IsIrreducible := by
    intro i
    simpa [IsIrreducibleLeftRegularSummand] using hσ i
  -- The total intertwining dimension is positive and splits over the summands, so some summand
  -- has a positive-dimensional intertwining space with `τ`.
  have hsum_pos :
      0 < ∑ i, Module.finrank K (((σ i).toRepresentation).IntertwiningMap τ) := by
    have htotal :
        Module.finrank K ((leftRegular K G).IntertwiningMap τ) =
          ∑ i, Module.finrank K (((σ i).toRepresentation).IntertwiningMap τ) :=
      finrank_intertwiningMap_eq_sum_of_isInternal (leftRegular K G) σ hinternal τ
    have hleft : Module.finrank K ((leftRegular K G).IntertwiningMap τ) = Module.finrank K W :=
      leftRegular_intertwining_finrank_eq_degree τ
    rw [← htotal, hleft]
    exact hτ_pos
  -- Positivity of the sum forces a positive term.
  have hexists :
      ∃ i, 0 < Module.finrank K (((σ i).toRepresentation).IntertwiningMap τ) := by
    by_contra hcon
    push_neg at hcon
    have hzero : ∀ i, Module.finrank K (((σ i).toRepresentation).IntertwiningMap τ) = 0 := by
      intro i
      exact Nat.le_zero.mp (hcon i)
    have : (∑ i, Module.finrank K (((σ i).toRepresentation).IntertwiningMap τ)) = 0 := by
      simp [hzero]
    omega
  obtain ⟨i, hi_pos'⟩ := hexists
  -- A positive-dimensional intertwining space contains a nonzero intertwiner, which Schur turns
  -- into an isomorphism `σ i ≃ τ`.
  obtain ⟨f, hf⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp hi_pos'
  letI : (σ i).toRepresentation.IsIrreducible := hσ' i
  have hequiv : Nonempty ((σ i).toRepresentation.Equiv τ) :=
    ⟨f.ofBijective
      ((Representation.IsIrreducible.bijective_or_eq_zero
        (ρ := (σ i).toRepresentation) (σ := τ) f).resolve_right hf)⟩
  exact Nat.card_pos_iff.mpr ⟨⟨i, hequiv⟩, inferInstance⟩

end

/-! ### Main theorem -/

section

variable {G : Type u} [Group G] [Finite G]
variable {ι : Type u} [Fintype ι]
variable {K : Type u} [Field K] [NeZero (Nat.card G : K)]
variable (π : ι → FDRep K G)

/-- A finite complete pairwise nonisomorphic irreducible family has square-degree sum equal to the
group order, assuming `K` splits each member (one-dimensional self-intertwiner space). This is the
field-general version of
`Representation.sum_sq_degree_eq_card_of_complete_irreducible_family`, with `[IsAlgClosed K]`
replaced by the explicit splitting hypothesis `hsplit`. -/
theorem sum_sq_degree_eq_card_of_complete_irreducible_family_split
    (hπ_complete : Representation.IsCompleteIrreducibleFamily π)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hsplit : ∀ i, Module.finrank K (Representation.IntertwiningMap (π i).ρ (π i).ρ) = 1) :
    ∑ i : ι, Module.finrank K (π i) ^ 2 = Nat.card G := by
  classical
  obtain ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type u) (_ : Fintype κ) (σ : κ → Subrepresentation (leftRegular K G)),
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
    intro i i' hii
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨e'⟩
    have hiso : Nonempty (π i ≅ π i') := by
      refine ⟨?_⟩
      simpa using (e.symm.trans e').toFDRepIso
    exact hπ_pairwise hii hiso
  have hS_card (i : ι) : (S i).card = Module.finrank K (π i) := by
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
        (leftRegular_irreducible_multiplicity_eq_finrank_of_split
          σ hinternal hσ_irr (π i).ρ hπi_irreducible (hsplit i) :
            Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π i).ρ) } =
              Module.finrank K (π i))
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using hmult
  have hS_sum (i : ι) : Finset.sum (S i) dimσ = Module.finrank K (π i) ^ 2 := by
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
  have htotal_eq_card : ∑ j : κ, dimσ j = Nat.card G := by
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

/-- A finite pairwise nonisomorphic simple family whose square-degree sum is the group order is
complete, assuming `K` splits each member (one-dimensional self-intertwiner space). This is the
field-general version of
`Representation.isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card`, with `[IsAlgClosed K]`
replaced by the explicit splitting hypothesis `hsplit`.

The splitting hypothesis on the members `π i` enters exactly where the original used algebraic
closedness to compute the multiplicity of each `π i` in the left regular representation. For the
arbitrary simple target `τ` produced in the completeness step we do **not** need to split `τ`: only
positivity of its multiplicity is required, and that is supplied field-generally by Schur's lemma
(`exists_summand_equiv_of_isIrreducible`). -/
theorem isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card_split
    (hπ_simple : ∀ i, CategoryTheory.Simple (π i))
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hsplit : ∀ i, Module.finrank K (Representation.IntertwiningMap (π i).ρ (π i).ρ) = 1)
    (hπ_sum : ∑ i : ι, Module.finrank K (π i) ^ 2 = Nat.card G) :
    Representation.IsCompleteIrreducibleFamily π := by
  classical
  obtain ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type u) (_ : Fintype κ) (σ : κ → Subrepresentation (leftRegular K G)),
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
      (leftRegular_irreducible_multiplicity_eq_finrank_of_split
        σ hinternal hσ_irr (π i).ρ hπ_irreducible (hsplit i) :
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
  -- For the arbitrary simple target `τ` we only need positivity of its multiplicity, which Schur
  -- supplies over any field (no splitting hypothesis on `τ`).
  have hτ_count_pos : 0 < Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } := by
    exact
      exists_summand_equiv_of_isIrreducible σ hinternal hσ_irr τρ hτρ_irreducible hτ_pos
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

end

end SumSqSplit

end Representation

#print axioms Representation.SumSqSplit.sum_sq_degree_eq_card_of_complete_irreducible_family_split

#print axioms Representation.SumSqSplit.isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card_split
