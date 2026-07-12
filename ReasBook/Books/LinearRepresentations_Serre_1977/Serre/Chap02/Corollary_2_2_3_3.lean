import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w u₁ u₂ u₃

namespace Representation

noncomputable section

section

open CategoryTheory
open scoped Representation
open scoped MonoidAlgebra

variable {G : Type u} [Group G] [Finite G]
variable {K : Type u₁} [Field K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

local instance (α : Type*) [Finite α] : DecidableEq α :=
  Classical.decEq α

-- Source/core/bridge triage:
-- * source-facing: the decomposition-independent multiplicity statement below.
-- * core/canonical: `Representation.IntertwiningMap` via the owner theorem
--   `card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`.
-- * bridge/view: the internal direct-sum decompositions `σ₁`, `σ₂`.
--
-- Proof sketch: when `τ` is irreducible, apply the canonical multiplicity owner theorem to each
-- decomposition and compare both counts with the same invariant
-- `Module.finrank K (ρ.IntertwiningMap τ)`. If `τ` is not irreducible, then no irreducible
-- summand can be equivalent to `τ`, so both counted subtypes are empty.
omit [Finite G] [IsAlgClosed K] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: irreducibility is preserved by an equivalence of
representations. -/
private theorem isIrreducible_of_equiv
    {V' : Type*} [AddCommGroup V'] [Module K V']
    {W' : Type*} [AddCommGroup W'] [Module K W']
    {ρ : Representation K G V'} {σ : Representation K G W'}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) :
    σ.IsIrreducible := by
  letI : Module K[G] V' := ρ.instModuleMonoidAlgebraAsModule
  letI : Module K[G] W' := σ.instModuleMonoidAlgebraAsModule
  -- Translate irreducibility to simplicity over the group ring.
  have hρsimple : IsSimpleModule K[G] V' := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  -- Transport simplicity through the `K[G]`-linear equivalence induced by `e`.
  let eAsModule : V' ≃ₗ[K[G]] W' :=
    LinearEquiv.ofBijective
      (show V' →ₗ[K[G]] W' from
        (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := σ))
          e.toIntertwiningMap)
      (show Function.Bijective
          (((Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := σ))
            e.toIntertwiningMap) : V' → W') from
        e.toLinearEquiv.bijective)
  have hσsimple : IsSimpleModule K[G] W' :=
    (LinearEquiv.isSimpleModule_iff eAsModule).mp hρsimple
  -- Translate back to irreducibility of the target representation.
  simpa using (Representation.irreducible_iff_isSimpleModule_asModule σ).mpr hσsimple

omit [Finite G] [IsAlgClosed K] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: any representation equivalent to an irreducible one is
irreducible. -/
private theorem isIrreducible_of_nonempty_rep_equiv
    {V' : Type*} [AddCommGroup V'] [Module K V']
    {W' : Type*} [AddCommGroup W'] [Module K W']
    {ρ : Representation K G V'} {σ : Representation K G W'}
    [ρ.IsIrreducible] (h : Nonempty (ρ.Equiv σ)) :
    σ.IsIrreducible := by
  -- Unpack the equivalence witness and transport irreducibility along it.
  rcases h with ⟨e⟩
  exact isIrreducible_of_equiv e

omit [Finite G] [IsAlgClosed K] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: an irreducible representation cannot be equivalent to a
reducible one. -/
private theorem not_nonempty_rep_equiv_of_isIrreducible_of_not_isIrreducible
    {V' : Type*} [AddCommGroup V'] [Module K V']
    {W' : Type*} [AddCommGroup W'] [Module K W']
    {ρ : Representation K G V'} {σ : Representation K G W'}
    (hρ : ρ.IsIrreducible) (hσ : ¬ σ.IsIrreducible) :
    ¬ Nonempty (ρ.Equiv σ) := by
  -- Any equivalence would transport irreducibility from `ρ` to `σ`.
  intro h
  letI : ρ.IsIrreducible := hρ
  exact hσ (isIrreducible_of_nonempty_rep_equiv h)

omit [Finite G] [IsAlgClosed K] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: if the target representation is not irreducible, then the
summand indices carrying an equivalent representation form an empty type. -/
private theorem isEmpty_isomorphic_irreducible_summands_of_not_isIrreducible
    {ι : Type*} [Finite ι] {V' : Type*} [AddCommGroup V'] [Module K V']
    (ρ : Representation K G V')
    (σ : ι → Subrepresentation ρ)
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    {W' : Type*} [AddCommGroup W'] [Module K W']
    (τ : Representation K G W')
    (hτ : ¬ τ.IsIrreducible) :
    IsEmpty { i // Nonempty ((σ i).toRepresentation.Equiv τ) } := by
  -- Any witness would contradict the incompatibility between irreducibility and reducibility.
  refine ⟨fun i ↦ ?_⟩
  exact
    not_nonempty_rep_equiv_of_isIrreducible_of_not_isIrreducible
      (hσ i.1) hτ i.2

omit [Finite G] [IsAlgClosed K] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: if the target representation is not irreducible, then no
irreducible summand in a decomposition can be equivalent to it, so the counted subtype has
cardinality zero. -/
private theorem nat_card_isomorphic_irreducible_summands_eq_zero_of_not_isIrreducible
    {ι : Type*} [Finite ι] {V' : Type*} [AddCommGroup V'] [Module K V']
    (ρ : Representation K G V')
    (σ : ι → Subrepresentation ρ)
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    {W' : Type*} [AddCommGroup W'] [Module K W']
    (τ : Representation K G W')
    (hτ : ¬ τ.IsIrreducible) :
    Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv τ) } = 0 := by
  -- First show the witness type is empty, then read off its cardinality.
  letI : IsEmpty { i // Nonempty ((σ i).toRepresentation.Equiv τ) } :=
    isEmpty_isomorphic_irreducible_summands_of_not_isIrreducible ρ σ hσ τ hτ
  exact Nat.card_of_isEmpty

omit [Finite G] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: when the target representation is irreducible, the number of
isomorphic irreducible summands in a fixed decomposition is the finrank of the intertwining
space. -/
private theorem nat_card_isomorphic_irreducible_summands_eq_finrank_of_isIrreducible
    {ι : Type*} [Finite ι] {V' : Type*} [AddCommGroup V'] [Module K V']
    [FiniteDimensional K V']
    (ρ : Representation K G V')
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    {W' : Type*} [AddCommGroup W'] [Module K W'] [FiniteDimensional K W']
    (τ : Representation K G W')
    (hτ : τ.IsIrreducible) :
    Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv τ) } =
      Module.finrank K (ρ.IntertwiningMap τ) := by
  -- This is exactly the owner multiplicity theorem from Theorem 2-2.3-2.
  simpa using
    card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
      ρ σ hinternal hσ τ hτ

omit [Finite G] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-3: when `τ` is irreducible, two irreducible decompositions of `ρ`
have the same number of summands equivalent to `τ` because both counts equal the same
intertwining-space dimension. -/
private theorem card_isomorphic_irreducible_summands_eq_of_two_decompositions_of_isIrreducible
    {ι₁ : Type u₂} [Finite ι₁] {ι₂ : Type u₃} [Finite ι₂]
    (ρ : Representation K G V)
    (σ₁ : ι₁ → Subrepresentation ρ)
    (hinternal₁ : DirectSum.IsInternal (fun i ↦ (σ₁ i).toSubmodule))
    (hσ₁ : ∀ i, (σ₁ i).toRepresentation.IsIrreducible)
    (σ₂ : ι₂ → Subrepresentation ρ)
    (hinternal₂ : DirectSum.IsInternal (fun i ↦ (σ₂ i).toSubmodule))
    (hσ₂ : ∀ i, (σ₂ i).toRepresentation.IsIrreducible)
    (τ : Representation K G W)
    (hτ : τ.IsIrreducible) :
    Nat.card { i // Nonempty ((σ₁ i).toRepresentation.Equiv τ) } =
      Nat.card { i // Nonempty ((σ₂ i).toRepresentation.Equiv τ) } := by
  -- Compare both decomposition counts through the same canonical intertwining-space invariant.
  calc
    Nat.card { i // Nonempty ((σ₁ i).toRepresentation.Equiv τ) } =
        Module.finrank K (ρ.IntertwiningMap τ) := by
      exact
        nat_card_isomorphic_irreducible_summands_eq_finrank_of_isIrreducible
          ρ σ₁ hinternal₁ hσ₁ τ hτ
    _ = Nat.card { i // Nonempty ((σ₂ i).toRepresentation.Equiv τ) } := by
      symm
      exact
        nat_card_isomorphic_irreducible_summands_eq_finrank_of_isIrreducible
          ρ σ₂ hinternal₂ hσ₂ τ hτ

omit [Finite G] [IsAlgClosed K] [Invertible (Nat.card G : K)]
  [FiniteDimensional K V] [FiniteDimensional K W] in
/-- Helper for Corollary 2-2.3-3: when `τ` is not irreducible, no irreducible summand from either
decomposition can be equivalent to `τ`, so both multiplicity counts vanish. -/
private theorem card_isomorphic_irreducible_summands_eq_of_two_decompositions_of_not_isIrreducible
    {ι₁ : Type u₂} [Finite ι₁] {ι₂ : Type u₃} [Finite ι₂]
    (ρ : Representation K G V)
    (σ₁ : ι₁ → Subrepresentation ρ)
    (hσ₁ : ∀ i, (σ₁ i).toRepresentation.IsIrreducible)
    (σ₂ : ι₂ → Subrepresentation ρ)
    (hσ₂ : ∀ i, (σ₂ i).toRepresentation.IsIrreducible)
    (τ : Representation K G W)
    (hτ : ¬ τ.IsIrreducible) :
    Nat.card { i // Nonempty ((σ₁ i).toRepresentation.Equiv τ) } =
      Nat.card { i // Nonempty ((σ₂ i).toRepresentation.Equiv τ) } := by
  have hzero₁ :
      Nat.card { i // Nonempty ((σ₁ i).toRepresentation.Equiv τ) } = 0 :=
    nat_card_isomorphic_irreducible_summands_eq_zero_of_not_isIrreducible ρ σ₁ hσ₁ τ hτ
  have hzero₂ :
      Nat.card { i // Nonempty ((σ₂ i).toRepresentation.Equiv τ) } = 0 :=
    nat_card_isomorphic_irreducible_summands_eq_zero_of_not_isIrreducible ρ σ₂ hσ₂ τ hτ
  -- Compare both sides through the common zero value forced by reducibility of `τ`.
  calc
    Nat.card { i // Nonempty ((σ₁ i).toRepresentation.Equiv τ) } = 0 := hzero₁
    _ = Nat.card { i // Nonempty ((σ₂ i).toRepresentation.Equiv τ) } := hzero₂.symm

omit [Finite G] [Invertible (Nat.card G : K)] in
/-- Corollary 2-2.3-3: for a finite-dimensional representation `τ`, the number of irreducible
summands of a decomposition of `ρ` that are isomorphic to `τ` is independent of the chosen
decomposition. In particular, when `τ` is irreducible this common value is the multiplicity of
`τ` in `ρ`. -/
theorem card_isomorphic_irreducible_summands_eq_of_two_decompositions
    {ι₁ : Type u₂} [Finite ι₁] {ι₂ : Type u₃} [Finite ι₂]
    (ρ : Representation K G V)
    (σ₁ : ι₁ → Subrepresentation ρ)
    (hinternal₁ : DirectSum.IsInternal (fun i ↦ (σ₁ i).toSubmodule))
    (hσ₁ : ∀ i, (σ₁ i).toRepresentation.IsIrreducible)
    (σ₂ : ι₂ → Subrepresentation ρ)
    (hinternal₂ : DirectSum.IsInternal (fun i ↦ (σ₂ i).toSubmodule))
    (hσ₂ : ∀ i, (σ₂ i).toRepresentation.IsIrreducible)
    (τ : Representation K G W) :
    Nat.card { i // Nonempty ((σ₁ i).toRepresentation.Equiv τ) } =
      Nat.card { i // Nonempty ((σ₂ i).toRepresentation.Equiv τ) } := by
  classical
  by_cases hτ : τ.IsIrreducible
  · -- In the irreducible branch, reduce immediately to the common intertwining-space dimension.
    exact
      card_isomorphic_irreducible_summands_eq_of_two_decompositions_of_isIrreducible
        ρ σ₁ hinternal₁ hσ₁ σ₂ hinternal₂ hσ₂ τ hτ
  · -- In the reducible branch, reduce immediately to the common zero multiplicity.
    exact
      card_isomorphic_irreducible_summands_eq_of_two_decompositions_of_not_isIrreducible
        ρ σ₁ hσ₁ σ₂ hσ₂ τ hτ

end

end

end Representation
