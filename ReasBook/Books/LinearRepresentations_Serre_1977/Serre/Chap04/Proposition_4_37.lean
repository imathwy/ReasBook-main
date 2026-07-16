import LinearRepresentations_Serre_1977.Serre.Chap04.Proposition_4_34

noncomputable section

open scoped BigOperators MonoidAlgebra Representation

-- Semantic recall: `lean_leansearch` surfaced `isotypicComponent`, so this item keeps the
-- explicit matrix-coefficient projection API from Proposition 4-34 while referring to `V_i`
-- through the canonical isotypic component submodule.

universe u v w y

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V]
variable {Hπ : Type w} [NormedAddCommGroup Hπ] [InnerProductSpace ℂ Hπ]
  [FiniteDimensional ℂ Hπ]
variable {ι : Type y} [Fintype ι]

/-- The vectors `x_α := p_{α,α₀}^{(i)}(x₁)` attached to a chosen `x₁ ∈ V_{i,α₀}`. -/
def matrixCoefficientProjectionGeneratedVector
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V) (α : ι) : V :=
  p[ρ, π, b; α, α₀] x₁

/-- The `ℂ`-subspace spanned by the vectors `x_α := p_{α,α₀}^{(i)}(x₁)`. -/
def matrixCoefficientProjectionGeneratedSubspace
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V) : Submodule ℂ V :=
  Submodule.span ℂ <|
    Set.range (matrixCoefficientProjectionGeneratedVector ρ π b α₀ x₁)

/-- Helper: if `x₁ ∈ V_{i,α₀}`, then `x_α := p_{α,α₀}^{(i)}(x₁)` lies in `V_{i,α}`. -/
theorem matrixCoefficientProjectionGeneratedVector_mem_subspace
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; α₀])
    (α : ι) :
    matrixCoefficientProjectionGeneratedVector ρ π b α₀ x₁ α ∈ V[ρ, π, b; α] := by
  -- The generated vector is exactly `p_{α,α₀}^{(i)} x₁`, so Proposition 4-34 (7) applies.
  simpa [matrixCoefficientProjectionGeneratedVector] using
    matrixCoefficientProjection_mapsToSubspace ρ π b α α₀ x₁ hx₁_mem

/-- Helper for Proposition 4-37: the canonical intertwining map sends `b α` to the generated
vector `x_α`. -/
theorem matrixCoefficientProjectionIntertwiningMap_apply_basis
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ α : ι) (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; α₀]) :
    matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem (b α) =
      matrixCoefficientProjectionGeneratedVector ρ π b α₀ x₁ α := by
  -- Evaluating at a basis vector collapses the defining finite sum to the `α`-term.
  rw [matrixCoefficientProjectionGeneratedVector, matrixCoefficientProjectionIntertwiningMap_apply]
  rw [Finset.sum_eq_single α]
  · simp [b.repr_apply_apply]
  · intro β hβ hβα
    simp [b.repr_apply_apply, hβα]
  · intro hα
    exact (hα (Finset.mem_univ α)).elim

/-- Helper for Proposition 4-37: a nonzero vector in `V[ρ, π, b; α₀]` yields an injective
canonical intertwining map. -/
theorem matrixCoefficientProjectionIntertwiningMap_ker_eq_bot_of_mem_ne_zero
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; α₀])
    (hx₁_ne : x₁ ≠ 0) :
    ((matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem).toLinearMap).ker = ⊥ := by
  let f : π.IntertwiningMap ρ := matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem
  let x₁sub : V[ρ, π, b; α₀] := ⟨x₁, hx₁_mem⟩
  have hx₁sub_ne : x₁sub ≠ 0 := by
    -- The subtype version of `x₁` is still nonzero because its value is `x₁`.
    simpa [x₁sub] using hx₁_ne
  have himage_ne :
      matrixCoefficientProjectionSubspaceLinearEquiv ρ π b α₀ α₀ x₁sub ≠ 0 := by
    -- The diagonal projector acts by a linear equivalence on `V[ρ, π, b; α₀]`.
    intro hzero
    have hzero' :
        matrixCoefficientProjectionSubspaceLinearEquiv ρ π b α₀ α₀ x₁sub =
          matrixCoefficientProjectionSubspaceLinearEquiv ρ π b α₀ α₀ 0 := by
      simpa using hzero
    exact hx₁sub_ne ((matrixCoefficientProjectionSubspaceLinearEquiv ρ π b α₀ α₀).injective hzero')
  have hsubtype_ne :
      V[ρ, π, b; α₀].subtype (matrixCoefficientProjectionSubspaceLinearEquiv ρ π b α₀ α₀ x₁sub) ≠
        0 := by
    -- Passing to the ambient space preserves nontriviality for a subtype element.
    intro hzero
    apply himage_ne
    exact Subtype.ext hzero
  have hvalue_eq :
      V[ρ, π, b; α₀].subtype (matrixCoefficientProjectionSubspaceLinearEquiv ρ π b α₀ α₀ x₁sub) =
        matrixCoefficientProjectionGeneratedVector ρ π b α₀ x₁ α₀ := by
    -- The diagonal equivalence evaluates to `p_{α₀,α₀}^{(i)} x₁`.
    simpa [x₁sub, matrixCoefficientProjectionGeneratedVector] using
      matrixCoefficientProjectionSubspaceLinearEquiv_apply ρ π b α₀ α₀ x₁sub
  have hvalue_ne :
      matrixCoefficientProjectionGeneratedVector ρ π b α₀ x₁ α₀ ≠ 0 := by
    -- Forgetting the subtype identifies the image with the distinguished generated vector.
    rw [← hvalue_eq]
    exact hsubtype_ne
  have hf_ne : f ≠ 0 := by
    -- Evaluating `f` at `b α₀` detects the nonzero generated vector `x_{α₀}`.
    intro hf_zero
    have hf_eval_zero : f (b α₀) = 0 := by
      simpa using congrArg (fun g : π.IntertwiningMap ρ ↦ g (b α₀)) hf_zero
    apply hvalue_ne
    rw [← matrixCoefficientProjectionIntertwiningMap_apply_basis ρ π b α₀ α₀ x₁ hx₁_mem]
    simpa [f] using hf_eval_zero
  -- Irreducibility of `π` turns a nonzero intertwiner into an injective linear map.
  exact LinearMap.ker_eq_bot.2 <|
    (Representation.IsIrreducible.injective_or_eq_zero (ρ := π) (σ := ρ) f).resolve_right hf_ne

/-- Helper for Proposition 4-37: the generated vectors transform by the matrix coefficients of
`π`. -/
theorem map_matrixCoefficientProjectionGeneratedVector_of_mem
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; α₀])
    (s : G) (α : ι) :
    ρ s (matrixCoefficientProjectionGeneratedVector ρ π b α₀ x₁ α) =
      ∑ β, mc[π, b, β, α] s • matrixCoefficientProjectionGeneratedVector ρ π b α₀ x₁ β := by
  -- Rewrite the generated vector as the image of `b α` under the canonical intertwiner.
  have hintertw :=
    (matrixCoefficientProjectionLinearMap_isIntertwining ρ π b α₀ x₁ hx₁_mem).isIntertwining s (b α)
  calc
    ρ s (matrixCoefficientProjectionGeneratedVector ρ π b α₀ x₁ α)
        = ρ s (matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem (b α)) := by
            rw [matrixCoefficientProjectionIntertwiningMap_apply_basis ρ π b α₀ α x₁ hx₁_mem]
    _ = matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem (π s (b α)) := by
          simpa using hintertw.symm
    _ = ∑ β, (b.repr (π s (b α)) β) • p[ρ, π, b; β, α₀] x₁ := by
          rw [matrixCoefficientProjectionIntertwiningMap_apply]
    _ = ∑ β, mc[π, b, β, α] s • matrixCoefficientProjectionGeneratedVector ρ π b α₀ x₁ β := by
          refine Finset.sum_congr rfl ?_
          intro β hβ
          rw [b.repr_apply_apply, matrixCoefficient_eq_inner]
          rw [matrixCoefficientProjectionGeneratedVector]

omit [CompleteSpace V] [FiniteDimensional ℂ Hπ] in
/-- Helper for Proposition 4-37: the explicit linear map is the basis constructor on the family
`α ↦ x_α`. -/
theorem matrixCoefficientProjectionLinearMap_eq_basisConstr
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V) :
    matrixCoefficientProjectionLinearMap ρ π b α₀ x₁ =
      b.toBasis.constr ℂ (matrixCoefficientProjectionGeneratedVector ρ π b α₀ x₁) := by
  -- Both linear maps are determined by their values on the basis `b`.
  symm
  refine b.toBasis.constr_eq ℂ ?_
  intro α
  rw [matrixCoefficientProjectionGeneratedVector, matrixCoefficientProjectionLinearMap_apply]
  symm
  rw [Finset.sum_eq_single α]
  · simp [b.repr_apply_apply]
  · intro β hβ hβα
    simp [b.repr_apply_apply, hβα]
  · intro hα
    exact (hα (Finset.mem_univ α)).elim

section

variable [One ι]

/-- For Proposition 4-37, part (1): if `0 ≠ x₁ ∈ V_{i,1}` and
`x_α := p_{α,1}^{(i)}(x₁)`, then the family `(x_α)_α` is linearly independent. -/
theorem linearIndependent_matrixCoefficientProjectionGeneratedVector
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; (1 : ι)])
    (hx₁_ne : x₁ ≠ 0) :
    LinearIndependent ℂ (matrixCoefficientProjectionGeneratedVector ρ π b (1 : ι) x₁) := by
  -- Route correction: linear independence is proved through injectivity of the canonical
  -- intertwiner, not by a direct coefficient chase among the generators.
  have hker :=
    matrixCoefficientProjectionIntertwiningMap_ker_eq_bot_of_mem_ne_zero
      ρ π b (1 : ι) x₁ hx₁_mem hx₁_ne
  have hker_linear :
      (matrixCoefficientProjectionLinearMap ρ π b (1 : ι) x₁).ker = ⊥ := by
    simpa [matrixCoefficientProjectionIntertwiningMap_toLinearMap] using hker
  have hfamily :
      (fun α => matrixCoefficientProjectionLinearMap ρ π b (1 : ι) x₁ (b α)) =
        matrixCoefficientProjectionGeneratedVector ρ π b (1 : ι) x₁ := by
    -- The basis constructor sends each basis vector `b α` to the corresponding generator `x_α`.
    funext α
    rw [matrixCoefficientProjectionGeneratedVector, matrixCoefficientProjectionLinearMap_apply]
    rw [Finset.sum_eq_single α]
    · simp [b.repr_apply_apply]
    · intro β hβ hβα
      simp [b.repr_apply_apply, hβα]
    · intro hα
      exact (hα (Finset.mem_univ α)).elim
  -- Map the orthonormal basis through the injective linear map underlying the intertwiner.
  have hlin :
      LinearIndependent ℂ
        (fun α => matrixCoefficientProjectionLinearMap ρ π b (1 : ι) x₁ (b α)) := by
    simpa [Function.comp] using
      LinearIndependent.map' b.toBasis.linearIndependent
        (matrixCoefficientProjectionLinearMap ρ π b (1 : ι) x₁) hker_linear
  rw [hfamily] at hlin
  exact hlin

omit [One ι] in
/-- Helper: the span of the vectors `x_α := p_{α,α₀}^{(i)}(x₁)` is stable under `ρ`. -/
theorem matrixCoefficientProjectionGeneratedSubspace_stable_of_mem
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; α₀])
    (s : G) {v : V}
    (hv : v ∈ matrixCoefficientProjectionGeneratedSubspace ρ π b α₀ x₁) :
    ρ s v ∈ matrixCoefficientProjectionGeneratedSubspace ρ π b α₀ x₁ := by
  -- It suffices to check stability on the generating family `x_α`.
  refine Submodule.span_induction (fun v hv_range ↦ ?_) ?_ ?_ ?_ hv
  · rcases hv_range with ⟨α, rfl⟩
    rw [map_matrixCoefficientProjectionGeneratedVector_of_mem ρ π b α₀ x₁ hx₁_mem s α]
    refine Submodule.sum_mem _ ?_
    intro β hβ
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨β, rfl⟩)
  · simp [matrixCoefficientProjectionGeneratedSubspace]
  · intro v w hv hw hv_mem hw_mem
    simpa [map_add] using
      (matrixCoefficientProjectionGeneratedSubspace ρ π b α₀ x₁).add_mem hv_mem hw_mem
  · intro c v hv hv_mem
    simpa [map_smul] using
      (matrixCoefficientProjectionGeneratedSubspace ρ π b α₀ x₁).smul_mem c hv_mem

omit [One ι] in
/-- The `G`-stable subrepresentation generated by the vectors
`x_α := p_{α,α₀}^{(i)}(x₁)`. -/
def matrixCoefficientProjectionGeneratedSubrepresentation
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; α₀]) : Subrepresentation ρ :=
  (matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem).range

omit [One ι] in
/-- Proposition 4-37: the underlying submodule of the generated subrepresentation is the span of
the vectors `x_α := p_{α,α₀}^{(i)}(x₁)`. -/
theorem matrixCoefficientProjectionGeneratedSubrepresentation_toSubmodule_eq
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; α₀]) :
    (matrixCoefficientProjectionGeneratedSubrepresentation ρ π b α₀ x₁ hx₁_mem).toSubmodule =
      matrixCoefficientProjectionGeneratedSubspace ρ π b α₀ x₁ := by
  -- The generated subrepresentation is the range of the canonical intertwiner.
  rw [matrixCoefficientProjectionGeneratedSubrepresentation]
  rw [matrixCoefficientProjectionGeneratedSubspace]
  -- Normalize that range using the basis-constructor description of the underlying linear map.
  change
    LinearMap.range (matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem).toLinearMap =
    Submodule.span ℂ (Set.range (matrixCoefficientProjectionGeneratedVector ρ π b α₀ x₁))
  rw [matrixCoefficientProjectionIntertwiningMap_toLinearMap,
    matrixCoefficientProjectionLinearMap_eq_basisConstr]
  simpa using
    (Module.Basis.constr_range (b := b.toBasis) (S := ℂ)
      (f := matrixCoefficientProjectionGeneratedVector ρ π b α₀ x₁))

/- Helper: if `x₁ ∈ V_{i,α₀}`, then the generated span lies in the canonical `π`-isotypic
component. -/
omit [One ι] in theorem matrixCoefficientProjectionGeneratedSubspace_le_piIsotypicComponent_of_mem
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; α₀]) :
    matrixCoefficientProjectionGeneratedSubspace ρ π b α₀ x₁ ≤
      (ρ.moduleIsotypicComponent π).restrictScalars ℂ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨α, rfl⟩
  exact
    (matrixCoefficientProjectionSubspace_le_piIsotypicComponent ρ π b α)
      (matrixCoefficientProjectionGeneratedVector_mem_subspace ρ π b α₀ x₁ hx₁_mem α)

/-- For Proposition 4-37, part (3): if `x₁ ∈ V_{i,1}` and
`x_α := p_{α,1}^{(i)}(x₁)`, then the generated subspace `W(x₁)` lies in the
`π`-isotypic component `V_i`. -/
theorem matrixCoefficientProjectionGeneratedSubspace_le_piIsotypicComponent
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; (1 : ι)]) :
    matrixCoefficientProjectionGeneratedSubspace ρ π b (1 : ι) x₁ ≤
      (ρ.moduleIsotypicComponent π).restrictScalars ℂ := by
  simpa using
    matrixCoefficientProjectionGeneratedSubspace_le_piIsotypicComponent_of_mem
      ρ π b (1 : ι) x₁ hx₁_mem

/-- For Proposition 4-37, part (2): if `x₁ ∈ V_{i,1}` and
`x_α := p_{α,1}^{(i)}(x₁)`, then the generated subspace `W(x₁)` is `G`-stable under `ρ`. -/
theorem matrixCoefficientProjectionGeneratedSubspace_stable
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; (1 : ι)])
    (s : G) {v : V}
    (hv : v ∈ matrixCoefficientProjectionGeneratedSubspace ρ π b (1 : ι) x₁) :
    ρ s v ∈ matrixCoefficientProjectionGeneratedSubspace ρ π b (1 : ι) x₁ :=
  matrixCoefficientProjectionGeneratedSubspace_stable_of_mem ρ π b (1 : ι) x₁ hx₁_mem s hv

/-- For Proposition 4-37, part (4): if `0 ≠ x₁ ∈ V_{i,1}` and
`x_α := p_{α,1}^{(i)}(x₁)`, then the generated stable subspace `W(x₁)` has dimension
`n_i = Module.finrank ℂ Hπ`. -/
theorem finrank_matrixCoefficientProjectionGeneratedSubrepresentation
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; (1 : ι)])
    (hx₁_ne : x₁ ≠ 0) :
    Module.finrank ℂ (matrixCoefficientProjectionGeneratedSubspace ρ π b (1 : ι) x₁) =
      Module.finrank ℂ Hπ := by
  have hlin :=
    linearIndependent_matrixCoefficientProjectionGeneratedVector ρ π b x₁ hx₁_mem hx₁_ne
  -- The generated subspace is the span of a linearly independent family indexed by `ι`.
  calc
    Module.finrank ℂ (matrixCoefficientProjectionGeneratedSubspace ρ π b (1 : ι) x₁)
        = Fintype.card ι := by
            simpa [matrixCoefficientProjectionGeneratedSubspace] using
              (finrank_span_eq_card (R := ℂ)
                (b := matrixCoefficientProjectionGeneratedVector ρ π b (1 : ι) x₁) hlin)
    _ = Module.finrank ℂ Hπ := by
          simpa using (Module.finrank_eq_card_basis b.toBasis).symm

/-- For Proposition 4-37, part (5): if `x₁ ∈ V_{i,1}` and
`x_α := p_{α,1}^{(i)}(x₁)`, then for every `s ∈ G`,
`ρ s x_α = ∑ β, mc[π, b, β, α] s • x_β`. -/
theorem map_matrixCoefficientProjectionGeneratedVector
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; (1 : ι)])
    (s : G) (α : ι) :
    ρ s (matrixCoefficientProjectionGeneratedVector ρ π b (1 : ι) x₁ α) =
      ∑ β, mc[π, b, β, α] s • matrixCoefficientProjectionGeneratedVector ρ π b (1 : ι) x₁ β :=
  by
  -- Specialize the general equivariance formula to the distinguished index `(1 : ι)`.
  simpa using
    map_matrixCoefficientProjectionGeneratedVector_of_mem
      ρ π b (1 : ι) x₁ hx₁_mem s α

/-- For Proposition 4-37, part (6): if `0 ≠ x₁ ∈ V_{i,1}` and
`x_α := p_{α,1}^{(i)}(x₁)`, then the generated stable subrepresentation `W(x₁)` is equivalent
to `π`. -/
theorem matrixCoefficientProjectionGeneratedSubrepresentation_nonempty_equiv
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; (1 : ι)])
    (hx₁_ne : x₁ ≠ 0) :
    Nonempty
      (π.Equiv
        (matrixCoefficientProjectionGeneratedSubrepresentation
          ρ π b (1 : ι) x₁ hx₁_mem).toRepresentation) := by
  simpa [matrixCoefficientProjectionGeneratedSubrepresentation] using
    matrixCoefficientProjectionIntertwiningMap_range_nonempty_equiv
      ρ π b (1 : ι) x₁ hx₁_mem hx₁_ne

end

end

end Representation
