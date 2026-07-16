import LinearRepresentations_Serre_1977.Serre.Chap02.Exercise_2_2_6_3
import LinearRepresentations_Serre_1977.Serre.Chap04.Lemma_4_22
import LinearRepresentations_Serre_1977.Serre.Chap04.Proposition_4_27
import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_33

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace MonoidAlgebra Representation

-- Semantic recall: `lean_leansearch` only surfaced character-orthogonality results, so this
-- source-facing item uses the explicit averaged matrix-coefficient operators from Lemma 4-22
-- together with the averaging operator owner from Proposition 4-27.

universe u v w x y z

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V]
variable {Hπ : Type w} [NormedAddCommGroup Hπ] [InnerProductSpace ℂ Hπ]
  [FiniteDimensional ℂ Hπ]
variable {ι : Type y} [Fintype ι]

/-- The matrix-coefficient projector `p_{αβ}^{(i)}` attached to `π`, `b`, and the indices
`α`, `β`. It is the averaged operator
`n_i ∫ t, conj (r_{αβ}^{(i)} t) • ρ t`, where `n_i = Module.finrank ℂ Hπ`. -/
def matrixCoefficientProjection
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) (b : OrthonormalBasis ι ℂ Hπ)
    (α β : ι) : V →L[ℂ] V :=
  classFunctionAveragedEndomorphism ρ
    (fun t ↦ (Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, α, β] t))

/- Source-facing notation for the projector `p_{αβ}^{(i)}` attached to `ρ`, `π`, and `b`. -/
scoped notation:max "p[" ρ ", " π ", " b "; " α ", " β "]" =>
  matrixCoefficientProjection ρ π b α β

/-- The subspace `V_{i,α}` cut out by the diagonal projector `p_{αα}^{(i)}`. -/
def matrixCoefficientProjectionSubspace
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) (b : OrthonormalBasis ι ℂ Hπ)
    (α : ι) : Submodule ℂ V :=
  LinearMap.range (p[ρ, π, b; α, α]).toLinearMap

/- Source-facing notation for the subspace `V_{i,α}` cut out by `p_{αα}^{(i)}`. -/
scoped notation:max "V[" ρ ", " π ", " b "; " α "]" =>
  matrixCoefficientProjectionSubspace ρ π b α

omit [CompleteSpace V] [FiniteDimensional ℂ Hπ] in
/-- Helper: membership in `V[ρ, π, b; α]` is equivalent to being in the image of the diagonal
matrix-coefficient projector `p_{αα}^{(i)}`. -/
@[simp] theorem mem_matrixCoefficientProjectionSubspace_iff
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) (b : OrthonormalBasis ι ℂ Hπ)
    (α : ι) (v : V) :
    v ∈ V[ρ, π, b; α] ↔ ∃ w : V, p[ρ, π, b; α, α] w = v := Iff.rfl

/-- The explicit linear map `Hπ →ₗ[ℂ] V` attached to `x₁ ∈ V_{i,α₀}` in Proposition 4-34 (1),
with value
`v ↦ ∑ α, (b.repr v α) • p_{α,α₀}^{(i)} x₁`. -/
def matrixCoefficientProjectionLinearMap
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V) : Hπ →ₗ[ℂ] V where
  toFun v := ∑ α, (b.repr v α) • p[ρ, π, b; α, α₀] x₁
  map_add' v w := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    have hrepr : b.repr (c • v) = c • b.repr v := by
      ext α
      simp
    rw [hrepr]
    simp [Finset.smul_sum, mul_smul]

omit [CompleteSpace V] [FiniteDimensional ℂ Hπ] in
/-- Evaluating `matrixCoefficientProjectionLinearMap` gives the explicit finite sum from
Proposition 4-34 (1). -/
@[simp] theorem matrixCoefficientProjectionLinearMap_apply
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V) (v : Hπ) :
    matrixCoefficientProjectionLinearMap ρ π b α₀ x₁ v =
      ∑ α, (b.repr v α) • p[ρ, π, b; α, α₀] x₁ :=
  rfl

-- Route correction: several downstream clauses of Proposition 4-34 use the matrix-unit relation,
-- so the compact-group proof first builds the projector action/composition interface.

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [FiniteDimensional ℂ Hπ] in
/-- Helper for Proposition 4-34: the matrix coefficient `mc[π, b, i, j]` is continuous when `π`
is continuous. -/
private theorem matrixCoefficient_continuous
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (b : OrthonormalBasis ι ℂ Hπ) (i j : ι) :
    Continuous (mc[π, b, i, j]) := by
  -- Rewrite the coefficient as one fixed inner product against the orbit map of `b j`.
  have hmc : mc[π, b, i, j] = fun t ↦ inner ℂ (b i) (π t (b j)) := by
    funext t
    rw [matrixCoefficient_eq_inner]
  rw [hmc]
  simpa [Function.comp] using
    (innerSL ℂ (b i)).continuous.comp (Representation.continuous_apply π (b j))

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [FiniteDimensional ℂ Hπ] in
/-- Helper for Proposition 4-34: the scalar weight defining `p[ρ, π, b; α, β]` is continuous. -/
private theorem matrixCoefficientProjectionWeight_continuous
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (b : OrthonormalBasis ι ℂ Hπ) (α β : ι) :
    Continuous fun t ↦ (Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, α, β] t) := by
  -- Combine continuity of matrix coefficients with continuity of complex conjugation.
  simpa using
    (continuous_const.mul <|
      Complex.continuous_conj.comp (matrixCoefficient_continuous π b α β))

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G] in
/-- Helper for Proposition 4-34: conjugating `mc[π, b, γ, δ] (s⁻¹ * t)` expands along the first
index using the basis coordinates of `π s (b γ)`. -/
private theorem conj_matrixCoefficient_mul_left_inv
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (s t : G) (γ δ : ι) :
    conj (mc[π, b, γ, δ] (s⁻¹ * t)) =
      ∑ η, mc[π, b, η, γ] s * conj (mc[π, b, η, δ] t) := by
  -- Move `π s` across the inner product using unitarity.
  have hmove :
      ⟪π s⁻¹ (π t (b δ)), b γ⟫_ℂ = ⟪π t (b δ), π s (b γ)⟫_ℂ := by
    let e : Hπ →ₗᵢ[ℂ] Hπ := (π s).toLinearIsometry (Representation.isometry π s)
    have hs : e (π s⁻¹ (π t (b δ))) = π t (b δ) := by
      change π s (π s⁻¹ (π t (b δ))) = π t (b δ)
      exact (π.toContinuousLinearEquivHom s).apply_symm_apply (π t (b δ))
    have hγ : e (b γ) = π s (b γ) := by
      rfl
    calc
      ⟪π s⁻¹ (π t (b δ)), b γ⟫_ℂ
          = ⟪e (π s⁻¹ (π t (b δ))), e (b γ)⟫_ℂ := by
              symm
              exact LinearIsometry.inner_map_map e (π s⁻¹ (π t (b δ))) (b γ)
      _ = ⟪π t (b δ), e (b γ)⟫_ℂ := by
            simp [hs]
      _ = ⟪π t (b δ), π s (b γ)⟫_ℂ := by
            rw [hγ]
  -- Expand the resulting inner product along the orthonormal basis `b`.
  calc
    conj (mc[π, b, γ, δ] (s⁻¹ * t)) = ⟪π (s⁻¹ * t) (b δ), b γ⟫_ℂ := by
      rw [matrixCoefficient_eq_inner, inner_conj_symm]
    _ = ⟪π s⁻¹ (π t (b δ)), b γ⟫_ℂ := by
          simp [map_mul]
    _ = ⟪π t (b δ), π s (b γ)⟫_ℂ := hmove
    _ = ∑ η, ⟪π t (b δ), b η⟫_ℂ * ⟪b η, π s (b γ)⟫_ℂ := by
          symm
          simpa using OrthonormalBasis.sum_inner_mul_inner b (π t (b δ)) (π s (b γ))
    _ = ∑ η, mc[π, b, η, γ] s * conj (mc[π, b, η, δ] t) := by
          refine Finset.sum_congr rfl ?_
          intro η hη
          rw [matrixCoefficient_eq_inner, matrixCoefficient_eq_inner, inner_conj_symm]
          ring

/-- Helper for Proposition 4-34: left-translation of `p[ρ, π, b; γ, δ]` expands along the first
index with the matrix coefficients of `π s`. -/
private theorem matrixCoefficientProjection_leftActionExpansion
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (s : G) (γ δ : ι) (v : V) :
    ρ s (p[ρ, π, b; γ, δ] v) =
      ∑ η, mc[π, b, η, γ] s • p[ρ, π, b; η, δ] v := by
  let f : G → ℂ := fun t ↦ (Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, γ, δ] t)
  have hf_cont : Continuous f := matrixCoefficientProjectionWeight_continuous π b γ δ
  have hIntTerm (η : ι) :
      MeasureTheory.Integrable
        (fun t ↦ mc[π, b, η, γ] s •
          (((Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, η, δ] t)) • ρ t v)) μG := by
    have hcont :
        Continuous (fun t ↦ mc[π, b, η, γ] s •
          (((Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, η, δ] t)) • ρ t v)) := by
      exact continuous_const.smul <|
        (matrixCoefficientProjectionWeight_continuous π b η δ).smul
          (Representation.continuous_apply ρ v)
    have hIntOn :
        MeasureTheory.IntegrableOn
          (fun t ↦ mc[π, b, η, γ] s •
            (((Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, η, δ] t)) • ρ t v))
          Set.univ μG := by
      exact ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ hcont.continuousOn
    simpa [MeasureTheory.integrableOn_univ] using hIntOn
  -- Translate the Haar integral by `t ↦ s⁻¹ * t` before expanding the coefficient.
  calc
    ρ s (p[ρ, π, b; γ, δ] v) = ρ s (∫ t, f t • ρ t v ∂μG) := by
      rw [matrixCoefficientProjection, classFunctionAveragedEndomorphism_apply ρ f hf_cont]
    _ = ρ s (∫ t, f (s⁻¹ * t) • ρ (s⁻¹ * t) v ∂μG) := by
          congr 1
          simpa [f] using
            (MeasureTheory.integral_mul_left_eq_self (μ := (normalizedHaarMeasure : Measure G))
              (fun t ↦ f t • ρ t v) s⁻¹).symm
    _ = ∫ t, ρ s (f (s⁻¹ * t) • ρ (s⁻¹ * t) v) ∂μG := by
          symm
          simpa [Representation.toContinuousLinearEquivHom_apply_apply] using
            (ContinuousLinearEquiv.integral_comp_comm (ρ.toContinuousLinearEquivHom s)
              (fun t ↦ f (s⁻¹ * t) • ρ (s⁻¹ * t) v))
    _ = ∫ t, f (s⁻¹ * t) • ρ t v ∂μG := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with t
          simp [f, map_mul]
    _ = ∫ t, ∑ η, mc[π, b, η, γ] s •
          (((Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, η, δ] t)) • ρ t v) ∂μG := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with t
          calc
            f (s⁻¹ * t) • ρ t v
                = (((Module.finrank ℂ Hπ : ℂ) *
                    ∑ η, mc[π, b, η, γ] s * conj (mc[π, b, η, δ] t))) • ρ t v := by
                      rw [show f (s⁻¹ * t) =
                        (Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, γ, δ] (s⁻¹ * t)) by
                        rfl]
                      rw [conj_matrixCoefficient_mul_left_inv π b s t γ δ]
            _ = (∑ η,
                  ((Module.finrank ℂ Hπ : ℂ) *
                    (mc[π, b, η, γ] s * conj (mc[π, b, η, δ] t)))) • ρ t v := by
                    rw [Finset.mul_sum]
            _ = ∑ η, mc[π, b, η, γ] s •
                  (((Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, η, δ] t)) • ρ t v) := by
                    rw [Finset.sum_smul]
                    refine Finset.sum_congr rfl ?_
                    intro η hη
                    simp [smul_smul, mul_left_comm]
    _ = ∑ η, mc[π, b, η, γ] s •
          ∫ t, ((Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, η, δ] t)) • ρ t v ∂μG := by
          rw [MeasureTheory.integral_finset_sum Finset.univ (fun η _ ↦ hIntTerm η)]
          refine Finset.sum_congr rfl ?_
          intro η hη
          rw [MeasureTheory.integral_smul]
    _ = ∑ η, mc[π, b, η, γ] s • p[ρ, π, b; η, δ] v := by
          refine Finset.sum_congr rfl ?_
          intro η hη
          rw [matrixCoefficientProjection, classFunctionAveragedEndomorphism_apply ρ
            (fun t ↦ (Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, η, δ] t))
            (matrixCoefficientProjectionWeight_continuous π b η δ)]

omit [FiniteDimensional ℂ Hπ] in
/-- Helper for Proposition 4-34: composing two matrix-coefficient projectors first expands into
one `η`-sum whose coefficients are the orthogonality integrals from Lemma 4-22. -/
private theorem matrixCoefficientProjection_compExpansion
    {Hσ : Type x} [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ] [FiniteDimensional ℂ Hσ]
    {ισ : Type z} [Fintype ισ]
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsUnitary π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ] [Representation.IsUnitary σ]
    (bπ : OrthonormalBasis ι ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (α β : ι) (γ δ : ισ) :
    (p[ρ, π, bπ; α, β]).comp (p[ρ, σ, bσ; γ, δ]) =
      ∑ η : ισ,
        (((Module.finrank ℂ Hπ : ℂ) *
            ∫ t, mc[σ, bσ, η, γ] t * conj (mc[π, bπ, α, β] t) ∂μG)) •
          p[ρ, σ, bσ; η, δ] := by
  let fπ : G → ℂ := fun t ↦ (Module.finrank ℂ Hπ : ℂ) * conj (mc[π, bπ, α, β] t)
  have hfπ_cont : Continuous fπ := matrixCoefficientProjectionWeight_continuous π bπ α β
  ext v
  have hIntTerm (η : ισ) :
      MeasureTheory.Integrable
        (fun t ↦ (fπ t * mc[σ, bσ, η, γ] t) • p[ρ, σ, bσ; η, δ] v) μG := by
    have hcont :
        Continuous (fun t ↦ (fπ t * mc[σ, bσ, η, γ] t) • p[ρ, σ, bσ; η, δ] v) := by
      exact (hfπ_cont.mul (matrixCoefficient_continuous σ bσ η γ)).smul continuous_const
    have hIntOn :
        MeasureTheory.IntegrableOn
          (fun t ↦ (fπ t * mc[σ, bσ, η, γ] t) • p[ρ, σ, bσ; η, δ] v)
          Set.univ μG := by
      exact ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ hcont.continuousOn
    simpa [MeasureTheory.integrableOn_univ] using hIntOn
  -- Expand the outer projector and normalize the inner action term first at the value level.
  calc
    ((p[ρ, π, bπ; α, β]).comp (p[ρ, σ, bσ; γ, δ])) v
      = p[ρ, π, bπ; α, β] (p[ρ, σ, bσ; γ, δ] v) := by
          rfl
    _ = ∫ t, fπ t • ρ t (p[ρ, σ, bσ; γ, δ] v) ∂μG := by
          rw [matrixCoefficientProjection, classFunctionAveragedEndomorphism_apply ρ fπ hfπ_cont]
    _ = ∫ t, ∑ η : ισ,
          (fπ t * mc[σ, bσ, η, γ] t) • p[ρ, σ, bσ; η, δ] v ∂μG := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with t
          rw [matrixCoefficientProjection_leftActionExpansion ρ σ bσ t γ δ v]
          calc
            fπ t • ∑ η : ισ, mc[σ, bσ, η, γ] t • p[ρ, σ, bσ; η, δ] v
              = ∑ η : ισ, fπ t • (mc[σ, bσ, η, γ] t • p[ρ, σ, bσ; η, δ] v) := by
                  exact Finset.smul_sum
            _ = ∑ η : ισ,
                  (fπ t * mc[σ, bσ, η, γ] t) • p[ρ, σ, bσ; η, δ] v := by
                    refine Finset.sum_congr rfl ?_
                    intro η hη
                    simp [smul_smul]
    _ = ∑ η : ισ,
          ∫ t, (fπ t * mc[σ, bσ, η, γ] t) • p[ρ, σ, bσ; η, δ] v ∂μG := by
          rw [MeasureTheory.integral_finset_sum Finset.univ (fun η _ ↦ hIntTerm η)]
    _ = ∑ η : ισ,
          (∫ t, fπ t * mc[σ, bσ, η, γ] t ∂μG) • p[ρ, σ, bσ; η, δ] v := by
          refine Finset.sum_congr rfl ?_
          intro η hη
          rw [integral_smul_const]
          rfl
    _ = ∑ η : ισ,
          (((Module.finrank ℂ Hπ : ℂ) *
              ∫ t, mc[σ, bσ, η, γ] t * conj (mc[π, bπ, α, β] t) ∂μG)) •
            p[ρ, σ, bσ; η, δ] v := by
          refine Finset.sum_congr rfl ?_
          intro η hη
          congr 1
          -- Pull the constant dimension factor out of the scalar integral.
          calc
            ∫ t, fπ t * mc[σ, bσ, η, γ] t ∂μG
              = ∫ t, ((Module.finrank ℂ Hπ : ℂ) *
                  (conj (mc[π, bπ, α, β] t) * mc[σ, bσ, η, γ] t)) ∂μG := by
                    refine MeasureTheory.integral_congr_ae ?_
                    filter_upwards with t
                    simp [fπ]
                    ring
            _ = (Module.finrank ℂ Hπ : ℂ) *
                ∫ t, conj (mc[π, bπ, α, β] t) * mc[σ, bσ, η, γ] t ∂μG := by
                  simpa using
                    (MeasureTheory.integral_const_mul (μ := μG)
                      (Module.finrank ℂ Hπ : ℂ)
                      (fun t ↦ conj (mc[π, bπ, α, β] t) * mc[σ, bσ, η, γ] t))
            _ = (Module.finrank ℂ Hπ : ℂ) *
                ∫ t, mc[σ, bσ, η, γ] t * conj (mc[π, bπ, α, β] t) ∂μG := by
                  congr 1
                  refine MeasureTheory.integral_congr_ae ?_
                  filter_upwards with t
                  ring
    _ = (∑ η : ισ,
          (((Module.finrank ℂ Hπ : ℂ) *
              ∫ t, mc[σ, bσ, η, γ] t * conj (mc[π, bπ, α, β] t) ∂μG)) •
            p[ρ, σ, bσ; η, δ]) v := by
          simp [Finset.sum_apply]

/-- Helper for Proposition 4-34: if `π` and `σ` are nonisomorphic irreducible unitary
representations, then their matrix-coefficient projectors have zero product. -/
private theorem matrixCoefficientProjection_comp_eq_zero_of_not_isomorphic_local
    {Hσ : Type x} [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ] [FiniteDimensional ℂ Hσ]
    {ισ : Type z} [Fintype ισ]
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ] [Representation.IsIrreducible σ]
    [Representation.IsUnitary π] [Representation.IsUnitary σ]
    (bπ : OrthonormalBasis ι ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (α β : ι) (γ δ : ισ) (hπσ : ¬ Nonempty (π.Equiv σ)) :
    (p[ρ, π, bπ; α, β]).comp (p[ρ, σ, bσ; γ, δ]) = 0 := by
  -- Collapse the expansion coefficients with the nonisomorphic branch of Lemma 4-22.
  rw [matrixCoefficientProjection_compExpansion ρ π σ bπ bσ α β γ δ]
  have hσπ : ¬ Nonempty (σ.Equiv π) := by
    intro h
    exact hπσ ⟨h.some.symm⟩
  have hcoeff :
      ∀ η : ισ,
        ((Module.finrank ℂ Hπ : ℂ) *
            ∫ t, mc[σ, bσ, η, γ] t * conj (mc[π, bπ, α, β] t) ∂μG) = 0 := by
    intro η
    have hint :
        ∫ t, mc[σ, bσ, η, γ] t * conj (mc[π, bπ, α, β] t) ∂μG = 0 := by
      simpa [mul_comm] using
        Representation.matrixCoefficientIntegral_eq_zero_of_not_isomorphic
          σ π bσ bπ η γ α β hσπ
    rw [hint]
    simp
  simp_rw [hcoeff]
  simp

/-- Helper for Proposition 4-34: for one irreducible unitary representation `π`, the operators
`p[ρ, π, b; α, β]` satisfy the matrix-unit relation. -/
private theorem matrixCoefficientProjection_comp_local
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α β γ δ : ι) :
    (p[ρ, π, b; α, β]).comp (p[ρ, π, b; γ, δ]) =
      if β = γ then p[ρ, π, b; α, δ] else 0 := by
  letI : Module (MonoidAlgebra ℂ G) Hπ := π.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule (MonoidAlgebra ℂ G) Hπ := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule π).mp inferInstance
  letI : Nontrivial Hπ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) Hπ
  have hfinrank_ne_zero : (Module.finrank ℂ Hπ : ℂ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  -- Collapse the coefficient integral with the irreducible orthogonality formula from Lemma 4-22.
  rw [matrixCoefficientProjection_compExpansion ρ π π b b α β γ δ]
  by_cases hβγ : β = γ
  · have hcoeff :
      ∀ η : ι,
        ((Module.finrank ℂ Hπ : ℂ) *
            ∫ t, mc[π, b, η, γ] t * conj (mc[π, b, α, β] t) ∂μG) =
          if α = η then 1 else 0 := by
      intro η
      calc
        ((Module.finrank ℂ Hπ : ℂ) *
            ∫ t, mc[π, b, η, γ] t * conj (mc[π, b, α, β] t) ∂μG)
          = (Module.finrank ℂ Hπ : ℂ) *
              ((Module.finrank ℂ Hπ : ℂ)⁻¹ *
                (if η = α then 1 else 0) * (if γ = β then 1 else 0)) := by
                  rw [Representation.matrixCoefficientIntegral_eq_inv_finrank_mul_kronecker
                    π b η γ α β]
        _ = if α = η then 1 else 0 := by
              simp [hβγ, hfinrank_ne_zero, eq_comm]
    simp_rw [hcoeff]
    simp [hβγ]
  · have hcoeff :
      ∀ η : ι,
        ((Module.finrank ℂ Hπ : ℂ) *
            ∫ t, mc[π, b, η, γ] t * conj (mc[π, b, α, β] t) ∂μG) = 0 := by
      intro η
      calc
        ((Module.finrank ℂ Hπ : ℂ) *
            ∫ t, mc[π, b, η, γ] t * conj (mc[π, b, α, β] t) ∂μG)
          = (Module.finrank ℂ Hπ : ℂ) *
              ((Module.finrank ℂ Hπ : ℂ)⁻¹ *
                (if η = α then 1 else 0) * (if γ = β then 1 else 0)) := by
                  rw [Representation.matrixCoefficientIntegral_eq_inv_finrank_mul_kronecker
                    π b η γ α β]
        _ = 0 := by
              simp [hβγ, eq_comm]
    simp_rw [hcoeff]
    simp [hβγ]

/-- Helper for Proposition 4-34: the diagonal projector `p[ρ, π, b; α, α]` is idempotent. -/
private theorem matrixCoefficientProjection_idempotent_local
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α : ι) :
    (p[ρ, π, b; α, α]).comp (p[ρ, π, b; α, α]) = p[ρ, π, b; α, α] := by
  classical
  simpa using matrixCoefficientProjection_comp_local ρ π b α α α α

/-- If `x₁ ∈ V_{i,α₀}`, then the explicit linear map from Proposition 4-34 (1) intertwines `π`
with `ρ`. -/
theorem matrixCoefficientProjectionLinearMap_isIntertwining
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V)
    (_hx₁_mem : x₁ ∈ V[ρ, π, b; α₀]) :
    π.IsIntertwiningMap ρ (matrixCoefficientProjectionLinearMap ρ π b α₀ x₁) := by
  classical
  refine Representation.IsIntertwiningMap.mk ?_
  intro s v
  have hbasis (γ : ι) :
      matrixCoefficientProjectionLinearMap ρ π b α₀ x₁ (π s (b γ)) =
        ρ s (matrixCoefficientProjectionLinearMap ρ π b α₀ x₁ (b γ)) := by
    -- Compute both sides on the basis vector `b γ`.
    rw [matrixCoefficientProjectionLinearMap_apply]
    calc
      ∑ α, (b.repr (π s (b γ)) α) • p[ρ, π, b; α, α₀] x₁
        = ∑ α, mc[π, b, α, γ] s • p[ρ, π, b; α, α₀] x₁ := by
            refine Finset.sum_congr rfl ?_
            intro α hα
            rw [b.repr_apply_apply, matrixCoefficient_eq_inner]
      _ = ρ s (p[ρ, π, b; γ, α₀] x₁) := by
            symm
            exact matrixCoefficientProjection_leftActionExpansion ρ π b s γ α₀ x₁
      _ = ρ s (matrixCoefficientProjectionLinearMap ρ π b α₀ x₁ (b γ)) := by
            congr 1
            rw [matrixCoefficientProjectionLinearMap_apply]
            calc
              p[ρ, π, b; γ, α₀] x₁
                = ∑ x : ι, if x = γ then p[ρ, π, b; x, α₀] x₁ else 0 := by
                    symm
                    rw [Finset.sum_eq_single γ]
                    · simp
                    · intro x hx hneq
                      simp [hneq]
                    · intro hγ
                      exact (hγ (Finset.mem_univ γ)).elim
              _ = ∑ x : ι, ⟪b x, b γ⟫_ℂ • p[ρ, π, b; x, α₀] x₁ := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    have horth :
                        ⟪b x, b γ⟫_ℂ = if x = γ then 1 else 0 := by
                      simpa using (orthonormal_iff_ite.mp b.orthonormal x γ)
                    rw [horth]
                    by_cases h : x = γ <;> simp [h]
              _ = ∑ α, (b.repr (b γ) α) • p[ρ, π, b; α, α₀] x₁ := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    rw [b.repr_apply_apply]
  -- Expand `v` in the orthonormal basis and use the basis-vector intertwining formula.
  calc
    matrixCoefficientProjectionLinearMap ρ π b α₀ x₁ (π s v)
      = matrixCoefficientProjectionLinearMap ρ π b α₀ x₁
          (π s (∑ γ, (b.repr v γ) • b γ)) := by
            rw [b.sum_repr]
    _ = matrixCoefficientProjectionLinearMap ρ π b α₀ x₁
          (∑ γ, (b.repr v γ) • π s (b γ)) := by
            simp [map_sum, map_smul]
    _ = ∑ γ, (b.repr v γ) •
          matrixCoefficientProjectionLinearMap ρ π b α₀ x₁ (π s (b γ)) := by
            simp [map_sum, map_smul]
    _ = ∑ γ, (b.repr v γ) •
          ρ s (matrixCoefficientProjectionLinearMap ρ π b α₀ x₁ (b γ)) := by
            refine Finset.sum_congr rfl ?_
            intro γ hγ
            rw [hbasis]
    _ = ρ s
          (∑ γ, (b.repr v γ) • matrixCoefficientProjectionLinearMap ρ π b α₀ x₁ (b γ)) := by
            simp [map_sum, map_smul]
    _ = ρ s
          (matrixCoefficientProjectionLinearMap ρ π b α₀ x₁
            (∑ γ, (b.repr v γ) • b γ)) := by
              congr 1
              symm
              simp [map_sum, map_smul]
    _ = ρ s (matrixCoefficientProjectionLinearMap ρ π b α₀ x₁ v) := by
          rw [b.sum_repr]

/-- The canonical intertwining map from Proposition 4-34 (1), built from
`x₁ ∈ V[ρ, π, b; α₀]`. -/
def matrixCoefficientProjectionIntertwiningMap
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; α₀]) :
    π.IntertwiningMap ρ :=
  (matrixCoefficientProjectionLinearMap ρ π b α₀ x₁).intertwiningMap_of_isIntertwiningMap π ρ
    (matrixCoefficientProjectionLinearMap_isIntertwining
      ρ π b α₀ x₁ hx₁_mem).isIntertwining

/-- The underlying linear map of `matrixCoefficientProjectionIntertwiningMap` is the explicit sum
`matrixCoefficientProjectionLinearMap ρ π b α₀ x₁`. -/
@[simp] theorem matrixCoefficientProjectionIntertwiningMap_toLinearMap
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; α₀]) :
    (matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem).toLinearMap =
      matrixCoefficientProjectionLinearMap ρ π b α₀ x₁ :=
  rfl

/-- Evaluating `matrixCoefficientProjectionIntertwiningMap` recovers the explicit formula from
Proposition 4-34 (1). -/
@[simp] theorem matrixCoefficientProjectionIntertwiningMap_apply
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; α₀])
    (v : Hπ) :
    matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem v =
      ∑ α, (b.repr v α) • p[ρ, π, b; α, α₀] x₁ := by
  rfl

/-- Clause (1) of Proposition 4-34: if `0 ≠ x₁ ∈ V_{i,α₀}`, then the image of
the canonical intertwining map assembled from the vectors
`x_α := p_{α,α₀}^{(i)} x₁` is a subrepresentation of `ρ` equivalent to `π`. -/
theorem matrixCoefficientProjectionIntertwiningMap_range_nonempty_equiv
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ : ι) (x₁ : V)
    (hx₁_mem : x₁ ∈ V[ρ, π, b; α₀])
    (hx₁_ne : x₁ ≠ 0) :
    Nonempty
      (π.Equiv
        (matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem).range.toRepresentation) :=
  by
  have hx₁_fix : p[ρ, π, b; α₀, α₀] x₁ = x₁ := by
    rcases (mem_matrixCoefficientProjectionSubspace_iff ρ π b α₀ x₁).mp hx₁_mem with ⟨u, hu⟩
    calc
      p[ρ, π, b; α₀, α₀] x₁ = p[ρ, π, b; α₀, α₀] (p[ρ, π, b; α₀, α₀] u) := by
            rw [hu]
      _ = p[ρ, π, b; α₀, α₀] u := by
            simpa [LinearMap.comp_apply] using
              congrArg (fun f : V →L[ℂ] V ↦ f u)
                (matrixCoefficientProjection_idempotent_local ρ π b α₀)
      _ = x₁ := hu
  have hvalue :
      matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem (b α₀) = x₁ := by
    rw [matrixCoefficientProjectionIntertwiningMap_apply]
    calc
      ∑ α, (b.repr (b α₀) α) • p[ρ, π, b; α, α₀] x₁ = p[ρ, π, b; α₀, α₀] x₁ := by
            rw [Finset.sum_eq_single α₀]
            · simp [b.repr_apply_apply]
            · intro α hα hα_ne
              simp [b.repr_apply_apply, hα_ne]
            · intro hα₀
              exact (hα₀ (Finset.mem_univ α₀)).elim
      _ = x₁ := hx₁_fix
  have hnonzero :
      matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem ≠ 0 := by
    intro hzero
    apply hx₁_ne
    simpa [hvalue] using congrArg
      (fun f : π.IntertwiningMap ρ ↦ f (b α₀)) hzero
  let f : π.IntertwiningMap ρ :=
    matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x₁ hx₁_mem
  let fRange : π.IntertwiningMap f.range.toRepresentation :=
    let fLin := f.toLinearMap.rangeRestrict
    fLin.intertwiningMap_of_isIntertwiningMap π f.range.toRepresentation
      (fun s w ↦ by
        have hintertw :
            π.IsIntertwiningMap ρ (matrixCoefficientProjectionLinearMap ρ π b α₀ x₁) :=
          matrixCoefficientProjectionLinearMap_isIntertwining ρ π b α₀ x₁ hx₁_mem
        apply Subtype.ext
        change f.toLinearMap ((π s) w) = ρ s (f.toLinearMap w)
        simpa [f, matrixCoefficientProjectionIntertwiningMap_toLinearMap] using
          hintertw.isIntertwining s w)
  have hf_inj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero (ρ := π) (σ := ρ) f).resolve_right hnonzero
  have hfRange_bij : Function.Bijective fRange := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hf_inj
      exact congrArg Subtype.val hxy
    · simpa [fRange] using LinearMap.surjective_rangeRestrict f.toLinearMap
  exact Representation.nonempty_equiv_of_bijective_intertwiningMap
    (ρ1 := π) (ρ2 := f.range.toRepresentation) fRange hfRange_bij

/-- Helper for Proposition 4-34: the diagonal sum of the matrix-coefficient projectors is the
explicit character-average operator from Theorem 4-33. -/
private theorem matrixCoefficientProjection_diagSum_eq_isotypicCharacterAverage_local
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ) :
    ∑ α, (p[ρ, π, b; α, α]).toLinearMap = isotypicCharacterAverage ρ π := by
  classical
  ext v
  have hIntDiag (α : ι) :
      MeasureTheory.Integrable
        (fun t ↦ ((Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, α, α] t)) • ρ t v) μG := by
    have hcont :
        Continuous (fun t ↦ ((Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, α, α] t)) • ρ t v) := by
      exact (matrixCoefficientProjectionWeight_continuous π b α α).smul
        (Representation.continuous_apply ρ v)
    have hIntOn :
        MeasureTheory.IntegrableOn
          (fun t ↦ ((Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, α, α] t)) • ρ t v)
          Set.univ μG := by
      exact ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ hcont.continuousOn
    simpa [MeasureTheory.integrableOn_univ] using hIntOn
  -- Commute the finite diagonal sum through the Haar integral and rewrite it as the character.
  calc
    (∑ α, (p[ρ, π, b; α, α]).toLinearMap) v = ∑ α, p[ρ, π, b; α, α] v := by
          simp [Finset.sum_apply]
    _ = ∑ α, ∫ t, ((Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, α, α] t)) • ρ t v ∂μG := by
          refine Finset.sum_congr rfl ?_
          intro α hα
          rw [matrixCoefficientProjection, classFunctionAveragedEndomorphism_apply ρ
            (fun t ↦ (Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, α, α] t))
            (matrixCoefficientProjectionWeight_continuous π b α α)]
    _ = ∫ t, ∑ α, ((Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, α, α] t)) • ρ t v ∂μG := by
          symm
          rw [MeasureTheory.integral_finset_sum Finset.univ (fun α _ ↦ hIntDiag α)]
    _ = ∫ t, ((Module.finrank ℂ Hπ : ℂ) * conj (∑ α, mc[π, b, α, α] t)) • ρ t v ∂μG := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with t
          calc
            ∑ α, ((Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, α, α] t)) • ρ t v
              = (∑ α, (Module.finrank ℂ Hπ : ℂ) * conj (mc[π, b, α, α] t)) • ρ t v := by
                  symm
                  exact Finset.sum_smul
            _ = ((Module.finrank ℂ Hπ : ℂ) * conj (∑ α, mc[π, b, α, α] t)) • ρ t v := by
                  simp [Finset.mul_sum]
    _ = ∫ t, (Module.finrank ℂ Hπ : ℂ) • (conj (π.character t) • ρ t v) ∂μG := by
          congr 1
          funext t
          rw [Representation.character_eq_sumDiagonalMatrixCoefficient π b]
          simp [smul_smul]
    _ = (Module.finrank ℂ Hπ : ℂ) • ∫ t, conj (π.character t) • ρ t v ∂μG := by
          rw [MeasureTheory.integral_smul]
    _ = isotypicCharacterAverage ρ π v := by
          rw [Representation.isotypicCharacterAverage_apply]

/-- Helper for Proposition 4-34: the diagonal projector fixes every vector already lying in its
matrix-coefficient subspace. -/
private theorem matrixCoefficientProjection_eq_self_of_mem_subspace
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α : ι) {x : V}
    (hx : x ∈ V[ρ, π, b; α]) :
    p[ρ, π, b; α, α] x = x := by
  -- Write `x` as `p[ρ, π, b; α, α] u` and collapse the second projector with idempotence.
  rcases (mem_matrixCoefficientProjectionSubspace_iff ρ π b α x).mp hx with ⟨u, rfl⟩
  simpa [LinearMap.comp_apply] using
    congrArg (fun f : V →L[ℂ] V ↦ f u)
      (matrixCoefficientProjection_idempotent_local ρ π b α)

/-- Helper for Proposition 4-34: applying `p[ρ, π, b; α₀, η]` to the canonical intertwiner built
from `x ∈ V[ρ, π, b; α₀]` isolates the `η`-th basis coefficient and recovers `x`. -/
private theorem matrixCoefficientProjectionIntertwiningMap_isolation
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α₀ η : ι) {x : V}
    (hx : x ∈ V[ρ, π, b; α₀]) (w : Hπ) :
    p[ρ, π, b; α₀, η]
        (matrixCoefficientProjectionIntertwiningMap ρ π b α₀ x hx w) =
      (b.repr w η) • x := by
  classical
  have hfix : p[ρ, π, b; α₀, α₀] x = x :=
    matrixCoefficientProjection_eq_self_of_mem_subspace ρ π b α₀ hx
  -- Expand the intertwiner value and collapse the matrix-unit product termwise.
  rw [matrixCoefficientProjectionIntertwiningMap_apply]
  calc
    p[ρ, π, b; α₀, η] (∑ α, (b.repr w α) • p[ρ, π, b; α, α₀] x)
      = ∑ α, (b.repr w α) • p[ρ, π, b; α₀, η] (p[ρ, π, b; α, α₀] x) := by
          simp [map_sum]
    _ = ∑ α, (b.repr w α) • (if η = α then p[ρ, π, b; α₀, α₀] x else 0) := by
          refine Finset.sum_congr rfl ?_
          intro α hα
          by_cases hηα : η = α
          · simpa [hηα, LinearMap.comp_apply] using
              congrArg (fun z : V ↦ (b.repr w α) • z)
                (congrArg (fun f : V →L[ℂ] V ↦ f x)
                  (matrixCoefficientProjection_comp_local ρ π b α₀ η α α₀))
          · simpa [hηα, LinearMap.comp_apply] using
              congrArg (fun z : V ↦ (b.repr w α) • z)
                (congrArg (fun f : V →L[ℂ] V ↦ f x)
                  (matrixCoefficientProjection_comp_local ρ π b α₀ η α α₀))
    _ = (b.repr w η) • p[ρ, π, b; α₀, α₀] x := by
          rw [Finset.sum_eq_single η]
          · simp
          · intro α hα hαη
            have hηα : η ≠ α := by
              exact fun h ↦ hαη h.symm
            simp [hηα]
          · intro hη
            exact (hη (Finset.mem_univ η)).elim
    _ = (b.repr w η) • x := by
          rw [hfix]

/-- Proposition 4-34 (2): after choosing a basis of `V_{i,α₀}`, there is an equivalence from the
direct sum of copies of `π` indexed by that basis to the `π`-isotypic component of `ρ`, with the
`k`-th copy generated from the basis vector `c k`. -/
theorem exists_piIsotypicComponent_equiv_directSum_of_matrixCoefficientBasis
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ) (α₀ : ι)
    {κ : Type z}
    [DecidableEq κ]
    (c : Module.Basis κ ℂ V[ρ, π, b; α₀]) :
    ∃ e : (Representation.directSum fun _ : κ ↦ π).Equiv
      (ρ.isotypicSubrepresentation π).toRepresentation,
      ∀ k : κ, ∀ v : Hπ,
        (ρ.isotypicSubrepresentation π).toSubmodule.subtype
          (e (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v)) =
            ∑ α, (b.repr v α) • p[ρ, π, b; α, α₀] (c k) := by
  classical
  -- Route correction: rather than import a finite-group-only bijectivity theorem, build the
  -- direct-sum evaluation map from the basis `c` and invert it by recovering the `α₀`-column
  -- projector coordinates.
  let h : κ → π.IntertwiningMap ρ := fun k ↦
    matrixCoefficientProjectionIntertwiningMap ρ π b α₀ (c k) (c k).property
  let F :
      (Representation.directSum fun _ : κ ↦ π).IntertwiningMap
        (ρ.isotypicSubrepresentation π).toRepresentation :=
    ρ.familyDirectSumEvaluation π h
  -- The `α₀`-row projector lands back in the distinguished subspace `V[ρ, π, b; α₀]`.
  let toBaseComponent :
      ι → ↥(ρ.isotypicSubrepresentation π).toSubmodule →ₗ[ℂ] V[ρ, π, b; α₀] :=
    fun η ↦
      (((p[ρ, π, b; α₀, η]).toLinearMap).comp
        (ρ.isotypicSubrepresentation π).toSubmodule.subtype).codRestrict (V[ρ, π, b; α₀])
        fun y ↦ by
        -- The matrix-unit relation already puts `p[ρ, π, b; α₀, η] y` in the image of
        -- `p[ρ, π, b; α₀, α₀]`.
        refine LinearMap.mem_range.mpr ?_
        refine ⟨p[ρ, π, b; α₀, η] y, ?_⟩
        simpa [LinearMap.comp_apply] using
          congrArg (fun f : V →L[ℂ] V ↦ f y)
            (matrixCoefficientProjection_comp_local ρ π b α₀ α₀ α₀ η)
  -- Rebuild a direct-sum vector from the basis coordinates of the distinguished `α₀`-column
  -- projector pieces.
  let reconstruction :
      ↥(ρ.isotypicSubrepresentation π).toSubmodule →ₗ[ℂ]
        DirectSum κ (fun _ : κ ↦ Hπ) :=
    ∑ η, (Finsupp.linearCombination ℂ
        (fun k : κ ↦ DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k (b η))).comp
        (c.repr.toLinearMap.comp (toBaseComponent η))
  have hgenerator_eval :
      ∀ k : κ, ∀ v : Hπ,
        ((F (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v)) : V) =
          ∑ α, (b.repr v α) • p[ρ, π, b; α, α₀] (c k) := by
    intro k v
    -- On a direct-sum generator, `familyDirectSumEvaluation` is the chosen intertwiner `h k`.
    calc
      ((F (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v)) : V)
        = (DirectSum.toModule ℂ κ V
            (fun i ↦ matrixCoefficientProjectionLinearMap ρ π b α₀ (c i)))
            (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v) := by
              change (((ρ.familyDirectSumEvaluation π h)
                (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v)) : V) = _
              rfl
      _ = matrixCoefficientProjectionLinearMap ρ π b α₀ (c k) v := by
            rw [DirectSum.toModule_lof]
      _ = ∑ α, (b.repr v α) • p[ρ, π, b; α, α₀] (c k) := by
            rw [matrixCoefficientProjectionLinearMap_apply]
  have htoBase_generator :
      ∀ k : κ, ∀ η : ι, ∀ v : Hπ,
        toBaseComponent η (F (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v)) =
          (b.repr v η) • c k := by
    intro k η v
    apply Subtype.ext
    -- Applying `p[ρ, π, b; α₀, η]` to the generator value isolates the `η`-th coefficient.
    simpa [toBaseComponent, hgenerator_eval k v] using
      matrixCoefficientProjectionIntertwiningMap_isolation
        ρ π b α₀ η (c k).property v
  have hreconstruction_generator :
      ∀ k : κ, ∀ v : Hπ,
        reconstruction (F (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v)) =
          DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v := by
    intro k v
    -- Reconstruct the generator by recovering each basis coefficient and then summing the basis
    -- expansion of `v`.
    calc
      reconstruction (F (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v))
        = ∑ η,
            Finsupp.linearCombination ℂ
              (fun j : κ ↦ DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) j (b η))
              (c.repr ((b.repr v η) • c k)) := by
                simp [reconstruction, htoBase_generator k]
      _ = ∑ η, DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k ((b.repr v η) • b η) := by
            refine Finset.sum_congr rfl ?_
            intro η hη
            have hrepr :
                c.repr ((b.repr v η) • c k) = Finsupp.single k (b.repr v η) := by
              ext j
              by_cases hj : j = k
              · subst hj
                simp [Module.Basis.repr_self]
              · simp [Module.Basis.repr_self, hj]
            rw [hrepr, Finsupp.linearCombination_single]
            symm
            exact map_smul (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k) (b.repr v η) (b η)
      _ = (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k) (∑ η, (b.repr v η) • b η) := by
            symm
            exact map_sum (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k)
              (fun η ↦ (b.repr v η) • b η) Finset.univ
      _ = DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k v := by
            rw [b.sum_repr]
  have hleft : Function.LeftInverse reconstruction F := by
    intro x
    -- The reconstruction map is linear, so it suffices to check direct-sum generators.
    refine DirectSum.induction_on x ?_ ?_ ?_
    · simp [reconstruction]
    · intro k v
      exact hreconstruction_generator k v
    · intro x y hx hy
      simpa using congrArg₂ HAdd.hAdd hx hy
  have hcomponent_eval :
      ∀ η : ι, ∀ y : ↥(ρ.isotypicSubrepresentation π).toSubmodule,
        ((F (Finsupp.linearCombination ℂ
            (fun k : κ ↦ DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k (b η))
            (c.repr (toBaseComponent η y)))) : V) =
            p[ρ, π, b; η, α₀] (toBaseComponent η y) := by
    intro η y
    -- Evaluate the direct-sum linear combination termwise, then collapse it with
    -- `c.linearCombination_repr`.
    have hsum :
        ((F (Finsupp.linearCombination ℂ
            (fun k : κ ↦ DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k (b η))
            (c.repr (toBaseComponent η y)))) : V) =
          (c.repr (toBaseComponent η y)).sum
            (fun k a ↦ a • p[ρ, π, b; η, α₀] (c k)) := by
      let coeff := c.repr (toBaseComponent η y)
      have hsub :
          F.toLinearMap
              (Finsupp.linearCombination ℂ
                (fun k : κ ↦ DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k (b η)) coeff)
            =
              Finset.sum coeff.support
                (fun k ↦ coeff k •
                  (F.toLinearMap (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k (b η)))) := by
        rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [map_smul]
      calc
        ((F (Finsupp.linearCombination ℂ
            (fun k : κ ↦ DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k (b η))
            coeff)) : V)
          = ↑(Finset.sum coeff.support
              (fun k ↦ coeff k •
                (F.toLinearMap (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k (b η))))) := by
                simpa [coeff] using congrArg Subtype.val hsub
        _ = Finset.sum coeff.support
              (fun k ↦ coeff k •
                ((F.toLinearMap (DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k (b η))) : V)) := by
              simp
        _ = Finset.sum coeff.support
              (fun k ↦ coeff k • p[ρ, π, b; η, α₀] (c k)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              simpa [coeff, matrixCoefficientProjectionLinearMap_apply, b.repr_apply_apply] using
                congrArg (fun z : V ↦ coeff k • z) (hgenerator_eval k (b η))
        _ = coeff.sum (fun k a ↦ a • p[ρ, π, b; η, α₀] (c k)) := by
              rw [Finsupp.sum]
    calc
      ((F (Finsupp.linearCombination ℂ
          (fun k : κ ↦ DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k (b η))
          (c.repr (toBaseComponent η y)))) : V)
        = (c.repr (toBaseComponent η y)).sum
            (fun k a ↦ a • p[ρ, π, b; η, α₀] (c k)) := hsum
      _ = p[ρ, π, b; η, α₀]
            (Finsupp.linearCombination ℂ c (c.repr (toBaseComponent η y))) := by
              symm
              rw [Finsupp.linearCombination_apply, Finsupp.sum]
              calc
                p[ρ, π, b; η, α₀]
                    ↑(∑ a ∈ (c.repr (toBaseComponent η y)).support,
                      (c.repr (toBaseComponent η y)) a • c a)
                  =
                    ∑ a ∈ (c.repr (toBaseComponent η y)).support,
                          p[ρ, π, b; η, α₀]
                        (((c.repr (toBaseComponent η y)) a • c a : V[ρ, π, b; α₀]) : V) := by
                          simpa using
                            (map_sum (p[ρ, π, b; η, α₀]).toLinearMap
                              (fun a ↦
                                (((c.repr (toBaseComponent η y)) a • c a : V[ρ, π, b; α₀]) : V))
                              (c.repr (toBaseComponent η y)).support)
                _ = (c.repr (toBaseComponent η y)).sum
                      (fun k a ↦ a • p[ρ, π, b; η, α₀] (c k)) := by
                        rw [Finsupp.sum]
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        exact
                          (p[ρ, π, b; η, α₀]).toLinearMap.map_smul
                            ((c.repr (toBaseComponent η y)) i)
                            (((c i : V[ρ, π, b; α₀]) : V))
      _ = p[ρ, π, b; η, α₀] (toBaseComponent η y) := by
              exact congrArg
                (fun z : V[ρ, π, b; α₀] ↦ p[ρ, π, b; η, α₀] (z : V))
                (c.linearCombination_repr (toBaseComponent η y))
  have hright : Function.RightInverse reconstruction F := by
    intro y
    apply Subtype.ext
    -- Compute `F` on each reconstructed `η`-piece, identify it with `p[η,η] y`, and sum the
    -- diagonal projectors using the isotypic projection identity.
    have hy_diag :
        ∑ η, p[ρ, π, b; η, η] y = y := by
      have hy_fix : isotypicCharacterAverage ρ π y = y :=
        (LinearMap.IsProj.mem_iff_map_id (ρ.piIsotypicCharacterAverage_isProj π)).1 y.property
      calc
        ∑ η, p[ρ, π, b; η, η] y = (∑ η, (p[ρ, π, b; η, η]).toLinearMap) y := by
              simp [Finset.sum_apply]
        _ = isotypicCharacterAverage ρ π y := by
              exact congrArg (fun f : V →ₗ[ℂ] V ↦ f y)
                (matrixCoefficientProjection_diagSum_eq_isotypicCharacterAverage_local ρ π b)
        _ = y := hy_fix
    let reconstructedPiece : ι → V := fun η ↦
      ((F (Finsupp.linearCombination ℂ
          (fun k : κ ↦ DirectSum.lof ℂ κ (fun _ : κ ↦ Hπ) k (b η))
          (c.repr (toBaseComponent η y)))) : V)
    have hreconstruction_eval :
        ((F (reconstruction y)) : V) =
          ∑ η, reconstructedPiece η := by
      simp [reconstruction, reconstructedPiece, map_sum]
    calc
      ((F (reconstruction y)) : V)
        = ∑ η, reconstructedPiece η := hreconstruction_eval
      _ = ∑ η, p[ρ, π, b; η, α₀] (toBaseComponent η y) := by
            refine Finset.sum_congr rfl ?_
            intro η hη
            simpa [reconstructedPiece] using hcomponent_eval η y
      _ = ∑ η, p[ρ, π, b; η, α₀] (p[ρ, π, b; α₀, η] y) := by
            refine Finset.sum_congr rfl ?_
            intro η hη
            rfl
      _ = ∑ η, p[ρ, π, b; η, η] y := by
            refine Finset.sum_congr rfl ?_
            intro η hη
            simpa [LinearMap.comp_apply] using
              congrArg (fun f : V →L[ℂ] V ↦ f y)
                (matrixCoefficientProjection_comp_local ρ π b η α₀ α₀ η)
      _ = y := hy_diag
  have hbij : Function.Bijective F := ⟨hleft.injective, hright.surjective⟩
  let e :
      (Representation.directSum fun _ : κ ↦ π).Equiv
        (ρ.isotypicSubrepresentation π).toRepresentation :=
    F.ofBijective hbij
  refine ⟨e, ?_⟩
  intro k v
  -- The packaged equivalence has the same forward map as the evaluation intertwiner `F`.
  simpa [e, Representation.Equiv.mk_apply, LinearEquiv.ofBijective_apply] using
    hgenerator_eval k v

/-- Clause (3) of Proposition 4-34: each diagonal operator `p_{αα}^{(i)}` is the projection onto
`V_{i,α}`. -/
theorem matrixCoefficientProjection_isProj
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α : ι) :
    LinearMap.IsProj V[ρ, π, b; α] (p[ρ, π, b; α, α]).toLinearMap := by
  -- The diagonal projector is idempotent and has image exactly `V[ρ, π, b; α]` by definition.
  refine LinearMap.IsProj.mk ?_ ?_
  · intro v
    exact LinearMap.mem_range_self _ v
  · intro v hv
    rcases LinearMap.mem_range.mp hv with ⟨u, rfl⟩
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : V →L[ℂ] V ↦ f u)
        (matrixCoefficientProjection_idempotent_local ρ π b α)

/-- Helper for Proposition 4-34: the diagonal projector `p[ρ, π, b; α, α]` acts as the identity
on `V[ρ, π, b; α]` and annihilates the other matrix-coefficient subspaces. -/
private theorem matrixCoefficientProjectionSubspace_isolation
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ Hπ)
    {α β : ι} {v : V}
    (hv : v ∈ V[ρ, π, b; β]) :
    p[ρ, π, b; α, α] v = if α = β then v else 0 := by
  by_cases hαβ : α = β
  · subst β
    simpa using
      (LinearMap.IsProj.mem_iff_map_id (matrixCoefficientProjection_isProj ρ π b α)).1 hv
  · rcases LinearMap.mem_range.mp hv with ⟨u, rfl⟩
    simpa [hαβ, LinearMap.comp_apply] using
      congrArg (fun f : V →L[ℂ] V ↦ f u)
        (matrixCoefficientProjection_comp_local ρ π b α α β β)

/-- Clause (4) of Proposition 4-34: the subspaces `V_{i,α}` are independent inside the sum that they
generate. -/
theorem iSupIndep_matrixCoefficientProjectionSubspaces
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ) :
    iSupIndep
      (fun α : ι ↦ (V[ρ, π, b; α]).comap (iSup fun α : ι ↦ V[ρ, π, b; α]).subtype) := by
  classical
  let S : Submodule ℂ V := iSup fun α : ι ↦ V[ρ, π, b; α]
  -- Apply the diagonal projector `p[ρ, π, b; α, α]` to isolate the `α`-th summand.
  rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero]
  intro s v hv hsum α hα
  apply Subtype.ext
  have happly :
      ∑ i ∈ s, p[ρ, π, b; α, α] (((v i : S) : V)) = 0 := by
    have := congrArg (fun z : S ↦ p[ρ, π, b; α, α] (z : V)) hsum
    simpa [map_sum] using this
  calc
    ((v α : S) : V) = ∑ i ∈ s, if α = i then (((v i : S) : V)) else 0 := by
          symm
          rw [Finset.sum_eq_single_of_mem α hα]
          · simp
          · intro i hi hneq
            by_cases hαi : α = i
            · exact (hneq hαi.symm).elim
            · simp [hαi]
    _ = ∑ i ∈ s, p[ρ, π, b; α, α] (((v i : S) : V)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hmem : (((v i : S) : V)) ∈ V[ρ, π, b; i] := by
            simpa using hv i hi
          symm
          simpa using matrixCoefficientProjectionSubspace_isolation ρ π b hmem (α := α) (β := i)
    _ = 0 := happly

/-- Clause (5) of Proposition 4-34: the `π`-isotypic component of `ρ` is the sum of the subspaces
`V_{i,α}`. -/
theorem iSup_matrixCoefficientProjectionSubspaces_eq_piIsotypicComponent
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ) :
    iSup (fun α : ι ↦ V[ρ, π, b; α]) =
      (ρ.moduleIsotypicComponent π).restrictScalars ℂ := by
  classical
  apply le_antisymm
  · refine iSup_le ?_
    intro α x hx
    -- A vector in `V[ρ, π, b; α]` is fixed by the diagonal projector sum, hence by the isotypic
    -- projector identified in the diagonal-sum helper above.
    have hfix : isotypicCharacterAverage ρ π x = x := by
      rcases LinearMap.mem_range.mp hx with ⟨u, rfl⟩
      have hsumComp :
          (∑ η : ι, (p[ρ, π, b; η, η]).toLinearMap).comp (p[ρ, π, b; α, α]).toLinearMap =
            (p[ρ, π, b; α, α]).toLinearMap := by
        ext v
        calc
          ((∑ η : ι, (p[ρ, π, b; η, η]).toLinearMap).comp (p[ρ, π, b; α, α]).toLinearMap) v
            = ∑ η : ι, p[ρ, π, b; η, η] (p[ρ, π, b; α, α] v) := by
                simp [LinearMap.comp_apply, Finset.sum_apply]
          _ = ∑ η : ι, if η = α then p[ρ, π, b; α, α] v else 0 := by
                apply Finset.sum_congr rfl
                intro η hη
                by_cases hηα : η = α
                · subst η
                  simpa [LinearMap.comp_apply] using
                    congrArg (fun f : V →L[ℂ] V ↦ f v)
                      (matrixCoefficientProjection_comp_local ρ π b α α α α)
                · simpa [hηα, LinearMap.comp_apply] using
                    congrArg (fun f : V →L[ℂ] V ↦ f v)
                      (matrixCoefficientProjection_comp_local ρ π b η η α α)
          _ = p[ρ, π, b; α, α] v := by
                simp
      calc
        isotypicCharacterAverage ρ π (p[ρ, π, b; α, α] u)
          = (∑ η : ι, (p[ρ, π, b; η, η]).toLinearMap) (p[ρ, π, b; α, α] u) := by
              rw [← matrixCoefficientProjection_diagSum_eq_isotypicCharacterAverage_local ρ π b]
        _ = p[ρ, π, b; α, α] u := by
              simpa [LinearMap.comp_apply] using
                congrArg (fun f : V →ₗ[ℂ] V ↦ f u) hsumComp
    exact
      (LinearMap.IsProj.mem_iff_map_id (ρ.piIsotypicCharacterAverage_isProj π)).2 hfix
  · intro x hx
    -- A vector in the isotypic component is fixed by the projector, hence equals the sum of its
    -- diagonal matrix-coefficient components.
    have hfix : isotypicCharacterAverage ρ π x = x := by
      exact
        (LinearMap.IsProj.mem_iff_map_id (ρ.piIsotypicCharacterAverage_isProj π)).1 hx
    rw [← matrixCoefficientProjection_diagSum_eq_isotypicCharacterAverage_local ρ π b] at hfix
    rw [← hfix]
    simpa using
      (Submodule.sum_mem (iSup fun α : ι ↦ V[ρ, π, b; α])
        (fun α hα ↦ Submodule.mem_iSup_of_mem α (LinearMap.mem_range_self _ x)))

/-- Helper: each subspace `V_{i,α}` lies in the canonical `π`-isotypic component of `ρ`. -/
theorem matrixCoefficientProjectionSubspace_le_piIsotypicComponent
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α : ι) :
    V[ρ, π, b; α] ≤ (ρ.moduleIsotypicComponent π).restrictScalars ℂ := by
  simpa [iSup_matrixCoefficientProjectionSubspaces_eq_piIsotypicComponent ρ π b] using
    (le_iSup (fun α : ι ↦ V[ρ, π, b; α]) α)

/-- Clause (6) of Proposition 4-34: the operator `p_{αβ}^{(i)}` vanishes on `V_{i,γ}` whenever
`γ ≠ β`. -/
theorem matrixCoefficientProjection_apply_eq_zero_of_mem_otherSubspace
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    {α β γ : ι} (hγβ : γ ≠ β) {v : V}
    (hv : v ∈ V[ρ, π, b; γ]) :
    p[ρ, π, b; α, β] v = 0 := by
  classical
  rcases LinearMap.mem_range.mp hv with ⟨u, rfl⟩
  have hβγ : β ≠ γ := fun hβγ_eq ↦ hγβ hβγ_eq.symm
  simpa [LinearMap.comp_apply, hβγ] using
    congrArg (fun f : V →L[ℂ] V ↦ f u)
      (matrixCoefficientProjection_comp_local ρ π b α β γ γ)

/-- The operator `p_{αβ}^{(i)}` carries `V_{i,β}` into `V_{i,α}`. -/
theorem matrixCoefficientProjection_mapsToSubspace
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α β : ι) (v : V)
    (hv : v ∈ V[ρ, π, b; β]) :
    p[ρ, π, b; α, β] v ∈ V[ρ, π, b; α] := by
  classical
  rcases LinearMap.mem_range.mp hv with ⟨u, rfl⟩
  -- Write `v` as `p[ρ, π, b; β, β] u` and isolate the target subspace with the matrix-unit law.
  refine LinearMap.mem_range.mpr ?_
  refine ⟨p[ρ, π, b; α, β] u, ?_⟩
  calc
    p[ρ, π, b; α, α] (p[ρ, π, b; α, β] u) = p[ρ, π, b; α, β] u := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun f : V →L[ℂ] V ↦ f u)
          (matrixCoefficientProjection_comp_local ρ π b α α α β)
    _ = p[ρ, π, b; α, β] (p[ρ, π, b; β, β] u) := by
      symm
      simpa [LinearMap.comp_apply] using
        congrArg (fun f : V →L[ℂ] V ↦ f u)
          (matrixCoefficientProjection_comp_local ρ π b α β β β)

/-- Clause (7) of Proposition 4-34: for one irreducible representation `π`, the operator
`p_{αβ}^{(i)}` induces a linear equivalence `V[ρ, π, b; β] ≃ₗ[ℂ] V[ρ, π, b; α]`. -/
def matrixCoefficientProjectionSubspaceLinearEquiv
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α β : ι) :
    V[ρ, π, b; β] ≃ₗ[ℂ] V[ρ, π, b; α] where
  toFun v := ⟨p[ρ, π, b; α, β] v, matrixCoefficientProjection_mapsToSubspace ρ π b α β v v.property⟩
  invFun v := by
    refine ⟨p[ρ, π, b; β, α] v, ?_⟩
    exact matrixCoefficientProjection_mapsToSubspace ρ π b β α v v.property
  left_inv := by
    classical
    intro v
    rcases LinearMap.mem_range.mp v.property with ⟨u, hu⟩
    apply Subtype.ext
    change p[ρ, π, b; β, α] (p[ρ, π, b; α, β] v) = v
    calc
      p[ρ, π, b; β, α] (p[ρ, π, b; α, β] v)
          = p[ρ, π, b; β, α] (p[ρ, π, b; α, β] (p[ρ, π, b; β, β] u)) := by
            simpa using congrArg
              (fun x : V ↦ p[ρ, π, b; β, α] (p[ρ, π, b; α, β] x)) hu.symm
      _ = p[ρ, π, b; β, β] (p[ρ, π, b; β, β] u) := by
        simpa [LinearMap.comp_apply] using
          congrArg (fun f : V →L[ℂ] V ↦ f (p[ρ, π, b; β, β] u))
            (matrixCoefficientProjection_comp_local ρ π b β α α β)
      _ = p[ρ, π, b; β, β] u := by
        simpa [LinearMap.comp_apply] using
          congrArg (fun f : V →L[ℂ] V ↦ f u)
            (matrixCoefficientProjection_idempotent_local ρ π b β)
      _ = v := by
            exact hu
  right_inv := by
    classical
    intro v
    rcases LinearMap.mem_range.mp v.property with ⟨u, hu⟩
    apply Subtype.ext
    change p[ρ, π, b; α, β] (p[ρ, π, b; β, α] v) = v
    calc
      p[ρ, π, b; α, β] (p[ρ, π, b; β, α] v)
          = p[ρ, π, b; α, β] (p[ρ, π, b; β, α] (p[ρ, π, b; α, α] u)) := by
            simpa using congrArg
              (fun x : V ↦ p[ρ, π, b; α, β] (p[ρ, π, b; β, α] x)) hu.symm
      _ = p[ρ, π, b; α, α] (p[ρ, π, b; α, α] u) := by
        simpa [LinearMap.comp_apply] using
          congrArg (fun f : V →L[ℂ] V ↦ f (p[ρ, π, b; α, α] u))
            (matrixCoefficientProjection_comp_local ρ π b α β β α)
      _ = p[ρ, π, b; α, α] u := by
        simpa [LinearMap.comp_apply] using
          congrArg (fun f : V →L[ℂ] V ↦ f u)
            (matrixCoefficientProjection_idempotent_local ρ π b α)
      _ = v := by
            exact hu
  map_add' v w := by
    ext
    simp
  map_smul' c v := by
    ext
    simp

/-- Applying `matrixCoefficientProjectionSubspaceLinearEquiv` and then forgetting the subtype
recovers the operator `p_{αβ}^{(i)}`. -/
@[simp] theorem matrixCoefficientProjectionSubspaceLinearEquiv_apply
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α β : ι) (v : V[ρ, π, b; β]) :
    V[ρ, π, b; α].subtype (matrixCoefficientProjectionSubspaceLinearEquiv ρ π b α β v) =
      p[ρ, π, b; α, β] v :=
  rfl

/-- Helper: the induced linear equivalence from Proposition 4-34 (7) can be chosen so that it
commutes with the ambient inclusion maps and the operator `p_{αβ}^{(i)}`. -/
theorem matrixCoefficientProjectionSubspaceLinearEquiv_commutes
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α β : ι) :
    V[ρ, π, b; α].subtype.comp
        (matrixCoefficientProjectionSubspaceLinearEquiv ρ π b α β).toLinearMap =
      (p[ρ, π, b; α, β]).toLinearMap.comp V[ρ, π, b; β].subtype := by
  ext v
  exact matrixCoefficientProjectionSubspaceLinearEquiv_apply ρ π b α β v

/-- Helper: the diagonal sum of the matrix-coefficient projectors is the explicit character-average
operator from Theorem 4-33. -/
theorem sum_matrixCoefficientProjection_diag_eq_isotypicCharacterAverage
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ) :
    ∑ α, (p[ρ, π, b; α, α]).toLinearMap = isotypicCharacterAverage ρ π := by
  simpa using matrixCoefficientProjection_diagSum_eq_isotypicCharacterAverage_local ρ π b

/-- Helper: if `c` is the canonical summand indexed by the `π`-isotypic component, then the
diagonal sum of the matrix-coefficient projectors is the projection onto that summand. -/
  theorem sum_matrixCoefficientProjection_diag_isProj_isotypicComponent
      (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
      (c : ρ.isotypicComponentsSet)
      (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
      [Representation.IsUnitary π]
      (hcπ : c.1 = ρ.moduleIsotypicComponent π)
      (b : OrthonormalBasis ι ℂ Hπ) :
      LinearMap.IsProj (ρ.isotypicSubmoduleFamily c)
        (∑ α, (p[ρ, π, b; α, α]).toLinearMap) := by
    rw [sum_matrixCoefficientProjection_diag_eq_isotypicCharacterAverage]
    exact ρ.isotypicCharacterAverage_isProj c π hcπ

/-- Clause (8) of Proposition 4-34: the diagonal sum `∑ α, p_{αα}^{(i)}` is the projection onto the
canonical `π`-isotypic component of `ρ`. -/
theorem sum_matrixCoefficientProjection_diag_isProj_piIsotypicComponent
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ) :
    LinearMap.IsProj ((ρ.moduleIsotypicComponent π).restrictScalars ℂ)
      (∑ α, (p[ρ, π, b; α, α]).toLinearMap) := by
  rw [sum_matrixCoefficientProjection_diag_eq_isotypicCharacterAverage]
  exact ρ.piIsotypicCharacterAverage_isProj π

variable {Hσ : Type x} [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ]
  [FiniteDimensional ℂ Hσ]
variable {ισ : Type z} [Fintype ισ]

/-- Clause (9) of Proposition 4-34: matrix-coefficient projections attached to
nonisomorphic irreducible representations have zero product. -/
theorem matrixCoefficientProjection_comp_eq_zero_of_not_isomorphic
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ] [Representation.IsIrreducible σ]
    [Representation.IsUnitary π] [Representation.IsUnitary σ]
    (bπ : OrthonormalBasis ι ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (α β : ι) (γ δ : ισ) (hπσ : ¬ Nonempty (π.Equiv σ)) :
    (p[ρ, π, bπ; α, β]).comp (p[ρ, σ, bσ; γ, δ]) = 0 := by
  simpa using
    matrixCoefficientProjection_comp_eq_zero_of_not_isomorphic_local
      ρ π σ bπ bσ α β γ δ hπσ

/-- Clause (10) of Proposition 4-34: for one irreducible representation `π`, the operators
`p_{αβ}^{(i)}` satisfy the matrix-unit relation `p_{αβ}^{(i)} p_{γδ}^{(i)} =
δ_{βγ} p_{αδ}^{(i)}`. -/
theorem matrixCoefficientProjection_comp
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α β γ δ : ι) :
    (p[ρ, π, b; α, β]).comp (p[ρ, π, b; γ, δ]) =
      if β = γ then p[ρ, π, b; α, δ] else 0 := by
  simpa using matrixCoefficientProjection_comp_local ρ π b α β γ δ

/-- Helper: each diagonal operator `p_{αα}^{(i)}` is a projection. -/
theorem matrixCoefficientProjection_idempotent
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ)
    (α : ι) :
    (p[ρ, π, b; α, α]).comp (p[ρ, π, b; α, α]) = p[ρ, π, b; α, α] := by
  simpa using matrixCoefficientProjection_idempotent_local ρ π b α

end

end Representation
