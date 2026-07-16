import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.RepresentationTheory.Irreducible
import LinearRepresentations_Serre_1977.Serre.Chap04.Definition_4_9
import LinearRepresentations_Serre_1977.Serre.Chap04.Proposition_4_21
import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_5

noncomputable section

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

/- Source/core/bridge triage:
- `source-facing`: Lemma 4-22 is the matrix-coefficient orthogonality relation for irreducible
  unitary representations of a compact group.
- `core/canonical`: the chapter already reuses `Representation.matrixCoefficient` in the
  projection and Peter-Weyl files.
- `bridge/view`: the companion lemmas below identify the same coefficient both as a basis
  coordinate and as the inner product `⟪b i, ρ t (b j)⟫_ℂ`.
-
No more canonical compact-group matrix-coefficient owner was found in the local API, so this file
remains the source-facing owner for that coefficient surface.
-/

universe u v w w' w''

namespace Representation

section Unitary

variable {G : Type u} [Group G]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A complex representation on an inner product space is unitary when every group element acts
by an isometry. -/
class IsUnitary (ρ : Representation ℂ G H) : Prop where
  /-- Each operator `ρ t` preserves the norm. -/
  isometry (t : G) : Isometry (ρ t)

/-- A packaged proof of pointwise isometry supplies the canonical unitary-structure class. -/
instance instIsUnitaryOfFactIsometry (ρ : Representation ℂ G H)
    [hρ : Fact (∀ t : G, Isometry (ρ t))] :
    IsUnitary ρ where
  isometry t := hρ.out t

/-- Build `ρ.IsUnitary` from the pointwise isometry condition. -/
theorem isUnitary_of_isometry (ρ : Representation ℂ G H)
    (hρ : ∀ t : G, Isometry (ρ t)) :
    IsUnitary ρ := by
  letI : Fact (∀ t : G, Isometry (ρ t)) := ⟨hρ⟩
  infer_instance

/-- A unitary representation acts by isometries. -/
theorem isometry (ρ : Representation ℂ G H) [hρ : IsUnitary ρ] (t : G) :
    Isometry (ρ t) :=
  hρ.isometry t

/-- The Lean owner `ρ.IsUnitary` is exactly the pointwise isometry condition. -/
theorem isUnitary_iff (ρ : Representation ℂ G H) :
    IsUnitary ρ ↔ ∀ t : G, Isometry (ρ t) :=
  ⟨fun _ t ↦ isometry ρ t, isUnitary_of_isometry ρ⟩

end Unitary

section MatrixCoefficient

variable {G : Type u} [Group G]
variable {Hπ : Type v} [NormedAddCommGroup Hπ] [InnerProductSpace ℂ Hπ]

/-- Helper for Lemma 4-22: the `(i, j)` matrix coefficient of `ρ` in the orthonormal basis `b`. -/
def matrixCoefficient {ι : Type w'} [Fintype ι]
    (ρ : Representation ℂ G Hπ) (b : OrthonormalBasis ι ℂ Hπ)
    (i j : ι) : G → ℂ :=
  fun t ↦ b.repr (ρ t (b j)) i

/- Source-facing notation for the `(i, j)` matrix coefficient of `ρ` in the basis `b`. -/
scoped notation:max "mc[" ρ ", " b ", " i ", " j "]" => matrixCoefficient ρ b i j

open scoped Representation

/-- Evaluating `mc[ρ, b, i, j]` at `t` reads off the `i`-th basis coordinate of `ρ t (b j)`. -/
@[simp] theorem matrixCoefficient_apply {ι : Type w'} [Fintype ι]
    (ρ : Representation ℂ G Hπ) (b : OrthonormalBasis ι ℂ Hπ)
    (i j : ι) (t : G) :
    mc[ρ, b, i, j] t = b.repr (ρ t (b j)) i :=
  rfl

/-- The matrix coefficient `mc[ρ, b, i, j] t` is the inner product `⟪b i, ρ t (b j)⟫_ℂ`. -/
@[simp] theorem matrixCoefficient_eq_inner {ι : Type w'} [Fintype ι]
    (ρ : Representation ℂ G Hπ) (b : OrthonormalBasis ι ℂ Hπ)
    (i j : ι) (t : G) :
    mc[ρ, b, i, j] t = ⟪b i, ρ t (b j)⟫_ℂ := by
  simpa [matrixCoefficient] using b.repr_apply_apply (ρ t (b j)) i

end MatrixCoefficient

section Orthogonality

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
variable {Hπ : Type v} [NormedAddCommGroup Hπ] [InnerProductSpace ℂ Hπ] [FiniteDimensional ℂ Hπ]
variable {Hσ : Type w} [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ] [FiniteDimensional ℂ Hσ]

/-- Helper for Lemma 4-22: the vector-valued integrand obtained by conjugating the rank-one map
`rankOne ℂ (bπ j) (bσ l)` by the actions of `π` and `σ`. -/
def matrixCoefficientAveragedIntegrand
    {ιπ : Type w'} [Fintype ιπ] {ισ : Type w''} [Fintype ισ]
    (π : Representation ℂ G Hπ) (σ : Representation ℂ G Hσ)
    (bπ : OrthonormalBasis ιπ ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (j : ιπ) (l : ισ) (v : Hσ) : G → Hπ :=
  fun t ↦ π t ((InnerProductSpace.rankOne ℂ (bπ j) (bσ l)) (σ t⁻¹ v))

/-- Helper for Lemma 4-22: the averaged rank-one integrand is continuous in the group variable. -/
theorem matrixCoefficientAveragedIntegrand_continuous
    {ιπ : Type w'} [Fintype ιπ] {ισ : Type w''} [Fintype ισ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ]
    (bπ : OrthonormalBasis ιπ ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (j : ιπ) (l : ισ) (v : Hσ) :
    Continuous (matrixCoefficientAveragedIntegrand π σ bπ bσ j l v) := by
  -- First transport `v` by the inverse `σ`-orbit, then apply the fixed rank-one map, and finally
  -- use continuity of the `π`-action.
  let A : Hσ →L[ℂ] Hπ := InnerProductSpace.rankOne ℂ (bπ j) (bσ l)
  have hσv : Continuous fun t : G ↦ σ t⁻¹ v :=
    (Representation.continuous_apply σ v).comp continuous_inv
  have hmid : Continuous fun t : G ↦ A (σ t⁻¹ v) :=
    A.continuous.comp hσv
  simpa [matrixCoefficientAveragedIntegrand, A] using
    (Representation.continuousAction π).comp (continuous_id.prodMk hmid)

/-- Helper for Lemma 4-22: the averaged rank-one integrand is Bochner integrable. -/
theorem matrixCoefficientAveragedIntegrand_integrable
    {ιπ : Type w'} [Fintype ιπ] {ισ : Type w''} [Fintype ισ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ]
    (bπ : OrthonormalBasis ιπ ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (j : ιπ) (l : ισ) (v : Hσ) :
    Integrable (matrixCoefficientAveragedIntegrand π σ bπ bσ j l v) μG := by
  -- Compactness upgrades continuity of the integrand to integrability on the whole group.
  have hcont :=
    matrixCoefficientAveragedIntegrand_continuous π σ bπ bσ j l v
  have hIntOn :
      IntegrableOn (matrixCoefficientAveragedIntegrand π σ bπ bσ j l v) Set.univ μG :=
    ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ hcont.continuousOn
  simpa [MeasureTheory.integrableOn_univ] using hIntOn

/-- Helper for Lemma 4-22: the averaged map is additive in the input vector. -/
theorem matrixCoefficientAveragedMap_map_add
    {ιπ : Type w'} [Fintype ιπ] {ισ : Type w''} [Fintype ισ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ]
    (bπ : OrthonormalBasis ιπ ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (j : ιπ) (l : ισ) (v w : Hσ) :
    (∫ t, matrixCoefficientAveragedIntegrand π σ bπ bσ j l (v + w) t ∂μG) =
      ∫ t, matrixCoefficientAveragedIntegrand π σ bπ bσ j l v t ∂μG +
        ∫ t, matrixCoefficientAveragedIntegrand π σ bπ bσ j l w t ∂μG := by
  -- Rewrite the integrand pointwise and then use additivity of the Bochner integral.
  have hv :=
    matrixCoefficientAveragedIntegrand_integrable π σ bπ bσ j l v
  have hw :=
    matrixCoefficientAveragedIntegrand_integrable π σ bπ bσ j l w
  calc
    ∫ t, matrixCoefficientAveragedIntegrand π σ bπ bσ j l (v + w) t ∂μG
      = ∫ t,
          (matrixCoefficientAveragedIntegrand π σ bπ bσ j l v t +
            matrixCoefficientAveragedIntegrand π σ bπ bσ j l w t) ∂μG := by
            refine integral_congr_ae ?_
            filter_upwards with t
            simp [matrixCoefficientAveragedIntegrand, map_add]
    _ = _ := integral_add hv hw

/-- Helper for Lemma 4-22: the averaged map is `ℂ`-linear in the input vector. -/
theorem matrixCoefficientAveragedMap_map_smul
    {ιπ : Type w'} [Fintype ιπ] {ισ : Type w''} [Fintype ισ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ]
    (bπ : OrthonormalBasis ιπ ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (j : ιπ) (l : ισ) (c : ℂ) (v : Hσ) :
    (∫ t, matrixCoefficientAveragedIntegrand π σ bπ bσ j l (c • v) t ∂μG) =
      c • ∫ t, matrixCoefficientAveragedIntegrand π σ bπ bσ j l v t ∂μG := by
  -- Rewrite the integrand pointwise and pull the scalar through the integral.
  calc
    ∫ t, matrixCoefficientAveragedIntegrand π σ bπ bσ j l (c • v) t ∂μG
      = ∫ t, c • matrixCoefficientAveragedIntegrand π σ bπ bσ j l v t ∂μG := by
          refine integral_congr_ae ?_
          filter_upwards with t
          simp [matrixCoefficientAveragedIntegrand]
    _ = _ := integral_smul c _

/-- Helper for Lemma 4-22: averaging the conjugates of the rank-one map
`rankOne ℂ (bπ j) (bσ l)` produces a linear map `Hσ →ₗ[ℂ] Hπ`. -/
def matrixCoefficientAveragedMap
    {ιπ : Type w'} [Fintype ιπ] {ισ : Type w''} [Fintype ισ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ]
    (bπ : OrthonormalBasis ιπ ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (j : ιπ) (l : ισ) : Hσ →ₗ[ℂ] Hπ where
  toFun := fun v ↦ ∫ t, matrixCoefficientAveragedIntegrand π σ bπ bσ j l v t ∂μG
  map_add' := matrixCoefficientAveragedMap_map_add π σ bπ bσ j l
  map_smul' := matrixCoefficientAveragedMap_map_smul π σ bπ bσ j l

/-- Helper for Lemma 4-22: evaluating the averaged map is just the defining integral. -/
@[simp] theorem matrixCoefficientAveragedMap_apply
    {ιπ : Type w'} [Fintype ιπ] {ισ : Type w''} [Fintype ισ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ]
    (bπ : OrthonormalBasis ιπ ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (j : ιπ) (l : ισ) (v : Hσ) :
    matrixCoefficientAveragedMap π σ bπ bσ j l v =
      ∫ t, matrixCoefficientAveragedIntegrand π σ bπ bσ j l v t ∂μG :=
  rfl

/-- Helper for Lemma 4-22: left-translating the averaged integrand for `σ s v` matches applying
`π s` to the original averaged integrand for `v`. -/
theorem matrixCoefficientAveragedIntegrand_mul_left
    {ιπ : Type w'} [Fintype ιπ] {ισ : Type w''} [Fintype ισ]
    (π : Representation ℂ G Hπ)
    (σ : Representation ℂ G Hσ)
    (bπ : OrthonormalBasis ιπ ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (j : ιπ) (l : ισ) (s t : G) (v : Hσ) :
    matrixCoefficientAveragedIntegrand π σ bπ bσ j l (σ s v) (s * t) =
      π s (matrixCoefficientAveragedIntegrand π σ bπ bσ j l v t) := by
  -- Expand the translated integrand and collapse the inverse-action pair `σ s⁻¹` and `σ s`.
  have hs : σ s⁻¹ (σ s v) = v := by
    simpa [Representation.toContinuousLinearEquivHom_apply_apply] using
      (σ.toContinuousLinearEquivHom s).symm_apply_apply v
  simp [matrixCoefficientAveragedIntegrand, mul_assoc, hs]

/-- Helper for Lemma 4-22: the averaged map intertwines `σ` and `π`. -/
theorem matrixCoefficientAveragedMap_isIntertwining
    {ιπ : Type w'} [Fintype ιπ] {ισ : Type w''} [Fintype ισ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ]
    (bπ : OrthonormalBasis ιπ ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (j : ιπ) (l : ισ) :
    σ.IsIntertwiningMap π (matrixCoefficientAveragedMap π σ bπ bσ j l) := by
  refine Representation.IsIntertwiningMap.mk ?_
  intro s v
  let F : G → Hπ := matrixCoefficientAveragedIntegrand π σ bπ bσ j l (σ s v)
  -- Translate the integral on the left, then pull `π s` through the integral on the right.
  calc
    matrixCoefficientAveragedMap π σ bπ bσ j l (σ s v)
      = ∫ t, matrixCoefficientAveragedIntegrand π σ bπ bσ j l (σ s v) t ∂μG := rfl
    _ = ∫ t, F (s * t) ∂μG := by
          simpa [F] using
            (integral_mul_left_eq_self (μ := (normalizedHaarMeasure : Measure G)) F s).symm
    _ = ∫ t, π s (matrixCoefficientAveragedIntegrand π σ bπ bσ j l v t) ∂μG := by
          refine integral_congr_ae ?_
          filter_upwards with t
          simpa [F] using matrixCoefficientAveragedIntegrand_mul_left π σ bπ bσ j l s t v
    _ = π s (∫ t, matrixCoefficientAveragedIntegrand π σ bπ bσ j l v t ∂μG) := by
          simpa [Representation.toContinuousLinearEquivHom_apply_apply] using
            (ContinuousLinearEquiv.integral_comp_comm (π.toContinuousLinearEquivHom s)
              (matrixCoefficientAveragedIntegrand π σ bπ bσ j l v))
    _ = π s (matrixCoefficientAveragedMap π σ bπ bσ j l v) := by
          rfl

/-- Helper for Lemma 4-22: unitarity turns the inverse-action coefficient into the conjugate of
the original matrix coefficient. -/
theorem matrixCoefficientConj_eq_inner_inv
    {ισ : Type w''} [Fintype ισ]
    (σ : Representation ℂ G Hσ) [Representation.IsUnitary σ]
    (bσ : OrthonormalBasis ισ ℂ Hσ) (k l : ισ) (t : G) :
    ⟪bσ l, σ t⁻¹ (bσ k)⟫_ℂ = conj (mc[σ, bσ, k, l] t) := by
  -- Apply the isometry `σ t` to both entries of the inner product and then use conjugate symmetry.
  let e : Hσ →ₗᵢ[ℂ] Hσ := (σ t).toLinearIsometry (Representation.isometry σ t)
  have hmap :
      ⟪σ t (bσ l), σ t (σ t⁻¹ (bσ k))⟫_ℂ = ⟪bσ l, σ t⁻¹ (bσ k)⟫_ℂ := by
    change ⟪e (bσ l), e (σ t⁻¹ (bσ k))⟫_ℂ = ⟪bσ l, σ t⁻¹ (bσ k)⟫_ℂ
    exact LinearIsometry.inner_map_map e (bσ l) (σ t⁻¹ (bσ k))
  have hs : σ t (σ t⁻¹ (bσ k)) = bσ k := by
    simpa [Representation.toContinuousLinearEquivHom_apply_apply] using
      (σ.toContinuousLinearEquivHom t).apply_symm_apply (bσ k)
  calc
    ⟪bσ l, σ t⁻¹ (bσ k)⟫_ℂ = ⟪σ t (bσ l), σ t (σ t⁻¹ (bσ k))⟫_ℂ := by
      exact hmap.symm
    _ = ⟪σ t (bσ l), bσ k⟫_ℂ := by rw [hs]
    _ = conj ⟪bσ k, σ t (bσ l)⟫_ℂ := by
      rw [inner_conj_symm]
    _ = conj (mc[σ, bσ, k, l] t) := by
      rw [matrixCoefficient_eq_inner]

/-- Helper for Lemma 4-22: the `(i,k)` entry of the averaged map is the target matrix-coefficient
integral. -/
theorem matrixCoefficientAveragedMap_inner_eq_integral
    {ιπ : Type w'} [Fintype ιπ] {ισ : Type w''} [Fintype ισ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsUnitary π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ] [Representation.IsUnitary σ]
    (bπ : OrthonormalBasis ιπ ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (i j : ιπ) (k l : ισ) :
    ⟪bπ i, matrixCoefficientAveragedMap π σ bπ bσ j l (bσ k)⟫_ℂ =
      ∫ t, mc[π, bπ, i, j] t * conj (mc[σ, bσ, k, l] t) ∂μG := by
  let f : G → Hπ := matrixCoefficientAveragedIntegrand π σ bπ bσ j l (bσ k)
  have hf : Integrable f μG :=
    matrixCoefficientAveragedIntegrand_integrable π σ bπ bσ j l (bσ k)
  -- Commute the inner product with the integral, then simplify the pointwise integrand.
  calc
    ⟪bπ i, matrixCoefficientAveragedMap π σ bπ bσ j l (bσ k)⟫_ℂ
      = ⟪bπ i, ∫ t, f t ∂μG⟫_ℂ := by
          rfl
    _ = ∫ t, ⟪bπ i, f t⟫_ℂ ∂μG := by
          simpa [f] using
            (ContinuousLinearMap.integral_comp_comm (innerSL ℂ (bπ i)) hf).symm
    _ = ∫ t, mc[π, bπ, i, j] t * conj (mc[σ, bσ, k, l] t) ∂μG := by
          refine integral_congr_ae ?_
          filter_upwards with t
          calc
            ⟪bπ i, f t⟫_ℂ
              = ⟪bπ i, π t ((InnerProductSpace.rankOne ℂ (bπ j) (bσ l)) (σ t⁻¹ (bσ k)))⟫_ℂ := by
                  rfl
            _ = ⟪bπ i, π t (⟪bσ l, σ t⁻¹ (bσ k)⟫_ℂ • bπ j)⟫_ℂ := by
                  simp [f, matrixCoefficientAveragedIntegrand]
            _ = ⟪bσ l, σ t⁻¹ (bσ k)⟫_ℂ * ⟪bπ i, π t (bπ j)⟫_ℂ := by
                  simp
            _ = conj (mc[σ, bσ, k, l] t) * mc[π, bπ, i, j] t := by
                  rw [matrixCoefficientConj_eq_inner_inv, ← matrixCoefficient_eq_inner]
            _ = mc[π, bπ, i, j] t * conj (mc[σ, bσ, k, l] t) := by
                  ring

/-- Helper for Lemma 4-22: summing the diagonal matrix-coefficient products gives the Kronecker
delta `δ_jl`. -/
theorem matrixCoefficientDiagonalSum_eq_kronecker
    {ι : Type w'} [Fintype ι] [DecidableEq ι]
    (π : Representation ℂ G Hπ) [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ) (j l : ι) (t : G) :
    ∑ i, mc[π, b, i, j] t * conj (mc[π, b, i, l] t) = if j = l then 1 else 0 := by
  let e : Hπ →ₗᵢ[ℂ] Hπ := (π t).toLinearIsometry (Representation.isometry π t)
  have hsum :
      ∑ i, ⟪π t (b l), b i⟫_ℂ * ⟪b i, π t (b j)⟫_ℂ =
        ⟪π t (b l), π t (b j)⟫_ℂ := by
    simpa using OrthonormalBasis.sum_inner_mul_inner b (π t (b l)) (π t (b j))
  have hunit : ⟪π t (b l), π t (b j)⟫_ℂ = ⟪b l, b j⟫_ℂ := by
    exact LinearIsometry.inner_map_map e (b l) (b j)
  have hbasis : ⟪b l, b j⟫_ℂ = if j = l then 1 else 0 := by
    simpa [eq_comm] using b.repr_apply_apply (b j) l
  -- Convert the diagonal sum into the orthonormal-basis completeness relation.
  calc
    ∑ i, mc[π, b, i, j] t * conj (mc[π, b, i, l] t)
      = ∑ i, ⟪π t (b l), b i⟫_ℂ * ⟪b i, π t (b j)⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [matrixCoefficient_eq_inner, matrixCoefficient_eq_inner, inner_conj_symm, mul_comm]
    _ = ⟪π t (b l), π t (b j)⟫_ℂ := hsum
    _ = ⟪b l, b j⟫_ℂ := hunit
    _ = if j = l then 1 else 0 := hbasis

/-- Lemma 4-22 (1): for nonisomorphic irreducible unitary representations `π` and `σ` of a
compact group, the integral of `mc[π, bπ, i, j] t * conj (mc[σ, bσ, k, l] t)` over `G` is `0`. -/
theorem matrixCoefficientIntegral_eq_zero_of_not_isomorphic
    {ιπ : Type w'} [Fintype ιπ] {ισ : Type w''} [Fintype ισ]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (σ : Representation ℂ G Hσ) [Representation.IsContinuous σ] [Representation.IsIrreducible σ]
    [Representation.IsUnitary π] [Representation.IsUnitary σ]
    (bπ : OrthonormalBasis ιπ ℂ Hπ) (bσ : OrthonormalBasis ισ ℂ Hσ)
    (i j : ιπ) (k l : ισ) (hπσ : ¬ Nonempty (π.Equiv σ)) :
    ∫ t, mc[π, bπ, i, j] t * conj (mc[σ, bσ, k, l] t) ∂μG = 0 := by
  let T := matrixCoefficientAveragedMap π σ bπ bσ j l
  let TI : σ.IntertwiningMap π :=
    T.intertwiningMap_of_isIntertwiningMap σ π
      (matrixCoefficientAveragedMap_isIntertwining π σ bπ bσ j l).isIntertwining
  have hσπ : ¬ Nonempty (σ.Equiv π) := by
    intro h
    exact hπσ ⟨h.some.symm⟩
  have hTI : TI = 0 :=
    Representation.intertwiningMap_eq_zero_of_not_isomorphic (ρ1 := σ) (ρ2 := π) TI hσπ
  have hT : T = 0 := by
    simpa [T, TI] using congrArg Representation.IntertwiningMap.toLinearMap hTI
  -- Schur kills the averaged intertwiner, so the target matrix entry of that map is zero.
  calc
    ∫ t, mc[π, bπ, i, j] t * conj (mc[σ, bσ, k, l] t) ∂μG
      = ⟪bπ i, T (bσ k)⟫_ℂ := by
          simpa [T] using
            (matrixCoefficientAveragedMap_inner_eq_integral π σ bπ bσ i j k l).symm
    _ = 0 := by
          simp [hT]

/-- Lemma 4-22 (2): for an irreducible unitary representation `π` of a compact group, the
integral of `mc[π, b, i, j] t * conj (mc[π, b, k, l] t)` over `G` is
`(dim_ℂ Hπ)⁻¹ δ_ik δ_jl`. -/
theorem matrixCoefficientIntegral_eq_inv_finrank_mul_kronecker
    {ι : Type w'} [Fintype ι] [DecidableEq ι]
    (π : Representation ℂ G Hπ) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    [Representation.IsUnitary π]
    (b : OrthonormalBasis ι ℂ Hπ) (i j k l : ι) :
    ∫ t, mc[π, b, i, j] t * conj (mc[π, b, k, l] t) ∂μG =
      (Module.finrank ℂ Hπ : ℂ)⁻¹ * (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
  let T := matrixCoefficientAveragedMap π π b b j l
  let TI : π.IntertwiningMap π :=
    T.intertwiningMap_of_isIntertwiningMap π π
      (matrixCoefficientAveragedMap_isIntertwining π π b b j l).isIntertwining
  obtain ⟨c, hTI⟩ :=
    Representation.intertwiningMap_eq_smul_id (ρ := π) TI
  have hT : T = c • LinearMap.id := by
    simpa [T, TI] using congrArg Representation.IntertwiningMap.toLinearMap hTI
  have hT_apply (x : Hπ) : T x = c • x := by
    simpa using congrArg (fun f : Hπ →ₗ[ℂ] Hπ ↦ f x) hT
  have hsumIntegral :
      ∑ m, ∫ t, mc[π, b, m, j] t * conj (mc[π, b, m, l] t) ∂μG =
        if j = l then 1 else 0 := by
    have hIntTerm (m : ι) :
        Integrable (fun t ↦ mc[π, b, m, j] t * conj (mc[π, b, m, l] t)) μG := by
      have hmj_eq :
          (fun t ↦ mc[π, b, m, j] t) = fun t ↦ ⟪b m, π t (b j)⟫_ℂ := by
        funext t
        rw [matrixCoefficient_eq_inner]
      have hml_eq :
          (fun t ↦ mc[π, b, m, l] t) = fun t ↦ ⟪b m, π t (b l)⟫_ℂ := by
        funext t
        rw [matrixCoefficient_eq_inner]
      have hmj : Continuous fun t ↦ mc[π, b, m, j] t := by
        rw [hmj_eq]
        exact ((innerSL ℂ (b m)).continuous.comp (Representation.continuous_apply π (b j)))
      have hmllin : Continuous fun t ↦ mc[π, b, m, l] t := by
        rw [hml_eq]
        exact ((innerSL ℂ (b m)).continuous.comp (Representation.continuous_apply π (b l)))
      have hml : Continuous fun t ↦ conj (mc[π, b, m, l] t) := by
        exact Complex.continuous_conj.comp hmllin
      have hIntOn :
          IntegrableOn (fun t ↦ mc[π, b, m, j] t * conj (mc[π, b, m, l] t)) Set.univ μG :=
        ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ
          ((hmj.mul hml).continuousOn)
      simpa [MeasureTheory.integrableOn_univ] using hIntOn
    -- Sum first over the basis index, then use the pointwise orthonormality identity.
    calc
      ∑ m, ∫ t, mc[π, b, m, j] t * conj (mc[π, b, m, l] t) ∂μG
        = ∫ t, ∑ m, mc[π, b, m, j] t * conj (mc[π, b, m, l] t) ∂μG := by
            rw [integral_finset_sum Finset.univ (fun m _ ↦ hIntTerm m)]
      _ = ∫ t, (if j = l then 1 else 0 : ℂ) ∂μG := by
            refine integral_congr_ae ?_
            filter_upwards with t
            simpa using matrixCoefficientDiagonalSum_eq_kronecker π b j l t
      _ = if j = l then 1 else 0 := by
            by_cases h : j = l
            · rw [if_pos h]
              rw [integral_const]
              simp [μG]
              exact one_smul ℂ (1 : ℂ)
            · rw [if_neg h]
              simpa using (integral_zero : ∫ t, (0 : ℂ) ∂μG = 0)
  have hsumScalar :
      ∑ m, ∫ t, mc[π, b, m, j] t * conj (mc[π, b, m, l] t) ∂μG =
        (Module.finrank ℂ Hπ : ℂ) * c := by
    have hsumInner :
        ∑ m, ⟪b m, T (b m)⟫_ℂ = (Module.finrank ℂ Hπ : ℂ) * c := by
      calc
        ∑ m, ⟪b m, T (b m)⟫_ℂ = ∑ m, c := by
            refine Finset.sum_congr rfl ?_
            intro m _
            symm
            have hbm : ⟪b m, b m⟫_ℂ = (1 : ℂ) := by
              simpa using b.repr_apply_apply (b m) m
            calc
              c = ⟪b m, c • b m⟫_ℂ := by
                    rw [inner_smul_right, hbm, mul_one]
              _ = ⟪b m, T (b m)⟫_ℂ := by
                    rw [hT_apply (b m)]
        _ = (Fintype.card ι : ℂ) * c := by
            simp [nsmul_eq_mul, mul_comm]
        _ = (Module.finrank ℂ Hπ : ℂ) * c := by
            rw [Module.finrank_eq_card_basis b.toBasis]
    -- The same diagonal sum is the trace of `T`, so Schur reduces it to a scalar multiple.
    calc
      ∑ m, ∫ t, mc[π, b, m, j] t * conj (mc[π, b, m, l] t) ∂μG
        = ∑ m, ⟪b m, T (b m)⟫_ℂ := by
            refine Finset.sum_congr rfl ?_
            intro m _
            simpa [T] using
              (matrixCoefficientAveragedMap_inner_eq_integral π π b b m j m l).symm
      _ = (Module.finrank ℂ Hπ : ℂ) * c := hsumInner
  letI : Nontrivial Hπ := ⟨⟨0, b i, by
    simpa using (b.orthonormal.ne_zero i).symm⟩⟩
  have hfin : (Module.finrank ℂ Hπ : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Module.finrank_pos (R := ℂ) (M := Hπ)))
  have hc :
      c = (Module.finrank ℂ Hπ : ℂ)⁻¹ * (if j = l then 1 else 0) := by
    have hmul : (Module.finrank ℂ Hπ : ℂ) * c = if j = l then 1 else 0 := by
      rw [← hsumScalar]
      exact hsumIntegral
    calc
      c = (1 : ℂ) * c := by simp
      _ = ((Module.finrank ℂ Hπ : ℂ)⁻¹ * (Module.finrank ℂ Hπ : ℂ)) * c := by
            rw [inv_mul_cancel₀ hfin]
      _ = (Module.finrank ℂ Hπ : ℂ)⁻¹ * ((Module.finrank ℂ Hπ : ℂ) * c) := by
            ring
      _ = (Module.finrank ℂ Hπ : ℂ)⁻¹ * (if j = l then 1 else 0) := by
            rw [hmul]
  -- Substitute the scalar identified from the diagonal sum back into the `(i,k)` matrix entry.
  calc
    ∫ t, mc[π, b, i, j] t * conj (mc[π, b, k, l] t) ∂μG
      = ⟪b i, T (b k)⟫_ℂ := by
          simpa [T] using
            (matrixCoefficientAveragedMap_inner_eq_integral π π b b i j k l).symm
    _ = ⟪b i, c • b k⟫_ℂ := by
          rw [hT_apply (b k)]
    _ = if i = k then c else 0 := by
          have hbik : ⟪b i, b k⟫_ℂ = if i = k then 1 else 0 := by
            simpa using (b.repr_apply_apply (b k) i).symm
          by_cases hik : i = k
          · subst k
            have hbk : ⟪b i, b i⟫_ℂ = (1 : ℂ) := by
              simpa using b.repr_apply_apply (b i) i
            rw [inner_smul_right, hbk, mul_one]
            simp
          · rw [inner_smul_right, hbik, if_neg hik, mul_zero, if_neg hik]
    _ = (Module.finrank ℂ Hπ : ℂ)⁻¹ * (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
          rw [hc]
          by_cases hik : i = k <;> by_cases hjl : j = l <;>
            simp [hik, hjl, mul_assoc, mul_left_comm, mul_comm]

end Orthogonality

end Representation
