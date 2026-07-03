import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.IsLocalHomeomorph
import SmoothManifoldsLee.Chap01.Sec01_04.Example_1_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped LinearAlgebra.Projectivization Manifold ContDiff

universe u

variable {n : ℕ}
variable {V : Type u} [AddCommGroup V] [Module ℝ V]

instance [TopologicalSpace V] : TopologicalSpace (ℙ ℝ V) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℝ V)))

namespace Projectivization

/-- The linear equivalence sending the standard coordinates on `ℝ^(n+1)` to the basis `b` of
`V`. -/
abbrev basisLinearEquiv (b : Module.Basis (Fin (n + 1)) ℝ V) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] V :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).toLinearEquiv.trans b.equivFun.symm

/-- The map on projectivizations induced by a linear equivalence. -/
private def mapLinearEquiv
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (e : E ≃ₗ[ℝ] F) : ℙ ℝ E → ℙ ℝ F :=
  Projectivization.map e.toLinearMap e.injective

/-- Mapping projective space across a linear equivalence and then back along its inverse is the
identity. -/
private theorem mapLinearEquiv_symm_apply_apply
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (e : E ≃ₗ[ℝ] F) (x : ℙ ℝ E) :
    mapLinearEquiv (e.symm) (mapLinearEquiv e x) = x := sorry

/-- Mapping projective space first along the inverse linear equivalence and then forward is the
identity. -/
private theorem mapLinearEquiv_apply_symm_apply
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (e : E ≃ₗ[ℝ] F) (x : ℙ ℝ F) :
    mapLinearEquiv e (mapLinearEquiv (e.symm) x) = x := sorry

/-- The projectivization equivalence induced by a linear equivalence. -/
private def equivLinearEquiv
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (e : E ≃ₗ[ℝ] F) : ℙ ℝ E ≃ ℙ ℝ F where
  toFun := mapLinearEquiv e
  invFun := mapLinearEquiv (e.symm)
  left_inv := mapLinearEquiv_symm_apply_apply e
  right_inv := mapLinearEquiv_apply_symm_apply e

/-- The map on projectivizations induced by the basis `b`. The source is the repository's
canonical owner `ℝP[n] = ℙ ℝ (EuclideanSpace ℝ (Fin (n + 1)))`. -/
def basisMap (b : Module.Basis (Fin (n + 1)) ℝ V) : ℝP[n] → ℙ ℝ V :=
  mapLinearEquiv (basisLinearEquiv b)

/-- The inverse projectivization map induced by the inverse basis equivalence. -/
def basisMapSymm (b : Module.Basis (Fin (n + 1)) ℝ V) : ℙ ℝ V → ℝP[n] :=
  mapLinearEquiv ((basisLinearEquiv b).symm)

/-- The basis-induced equivalence between the canonical standard real projective space and
`ℙ ℝ V`. -/
def basisEquiv (b : Module.Basis (Fin (n + 1)) ℝ V) : ℝP[n] ≃ ℙ ℝ V :=
  equivLinearEquiv (basisLinearEquiv b)

private abbrev topologicalSpaceOfBasis (b : Module.Basis (Fin (n + 1)) ℝ V) :
    TopologicalSpace (ℙ ℝ V) :=
  (basisEquiv b).symm.topologicalSpace

/-- Transport a standard chart on `ℝP[n]` across the basis homeomorphism. -/
private def chartOfBasis (b : Module.Basis (Fin (n + 1)) ℝ V)
    (e : OpenPartialHomeomorph ℝP[n] (EuclideanSpace ℝ (Fin n))) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    OpenPartialHomeomorph (ℙ ℝ V) (EuclideanSpace ℝ (Fin n)) :=
  let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
  ((basisEquiv b).symm.homeomorph).toOpenPartialHomeomorph.trans e

private abbrev chartedSpaceOfBasis (b : Module.Basis (Fin (n + 1)) ℝ V) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) :=
  let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
  (ChartedSpace.mk
    {e | ∃ e' ∈ atlas (EuclideanSpace ℝ (Fin n)) (ℝP[n]), e = chartOfBasis b e'}
    (fun x ↦ chartOfBasis b (chartAt (EuclideanSpace ℝ (Fin n)) ((basisEquiv b).symm x)))
    (by
      intro x
      simp [chartOfBasis])
    (by
      intro x
      refine ⟨chartAt (EuclideanSpace ℝ (Fin n)) ((basisEquiv b).symm x), ?_, rfl⟩
      exact chart_mem_atlas (EuclideanSpace ℝ (Fin n)) ((basisEquiv b).symm x)) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V))

private theorem isManifoldOfBasis (b : Module.Basis (Fin (n + 1)) ℝ V) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    let _ : @ChartedSpace (EuclideanSpace ℝ (Fin n)) _ (ℙ ℝ V) (topologicalSpaceOfBasis b) :=
      chartedSpaceOfBasis b
    IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := by
  sorry

section QuotientTopology

variable
    [TopologicalSpace V]
    [IsTopologicalAddGroup V]
    [ContinuousSMul ℝ V]
    [T2Space V]

/-- A continuous linear equivalence from the standard Euclidean model to `V`, induced by the
chosen basis `b`. This is the canonical topological owner for the continuity and manifold
transport layer. -/
private abbrev basisContinuousLinearEquiv (b : Module.Basis (Fin (n + 1)) ℝ V) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] V :=
  let _ : FiniteDimensional ℝ V := b.finiteDimensional_of_finite
  (basisLinearEquiv b).toContinuousLinearEquiv

/-- A continuous linear equivalence induces a continuous map on projectivizations. -/
theorem continuous_map_continuousLinearEquiv
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (e : E ≃L[ℝ] F) :
    Continuous (Projectivization.map e.toLinearMap e.injective : ℙ ℝ E → ℙ ℝ F) := by
  let f : { v : E // v ≠ 0 } → { v : F // v ≠ 0 } :=
    fun v ↦ ⟨e v, fun h ↦ v.2 <| e.injective <| by simpa using h⟩
  have hf : Continuous f := by
    exact Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  simpa [Projectivization.map, f] using
    hf.quotient_map' <| by
      intro u v h
      have h' : ∃ a : ℝˣ, a • (v : E) = (u : E) := by
        simpa [projectivizationSetoid, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] using h
      rcases h' with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      dsimp [f]
      rw [← ha]
      exact (e.map_smul (↑a) (v : E)).symm

/-- The basis-induced map on projectivizations is continuous for the quotient topologies. -/
private theorem continuous_basisMap (b : Module.Basis (Fin (n + 1)) ℝ V) :
    Continuous (basisMap b) := by
  simpa [basisMap, basisContinuousLinearEquiv] using
    continuous_map_continuousLinearEquiv (basisContinuousLinearEquiv b)

/-- The inverse basis-induced projectivization map is continuous. -/
private theorem continuous_basisMapSymm (b : Module.Basis (Fin (n + 1)) ℝ V) :
    Continuous (basisMapSymm b) := by
  simpa [basisMapSymm, basisContinuousLinearEquiv] using
    continuous_map_continuousLinearEquiv (basisContinuousLinearEquiv b).symm

end QuotientTopology

end Projectivization

namespace Projectivization

/-- A smooth structure on `ℙ ℝ V` is basis-compatible if every basis-induced map from the
standard real projective space `ℝP[n]` is a diffeomorphism for that fixed ambient manifold
structure. This is the source-facing basis-independence condition for Problem 2-11. -/
def BasisCompatible [TopologicalSpace (ℙ ℝ V)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V)]
    [IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V)] : Prop :=
  ∀ b : Module.Basis (Fin (n + 1)) ℝ V,
    ContMDiff (𝓡 n) (𝓡 n) ∞ (basisMap b) ∧
      ContMDiff (𝓡 n) (𝓡 n) ∞ (basisMapSymm b)

private theorem basisCompatible_ofBasis (b₀ : Module.Basis (Fin (n + 1)) ℝ V) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b₀
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := chartedSpaceOfBasis b₀
    let _ : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := isManifoldOfBasis b₀
    BasisCompatible (n := n) (V := V) := by
  sorry

end Projectivization

variable [FiniteDimensional ℝ V]

/-- Problem 2-11: if `V` is a real vector space of dimension `n + 1`, then `ℙ ℝ V` carries a
smooth `n`-manifold structure for which every basis-induced map `ℝP[n] → ℙ ℝ V` is a
diffeomorphism. The public owner is the ambient topological, charted, and manifold structure on
`ℙ ℝ V`; the chosen-basis transport used to construct those instances remains internal. -/
theorem real_projectivization_exists_basisCompatible_smoothStructure
    (hn : Module.finrank ℝ V = n + 1) :
    ∃ _ : TopologicalSpace (ℙ ℝ V),
      ∃ _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V),
        ∃ _ : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V),
          Projectivization.BasisCompatible (n := n) (V := V) := by
  let b := Module.finBasisOfFinrankEq ℝ V hn
  let t : TopologicalSpace (ℙ ℝ V) := Projectivization.topologicalSpaceOfBasis b
  let c : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) :=
    Projectivization.chartedSpaceOfBasis b
  let m : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := Projectivization.isManifoldOfBasis b
  refine ⟨t, c, m, ?_⟩
  letI : TopologicalSpace (ℙ ℝ V) := t
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := c
  letI : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := m
  simpa [b, t, c, m] using Projectivization.basisCompatible_ofBasis (n := n) b
