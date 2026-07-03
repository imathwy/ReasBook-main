import Mathlib
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.Tactic.Recall
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.IsLocalHomeomorph

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_11_extra_1 (from Chap02/Sec02_11) -/
universe u

namespace ContinuousMap

variable {M : Type u} [TopologicalSpace M]

/- Definition 2.11-extra-1: Proposition 2.25 expresses the bump-function conditions directly by
bounding the range in `[0, 1]`, requiring `EqOn ψ 1 A`, and requiring `tsupport ψ ⊆ U`. -/
#check Set.EqOn
#check tsupport

/-- The constant function `1` satisfies the bump-function conditions on the whole space. -/
theorem one_bumpConditions_univ :
    Set.range (1 : C(M, ℝ)) ⊆ Set.Icc (0 : ℝ) 1 ∧
      Set.EqOn (1 : C(M, ℝ)) 1 Set.univ ∧ tsupport (1 : C(M, ℝ)) ⊆ Set.univ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    simp
  · simp
  · simp

end ContinuousMap

/-! ### Definition_2_11_extra_2 (from Chap02/Sec02_11) -/
open scoped Manifold ContDiff
open TopologicalSpace

universe uK uE uH uM uE2 uH2 uN

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE2} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH2} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}

namespace Function

/-- Definition 2.11-extra-2: A map defined on a subset of a smooth manifold is smooth if every
point of the subset has an open neighborhood on which the map extends to a smooth map. We express
the local extension through the canonical owner `C^∞⟮I, U; I', N⟯` for smooth maps on the open set
`U : Opens M`. -/
def IsSmoothOn {A : Set M} (f : A → N) (I : ModelWithCorners 𝕜 E H)
    (I' : ModelWithCorners 𝕜 E' H') : Prop :=
  ∀ p : A,
    ∃ U : Opens M,
      (p : M) ∈ U ∧
        ∃ Fext : C^∞⟮I, U; I', N⟯,
          ∀ q : A, (hq : (q : M) ∈ U) → Fext ⟨q, hq⟩ = f q

/-- `Function.IsSmoothOn` is equivalent to the unbundled local-extension formulation. -/
theorem isSmoothOn_iff_exists_local_extension {A : Set M} {f : A → N} :
    f.IsSmoothOn I I' ↔
      ∀ p : A,
        ∃ U : Set M,
          IsOpen U ∧
            (p : M) ∈ U ∧
              ∃ Fext : M → N,
                ContMDiffOn I I' (∞ : ℕ∞ω) Fext U ∧
                  ∀ q : A, (q : M) ∈ U → Fext q = f q := by
  classical
  constructor
  · intro hf p
    rcases hf p with ⟨U, hpU, Fext, hFext⟩
    refine ⟨U, U.isOpen, hpU, ?_⟩
    let G : M → N := fun x ↦ if hx : x ∈ U then Fext ⟨x, hx⟩ else Fext ⟨p, hpU⟩
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      have hG_subtype : ContMDiffAt I I' (∞ : ℕ∞ω) (fun y : U ↦ G y) ⟨x, hx⟩ := by
        have hEq : (fun y : U ↦ G y) = Fext := by
          funext y
          change G y = Fext y
          simp [G]
        rw [hEq]
        exact Fext.contMDiff ⟨x, hx⟩
      exact (contMDiffAt_subtype_iff.1 hG_subtype).contMDiffWithinAt
    · intro q hq
      unfold G
      split_ifs with h
      · simpa using hFext q h
      · exact (h hq).elim
  · intro hf p
    rcases hf p with ⟨U, hU, hpU, Fext, hFext, hEq⟩
    let Uo : Opens M := ⟨U, hU⟩
    refine ⟨Uo, hpU, ?_⟩
    refine ⟨⟨fun x : Uo ↦ Fext x, ?_⟩, ?_⟩
    · intro x
      exact contMDiffAt_subtype_iff.2 <|
        (hFext x x.property).contMDiffAt <|
          hU.mem_nhds x.property
    · intro q hq
      exact hEq q hq

end Function

/-! ### Definition_2_11_extra_3 (from Chap02/Sec02_11) -/
universe u

namespace Function

open Filter Set

variable {M : Type u} [TopologicalSpace M]

/-- Definition 2.11-extra-3: An exhaustion function on `M` is a continuous real-valued function
whose closed sublevel set `f ⁻¹' Iic c` is compact for every `c : ℝ`. -/
@[mk_iff isExhaustionFunction_iff]
class IsExhaustionFunction (f : M → ℝ) : Prop where
  continuous : Continuous f
  isCompact_sublevelSet (c : ℝ) : IsCompact (f ⁻¹' Iic c)

/-- An exhaustion function tends to `+∞` away from compact sets. -/
theorem IsExhaustionFunction.tendsto_atTop {f : M → ℝ} (hf : f.IsExhaustionFunction) :
    Tendsto f (cocompact M) atTop := by
  rw [Filter.atTop_basis_Ioi.tendsto_right_iff]
  intro c _
  change f ⁻¹' Ioi c ∈ cocompact M
  convert (hf.isCompact_sublevelSet c).compl_mem_cocompact using 1
  ext x
  simp [not_le]

/-- Every exhaustion function is a proper map. -/
theorem IsExhaustionFunction.isProperMap {f : M → ℝ} (hf : f.IsExhaustionFunction) :
    IsProperMap f :=
  isProperMap_iff_tendsto_cocompact.2 ⟨hf.continuous, hf.tendsto_atTop.trans atTop_le_cocompact⟩

/-- An exhaustion function canonically yields a proper map. -/
instance instIsProperMapOfIsExhaustionFunction {f : M → ℝ} [hf : f.IsExhaustionFunction] :
    IsProperMap f :=
  hf.isProperMap

/-- An exhaustion function canonically yields continuity of its underlying function. -/
instance instContinuousOfIsExhaustionFunction {f : M → ℝ} [hf : f.IsExhaustionFunction] :
    Continuous f :=
  hf.continuous

end Function

/-- Any continuous real-valued function on a compact space is an exhaustion function. -/
-- Proof sketch: for each `c`, the set `Set.Iic c` is closed in `ℝ`, so its preimage under a
-- continuous map is closed; closed subsets of a compact space are compact.
theorem Continuous.isExhaustionFunction {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {f : M → ℝ} (hf : Continuous f) : f.IsExhaustionFunction := by
  refine ⟨hf, fun c ↦ ?_⟩
  exact isCompact_univ.of_isClosed_subset (isClosed_Iic.preimage hf) (Set.subset_univ _)

/-! ### Exercise_2_11 (from Chap02/Sec02_08) -/
open TopologicalSpace
open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
variable {c : N} {U : Opens M}

/- Exercise 2.11 (1): part (a) of the preceding proposition is the canonical smoothness theorem
for constant maps between smooth manifolds. -/
recall contMDiff_const

/- Exercise 2.11 (2): part (b) of the preceding proposition is the canonical smoothness theorem
for the identity map of a smooth manifold. -/
recall contMDiff_id

/- Exercise 2.11 (3): part (c) of the preceding proposition is the canonical smoothness theorem
for the inclusion of an open submanifold `U : Opens M` into `M`. -/
recall contMDiff_subtype_val

/-! ### Problem_2_11 (from Chap02/Sec02_12) -/
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
