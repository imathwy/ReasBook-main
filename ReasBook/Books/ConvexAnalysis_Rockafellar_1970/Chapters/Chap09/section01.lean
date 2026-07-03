import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_9_1_0_2 (from Chap02) -/
open Set
open scoped Rockafellar

local notation "fstₗ[" 𝕜 "]" => (LinearMap.fst 𝕜 𝕜 𝕜 : (𝕜 × 𝕜) →ₗ[𝕜] 𝕜)

/-
Source/core/bridge triage:
- `source-facing`: this remark records a concrete counterexample showing that the recession cone of
  a linear image need not equal the image of the recession cone, even when both the source set and
  its image are closed.
- `core/canonical`: the owner abstraction in this domain is the Chapter 8 recession-cone API
  centered on `recessionCone`, together with the linear-image theorem
  `LinearMap.recessionCone_image_closure_eq_image_recessionCone` from Theorem 9.1. The linear
  map in the present concrete example is the canonical owner `LinearMap.fst 𝕜 𝕜 𝕜`.
- `bridge/view`: the set image under `LinearMap.fst 𝕜 𝕜 𝕜` is definitionally the first-coordinate
  projection image, so `Prod.fst` remains only an internal coercion view and not a second public
  owner for this file.
- Primitive data vs derived API: the primitive source datum `paraboloidEpigraph` and its basic
  owner-side facts `mem_paraboloidEpigraph_iff`, `paraboloidEpigraph_isClosed`, and
  `paraboloidEpigraph_convex` now live in the shared owner file. This remark keeps only the image
  and recession-cone calculations derived from that owner. The closedness of the image is not kept
  as a separate owner theorem here, because it is an immediate corollary of the image calculation
  `= univ`.
- Domain-style sampling used here: `recessionCone`, `0⁺`, `Set.mem_recessionCone_iff`,
  `LinearMap.recessionCone_image_closure_eq_image_recessionCone`, and
  `LinearMap.isClosed_image_of_recessionKernelTrivial`.
- Layer target: the public main entry stays `source-facing` as a concrete counterexample to the
  naive closed-image formula, rather than a second owner theorem parallel to Theorem 9.1.
  at the owner layer, while the closure-level counterexample is exposed first with the primitive
  closedness datum `IsClosed paraboloidEpigraph`; the stronger Theorem-9.1 ambient assumptions are
  used only in the downstream bridge that instantiates this datum via
  `paraboloidEpigraph_isClosed`.
-/

section Ordered

variable {𝕜 : Type*} [Semiring 𝕜] [Preorder 𝕜]

/-- The first-coordinate image of the paraboloid epigraph is all of `𝕜`. -/
-- Proof sketch: for any `η : 𝕜`, the point with coordinates `(η, η^2)` lies in the epigraph and
-- maps to `η`, so the image contains every scalar.
theorem paraboloidEpigraph_fst_image_eq_univ :
    fstₗ[𝕜] '' paraboloidEpigraph = (univ : Set 𝕜) := by
  ext η
  constructor
  · intro _
    simp
  · intro _
    refine ⟨(η, η ^ 2), ?_, rfl⟩
    simp

/-- The recession cone of the first-coordinate image of the paraboloid epigraph is all of `𝕜`. -/
-- Proof sketch: rewrite the image as `Set.univ`, and then observe that every forward ray stays in
-- `Set.univ`, so its recession cone is again `Set.univ`.
theorem recessionCone_paraboloidEpigraph_fst_image_eq_univ :
    0⁺[𝕜] (fstₗ[𝕜] '' paraboloidEpigraph) = (univ : Set 𝕜) := by
  rw [paraboloidEpigraph_fst_image_eq_univ, Set.recessionCone_univ]

end Ordered

section OrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The first-coordinate image of the recession cone of the paraboloid epigraph is exactly
`{0}`. -/
-- Proof sketch: if `z ∈ 0⁺[𝕜] paraboloidEpigraph`, the inequality
-- `ξ₂ + t z₂ ≥ (ξ₁ + t z₁)^2` for all `t ≥ 0` forces `z₁ = 0`; conversely, every vertical
-- direction with nonnegative second coordinate lies in the recession cone, so the projection image
-- is the singleton `{0}`.
theorem fst_image_recessionCone_paraboloidEpigraph_eq_singleton_zero :
    fstₗ[𝕜] '' 0⁺[𝕜] paraboloidEpigraph = ({0} : Set 𝕜) := by
  ext η
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Set.mem_recessionCone_iff] at hz
    by_cases hz1 : z.1 = 0
    · simp [hz1]
    · let ξ : 𝕜 := (z.2 - z.1 ^ 2 + 1) / (2 * z.1)
      have hξ_mem : (ξ, ξ ^ 2) ∈ paraboloidEpigraph := by
        simp
      have hmem := hz (ξ, ξ ^ 2) hξ_mem 1 zero_le_one
      have hquad : (ξ + z.1) ^ 2 ≤ ξ ^ 2 + z.2 := by
        simpa [mem_paraboloidEpigraph_iff] using hmem
      have hineq : z.2 ≥ 2 * ξ * z.1 + z.1 ^ 2 := by
        nlinarith [hquad]
      have hξ_eval : 2 * ξ * z.1 + z.1 ^ 2 = z.2 + 1 := by
        dsimp [ξ]
        field_simp [hz1]
        ring
      nlinarith [hineq, hξ_eval]
  · intro hη
    have hzero_mem : ((0 : 𝕜), (0 : 𝕜)) ∈ 0⁺[𝕜] paraboloidEpigraph := by
      rw [Set.mem_recessionCone_iff]
      intro x hx t ht
      rcases x with ⟨x₁, x₂⟩
      simpa [zero_smul, add_zero] using hx
    refine ⟨((0 : 𝕜), (0 : 𝕜)), hzero_mem, ?_⟩
    simpa using hη.symm

/-- Remark 9.1.0.2 in source-facing form on scalar `𝕜`:
for `C = {(ξ₁, ξ₂) | ξ₂ ≥ ξ₁²}` and `A (ξ₁, ξ₂) = ξ₁`, one has
`0⁺[𝕜] (A '' C) ≠ A '' 0⁺[𝕜] C`. -/
theorem recessionCone_fst_image_ne_fst_image_recessionCone_paraboloidEpigraph :
    0⁺[𝕜] (fstₗ[𝕜] '' paraboloidEpigraph) ≠
      fstₗ[𝕜] '' 0⁺[𝕜] paraboloidEpigraph := by
  rw [recessionCone_paraboloidEpigraph_fst_image_eq_univ,
    fst_image_recessionCone_paraboloidEpigraph_eq_singleton_zero]
  intro h
  have h1 : (1 : 𝕜) ∈ ({0} : Set 𝕜) := by
    simpa [h] using (show (1 : 𝕜) ∈ (univ : Set 𝕜) from trivial)
  simp at h1

end OrderedField

section Counterexample

variable {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜]

/-- Remark 9.1.0.2 on the Theorem-9.1 owner surface: even after writing the formula in closure
form, the paraboloid/projection example violates
`0⁺[𝕜] (A '' closure C) = A '' 0⁺[𝕜] (closure C)`. -/
theorem recessionCone_fst_image_closure_ne_fst_image_recessionCone_closure_paraboloidEpigraph :
    IsClosed (paraboloidEpigraph : Set (𝕜 × 𝕜)) →
    0⁺[𝕜] (fstₗ[𝕜] '' closure paraboloidEpigraph) ≠
      fstₗ[𝕜] '' 0⁺[𝕜] (closure paraboloidEpigraph) := by
  intro hClosed
  rw [hClosed.closure_eq]
  exact recessionCone_fst_image_ne_fst_image_recessionCone_paraboloidEpigraph (𝕜 := 𝕜)

/-- Source-facing existential counterexample form on the Theorem-9.1 owner surface:
there exist a closed convex set `C` and linear map `A` such that `A '' C` is closed but
`0⁺[𝕜] (A '' closure C) ≠ A '' 0⁺[𝕜] (closure C)`. -/
theorem exists_closed_convex_set_with_closed_linearImage_recessionCone_closure_image_ne :
    IsClosed (paraboloidEpigraph : Set (𝕜 × 𝕜)) →
    ∃ (C : Set (𝕜 × 𝕜)) (A : (𝕜 × 𝕜) →ₗ[𝕜] 𝕜),
      IsClosed C ∧ Convex 𝕜 C ∧ IsClosed (A '' C) ∧
        0⁺[𝕜] (A '' closure C) ≠ A '' 0⁺[𝕜] (closure C) := by
  intro hClosed
  refine ⟨paraboloidEpigraph, fstₗ[𝕜],
    hClosed, paraboloidEpigraph_convex, ?_, ?_⟩
  · rw [paraboloidEpigraph_fst_image_eq_univ]
    simp
  · exact recessionCone_fst_image_closure_ne_fst_image_recessionCone_closure_paraboloidEpigraph
      (𝕜 := 𝕜) hClosed

/-- Source-facing existential counterexample form of Remark 9.1.0.2:
there exist a closed convex set `C` and linear map `A` such that `A '' C` is closed and
`0⁺[𝕜] (A '' C) ≠ A '' 0⁺[𝕜] C`. -/
theorem exists_closed_convex_set_with_closed_linearImage_recessionCone_image_ne :
    IsClosed (paraboloidEpigraph : Set (𝕜 × 𝕜)) →
    ∃ (C : Set (𝕜 × 𝕜)) (A : (𝕜 × 𝕜) →ₗ[𝕜] 𝕜),
      IsClosed C ∧ Convex 𝕜 C ∧ IsClosed (A '' C) ∧ 0⁺[𝕜] (A '' C) ≠ A '' 0⁺[𝕜] C := by
  intro hClosed
  refine ⟨paraboloidEpigraph, fstₗ[𝕜],
    hClosed, paraboloidEpigraph_convex, ?_, ?_⟩
  · rw [paraboloidEpigraph_fst_image_eq_univ]
    simp
  · exact recessionCone_fst_image_ne_fst_image_recessionCone_paraboloidEpigraph

end Counterexample

section KernelLineality

variable {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsTopologicalRing 𝕜]

/-- The kernel-lineality hypothesis in Theorem 9.1 cannot hold for the
paraboloid/projection counterexample. -/
theorem not_recession_kernel_lineality_for_fst_paraboloidEpigraph :
    ¬ (fstₗ[𝕜].recessionKernelLeLineality (closure paraboloidEpigraph)) := by
  intro hkernel_lineality
  have hClosed : IsClosed (paraboloidEpigraph : Set (𝕜 × 𝕜)) := paraboloidEpigraph_isClosed
  have hCne : (paraboloidEpigraph : Set (𝕜 × 𝕜)).Nonempty := by
    exact ⟨(0, 0), by simp⟩
  have hEq :
      0⁺[𝕜] (fstₗ[𝕜] '' closure paraboloidEpigraph) =
        fstₗ[𝕜] '' 0⁺[𝕜] (closure paraboloidEpigraph) :=
    LinearMap.recessionCone_image_closure_eq_image_recessionCone
      (A := fstₗ[𝕜]) paraboloidEpigraph_convex hkernel_lineality hCne
  exact
    (recessionCone_fst_image_closure_ne_fst_image_recessionCone_closure_paraboloidEpigraph
      (𝕜 := 𝕜) hClosed) hEq

end KernelLineality

/-! ### Corollary_9_1_1 (from Chap02) -/
open scoped BigOperators Pointwise Rockafellar

section

universe u

open Set

section ZeroSumRecessionImpLineality

variable {ι : Type u} [Fintype ι]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E]

/-- Family-level compatibility condition from Corollary 9.1.1:
every zero-sum tuple of recession directions of the summand closures is termwise lineal in the
corresponding closure. -/
def Set.ZeroSumRecessionImpLineality
    (𝕜 : Type*) [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E] (C : ι → Set E) : Prop :=
  ∀ z : ι → E,
    (∀ i, z i ∈ 0⁺[𝕜] (closure (C i))) →
    (∑ i, z i) = 0 →
    ∀ i, z i ∈ lin[𝕜](closure (C i))

scoped[Rockafellar] notation:50 C " ⟂Σ₀⁺[" 𝕜 "]" =>
  Set.ZeroSumRecessionImpLineality 𝕜 C

end ZeroSumRecessionImpLineality

variable {ι : Type u} [Fintype ι]
variable
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜]
variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
  [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 9.1.1 gives closure and recession-cone formulas for a finite
  Minkowski sum `∑ i, C i` of convex sets under a zero-sum condition on recession directions, and
  deduces closedness when every summand is already closed. The source states this in `R^n`; the
  owner-level formalization keeps the same mathematics in an arbitrary finite-dimensional Hausdorff
  topological vector space indexed by an arbitrary finite type, with tuple-space
  finite-dimensionality treated as internal transport to Theorem 9.1.
- `core/canonical`: the owner abstraction is Theorem 9.1's linear-image criterion for closure and
  recession cones, specialized to the summation map on tuple space; the ambient owner notions are
  `closure`, the chapter owner `recessionCone`, the chapter owner `Set.lineal`, and the
  pointwise finite set sum `∑ i, C i`.
- `bridge/view`: the textbook family condition on tuples `(z₁, ..., z_m)` is expressed as a single
  hypothesis on functions `z : ι → E`; the conclusions remain direct set equalities and a
  closedness statement rather than a packaged family object.
- Domain-style sampling used here:
  `LinearMap.closure_image_eq_image_closure_of_recessionKernelLeLineality`,
  `LinearMap.recessionCone_image_closure_eq_image_recessionCone`, `recessionCone`,
  and `Set.lineal`.
- Primitive data vs derived API: the primitive inputs are the family `C`, its convexity
  hypothesis, and the zero-sum recession-direction condition. The closure identity,
  recession-cone identity, and closedness conclusion are the derived API, so they are exposed as
  separate atomic theorems. Familywise nonemptiness is not primitive here: if some summand is
  empty, then the finite pointwise sum is empty and all three conclusions are immediate.
- Layer target: this item stays `source-facing`, phrased directly in the canonical closure,
  recession-cone, lineality-space, and finite-sum language already used across the project.
-/

variable {C : ι → Set E}

private def sumLinearMap : (ι → E) →ₗ[𝕜] E where
  toFun z := ∑ i, z i
  map_add' x y := by
    classical
    simp [Finset.sum_add_distrib]
  map_smul' a z := by
    classical
    simp [Finset.smul_sum]

local notation "sumLM" => (sumLinearMap (𝕜 := 𝕜) (ι := ι) (E := E))

omit [TopologicalSpace 𝕜] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [T2Space E]
    [FiniteDimensional 𝕜 E] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] in
private theorem image_sumLinearMap_pi (S : ι → Set E) :
    sumLM '' pi univ S = ∑ i, S i := by
  change (fun z : ι → E ↦ ∑ i, z i) '' pi univ S = ∑ i, S i
  exact Set.image_fintype_sum_pi S

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [FiniteDimensional 𝕜 E] in
private theorem fintype_sum_eq_empty_of_eq_empty {S : ι → Set E} {i : ι} (hi : S i = ∅) :
    (∑ j, S j : Set E) = ∅ := by
  ext x
  constructor
  · intro hx
    rcases (Set.mem_fintype_sum S x).1 hx with ⟨y, hy, rfl⟩
    simpa [hi] using hy i
  · simp

omit [TopologicalSpace E] [Module 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [T2Space E] [FiniteDimensional 𝕜 E] in
private theorem fintype_sum_eq_univ_of_eq_univ (S : ι → Set E)
    (hzero : ∀ i, (0 : E) ∈ S i) {i : ι} (hi : S i = univ) :
    (∑ j, S j : Set E) = univ := by
  classical
  ext x
  constructor
  · intro _
    simp
  · intro _
    refine (mem_fintype_sum S x).2 ⟨Pi.single i x, ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · simp [hj, hi]
      · simpa [Pi.single, hj] using hzero j
    · exact Fintype.sum_pi_single' i x

omit [Fintype ι] [TopologicalSpace 𝕜] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] in
private theorem mem_recessionCone_pi_iff_of_nonempty {S : ι → Set E}
    (hne : ∀ i, (S i).Nonempty) {z : ι → E} :
    z ∈ 0⁺[𝕜] (pi univ S) ↔ ∀ i, z i ∈ 0⁺[𝕜] (S i) := by
  classical
  constructor
  · intro hz i
    rw [Set.mem_recessionCone_iff]
    intro x hx a ha
    choose y hy using hne
    let x' : ι → E := Function.update (fun j ↦ y j) i x
    have hx' : x' ∈ pi univ S := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        simp [x', hx]
      · simp [x', hji, hy j]
    have hxa : x' + a • z ∈ pi univ S := (Set.mem_recessionCone_iff.1 hz) x' hx' a ha
    simpa [x'] using hxa i (by simp)
  · intro hz
    rw [Set.mem_recessionCone_iff]
    intro x hx a ha i hi
    exact (Set.mem_recessionCone_iff.1 (hz i)) (x i) (hx i hi) a ha

omit [Fintype ι] [TopologicalSpace 𝕜] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] in
private theorem recessionCone_pi_eq_pi_recessionCone_of_nonempty {S : ι → Set E}
    (hne : ∀ i, (S i).Nonempty) :
    (0⁺[𝕜] (pi univ S) : Set (ι → E)) = pi univ (fun i ↦ 0⁺[𝕜] (S i)) := by
  ext z
  rw [mem_recessionCone_pi_iff_of_nonempty hne]
  simp

omit [TopologicalSpace 𝕜] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [FiniteDimensional 𝕜 E] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem sumLinearMap_kernel_le_lineality_of_zero_sum_recession_imp_lineality
    (hzero : C ⟂Σ₀⁺[𝕜])
    {z : ι → E} (hz : z ∈ 0⁺[𝕜] (closure (pi univ C)))
    (hzker : z ∈ (sumLM).ker) :
    z ∈ lin[𝕜](closure (pi univ C)) := by
  classical
  by_cases hne : ∀ i, (C i).Nonempty
  · have hclosure_nonempty : ∀ i, (closure (C i)).Nonempty :=
      fun i ↦ (hne i).mono subset_closure
    have hz_pi : z ∈ 0⁺[𝕜] (pi univ fun i ↦ closure (C i)) := by
      simpa [closure_pi_set] using hz
    have hz_coord : ∀ i, z i ∈ 0⁺[𝕜] (closure (C i)) :=
      (mem_recessionCone_pi_iff_of_nonempty hclosure_nonempty).mp hz_pi
    have hsum : (∑ i, z i) = 0 := by
      simpa [sumLinearMap] using LinearMap.mem_ker.mp hzker
    have hz_lineality : ∀ i, z i ∈ lin[𝕜](closure (C i)) := hzero z hz_coord hsum
    have hneg_coord : ∀ i, -z i ∈ 0⁺[𝕜] (closure (C i)) :=
      fun i ↦ (Set.mem_lineal_iff.mp (hz_lineality i)).2
    have hneg_pi : -z ∈ 0⁺[𝕜] (pi univ fun i ↦ closure (C i)) :=
      (mem_recessionCone_pi_iff_of_nonempty hclosure_nonempty).mpr fun i ↦ by
        simpa using hneg_coord i
    have hz_lineality_pi : z ∈ lin[𝕜](pi univ fun i ↦ closure (C i)) := by
      rw [Set.mem_lineal_iff]
      exact ⟨hz_pi, by simpa using hneg_pi⟩
    simpa [closure_pi_set] using hz_lineality_pi
  · have hnot_nonempty : ∃ i, ¬ (C i).Nonempty := by
      simpa only [not_forall] using hne
    obtain ⟨i, hi⟩ := hnot_nonempty
    have hCi : C i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    have hclosure_pi : closure (pi univ C) = ∅ := by
      calc
        closure (pi univ C) = pi univ (fun j ↦ closure (C j)) := by
          simp [closure_pi_set]
        _ = ∅ := by
          exact Set.univ_pi_eq_empty (by simpa [hCi])
    rw [Set.mem_lineal_iff]
    constructor <;> simp [hclosure_pi]

omit [TopologicalSpace 𝕜] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [FiniteDimensional 𝕜 E] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Canonical bridge from the source zero-sum recession condition to the Theorem 9.1 owner
hypothesis for the tuple-summation map. -/
private theorem sumLinearMap_recessionKernelLeLineality_of_zero_sum_recession_imp_lineality
    (hzero : C ⟂Σ₀⁺[𝕜]) :
    (sumLM).recessionKernelLeLineality (closure (pi univ C)) := by
  intro z hz
  exact sumLinearMap_kernel_le_lineality_of_zero_sum_recession_imp_lineality
    hzero hz.1 hz.2

/-- Corollary 9.1.1 (1), canonical-owner form: if the summation linear map satisfies the
Theorem 9.1 kernel-vs-lineality hypothesis on `closure (pi univ C)`, then the closure of the finite
Minkowski sum equals the finite sum of closures. -/
private theorem closure_sum_eq_sum_closure_of_recessionKernelLeLineality
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hkernel_lineality :
      (sumLM).recessionKernelLeLineality (closure (pi univ C))) :
    closure (∑ i, C i) = ∑ i, closure (C i) := by
  let A : (ι → E) →ₗ[𝕜] E := sumLM
  have hP_convex : Convex 𝕜 (pi univ C) := by
    simpa using (convex_pi fun i _ ↦ hconv i : Convex 𝕜 (pi univ C))
  have hclosure :
      closure (A '' pi univ C) = A '' closure (pi univ C) :=
    LinearMap.closure_image_eq_image_closure_of_recessionKernelLeLineality
      A hP_convex (by simpa [A] using hkernel_lineality)
  simpa [A, image_sumLinearMap_pi, closure_pi_set] using hclosure

/-- Corollary 9.1.1 (1): under the zero-sum recession-direction condition, the closure of the
finite Minkowski sum `C₁ + ··· + C_m` equals the finite Minkowski sum of the individual
closures. -/
-- Proof sketch: consider the product set `Set.pi Set.univ C ⊆ (ι → E)` and the linear
-- summation map `x ↦ ∑ i, x i`. The hypothesis exactly rules out nontrivial cancellation of
-- recession directions in the closures of the factors. If some factor is empty, both sides are
-- empty; otherwise the preceding theorem applies to the image of the product closure under the
-- summation map.
theorem Set.ZeroSumRecessionImpLineality.closure_sum_eq_sum_closure
    (hzero : C ⟂Σ₀⁺[𝕜])
    (hconv : ∀ i, Convex 𝕜 (C i)) :
    closure (∑ i, C i) = ∑ i, closure (C i) := by
  have hkernel_lineality :
      (sumLM).recessionKernelLeLineality (closure (pi univ C)) :=
    sumLinearMap_recessionKernelLeLineality_of_zero_sum_recession_imp_lineality
      hzero
  exact closure_sum_eq_sum_closure_of_recessionKernelLeLineality
    hconv hkernel_lineality

/-- Corollary 9.1.1 (2), canonical-owner form: under the same summation-map kernel-vs-lineality
hypothesis, the recession cone of the closure of the finite Minkowski sum is the finite sum of the
recession cones of the individual closures. -/
private theorem recessionCone_closure_sum_eq_sum_recessionCone_closure_of_recessionKernelLeLineality
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hkernel_lineality :
      (sumLM).recessionKernelLeLineality (closure (pi univ C))) :
    0⁺[𝕜] (closure (∑ i, C i)) = ∑ i, 0⁺[𝕜] (closure (C i)) := by
  classical
  by_cases hne : ∀ i, (C i).Nonempty
  · let P : Set (ι → E) := pi univ C
    let A : (ι → E) →ₗ[𝕜] E := sumLM
    have hP_convex : Convex 𝕜 P := by
      simpa [P] using (convex_pi fun i _ ↦ hconv i : Convex 𝕜 (pi univ C))
    have hP_nonempty : P.Nonempty := by
      change (pi univ C).Nonempty
      exact Set.univ_pi_nonempty_iff.2 hne
    have hcone :
        0⁺[𝕜] (A '' closure P) = A '' 0⁺[𝕜] (closure P) := by
      exact LinearMap.recessionCone_image_closure_eq_image_recessionCone
        A hP_convex (by simpa [A, P] using hkernel_lineality) hP_nonempty
    calc
      0⁺[𝕜] (closure (∑ i, C i)) = 0⁺[𝕜] (A '' closure P) := by
        rw [closure_sum_eq_sum_closure_of_recessionKernelLeLineality (C := C) hconv
          hkernel_lineality]
        rw [show ∑ i, closure (C i) = A '' closure P by
          simp [A, P, image_sumLinearMap_pi, closure_pi_set]]
      _ = A '' 0⁺[𝕜] (closure P) := hcone
      _ = A '' pi univ (fun i ↦ 0⁺[𝕜] (closure (C i))) := by
        congr 1
        rw [show closure P = pi univ (fun i ↦ closure (C i)) by
          simp [P, closure_pi_set]]
        exact recessionCone_pi_eq_pi_recessionCone_of_nonempty
          fun i ↦ (hne i).mono subset_closure
      _ = ∑ i, 0⁺[𝕜] (closure (C i)) := by
        simpa [A] using image_sumLinearMap_pi fun i ↦ 0⁺[𝕜] (closure (C i))
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (C i).Nonempty := by
      simpa only [not_forall] using hne
    have hCi : C i = ∅ := not_nonempty_iff_eq_empty.mp hi
    have hsum_empty : (∑ j, C j : Set E) = ∅ :=
      fintype_sum_eq_empty_of_eq_empty hCi
    have hi_univ : 0⁺[𝕜] (closure (C i)) = univ := by
      simp [hCi]
    have hsum_univ : (∑ j, 0⁺[𝕜] (closure (C j)) : Set E) = univ := by
      apply fintype_sum_eq_univ_of_eq_univ (fun j ↦ 0⁺[𝕜] (closure (C j)))
      · intro j
        rw [Set.mem_recessionCone_iff]
        intro x hx a ha
        simpa using hx
      exact hi_univ
    calc
      0⁺[𝕜] (closure (∑ i, C i)) = univ := by simp [hsum_empty]
      _ = ∑ i, 0⁺[𝕜] (closure (C i)) := hsum_univ.symm

/-- Corollary 9.1.1 (2): under the same hypothesis, the recession cone of the closure of the
finite Minkowski sum is the finite Minkowski sum of the recession cones of the individual
closures. -/
-- Proof sketch: apply the same product-set argument as in part (1), now to the recession cones of
-- the factor closures. If some summand is empty, part (1) reduces the claim to the empty-set
-- case; otherwise the recession cone of the direct product is the pointwise product of the factor
-- recession cones, and the summation map sends it to the recession cone of the summed closure.
theorem Set.ZeroSumRecessionImpLineality.recessionCone_closure_sum_eq_sum_recessionCone_closure
    (hzero : C ⟂Σ₀⁺[𝕜])
    (hconv : ∀ i, Convex 𝕜 (C i)) :
    0⁺[𝕜] (closure (∑ i, C i)) = ∑ i, 0⁺[𝕜] (closure (C i)) := by
  have hkernel_lineality :
      (sumLM).recessionKernelLeLineality (closure (pi univ C)) :=
    sumLinearMap_recessionKernelLeLineality_of_zero_sum_recession_imp_lineality
      hzero
  exact recessionCone_closure_sum_eq_sum_recessionCone_closure_of_recessionKernelLeLineality
    hconv hkernel_lineality

/-- Corollary 9.1.1 (3): if, in addition, all sets `C₁, …, C_m` are closed, then their finite
Minkowski sum is closed. -/
-- Proof sketch: if some summand is empty, the finite sum is empty and hence closed. Otherwise
-- part (1) identifies `closure (∑ i, C i)` with `∑ i, closure (C i)`. When every `C i` is
-- closed, each `closure (C i)` rewrites to `C i`, so the closure of the finite sum equals the sum
-- itself.
theorem Set.ZeroSumRecessionImpLineality.isClosed_sum
    (hzero : C ⟂Σ₀⁺[𝕜])
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hclosed : ∀ i, IsClosed (C i)) :
    IsClosed (∑ i, C i) := by
  rw [← closure_eq_iff_isClosed]
  calc
    closure (∑ i, C i) = ∑ i, closure (C i) :=
      hzero.closure_sum_eq_sum_closure hconv
    _ = ∑ i, C i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact (hclosed i).closure_eq

end

/-! ### Corollary_9_1_1_1 (from Chap02) -/
/-!
Source/core/bridge triage:
- `source-facing`: Corollary 9.1.1.1 isolates the closedness consequence of Corollary 9.1.1 for a
  finite Minkowski sum `C₁ + ··· + C_m`.
- `core/canonical`: the owner declaration is the already source-faithful theorem
  `Set.ZeroSumRecessionImpLineality.isClosed_sum` from Corollary 9.1.1.
- `bridge/view`: this file contributes no extra mathematics beyond isolating that already existing
  closedness clause, so it should reuse the owner theorem directly rather than restating it as a
  second exact-interface theorem.

Domain-style sampling used here:
- the owner theorem
  `Set.ZeroSumRecessionImpLineality.isClosed_sum`;
- the owner-side recession and lineality operators `0⁺[𝕜]` and `lin[𝕜](·)`;
- the owner-side closedness predicate `IsClosed`.

Primitive data vs derived API:
- this item adds no new primitive data beyond the hypotheses already accepted by the owner theorem;
- the only content is direct canonical reuse of that existing closedness statement.

Layer target: `bridge/view`; the file is a recall-only reuse of the canonical chapter theorem.
-/

/- Corollary 9.1.1.1 isolates the already established closedness clause of Corollary 9.1.1, so
the canonical chapter entry is recalled directly instead of introducing a duplicate theorem. -/
recall Set.ZeroSumRecessionImpLineality.isClosed_sum

/-! ### Theorem_9_1 (from Chap02) -/
open Set
open scoped Rockafellar

section

variable
    {𝕜 : Type*} [Semiring 𝕜] [LE 𝕜]
    {E F : Type*}
    [AddCommGroup E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F]

namespace LinearMap

/-- Kernel-vs-lineality side condition from Theorem 9.1:
every recession direction of `C` in `A.ker` lies in `lin[𝕜](C)`. -/
def recessionKernelLeLineality (A : E →ₗ[𝕜] F) (C : Set E) : Prop :=
  0⁺[𝕜] C ∩ (A.ker : Set E) ⊆ lin[𝕜](C)

/-- Trivial-kernel-recession side condition from Theorem 9.1 (3):
the only recession direction of `C` in `A.ker` is `0`. -/
def recessionKernelTrivial (A : E →ₗ[𝕜] F) (C : Set E) : Prop :=
  0⁺[𝕜] C ∩ (A.ker : Set E) ⊆ ({0} : Set E)

/-- Upstream owner bridge: the trivial-kernel recession condition implies the
kernel-vs-lineality condition. -/
theorem recessionKernelLeLineality_of_recessionKernelTrivial
    {A : E →ₗ[𝕜] F} {C : Set E}
    (hkernel_trivial : A.recessionKernelTrivial C) :
    A.recessionKernelLeLineality C := by
  intro z hz
  have hz0 : z = 0 := by
    have hz_mem : z ∈ ({0} : Set E) := hkernel_trivial hz
    simpa using hz_mem
  subst hz0
  rw [Set.mem_lineal_iff]
  constructor <;> rw [Set.mem_recessionCone_iff] <;>
    intro x hx a ha <;> simpa [zero_smul, add_zero] using hx

end LinearMap

section

variable
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜]
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
    [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 9.1 gives a closed-image criterion for a convex set under a linear map,
  together with the corresponding recession-cone image formula for the canonical closed image. The
  source states this in Euclidean spaces, but the intrinsic owner-level formulation only needs a
  finite-dimensional Hausdorff topological vector space over an ordered topological scalar field `𝕜`
  as source and a Hausdorff topological vector space over `𝕜` as target.
- `core/canonical`: the owner abstractions already present in the chapter are `Convex 𝕜 C`,
  `closure`, the set image `A '' C` of a `LinearMap`, the kernel owner `A.ker`,
  `0⁺[𝕜] C`, and `lin[𝕜](C)`.
- `bridge/view`: Rockafellar's notation `0⁺ C` is the real specialization (`𝕜 = ℝ`) of
  `0⁺[𝕜] C`, while the lineality space of `cl C` is rendered by `lin[𝕜](closure C)`. Under the
  part (1) hypothesis, the source's closed image `cl (A C)` is canonically the set `A '' closure C`,
  so part (2) is best exposed directly on that owner. The auxiliary source-facing predicate
  `RecedesInDirection` is only the nonzero view on `recessionCone`, so it is not the owner
  abstraction for the main hypotheses here.
- Domain-style sampling used here: `image_closure_subset_closure_image`,
  `LinearMap.continuous_of_finiteDimensional`, `LinearMap.isClosedEmbedding_of_injective`,
  `Submodule.closed_of_finiteDimensional`, `LinearMap.ker`, `recessionCone`, and
  `Set.lineal`.
- Primitive data vs derived API: the primitive inputs are the convex set `C`, the linear map `A`,
  and the owner-level kernel-versus-lineality hypothesis on recession directions of an ambient set,
  phrased intrinsically through the kernel submodule `A.ker`; in Theorem 9.1 this ambient set is
  `closure C`, passed explicitly in the theorem hypotheses. The core closed-image owner statement
  is first exposed as `IsClosed (A '' K)` on a closed convex ambient set `K`; the recession-cone
  image formula is likewise first exposed on such a closed convex nonempty ambient owner `K`. The
  source-facing closure/recession statements for `C` are then direct corollaries at
  `K = closure C`. The closure identity is derived directly from those data and does not need a
  nonemptiness hypothesis because it remains true for `C = ∅`; by contrast, the recession-cone
  image formula still genuinely needs nonemptiness, taken on the primitive source owner `C`.
  No norm structure and no finite-dimensional structure on the codomain are primitive data here.
  The Hausdorff codomain assumption is primitive for the closed-image clauses, because the canonical
  closed owner `A '' closure C` and the finite-dimensional linear-image closedness facts used in
  the background rely on the codomain Hausdorff condition, while continuity of `A` still follows
  from finite dimensionality of the Hausdorff source.
- Layer target: part (1) and part (2) stay `source-facing`, stated directly in the owner language
  already used throughout the chapter; part (3) is the corresponding source-facing closed-image
  corollary, backed by a core closed-image owner theorem.
-/

namespace LinearMap

variable {C : Set E} (A : E →ₗ[𝕜] F)

/-- Core closed-image owner theorem for Theorem 9.1:
if `K` is closed and convex and the kernel slice of its recession cone lies in its lineality
space, then the linear image `A '' K` is closed. -/
-- Proof sketch: this is the intrinsic closed-owner form of Theorem 9.1 (1). The source-facing
-- closure identity `closure (A '' C) = A '' closure C` is recovered by applying this theorem to
-- `K = closure C`.
theorem isClosed_image_of_recessionKernelLeLineality
    {K : Set E}
    (hK : Convex 𝕜 K) (hK_closed : IsClosed K)
    (hkernel_lineality : A.recessionKernelLeLineality K) :
    IsClosed (A '' K) := sorry

/-- Theorem 9.1 (1): if the kernel slice of the recession cone of `closure C` is contained in the
lineality space of `closure C`, then the closure of the image `A '' C` is exactly the image of
the closure `A '' closure C`. The textbook source is recovered by specializing `𝕜 = ℝ`. -/
-- Proof sketch: the inclusion `A '' closure C ⊆ closure (A '' C)` is the general continuity
-- inclusion from Theorem 6.6. For the reverse inclusion, intersect `closure C` with a complement
-- to the common subspace `lin[𝕜](closure C) ∩ (A.ker : Set E)` and use the hypothesis to
-- show the resulting approximate fibers are bounded. Apply Theorem 8.4 to those closed convex
-- slices and then pass to a nested-intersection argument to recover a preimage point in
-- `closure C`.
theorem closure_image_eq_image_closure_of_recessionKernelLeLineality
    (hC : Convex 𝕜 C)
    (hkernel_lineality : A.recessionKernelLeLineality (closure C))
    :
    closure (A '' C) = A '' closure C := sorry

/-- Core recession-cone-image owner theorem for Theorem 9.1:
if `K` is closed, convex, and nonempty and the kernel slice of its recession cone lies in its
lineality space, then the recession cone of `A '' K` is exactly the image under `A` of the
recession cone of `K`. -/
theorem recessionCone_image_eq_image_recessionCone_of_recessionKernelLeLineality
    {K : Set E}
    (hK : Convex 𝕜 K) (hK_closed : IsClosed K)
    (hkernel_lineality : A.recessionKernelLeLineality K)
    (hK_nonempty : K.Nonempty) :
    0⁺[𝕜] (A '' K) = A '' 0⁺[𝕜] K := sorry

/-- Theorem 9.1 (2): under the same kernel-slice inclusion hypothesis, the recession cone of the
canonical closed image `A '' closure C` is exactly the image under `A` of the recession cone of
`closure C`. The textbook source is recovered by specializing `𝕜 = ℝ`. -/
-- Proof sketch: first use part (1) to identify the source's closed image `closure (A '' C)` with
-- the canonical owner `A '' closure C`. Then apply the homogenization argument from the source
-- proof and use Theorem 8.2 to identify the zero-height slices of the relevant closures with the
-- recession cones of `closure C` and `A '' closure C`.
theorem recessionCone_image_closure_eq_image_recessionCone
    (hC : Convex 𝕜 C)
    (hkernel_lineality : A.recessionKernelLeLineality (closure C))
    (hC_nonempty : C.Nonempty) :
    0⁺[𝕜] (A '' closure C) = A '' 0⁺[𝕜] (closure C) := sorry

/-- Theorem 9.1 (3): if `C` is a closed convex set and the only recession direction of `C`
annihilated by `A` is the zero vector, then the linear image `A '' C` is closed. The textbook
source is recovered by specializing `𝕜 = ℝ`. -/
-- Proof sketch: since `C` is closed, rewrite `closure C` as `C` in part (1). The stronger kernel
-- hypothesis implies the lineality hypothesis there, because the only kernel direction in
-- `0⁺[𝕜] C` is `0`. The resulting equality `closure (A '' C) = A '' C` is exactly the
-- closedness of the image.
theorem isClosed_image_of_recessionKernelTrivial
    (hC : Convex 𝕜 C) (hC_closed : IsClosed C)
    (hkernel_trivial : A.recessionKernelTrivial C) :
    IsClosed (A '' C) := sorry

end LinearMap

end

end

/-! ### Corollary_9_1_2 (from Chap02) -/
open scoped BigOperators Pointwise Rockafellar

section NoOppositeRecessionDirections

variable {𝕜 : Type*} [Zero 𝕜] [LE 𝕜]
variable {E : Type*} [Zero E] [Add E] [Neg E] [SMul 𝕜 E]

namespace Set

/-- Binary opposite-recession exclusion condition used in Corollary 9.1.2:
no nonzero direction is simultaneously a recession direction of `C₁` and the opposite of a
recession direction of `C₂`. -/
def NoOppositeRecessionDirections (𝕜 : Type*) [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E]
    (C₁ C₂ : Set E) : Prop :=
  ∀ ⦃y : E⦄, y ∈ 0⁺[𝕜] C₁ → -y ∈ 0⁺[𝕜] C₂ → y = 0

end Set

scoped[Rockafellar] notation:50 C₁ " ⟂₀⁺[" 𝕜 "] " C₂ =>
  Set.NoOppositeRecessionDirections 𝕜 C₁ C₂

end NoOppositeRecessionDirections

section

open Set

variable
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜]
  {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 9.1.2 is the binary (`m = 2`) specialization of Corollary 9.1.1:
  closedness of the Minkowski sum and the recession-cone identity for the Minkowski sum
  of two closed convex subsets of a finite-dimensional Hausdorff topological vector space over
  `𝕜`, together with the
  corresponding recession-cone formula. The source states this in `ℝ^n`, but the owner theorem
  already lives intrinsically and the present binary specialization uses no coordinate data.
- `core/canonical`: the owner-side notions already present in the chapter are the recession-cone
  owner `0⁺[𝕜]C` and lineality-space owner `lin[𝕜](C)`.
- `bridge/view`: the textbook phrase "there is no direction of recession of `C₁` whose opposite is
  a direction of recession of `C₂`" is rendered on the owner surface as
  `y ∈ 0⁺[𝕜]C₁ → -y ∈ 0⁺[𝕜]C₂ → y = 0`.

Domain-style sampling used here:
- the finite-family owner theorems
  `Set.ZeroSumRecessionImpLineality.isClosed_sum` and
  `Set.ZeroSumRecessionImpLineality.recessionCone_closure_sum_eq_sum_recessionCone_closure`
  from Corollary 9.1.1;
- the chapter owner `recessionCone` from Definition 8.0.2;
- the chapter owner `Set.linealitySpace` from Definition 8.4.2.

Primitive data vs derived API:
- primitive inputs: the two sets `C₁`, `C₂`, their convexity, and the owner-layer compatibility
  condition on closure recession directions
  `y ∈ 0⁺[𝕜](closure C₁) → -y ∈ 0⁺[𝕜](closure C₂) → y = 0`;
- derived source-facing outputs for this corollary: the closed-set statement
  `IsClosed (C₁ + C₂)` and the closed-set recession-cone identity
  `0⁺[𝕜] (C₁ + C₂) = 0⁺[𝕜]C₁ + 0⁺[𝕜]C₂`.
  The finite-sum owner theorem already absorbs the empty cases, so nonemptiness is not primitive
  public data here.

Layer target: this item exposes the binary specialization first at the closure owner layer, then
recovers the textbook closed-set surface as a corollary.

Assumption audit for this canonicalization pass:
- `Module 𝕜 E` is retained as a primitive owner-layer assumption: both `Convex 𝕜` and the
  textbook owner notation `0⁺[𝕜]C` are scalar-parameterized at this layer.
- `TopologicalSpace E`, `IsTopologicalAddGroup E`, and `ContinuousSMul 𝕜 E` are primitive for the
  ambient closedness/closure owners (`IsClosed`, `closure`) used by both conclusions.
- `FiniteDimensional 𝕜 E` and `T2Space E` are inherited from the first upstream owner source
  (`Theorem_9_1` via `Corollary_9_1_1`); this file does not introduce extra ambient structure
  beyond that owner layer.
- Topology-language audit: this item's mathematical content is ambient closedness of `C₁ + C₂`
  plus an ambient recession-cone identity. There is no stricter intrinsic/relative reformulation
  available in the local Chapter 9 owner ecosystem that would strictly generalize these two public
  theorem surfaces.
-/

variable {C₁ C₂ : Set E}

private def pairFamily (C₁ C₂ : Set E) : Bool → Set E := fun b ↦ cond b C₁ C₂

local notation "pairSets" => pairFamily C₁ C₂

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
  [FiniteDimensional 𝕜 E] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem pairSets_convex (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂) :
    ∀ b : Bool, Convex 𝕜 (pairSets b) := by
  intro b
  cases b
  · simpa [pairFamily] using hC₂_convex
  · simpa [pairFamily] using hC₁_convex

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Binary bridge to the canonical finite-family owner:
the no-opposite condition on closure recession directions implies the zero-sum lineality
condition for the `Bool`-indexed pair. -/
theorem Set.NoOppositeRecessionDirections.zeroSumRecessionImpLineality_pair
    (hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂)) :
    Set.ZeroSumRecessionImpLineality 𝕜 pairSets := by
  change (∀ {y : E}, y ∈ 0⁺[𝕜] (closure C₁) → -y ∈ 0⁺[𝕜] (closure C₂) → y = 0) at hNoOppositeClosure
  intro z hz hsum b
  have hz_true : z true ∈ 0⁺[𝕜] (closure C₁) := by
    simpa [pairFamily] using hz true
  have hz_false : z false ∈ 0⁺[𝕜] (closure C₂) := by
    simpa [pairFamily] using hz false
  have hsum' : z true + z false = 0 := by
    simpa [Fintype.sum_bool, add_comm, add_left_comm, add_assoc] using hsum
  have hsum'' : z false + z true = 0 := by
    simpa [add_comm] using hsum'
  have hz_false_neg : -z true ∈ 0⁺[𝕜] (closure C₂) := by
    simpa [eq_neg_of_add_eq_zero_left hsum''] using hz_false
  have hz_true_eq_zero : z true = 0 :=
    hNoOppositeClosure hz_true hz_false_neg
  have hz_false_eq_zero : z false = 0 := by
    simpa [hz_true_eq_zero] using hsum'
  have hzero₁ : (0 : E) ∈ 0⁺[𝕜] (closure C₁) := by
    rw [Set.mem_recessionCone_iff]
    intro x hx a ha
    simpa using hx
  have hzero₂ : (0 : E) ∈ 0⁺[𝕜] (closure C₂) := by
    rw [Set.mem_recessionCone_iff]
    intro x hx a ha
    simpa using hx
  cases b
  · rw [mem_lineal_iff]
    constructor <;> simpa [Set.mem_neg, hz_false_eq_zero] using hzero₂
  · rw [mem_lineal_iff]
    constructor <;> simpa [Set.mem_neg, hz_true_eq_zero] using hzero₁

/-- Binary specialization of Corollary 9.1.1 (1) on the closure-owner layer:
under the closure-level no-opposite condition, the closure of the Minkowski sum equals the
sum of closures. -/
theorem Set.NoOppositeRecessionDirections.closure_add_eq_add_closure
    (hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂))
    (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂) :
    closure (C₁ + C₂) = closure C₁ + closure C₂ := by
  have hpairZero :
      Set.ZeroSumRecessionImpLineality 𝕜 pairSets :=
    hNoOppositeClosure.zeroSumRecessionImpLineality_pair
  have hclosure :
      closure (∑ b, pairSets b : Set E) = ∑ b, closure (pairSets b) :=
    hpairZero.closure_sum_eq_sum_closure (pairSets_convex hC₁_convex hC₂_convex)
  simpa [Fintype.sum_bool, pairFamily, add_comm, add_left_comm, add_assoc] using hclosure

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem Set.NoOppositeRecessionDirections.closure_of_isClosed
    (hNoOpposite : C₁ ⟂₀⁺[𝕜] C₂)
    (hC₁_closed : IsClosed C₁) (hC₂_closed : IsClosed C₂) :
    (closure C₁) ⟂₀⁺[𝕜] (closure C₂) := by
  simpa [Set.NoOppositeRecessionDirections, hC₁_closed.closure_eq, hC₂_closed.closure_eq] using
    hNoOpposite

/-- Binary closure-layer specialization of Corollary 9.1.1 (1): if two convex sets satisfy the
closure-level compatibility condition on opposite recession directions, then the sum of their
closures is closed. -/
theorem Set.NoOppositeRecessionDirections.isClosed_add_closure
    (hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂))
    (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂) :
    IsClosed (closure C₁ + closure C₂) := by
  simpa [hNoOppositeClosure.closure_add_eq_add_closure hC₁_convex hC₂_convex] using
    (isClosed_closure : IsClosed (closure (C₁ + C₂)))

/-- Binary specialization of Corollary 9.1.1 (2) on the closure-owner layer:
under the same closure-level compatibility condition, the recession cone of the closure of the
Minkowski sum is the sum of the recession cones of the individual closures. -/
theorem Set.NoOppositeRecessionDirections.recessionCone_closure_add_eq_add_recessionCone_closure
    (hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂))
    (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂) :
    0⁺[𝕜] (closure (C₁ + C₂)) = 0⁺[𝕜] (closure C₁) + 0⁺[𝕜] (closure C₂) := by
  have hpairZero :
      Set.ZeroSumRecessionImpLineality 𝕜 pairSets :=
    hNoOppositeClosure.zeroSumRecessionImpLineality_pair
  have hcone :
      0⁺[𝕜] (closure (∑ b, pairSets b : Set E)) =
        ∑ b, 0⁺[𝕜] (closure (pairSets b)) :=
    hpairZero.recessionCone_closure_sum_eq_sum_recessionCone_closure
      (pairSets_convex hC₁_convex hC₂_convex)
  simpa [Fintype.sum_bool, pairFamily, add_comm, add_left_comm, add_assoc] using hcone

/-- Binary closure-layer specialization of Corollary 9.1.1 (2): under the same closure-level
compatibility condition, the recession cone of the sum of closures is the sum of the
recession cones of the individual closures. -/
theorem Set.NoOppositeRecessionDirections.recessionCone_add_closure_eq_add_recessionCone_closure
    (hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂))
    (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂) :
    0⁺[𝕜] (closure C₁ + closure C₂) = 0⁺[𝕜] (closure C₁) + 0⁺[𝕜] (closure C₂) := by
  have hcone_closure_add :
      0⁺[𝕜] (closure (C₁ + C₂)) = 0⁺[𝕜] (closure C₁) + 0⁺[𝕜] (closure C₂) :=
    hNoOppositeClosure.recessionCone_closure_add_eq_add_recessionCone_closure hC₁_convex hC₂_convex
  have hclosure_add : closure (C₁ + C₂) = closure C₁ + closure C₂ :=
    hNoOppositeClosure.closure_add_eq_add_closure hC₁_convex hC₂_convex
  simpa [hclosure_add] using hcone_closure_add

/-- Corollary 9.1.2 (1): if `C₁` and `C₂` are closed convex sets in a finite-dimensional
Hausdorff topological vector space over `𝕜` and every `y` with
`y ∈ 0⁺[𝕜]C₁` and `-y ∈ 0⁺[𝕜]C₂` is zero, then
their Minkowski sum `C₁ + C₂` is closed. In
particular, the hypothesis holds whenever either set is bounded. -/
-- Proof sketch: first transport the source-facing no-opposite condition to the closure owner
-- surface, then apply the closure-layer binary specialization
-- `Set.NoOppositeRecessionDirections.isClosed_add_closure`. Closedness of each summand rewrites
-- this directly to `IsClosed (C₁ + C₂)`.
theorem Set.NoOppositeRecessionDirections.isClosed_add
    (hC₁_closed : IsClosed C₁) (hC₂_closed : IsClosed C₂)
    (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂)
    (hNoOpposite : C₁ ⟂₀⁺[𝕜] C₂) :
    IsClosed (C₁ + C₂) := by
  have hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂) :=
    hNoOpposite.closure_of_isClosed hC₁_closed hC₂_closed
  simpa [hC₁_closed.closure_eq, hC₂_closed.closure_eq] using
    hNoOppositeClosure.isClosed_add_closure hC₁_convex hC₂_convex

/-- Corollary 9.1.2 (2): under the same hypotheses, the recession cone of the Minkowski sum is the
sum of the recession cones:
`0⁺[𝕜] (C₁ + C₂) = 0⁺[𝕜]C₁ + 0⁺[𝕜]C₂`. -/
-- Proof sketch: apply the closure-layer recession-cone theorem
-- `Set.NoOppositeRecessionDirections.recessionCone_add_closure_eq_add_recessionCone_closure`,
-- then rewrite closures using closedness of both summands and of `C₁ + C₂` from part (1).
theorem Set.NoOppositeRecessionDirections.recessionCone_add_eq_add_recessionCone
    (hC₁_closed : IsClosed C₁) (hC₂_closed : IsClosed C₂)
    (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂)
    (hNoOpposite : C₁ ⟂₀⁺[𝕜] C₂) :
    0⁺[𝕜] (C₁ + C₂) = 0⁺[𝕜]C₁ + 0⁺[𝕜]C₂ := by
  have hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂) :=
    hNoOpposite.closure_of_isClosed hC₁_closed hC₂_closed
  have hclosed_add : IsClosed (C₁ + C₂) :=
    hNoOpposite.isClosed_add hC₁_closed hC₂_closed hC₁_convex hC₂_convex
  have hcone_closure :
      0⁺[𝕜] (closure C₁ + closure C₂) = 0⁺[𝕜] (closure C₁) + 0⁺[𝕜] (closure C₂) :=
    hNoOppositeClosure.recessionCone_add_closure_eq_add_recessionCone_closure hC₁_convex hC₂_convex
  simpa [hclosed_add.closure_eq, hC₁_closed.closure_eq, hC₂_closed.closure_eq] using hcone_closure

end

/-! ### Corollary_9_1_3 (from Chap02) -/
open scoped BigOperators Pointwise Rockafellar

section

universe u

variable {ι : Type u} [Fintype ι]

variable
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜]
variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
  [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 9.1.3 specializes the finite-sum closure criterion to a finite family
  of nonempty convex cones, replacing the recession-direction hypothesis by the source-visible
  stronger condition that the zero-sum tuple already lies in the closures of the cones.
- `core/canonical`: the owner abstractions are mathlib's bundled `PointedCone 𝕜 E` (the intrinsic
  owner for nonempty cones), the chapter owner `Set.linealitySpace`, topological closure, and
  finite pointwise set sums.
- `bridge/view`: the result is a direct specialization of Corollary 9.1.1 to cone carriers; no new
  cone wrapper is introduced. The source hypothesis is kept as the direct zero-sum closure
  condition on cone families.
- Domain-style sampling used here: `PointedCone 𝕜 E`,
  `Set.linealitySpace`, `Set.mem_recessionCone_iff`,
  `Set.ZeroSumRecessionImpLineality`, and
  `Set.ZeroSumRecessionImpLineality.closure_sum_eq_sum_closure`.
- Primitive data vs derived API: the primitive inputs are the cone family `K` and the zero-sum
  condition on points of the closures. The finite-sum owner theorem already absorbs empty
  summands, so familywise nonemptiness is not primitive public data here. The closure identity for
  the finite Minkowski sum is the derived statement.
- Layer target: this item stays `source-facing`, but uses the canonical bundled cone owner for the
  summands and the same intrinsic finite-family ambient layer as Corollary 9.1.1 rather than the
  coordinate model `EuclideanSpace ℝ (Fin n)`.
--/

namespace PointedCone

-- Bridge from the source closure-level tuple condition to Corollary 9.1.1's canonical owner
-- condition on zero-sum recession directions of closure summands.
omit [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] in
theorem zeroSumRecessionImpLineality_of_zero_sum_closure_imp_lineality
    (K : ι → PointedCone 𝕜 E)
    (hzero :
      ∀ z : ι → E,
        (∀ i, z i ∈ closure (K i : Set E)) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ lin[𝕜](closure (K i : Set E))) :
    Set.ZeroSumRecessionImpLineality 𝕜 (fun i ↦ (K i : Set E)) := by
  intro z hz hsum i
  apply hzero z ?_ hsum i
  intro j
  have hzero_mem : (0 : E) ∈ closure (K j : Set E) := subset_closure (K j).zero_mem
  simpa using (Set.mem_recessionCone_iff.mp (hz j)) 0 hzero_mem (1 : 𝕜) zero_le_one

/-- Cone-specialized canonical-owner form of Corollary 9.1.1 (1):
under `⟂Σ₀⁺[𝕜]` for cone carriers, closure commutes with finite Minkowski sums. -/
theorem closure_sum_eq_sum_closure
    (K : ι → PointedCone 𝕜 E)
    (hzero : Set.ZeroSumRecessionImpLineality 𝕜 (fun i ↦ (K i : Set E))) :
    closure (∑ i, (K i : Set E)) = ∑ i, closure (K i : Set E) := by
  exact hzero.closure_sum_eq_sum_closure (fun i ↦ (K i).convex)

end PointedCone

-- Proof sketch: first convert the source closure-level tuple condition into the canonical
-- zero-sum recession owner condition on cone carriers; then apply the cone-specialized
-- canonical-owner closure theorem above.
/-- Corollary 9.1.3: for nonempty convex cones `K₁, …, K_m` in `R^n`, if every zero-sum tuple
`zᵢ ∈ cl Kᵢ` lies termwise in the lineality spaces of the closures, then the closure of the finite
Minkowski sum equals the finite sum of the individual closures. -/
theorem closure_sum_eq_sum_closure_of_zero_sum_closure_imp_lineality
    (K : ι → PointedCone 𝕜 E)
    (hzero :
      ∀ z : ι → E,
        (∀ i, z i ∈ closure (K i : Set E)) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ lin[𝕜](closure (K i : Set E))) :
    closure (∑ i, (K i : Set E)) = ∑ i, closure (K i : Set E) := by
  exact PointedCone.closure_sum_eq_sum_closure
    K (PointedCone.zeroSumRecessionImpLineality_of_zero_sum_closure_imp_lineality K hzero)

end
