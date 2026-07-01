import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_9_1

-- Declarations for this item will be appended below by the statement pipeline.

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
