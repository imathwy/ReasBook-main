import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_4_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

section

universe u v

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 8.4.8 says that for a closed convex set, the rank equals the dimension
  exactly when the set contains no affine line.
- `core/canonical`: the owner abstractions already present upstream are `Set.rank`, `Set.affineDim`,
  and `Set.lineal` (written as `lin[𝕜](C)`), together with the source-facing set owner
  `Set.HasAffineLine 𝕜 C`.
- `bridge/view`: the source phrase "contains no lines" is rendered in the chapter's existing
  owner `Set.HasAffineLine 𝕜 C`, while the proof bridges that formulation to the existing Chapter
  2 owner `lin[𝕜](C)` via
  `Convex.mem_recessionCone_of_nonneg_ray`.

Domain-style sampling used here:
- `Set.rank` from `Definiton_8_4_6`;
- `Set.lineality` from `Definition_8_4_4`;
- `Set.lineal` / `Set.mem_lineal_iff_forall` from `Definition_8_4_2`;
- the later source-facing no-line surface reused in `Theorem_18_5`;
- `Convex.mem_recessionCone_of_nonneg_ray` from `Theorem_8_3`.

Primitive data vs derived API:
- primitive source inputs: the nonempty set `C`, together with `IsClosed C` and `Convex 𝕜 C`;
- derived owner bridge: vanishing lineality versus absence of a nonzero vector in `lin[𝕜](C)`;
- source-facing output: the rank/dimension criterion formulated through excluded affine-line
  parametrizations.

Layer target: `source-facing`, stated directly on the intrinsic set-side owners rather than on the
older Euclidean-coordinate model. The only finite-dimensional hypotheses retained are the owner
instances already attached to `Set.rank` and `Set.lineality`.
-/

namespace Set

/-- Source-facing owner: `HasAffineLine 𝕜 C` means `C` contains a nontrivial affine line
`x + t • y` for some nonzero direction `y`. -/
def HasAffineLine (𝕜 : Type v) [Add E] [SMul 𝕜 E] (C : Set E) : Prop :=
  ∃ x y : E, y ≠ 0 ∧ ∀ t : 𝕜, x + t • y ∈ C

end Set

omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
private theorem zero_mem_lineal (C : Set E) : (0 : E) ∈ lin[𝕜](C) := by
  rw [Set.mem_lineal_iff]
  constructor <;> (rw [Set.mem_recessionCone_iff]; intro x hx a ha; simpa)

omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
private theorem lineality_nonneg (C : Set E)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction] :
    0 ≤ lineality[𝕜](C) := by
  let A : AffineSubspace 𝕜 E := affineSpan 𝕜 (lin[𝕜](C))
  have h0A : (0 : E) ∈ A :=
    (subset_affineSpan 𝕜 (lin[𝕜](C))) (zero_mem_lineal C)
  have hAne : A ≠ ⊥ := by
    intro hbot
    have : (0 : E) ∉ (A : Set E) := by
      simp [hbot]
    exact this h0A
  have hlinealityA : Set.lineality 𝕜 C = A.affineDim := by
    simpa [A] using (Set.lineality_eq_affineSpan_affineDim (𝕜 := 𝕜) (C := C))
  rw [hlinealityA, AffineSubspace.affineDim, if_neg hAne]
  exact_mod_cast Nat.zero_le (Module.finrank 𝕜 A.direction)

/- The owner invariant `Set.lineality 𝕜 C` vanishes exactly when `lin[𝕜](C)` has no nonzero
vector. This is the atomic set-side bridge from the lineality dimension to the intrinsic lineality
space owner. -/
omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
theorem Set.lineality_eq_zero_iff_not_exists_ne_zero_mem_lineal
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction] :
    lineality[𝕜](C) = 0 ↔ ¬ ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C) := by
  constructor
  · intro hC hy
    rcases hy with ⟨y, hyne, hy⟩
    let A : AffineSubspace 𝕜 E := affineSpan 𝕜 (lin[𝕜](C))
    have h0A : (0 : E) ∈ A :=
      (subset_affineSpan 𝕜 (lin[𝕜](C))) (zero_mem_lineal C)
    have hAne : A ≠ ⊥ := by
      intro hbot
      have : (0 : E) ∉ (A : Set E) := by
        simp [hbot]
      exact this h0A
    have hlinealityA : Set.lineality 𝕜 C = A.affineDim := by
      simpa [A] using (Set.lineality_eq_affineSpan_affineDim (𝕜 := 𝕜) (C := C))
    have hfin : Module.finrank 𝕜 A.direction = 0 := by
      rw [hlinealityA, AffineSubspace.affineDim, if_neg hAne] at hC
      exact_mod_cast hC
    have hdir : A.direction = ⊥ := Submodule.finrank_eq_zero.mp hfin
    have hyA : y ∈ A := by
      exact (subset_affineSpan 𝕜 (lin[𝕜](C))) hy
    have hydir : y ∈ A.direction := by
      simpa using A.vsub_mem_direction hyA h0A
    have hy0 : y = 0 := by
      simpa [hdir] using hydir
    exact hyne hy0
  · intro hC
    let A : AffineSubspace 𝕜 E := affineSpan 𝕜 (lin[𝕜](C))
    have h0 : (0 : E) ∈ lin[𝕜](C) := zero_mem_lineal C
    have h0A : (0 : E) ∈ A := by
      exact (subset_affineSpan 𝕜 (lin[𝕜](C))) h0
    have hAne : A ≠ ⊥ := by
      intro hbot
      have : (0 : E) ∉ (A : Set E) := by
        simp [hbot]
      exact this h0A
    have hsubset : lin[𝕜](C) ⊆ ({0} : Set E) := by
      intro y hy
      by_contra hy0
      exact hC ⟨y, by simpa using hy0, hy⟩
    have hsubset0 : ({0} : Set E) ⊆ lin[𝕜](C) := by
      intro y hy
      have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
      simpa [hy0] using h0
    have hspan : affineSpan 𝕜 (lin[𝕜](C)) = affineSpan 𝕜 ({0} : Set E) :=
      le_antisymm (affineSpan_mono 𝕜 hsubset) (affineSpan_mono 𝕜 hsubset0)
    have hdir : A.direction = ⊥ := by
      calc
        A.direction = (affineSpan 𝕜 ({0} : Set E)).direction := by
          simp [A, hspan]
        _ = vectorSpan 𝕜 ({0} : Set E) := by
          rw [direction_affineSpan 𝕜 ({0} : Set E)]
        _ = ⊥ := by
          rw [vectorSpan_singleton 𝕜 (0 : E)]
    have hlinealityA : Set.lineality 𝕜 C = A.affineDim := by
      simpa [A] using (Set.lineality_eq_affineSpan_affineDim (𝕜 := 𝕜) (C := C))
    rw [hlinealityA, AffineSubspace.affineDim, if_neg hAne, hdir]
    norm_num

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
theorem Set.hasAffineLine_of_exists_ne_zero_mem_lineal {C : Set E} (hCne : C.Nonempty)
    (hlin : ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C)) :
    Set.HasAffineLine 𝕜 C := by
  rcases hCne with ⟨x, hx⟩
  rcases hlin with ⟨y, hyne, hy⟩
  refine ⟨x, y, hyne, ?_⟩
  have hy_forall := Set.mem_lineal_iff_forall.mp hy
  intro t
  by_cases ht : 0 ≤ t
  · exact hy_forall.2 x hx t ht
  · have ht' : 0 ≤ -t := by linarith
    have hneg : x + (-t) • (-y) ∈ C := hy_forall.1 x hx (-t) ht'
    simpa [smul_neg, neg_smul] using hneg

theorem Set.exists_ne_zero_mem_lineal_of_hasAffineLine {C : Set E}
    (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C)
    (hline : Set.HasAffineLine 𝕜 C) :
    ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C) := by
  rcases hline with ⟨x, y, hyne, hline⟩
  have hRay : ∀ t : 𝕜, 0 ≤ t → x + t • y ∈ C := by
    intro t ht
    exact hline t
  have hNegRay : ∀ t : 𝕜, 0 ≤ t → x + t • (-y) ∈ C := by
    intro t ht
    simpa [smul_neg, neg_smul] using hline (-t)
  refine ⟨y, hyne, ?_⟩
  rw [Set.mem_lineal_iff]
  constructor
  · exact hCconv.mem_recessionCone_of_nonneg_ray hCclosed hRay
  · exact hCconv.mem_recessionCone_of_nonneg_ray hCclosed hNegRay

/- A nontrivial affine line in `C` is equivalent to a nonzero vector in the lineality space
`lin[𝕜](C)`. -/
theorem Set.hasAffineLine_iff_exists_ne_zero_mem_lineal {C : Set E} (hCne : C.Nonempty)
    (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C) :
    Set.HasAffineLine 𝕜 C ↔ ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C) := by
  constructor
  · exact Set.exists_ne_zero_mem_lineal_of_hasAffineLine hCclosed hCconv
  · exact Set.hasAffineLine_of_exists_ne_zero_mem_lineal hCne

/- Source-facing quantifier view of `Set.hasAffineLine_iff_exists_ne_zero_mem_lineal`. -/
theorem Set.exists_affineLine_iff_exists_ne_zero_mem_lineal {C : Set E} (hCne : C.Nonempty)
    (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C) :
    (∃ x y : E, y ≠ 0 ∧ ∀ t : 𝕜, x + t • y ∈ C) ↔ ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C) := by
  simpa [Set.HasAffineLine] using
    (Set.hasAffineLine_iff_exists_ne_zero_mem_lineal hCne hCclosed hCconv)

/- For a nonempty closed convex set, vanishing lineality is equivalent to exclusion of nontrivial
affine-line parametrizations contained in the set. This is the set-side analogue of the
function-side lineality/no-affine-line bridge from Chapter 2. -/
theorem Set.lineality_eq_zero_iff_not_hasAffineLine {C : Set E}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C) :
    lineality[𝕜](C) = 0 ↔ ¬ Set.HasAffineLine 𝕜 C := by
  have hline :
      Set.HasAffineLine 𝕜 C ↔
        ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C) :=
    Set.hasAffineLine_iff_exists_ne_zero_mem_lineal hCne hCclosed hCconv
  exact Set.lineality_eq_zero_iff_not_exists_ne_zero_mem_lineal.trans
    (not_congr hline.symm)

/- Source-facing quantifier view of `Set.lineality_eq_zero_iff_not_hasAffineLine`. -/
theorem Set.lineality_eq_zero_iff_not_exists_affineLine {C : Set E}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C) :
    lineality[𝕜](C) = 0 ↔ ¬ ∃ x y : E, y ≠ 0 ∧ ∀ t : 𝕜, x + t • y ∈ C := by
  simpa [Set.HasAffineLine] using
    (Set.lineality_eq_zero_iff_not_hasAffineLine hCne hCclosed hCconv)

/-- Theorem 8.4.8, owner form: for a nonempty closed convex set, once the canonical owner
instances for `Set.affineDim 𝕜 C` and `Set.lineality 𝕜 C` are available, the rank equals the
affine dimension exactly when `C` has no affine-line owner witness. -/
-- Proof sketch: rewrite `rank = affDim` as vanishing of the lineality invariant. Vanishing
-- lineality is equivalent to the absence of nonzero vectors in `lin[𝕜](C)`. A nonzero lineality
-- direction gives a full affine-line parametrization through any point of `C`, while such a
-- parametrization contributes a nonzero direction to `lin[𝕜](C)` by Theorem 8.3 applied to the
-- two ray directions `y` and `-y`.
theorem Set.rank_eq_affineDim_iff_not_hasAffineLine {C : Set E}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C) :
    rank[𝕜](C) = dim[𝕜](C) ↔ ¬ Set.HasAffineLine 𝕜 C := by
  have hlineality : lineality[𝕜](C) = 0 ↔ ¬ Set.HasAffineLine 𝕜 C :=
    Set.lineality_eq_zero_iff_not_hasAffineLine hCne hCclosed hCconv
  constructor
  · intro h
    have hlin0 : lineality[𝕜](C) = 0 := by
      rw [Set.rank_eq] at h
      have hnonneg : 0 ≤ lineality[𝕜](C) := lineality_nonneg C
      omega
    exact hlineality.mp hlin0
  · intro h
    have hlin0 : lineality[𝕜](C) = 0 := hlineality.mpr h
    rw [Set.rank_eq, hlin0]
    omega

/-- Theorem 8.4.8, textbook bridge: for a nonempty closed convex set, the rank equals the affine
dimension exactly when the set contains no nontrivial affine-line parametrization. -/
theorem rank_eq_affineDim_iff_no_lines {C : Set E}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex 𝕜 C) :
    rank[𝕜](C) = dim[𝕜](C) ↔ ¬ ∃ x y : E, y ≠ 0 ∧ ∀ t : 𝕜, x + t • y ∈ C := by
  simpa [Set.HasAffineLine] using
    (Set.rank_eq_affineDim_iff_not_hasAffineLine hCne hCclosed hCconv)

end
