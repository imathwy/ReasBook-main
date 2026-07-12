import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

open scoped ContDiff Manifold

section Pi

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type u} [Fintype ι] {r : WithTop ℕ∞}
variable {E : ι → Type v} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {H : ι → Type w} [∀ i, TopologicalSpace (H i)]
variable {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)}
variable {M : ι → Type x} [∀ i, TopologicalSpace (M i)]

omit [Fintype ι] in
/-- Helper for Example 1.8: the transition map between product charts is the product of the
factorwise transition maps. -/
lemma openPartialHomeomorph_pi_symm_trans_pi [Finite ι]
    (e e' : ∀ i, OpenPartialHomeomorph (M i) (H i)) :
    (OpenPartialHomeomorph.pi e).symm.trans (OpenPartialHomeomorph.pi e') =
      OpenPartialHomeomorph.pi (fun i ↦ (e i).symm.trans (e' i)) := by
  -- Compare the transition maps coordinatewise.
  apply OpenPartialHomeomorph.ext
  · intro x
    funext i
    rfl
  · intro x
    funext i
    rfl
  · ext x
    simp [Set.mem_pi]

/-- Helper for Example 1.8: membership in the product-source condition is equivalent to the
corresponding coordinatewise source conditions. -/
lemma mem_modelWithCorners_pi_source_iff
    {e : ∀ i, OpenPartialHomeomorph (H i) (H i)} {x : ∀ i, E i} :
    x ∈ (ModelWithCorners.pi I).symm ⁻¹' (OpenPartialHomeomorph.pi e).source ∩
        Set.range (ModelWithCorners.pi I) ↔
      ∀ i, x i ∈ (I i).symm ⁻¹' (e i).source ∩ Set.range (I i) := by
  -- Unfold the finite-product structures so the source condition separates by coordinates.
  have hrange :
      Set.range (ModelWithCorners.pi I) = Set.pi Set.univ (fun i ↦ Set.range (I i)) := by
    change Set.range (Pi.map fun i ↦ (I i)) = _
    simp
  rw [hrange]
  constructor
  · intro hx i
    have hx_source_mem :
        (ModelWithCorners.pi I).symm x ∈ Set.pi Set.univ (fun i ↦ (e i).source) := by
      simpa [OpenPartialHomeomorph.pi] using hx.1
    have hx_source_mem' :
        ∀ i ∈ Set.univ, ((ModelWithCorners.pi I).symm x) i ∈ (e i).source := by
      dsimp [ModelPi] at hx_source_mem ⊢
      rw [Set.mem_pi] at hx_source_mem
      exact hx_source_mem
    have hx_source_pi : ∀ i, ((ModelWithCorners.pi I).symm x) i ∈ (e i).source := by
      exact fun i ↦ hx_source_mem' i (by simp)
    have hx_source : ∀ i, (I i).symm (x i) ∈ (e i).source := by
      simpa [ModelWithCorners.pi, PartialEquiv.pi_symm_apply] using hx_source_pi
    have hx_range_mem : x ∈ Set.pi Set.univ (fun i ↦ Set.range (I i)) := hx.2
    have hx_range : ∀ i, x i ∈ Set.range (I i) := by
      rw [Set.mem_pi] at hx_range_mem
      exact fun i ↦ hx_range_mem i (by simp)
    exact ⟨hx_source i, hx_range i⟩
  · intro hx
    constructor
    · have hx_source : ∀ i, ((ModelWithCorners.pi I).symm x) i ∈ (e i).source := by
        simpa [ModelWithCorners.pi, PartialEquiv.pi_symm_apply] using fun i ↦ (hx i).1
      have hx_source_mem' :
          ∀ i ∈ Set.univ, ((ModelWithCorners.pi I).symm x) i ∈ (e i).source := by
        exact fun i _ ↦ hx_source i
      have hx_source_mem :
          (ModelWithCorners.pi I).symm x ∈ Set.pi Set.univ (fun i ↦ (e i).source) := by
        dsimp [ModelPi] at ⊢
        rw [Set.mem_pi]
        exact hx_source_mem'
      simpa [OpenPartialHomeomorph.pi] using hx_source_mem
    · rw [Set.mem_pi]
      exact fun i _ ↦ (hx i).2

/-- Helper for Example 1.8: each coordinate projection on a finite product model space is `C^r`. -/
lemma contDiffOn_pi_proj (i : ι) (s : Set (∀ i, E i)) :
    ContDiffOn 𝕜 r (fun x : ∀ i, E i ↦ x i) s := by
  -- Coordinate projections are continuous linear, hence `C^r`.
  simpa using
    ((((ContinuousLinearMap.proj (R := 𝕜) i) : (∀ i, E i) →L[𝕜] E i).contDiff).contDiffOn :
      ContDiffOn 𝕜 r ((ContinuousLinearMap.proj (R := 𝕜) i) : (∀ i, E i) → E i) s)

/-- Helper for Example 1.8: a finite product of `C^r` coordinate changes is again `C^r`. -/
lemma contDiffGroupoid_pi {e : ∀ i, OpenPartialHomeomorph (H i) (H i)}
    (he : ∀ i, e i ∈ contDiffGroupoid r (I i)) :
    OpenPartialHomeomorph.pi e ∈ contDiffGroupoid r (ModelWithCorners.pi I) := by
  refine (mem_groupoid_of_pregroupoid (PG := contDiffPregroupoid r (ModelWithCorners.pi I))).2 ?_
  constructor
  · -- Prove the forward map is `C^r` by checking each coordinate separately.
    refine contDiffOn_pi.2 ?_
    intro i
    have hi :=
      (mem_groupoid_of_pregroupoid (PG := contDiffPregroupoid r (I i))).1 (he i)
    simpa [Function.comp] using
      (show ContDiffOn 𝕜 r ((I i) ∘ e i ∘ (I i).symm)
          ((I i).symm ⁻¹' (e i).source ∩ Set.range (I i)) from by
            simpa [contDiffPregroupoid] using hi.1).comp
          (contDiffOn_pi_proj (𝕜 := 𝕜) (r := r) i _)
          fun x hx =>
        (mem_modelWithCorners_pi_source_iff (I := I) (e := e) (x := x)).1 hx i
  · -- Apply the same coordinatewise argument to the inverse product chart.
    refine contDiffOn_pi.2 ?_
    intro i
    have hi :=
      (mem_groupoid_of_pregroupoid (PG := contDiffPregroupoid r (I i))).1 (he i)
    simpa [Function.comp] using
      (show ContDiffOn 𝕜 r ((I i) ∘ (e i).symm ∘ (I i).symm)
          ((I i).symm ⁻¹' ((e i).symm).source ∩ Set.range (I i)) from by
            simpa [contDiffPregroupoid] using hi.2).comp
          (contDiffOn_pi_proj (𝕜 := 𝕜) (r := r) i _)
          fun x hx =>
        (mem_modelWithCorners_pi_source_iff (I := I) (e := fun i ↦ (e i).symm) (x := x)).1
          (by simpa [OpenPartialHomeomorph.pi] using hx) i

variable [∀ i, ChartedSpace (H i) (M i)]

-- Primitive data are the factorwise charted-space and manifold structures; the finite product
-- manifold structure is the canonical owner instance over `ModelWithCorners.pi`.
instance instBoundarylessPi [∀ i, (I i).Boundaryless] : (ModelWithCorners.pi I).Boundaryless := by
  constructor
  change Set.range (Pi.map fun i ↦ (I i)) = (Set.univ : Set ((i : ι) → E i))
  simp [ModelWithCorners.range_eq_univ]

set_option backward.isDefEq.respectTransparency false in
instance instIsManifoldPi [∀ i, IsManifold (I i) r (M i)] :
    IsManifold (ModelWithCorners.pi I) r (∀ i, M i) := by
  refine isManifold_of_contDiffOn (I := ModelWithCorners.pi I) r (∀ i, M i) ?_
  intro f g hf hg
  rcases hf with ⟨f', hf', rfl⟩
  rcases hg with ⟨g', hg', rfl⟩
  have hf_atlas : ∀ i, f' i ∈ atlas (H i) (M i) := by
    simpa [Set.mem_pi] using hf'
  have hg_atlas : ∀ i, g' i ∈ atlas (H i) (M i) := by
    simpa [Set.mem_pi] using hg'
  -- Rewrite the product transition map into its factorwise coordinate changes.
  rw [openPartialHomeomorph_pi_symm_trans_pi]
  -- Each factor transition is `C^r`, so the whole product transition is `C^r`.
  exact ((mem_groupoid_of_pregroupoid (PG := contDiffPregroupoid r (ModelWithCorners.pi I))).1 <|
    contDiffGroupoid_pi (I := I) (r := r) fun i =>
      (contDiffGroupoid r (I i)).compatible (hf_atlas i) (hg_atlas i)).1

end Pi

/-- Example 1.8 (Product Manifolds): a finite product of topological manifolds carries the
canonical topological manifold structure modeled on the finite product of the factor Euclidean
spaces. -/
theorem isManifold_pi
    {ι : Type u} [Fintype ι] {n : ι → ℕ}
    {M : ι → Type v} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin (n i))) (M i)]
    [∀ i, IsManifold (𝓡 (n i)) 0 (M i)] :
    IsManifold (ModelWithCorners.pi fun i ↦ 𝓡 (n i)) 0 (∀ i, M i) := by
  -- This is exactly the canonical finite-product manifold instance specialized to Euclidean models.
  infer_instance
