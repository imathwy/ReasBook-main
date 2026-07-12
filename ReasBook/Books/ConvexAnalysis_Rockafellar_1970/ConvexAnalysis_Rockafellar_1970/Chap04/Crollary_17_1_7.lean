import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_1_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section CanonicalWitness

variable {𝕜 : Type*}
variable {V : Type*}

/-- Canonical witness-set owner used in Corollary 17.1.7: the union of one linear hyperplane
fiber `f x = 0` with one off-hyperplane point `y`. -/
def linearHyperplaneWitnessSet [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (f : V →ₗ[𝕜] 𝕜) (y : V) : Set V :=
  ((linearHyperplane f (0 : 𝕜) : AffineSubspace 𝕜 V) : Set V) ∪ ({y} : Set V)

/-- Intrinsic nonclosed-convex-hull witness: if `u ≠ 0` lies in the hyperplane `f x = 0` and
`y` is off that hyperplane (`y ∉ linearHyperplane f 0`), then the convex hull of the witness set
`linearHyperplaneWitnessSet f y` is not closed. -/
theorem convexHull_linearHyperplaneWitnessSet_not_isClosed
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] [Archimedean 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousSMul 𝕜 V]
    {f : V →ₗ[𝕜] 𝕜} {u y : V} (hu : u ≠ 0)
    (hu_hyperplane : u ∈ linearHyperplane f (0 : 𝕜))
    (hy_offHyperplane : y ∉ linearHyperplane f (0 : 𝕜)) :
    ¬ IsClosed (convexHull 𝕜 (linearHyperplaneWitnessSet f y)) := by
  let H : Set V := ((linearHyperplane f (0 : 𝕜) : AffineSubspace 𝕜 V) : Set V)
  let S : Set V := linearHyperplaneWitnessSet f y
  have hS : S = H ∪ ({y} : Set V) := by
    simp [S, H, linearHyperplaneWitnessSet]
  have hH_nonempty : H.Nonempty := by
    refine ⟨0, ?_⟩
    simp [H, mem_linearHyperplane_iff]
  have h_image_H : f '' H = ({0} : Set 𝕜) := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 : f x = 0 := by
        simpa [H, mem_linearHyperplane_iff] using hx
      exact Set.mem_singleton_iff.mpr hx0
    · intro hr
      rcases Set.mem_singleton_iff.mp hr with rfl
      refine ⟨0, ?_, by simp⟩
      exact (mem_linearHyperplane_iff.mpr (by simp) : (0 : V) ∈ linearHyperplane f (0 : 𝕜))
  have hu_kernel : f u = 0 := by
    simpa [mem_linearHyperplane_iff] using hu_hyperplane
  have hy : f y ≠ 0 := by
    intro hy_eq
    exact hy_offHyperplane <| by
      simpa [mem_linearHyperplane_iff] using hy_eq
  have h_eq_y_of_mem :
      ∀ {x : V}, x ∈ convexHull 𝕜 S → f x = f y → x = y := by
    intro x hx hfx
    have hHull :
        convexHull 𝕜 S = convexJoin 𝕜 (convexHull 𝕜 H) (convexHull 𝕜 ({y} : Set V)) := by
      rw [hS]
      simpa using (convexHull_union (𝕜 := 𝕜) (s := H) (t := ({y} : Set V)))
        hH_nonempty (Set.singleton_nonempty y)
    have hxJoin : x ∈ convexJoin 𝕜 (convexHull 𝕜 H) (convexHull 𝕜 ({y} : Set V)) := by
      simpa [hHull] using hx
    rcases mem_convexJoin.mp hxJoin with ⟨a, ha, b, hb, hxSeg⟩
    have hb' : b = y := by
      simpa [convexHull_singleton] using hb
    subst b
    rcases hxSeg with ⟨α, β, hα, hβ, hαβ, rfl⟩
    have ha0 : f a = 0 := by
      have hfa : f a ∈ f '' convexHull 𝕜 H := ⟨a, ha, rfl⟩
      rw [LinearMap.image_convexHull, h_image_H, convexHull_singleton] at hfa
      simpa using hfa
    have hfx' : f (α • a + β • y) = β * f y := by
      calc
        f (α • a + β • y) = α * f a + β * f y := by
          simp [map_add, map_smul]
        _ = β * f y := by
          simp [ha0]
    have hβfy : β * f y = f y := by
      exact hfx'.symm.trans hfx
    have hβeq : β = 1 := by
      exact mul_right_cancel₀ hy (by simpa [one_mul] using hβfy)
    have hαeq : α = 0 := by linarith [hαβ, hβeq]
    simp [hαeq, hβeq]
  let z : ℕ → V := fun n => u + ((n : 𝕜) / (n + 1)) • y
  have hz_mem : ∀ n, z n ∈ convexHull 𝕜 S := by
    intro n
    have h_left : (((n : 𝕜) + 1) • u) ∈ S := by
      rw [hS]
      left
      simp [H, mem_linearHyperplane_iff, hu_kernel]
    have h_right : y ∈ S := by
      rw [hS]
      right
      simp
    have hzSeg : z n ∈ segment 𝕜 (((n : 𝕜) + 1) • u) y := by
      refine ⟨1 / ((n : 𝕜) + 1), (n : 𝕜) / ((n : 𝕜) + 1), by positivity, by positivity, ?_, ?_⟩
      · have hden : ((n : 𝕜) + 1) ≠ 0 := by positivity
        field_simp [hden]
        ring
      · have hden : ((n : 𝕜) + 1) ≠ 0 := by positivity
        dsimp [z]
        calc
          (1 / ((n : 𝕜) + 1)) • (((n : 𝕜) + 1) • u) + ((n : 𝕜) / ((n : 𝕜) + 1)) • y =
              (((n : 𝕜) + 1)⁻¹ * ((n : 𝕜) + 1)) • u + ((n : 𝕜) / ((n : 𝕜) + 1)) • y := by
            simp [smul_smul, div_eq_inv_mul]
          _ = u + ((n : 𝕜) / ((n : 𝕜) + 1)) • y := by
            simp [hden]
    exact segment_subset_convexHull h_left h_right hzSeg
  have hz_tendsto_coeff :
      Filter.Tendsto (fun n : ℕ => (n : 𝕜) / (n + 1)) Filter.atTop (nhds (1 : 𝕜)) := by
    have h_inv : Filter.Tendsto (fun n : ℕ => ((n : 𝕜) + 1)⁻¹) Filter.atTop (nhds (0 : 𝕜)) := by
      have h_add : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : 𝕜)) Filter.atTop Filter.atTop := by
        exact (Filter.tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop
      simpa [Nat.cast_add] using tendsto_inv_atTop_zero.comp h_add
    have h_coeff_eq :
        (fun n : ℕ => (n : 𝕜) / (n + 1)) = fun n : ℕ => (1 : 𝕜) - (((n : 𝕜) + 1)⁻¹) := by
      funext n
      have hden : ((n : 𝕜) + 1) ≠ 0 := by positivity
      field_simp [div_eq_mul_inv, hden]
      ring
    rw [h_coeff_eq]
    simpa [sub_eq_add_neg] using tendsto_const_nhds.add h_inv.neg
  have hz_tendsto : Filter.Tendsto z Filter.atTop (nhds (u + y)) := by
    have hsmul :
        Filter.Tendsto (fun n : ℕ => ((n : 𝕜) / (n + 1)) • y) Filter.atTop (nhds ((1 : 𝕜) • y)) :=
      hz_tendsto_coeff.smul_const y
    simpa [z, one_smul] using tendsto_const_nhds.add hsmul
  have h_not_mem : u + y ∉ convexHull 𝕜 S := by
    intro hmem
    have hfy : f (u + y) = f y := by
      simp [map_add, hu_kernel]
    have hEq : u + y = y := h_eq_y_of_mem hmem hfy
    have hu0 : u = 0 := by
      have hEq' : u + y = 0 + y := by simpa using hEq
      exact add_right_cancel hEq'
    exact hu hu0
  intro hClosed
  have hz_eventually : ∀ᶠ n in Filter.atTop, z n ∈ convexHull 𝕜 S :=
    Filter.Eventually.of_forall hz_mem
  exact h_not_mem (hClosed.mem_of_tendsto hz_tendsto hz_eventually)

theorem isClosed_linearHyperplaneWitnessSet
    [Ring 𝕜] [TopologicalSpace 𝕜] [T1Space 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [T1Space V]
    {f : V →ₗ[𝕜] 𝕜} (hf : Continuous f) (y : V) :
    IsClosed (linearHyperplaneWitnessSet f y) := by
  have hLineClosed : IsClosed (((linearHyperplane f (0 : 𝕜) : AffineSubspace 𝕜 V) : Set V)) := by
    have h_eq_preimage :
        (((linearHyperplane f (0 : 𝕜) : AffineSubspace 𝕜 V) : Set V)) = f ⁻¹' ({0} : Set 𝕜) := by
      ext x
      simp [mem_linearHyperplane_iff]
    rw [h_eq_preimage]
    exact isClosed_singleton.preimage hf
  exact hLineClosed.union isClosed_singleton

end CanonicalWitness

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 17.1.7 is stated intrinsically: if one has a continuous
  linear-hyperplane witness datum `(f, u, y)` with `f : V →L[𝕜] 𝕜`, `u ≠ 0`,
  `f u = 0`, and `f y ≠ 0`,
  then there exists a closed set whose convex hull is not closed.
- `core/canonical`: the primitive owner abstraction is
  `linearHyperplaneWitnessSet f y`, built from `linearHyperplane` and singleton union.
- `bridge/view`: combine the intrinsic closedness bridge
  `isClosed_linearHyperplaneWitnessSet` with the obstruction theorem
  `convexHull_linearHyperplaneWitnessSet_not_isClosed`.
- Domain-style sampling used here: `convexHull` from Definition 17.0.2 together with
  `linearHyperplaneWitnessSet`, `linearHyperplane`, and `Set.IsClosed.preimage`.
- Primitive data vs derived API: primitive witness data are one continuous linear form `f`,
  one nonzero point in the kernel equation `f x = 0`, and one off-hyperplane point `y` with
  `f y ≠ 0`; on the source-facing theorem surface this is packaged directly by a continuous linear
  form and the same geometric witnesses.
- Layer target: `source-facing`.
-/

/-- Corollary 17.1.7 (intrinsic owner form): if a topological `𝕜`-module admits
hyperplane witness data `(f, u, y)` with `f : V →L[𝕜] 𝕜`, `u ≠ 0`,
`f u = 0`, and `f y ≠ 0`,
then it has a closed subset whose convex hull is not closed. -/
theorem exists_closed_set_with_nonclosed_convexHull
    {𝕜 : Type*} {V : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] [Archimedean 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [T1Space V] [ContinuousAdd V]
    [ContinuousSMul 𝕜 V]
    (hdata : ∃ f : V →L[𝕜] 𝕜, ∃ u y : V, u ≠ 0 ∧
      f u = 0 ∧ f y ≠ 0) :
    ∃ S : Set V, IsClosed S ∧ ¬ IsClosed (convexHull 𝕜 S) := by
  rcases hdata with ⟨f, u, y, hu, hu_kernel, hy_ne_zero⟩
  let fₗ : V →ₗ[𝕜] 𝕜 := (f : V →ₗ[𝕜] 𝕜)
  have hu_hyperplane : u ∈ linearHyperplane fₗ (0 : 𝕜) := by
    simpa [fₗ, mem_linearHyperplane_iff] using hu_kernel
  have hy_offHyperplane : y ∉ linearHyperplane fₗ (0 : 𝕜) := by
    intro hy_mem
    exact hy_ne_zero (by simpa [fₗ, mem_linearHyperplane_iff] using hy_mem)
  refine ⟨linearHyperplaneWitnessSet fₗ y, ?_, ?_⟩
  · exact isClosed_linearHyperplaneWitnessSet (f := fₗ) f.continuous y
  · exact convexHull_linearHyperplaneWitnessSet_not_isClosed
      (f := fₗ) hu hu_hyperplane hy_offHyperplane

end
