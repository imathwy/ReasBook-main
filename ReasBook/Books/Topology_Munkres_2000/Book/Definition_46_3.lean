module

public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Topology_Munkres_2000.Book.Definition_46_3.CompactBall

public section

open Filter Set
open scoped CompactConvergence UniformConvergence

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [PseudoMetricSpace Y]

/- Definition 46.3: On `Y ^ X`, the topology of compact convergence (also called
the topology of uniform convergence on compact sets) is the topology carried by
`UniformOnFun X Y {C : Set X | IsCompact C}`. -/
#check UniformOnFun X Y {C : Set X | IsCompact C}

namespace UniformOnFun

/-- Pointwise distance bounds on compact sets give a cofinal neighborhood basis for compact
convergence. Unlike the textbook balls, these sets do not require the supremum to be below `ε`. -/
theorem hasBasis_compactConvergence_pointwise
    (f : X →ᵤ[{C : Set X | IsCompact C}] Y) :
    (nhds f).HasBasis
      (fun Cε : Set X × ℝ ↦ IsCompact Cε.1 ∧ 0 < Cε.2)
      (fun Cε ↦
        {g | ∀ x ∈ Cε.1,
          dist (toFun _ f x) (toFun _ g x) < Cε.2}) := by
  simpa [UniformOnFun.gen, dist_comm] using
    UniformOnFun.hasBasis_nhds_of_basis X Y {C : Set X | IsCompact C} f
      ⟨∅, isCompact_empty⟩ (directedOn_of_sup_mem fun _ _ ↦ IsCompact.union)
      Metric.uniformity_basis_dist

/-- Helper for Definition 46.3: a strict supremum-distance bound implies the same
pointwise distance bound at every point of the set. -/
private lemma uniformBallOn_subset_pointwise_lt
    {C : Set X} {f : X → Y} {ε : ℝ} :
    Metric.uniformBallOn C f ε ⊆
      {g | ∀ x ∈ C, dist (f x) (g x) < ε} := by
  intro g hg x hx
  rw [Metric.mem_uniformBallOn] at hg
  -- Each pointwise distance lies below the defining supremum.
  have hle :
      dist (f x) (g x) ≤ sSup ((fun z ↦ dist (f z) (g z)) '' C) :=
    le_csSup hg.1 ⟨x, hx, rfl⟩
  -- Rewrite through the owner computation lemma, then compose with the radius bound.
  have hle' : dist (f x) (g x) ≤ Metric.supDistOn C f g := by
    rwa [Metric.supDistOn_eq_sSup]
  exact hle'.trans_lt hg.2

/-- Helper for Definition 46.3: pointwise bounds by half a positive radius imply a
strict supremum-distance bound by the full radius. -/
private lemma pointwise_lt_half_subset_uniformBallOn
    {C : Set X} {f : X → Y} {ε : ℝ} (hε : 0 < ε) :
    {g | ∀ x ∈ C, dist (f x) (g x) < ε / 2} ⊆
      Metric.uniformBallOn C f ε := by
  intro g hg
  rw [Metric.mem_uniformBallOn]
  -- The half-radius is an upper bound for every pointwise distance in the image.
  have hUpper :
      ε / 2 ∈ upperBounds ((fun x ↦ dist (f x) (g x)) '' C) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hg x hx).le
  refine ⟨⟨ε / 2, hUpper⟩, ?_⟩
  -- Bound the defining supremum by the half-radius, then use positivity of `ε`.
  have hSup :
      sSup ((fun x ↦ dist (f x) (g x)) '' C) ≤ ε / 2 :=
    Real.sSup_le (fun _ hx ↦ hUpper hx) (half_pos hε).le
  have hSup' : Metric.supDistOn C f g ≤ ε / 2 := by
    rwa [Metric.supDistOn_eq_sSup]
  exact hSup'.trans_lt (half_lt_self hε)

/-- Definition 46.3: the textbook sets `B_C(f, ε)`, defined by a strict bound on the supremum
of the distances on the compact set `C`, form a neighborhood basis for compact convergence. -/
theorem hasBasis_compactConvergence
    (f : X →ᵤ[{C : Set X | IsCompact C}] Y) :
    (nhds f).HasBasis
      (fun Cε : Set X × ℝ ↦ IsCompact Cε.1 ∧ 0 < Cε.2)
      (fun Cε ↦ B_[Cε.1](f, Cε.2)) := by
  -- Replace the pointwise basis by the cofinal strict-supremum balls.
  refine (hasBasis_compactConvergence_pointwise f).to_hasBasis ?_ ?_
  · rintro ⟨C, ε⟩ ⟨hC, hε⟩
    refine ⟨⟨C, ε⟩, ⟨hC, hε⟩, ?_⟩
    exact uniformBallOn_subset_pointwise_lt
  · rintro ⟨C, ε⟩ ⟨hC, hε⟩
    -- Shrinking the pointwise radius makes its supremum strictly smaller than `ε`.
    refine ⟨⟨C, ε / 2⟩, ⟨hC, half_pos hε⟩, ?_⟩
    exact pointwise_lt_half_subset_uniformBallOn hε

end UniformOnFun
