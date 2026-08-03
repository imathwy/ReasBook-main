module

public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Separation.Hausdorff

public section

namespace RealTopology

/-- The finite-complement topology on `ℝ` is not Hausdorff. -/
theorem cofiniteNotT2Space : ¬ T2Space (CofiniteTopology ℝ) := by
  -- Disjoint nonempty cofinite opens would make the whole real line finite.
  intro hT2
  have hZeroNeOne : CofiniteTopology.of (0 : ℝ) ≠ CofiniteTopology.of 1 :=
    CofiniteTopology.of.injective.ne (by norm_num)
  obtain ⟨u, v, huOpen, hvOpen, hZeroMem, hOneMem, huv⟩ := hT2.t2 hZeroNeOne
  have huFinite : uᶜ.Finite :=
    (CofiniteTopology.isOpen_iff.mp huOpen) ⟨_, hZeroMem⟩
  have hvFinite : vᶜ.Finite :=
    (CofiniteTopology.isOpen_iff.mp hvOpen) ⟨_, hOneMem⟩
  have hUnivFinite : (Set.univ : Set (CofiniteTopology ℝ)).Finite :=
    (huFinite.union hvFinite).subset fun x _ ↦ by
      by_contra hx
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hx
      exact Set.disjoint_left.mp huv hx.1 hx.2
  have hInfinite : Infinite (CofiniteTopology ℝ) :=
    Infinite.of_injective (fun n : ℕ ↦ CofiniteTopology.of (n : ℝ))
      ((CofiniteTopology.of (X := ℝ)).injective.comp Nat.cast_injective)
  exact @Set.infinite_univ (CofiniteTopology ℝ) hInfinite hUnivFinite

end RealTopology
