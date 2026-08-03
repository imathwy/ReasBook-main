module

public import Mathlib.Topology.UrysohnsLemma

public section

open Set

universe u

/-- Theorem 33.1 (Urysohn lemma). If `A` and `B` are disjoint closed subsets of a
normal space `X`, then any closed real interval `Set.Icc a b` admits a continuous map
from `X` taking the value `a` on `A` and the value `b` on `B`. Here `T4Space` expresses
the book's convention for a normal space. -/
theorem exists_continuousMap_Icc_eq_endpoints {X : Type u} [TopologicalSpace X]
    [T4Space X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) {a b : ℝ} (hab : a ≤ b) :
    ∃ f : C(X, Icc a b),
      EqOn f (fun _ ↦ ⟨a, le_rfl, hab⟩) A ∧ EqOn f (fun _ ↦ ⟨b, hab, le_rfl⟩) B := by
  obtain ⟨f, hfA, hfB, hf⟩ := exists_continuous_zero_one_of_isClosed hA hB hAB
  have hmem (x : X) : AffineMap.lineMap a b (f x) ∈ Icc a b := by
    rw [AffineMap.lineMap_apply_ring]
    constructor <;> nlinarith [(hf x).1, (hf x).2]
  let g : C(X, Icc a b) :=
    ⟨fun x ↦ ⟨AffineMap.lineMap a b (f x), hmem x⟩,
      (AffineMap.lineMap_continuous.comp f.continuous).subtype_mk hmem⟩
  refine ⟨g, ?_, ?_⟩
  · intro x hx
    apply Subtype.ext
    simp [g, hfA hx]
  · intro x hx
    apply Subtype.ext
    simp [g, hfB hx]

end
