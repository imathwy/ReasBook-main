module

public import Mathlib.Topology.TietzeExtension

public section

open Set

universe u

/-- Theorem 35.1 (1). If `A` is a closed subspace of a normal space `X`, every
continuous map from `A` to a nonempty closed interval `Set.Icc a b` extends continuously to `X`.
Here `T4Space` expresses the book's convention for a normal space. -/
theorem continuousMap_exists_extension_Icc {X : Type u} [TopologicalSpace X] [T4Space X]
    {A : Set X} (hA : IsClosed A) {a b : ℝ} (hab : a ≤ b) (f : C(A, Set.Icc a b)) :
    ∃ g : C(X, Set.Icc a b), ContinuousMap.restrict A g = f := by
  let fReal : C(A, ℝ) := ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ f
  obtain ⟨g, hgIcc, hgf⟩ := fReal.exists_restrict_eq_forall_mem_of_closed
    (fun x ↦ (f x).property) ⟨a, le_rfl, hab⟩ hA
  let gIcc : C(X, Set.Icc a b) :=
    ⟨Set.codRestrict g (Set.Icc a b) hgIcc, g.continuous.codRestrict hgIcc⟩
  refine ⟨gIcc, ?_⟩
  ext x
  simpa [gIcc, fReal] using ContinuousMap.congr_fun hgf x

/-- Theorem 35.1 (2). If `A` is a closed subspace of a normal space `X`, every
continuous real-valued map on `A` extends continuously to `X`. Here `T4Space`
expresses the book's convention for a normal space. -/
theorem continuousMap_exists_extension_real {X : Type u} [TopologicalSpace X] [T4Space X]
    {A : Set X} (hA : IsClosed A) (f : C(A, ℝ)) :
    ∃ g : C(X, ℝ), ContinuousMap.restrict A g = f :=
  f.exists_restrict_eq hA
