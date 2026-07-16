import StacksProject_2024.stacks_project.Chap28.Lemma_28_5_12

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

-- Source/core/bridge triage:
-- - source-facing main statement: an infinite subset contains an infinite specialization-antichain;
-- - core/canonical owner: the topological specialization relation on the Noetherian scheme `S`;
-- - bridge: the later Lemma 28.5.12 identifies a canonical witness subset via minimal
--   specialization points, but this file keeps the source-facing existential statement itself as
--   the main public entry.

variable {S : Scheme.{u}}

/-- A subset has no nontrivial specializations among its points exactly when distinct points of the
subset do not specialize to one another. -/
theorem isAntichain_specializes_iff_forall_eq {T : Set S} :
    IsAntichain (· ⤳ ·) T ↔
      ∀ ⦃x y : S⦄, x ∈ T → y ∈ T → x ⤳ y → x = y := by
  change T.Pairwise (fun x y ↦ ¬ x ⤳ y) ↔
      ∀ ⦃x y : S⦄, x ∈ T → y ∈ T → x ⤳ y → x = y
  constructor
  · intro hT x y hx hy hxy
    by_cases hEq : x = y
    · exact hEq
    · exact (hT hx hy hEq hxy).elim
  · intro hT x hx y hy hxy hspecializes
    exact hxy (hT hx hy hspecializes)

/-- Lemma 28.5.11: an infinite subset of a Noetherian scheme contains an infinite subset with no
nontrivial specializations among its points. -/
@[stacks 0CXG]
theorem exists_infinite_subset_without_nontrivial_specializations
    [AlgebraicGeometry.IsNoetherian S] {T : Set S} (hT : T.Infinite) :
    ∃ T' ⊆ T, T'.Infinite ∧ IsAntichain (· ⤳ ·) T' := sorry

/-- The minimal specialization points of a subset form a specialization-antichain. -/
theorem isAntichain_minimalSpecializationPoints (T : Set S) :
    IsAntichain (· ⤳ ·) (S.minimalSpecializationPoints T) := by
  rw [isAntichain_specializes_iff_forall_eq]
  intro x y hx hy hxy
  exact minimalSpecializationPoints.eq_of_specializes hx hy hxy

/-- A subset of a scheme has no nontrivial specializations among its points exactly when it is
equal to its subset of minimal specialization points. -/
theorem minimalSpecializationPoints_eq_self_iff {T : Set S} :
    S.minimalSpecializationPoints T = T ↔ IsAntichain (· ⤳ ·) T := by
  rw [isAntichain_specializes_iff_forall_eq]
  constructor
  · intro hTmin x y hx hy hxy
    exact minimalSpecializationPoints.eq_of_specializes
      (show x ∈ S.minimalSpecializationPoints T from by simpa [hTmin] using hx)
      (show y ∈ S.minimalSpecializationPoints T from by simpa [hTmin] using hy)
      hxy
  · intro hT
    ext x
    constructor
    · intro hx
      exact minimalSpecializationPoints.subset T hx
    · intro hx
      exact (mem_minimalSpecializationPoints_iff S).2
        ⟨hx, fun _ hy hspecializes ↦ hT hy hx hspecializes⟩

/-- An antichain subset is fixed by `minimalSpecializationPoints`. -/
theorem minimalSpecializationPoints_eq_self_of_isAntichain {T : Set S}
    (hT : IsAntichain (· ⤳ ·) T) :
    S.minimalSpecializationPoints T = T :=
  minimalSpecializationPoints_eq_self_iff.2 hT

/-- If `T` is fixed by `minimalSpecializationPoints`, then it has no nontrivial specializations. -/
theorem isAntichain_of_minimalSpecializationPoints_eq_self {T : Set S}
    (hT : S.minimalSpecializationPoints T = T) :
    IsAntichain (· ⤳ ·) T :=
  minimalSpecializationPoints_eq_self_iff.1 hT

/-- Pointwise source-facing form of `minimalSpecializationPoints_eq_self_iff`. -/
theorem minimalSpecializationPoints_eq_self_iff_forall_eq {T : Set S} :
    S.minimalSpecializationPoints T = T ↔
      ∀ ⦃x y : S⦄, x ∈ T → y ∈ T → x ⤳ y → x = y := by
  rw [minimalSpecializationPoints_eq_self_iff, isAntichain_specializes_iff_forall_eq]

/-- Canonical bridge for Lemma 28.5.11: the infinite witness subset may be taken to be fixed by
`minimalSpecializationPoints`. -/
theorem exists_infinite_subset_minimalSpecializationPoints_eq_self
    [AlgebraicGeometry.IsNoetherian S] {T : Set S} (hT : T.Infinite) :
    ∃ T' ⊆ T, T'.Infinite ∧ S.minimalSpecializationPoints T' = T' := by
  obtain ⟨T', hT'sub, hT'inf, hT'⟩ :=
    exists_infinite_subset_without_nontrivial_specializations hT
  exact ⟨T', hT'sub, hT'inf, minimalSpecializationPoints_eq_self_of_isAntichain hT'⟩

end AlgebraicGeometry.Scheme
