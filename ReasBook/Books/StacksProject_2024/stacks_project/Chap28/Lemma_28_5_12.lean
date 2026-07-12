import Mathlib.AlgebraicGeometry.Noetherian

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

section

variable (S : Scheme.{u})

/-
Semantic recall: `lean_leansearch` was unavailable here (HTTP 429) and `lean_local_search` timed
out, so the owner choice was verified from local precedent instead. Chapter 5 already uses the
canonical specialization relation `Specializes`/`x ⤳ y`, the closure bridge
`specializes_iff_mem_closure`, and `TopologicalSpace.NoetherianSpace`; this item is therefore kept
as the source-facing subset of points of `T` that are minimal for specialization in the underlying
space of a Noetherian scheme.
-/

/-- The subset of `T` consisting of points with no strict generalization inside `T`. -/
def minimalSpecializationPoints (T : Set S) : Set S :=
  { t | t ∈ T ∧ ∀ ⦃t' : S⦄, t' ∈ T → t' ⤳ t → t' = t }

/-- Membership in `S.minimalSpecializationPoints T` means belonging to `T` and admitting no other
point of `T` specializing to it. -/
theorem mem_minimalSpecializationPoints_iff {T : Set S} {t : S} :
    t ∈ S.minimalSpecializationPoints T ↔
      t ∈ T ∧ ∀ ⦃t' : S⦄, t' ∈ T → t' ⤳ t → t' = t := Iff.rfl

namespace minimalSpecializationPoints

variable {S}

/-- A minimal specialization point of `T` belongs to `T`. -/
theorem subset (T : Set S) : S.minimalSpecializationPoints T ⊆ T := by
  intro t ht
  exact (mem_minimalSpecializationPoints_iff S).1 ht |>.1

/-- A point of `S.minimalSpecializationPoints T` admits no other point of `T` specializing to it. -/
theorem eq_of_mem_of_specializes {T : Set S} {t t' : S}
    (ht : t ∈ S.minimalSpecializationPoints T) (ht' : t' ∈ T) (h : t' ⤳ t) : t' = t :=
  (mem_minimalSpecializationPoints_iff S).1 ht |>.2 ht' h

/-- Specializations among points of `S.minimalSpecializationPoints T` are trivial. -/
theorem eq_of_specializes {T : Set S} {t₁ t₂ : S}
    (ht₁ : t₁ ∈ S.minimalSpecializationPoints T)
    (ht₂ : t₂ ∈ S.minimalSpecializationPoints T) (h : t₁ ⤳ t₂) : t₁ = t₂ :=
  eq_of_mem_of_specializes ht₂ (subset T ht₁) h

end minimalSpecializationPoints

/-- Lemma 28.5.12 (1): if two points of `T0 = S.minimalSpecializationPoints T` are related by
specialization, then they are equal. Equivalently, there are no nontrivial specializations among
the points of `T0`. -/
theorem eq_of_specializes_of_mem_minimalSpecializationPoints
    {T : Set S} {t1 t2 : S}
    (ht1 : t1 ∈ S.minimalSpecializationPoints T)
    (ht2 : t2 ∈ S.minimalSpecializationPoints T)
    (h : t1 ⤳ t2) : t1 = t2 :=
  minimalSpecializationPoints.eq_of_specializes ht1 ht2 h

/-- Lemma 28.5.12 (2): every point of `T` is a specialization of a point of
`S.minimalSpecializationPoints T`. -/
theorem exists_mem_minimalSpecializationPoints_specializingTo
    [AlgebraicGeometry.IsNoetherian S] {T : Set S} {t : S} (ht : t ∈ T) :
    ∃ t0 ∈ S.minimalSpecializationPoints T, t0 ⤳ t := sorry

/-- Lemma 28.5.12 (3): the closures of `T` and `S.minimalSpecializationPoints T` coincide. -/
theorem closure_eq_closure_minimalSpecializationPoints
    [AlgebraicGeometry.IsNoetherian S] {T : Set S} :
    closure T = closure (S.minimalSpecializationPoints T) := sorry

end

end AlgebraicGeometry.Scheme
