import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_6_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

section

universe u v

variable {R : Type v} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-!
Source/core/bridge triage:

- `source-facing`: Text 19.0.5 says that a finite family generates a convex cone exactly when the
  cone is the set of all nonnegative finite linear combinations of those generators.
- `core/canonical`: the raw owner is `PointedCone.hull R`; the source-facing owner notation is
  `cone[R]`.
- `bridge/view`: the textbook finite-sum display is the pointwise membership description of
  `(cone[R] s : Set E)` over a finite generator subtype `s`, with `Finset` as an operational
  specialization.

Domain-style sampling used here:
- `PointedCone.hull`;
- `PointedCone.mem_hull_set`;
- the coercion from `PointedCone R E` to its carrier set;
- `Finsupp` as the primitive finite-combination owner layer.

Primitive data vs derived API:
- primitive owner data: the generator owner set `s : Set E` and ambient finitely supported
  coefficients `weights : E →₀ R` with `weights.support ⊆ s`;
- derived API: subtype-indexed coefficient views, finite nonnegative-sum membership/set-equality
  formulas, and the `Finset` specialization.

Ambient minimization:
- the theorem uses only the ordered-semiring/module structure already required by
  `PointedCone.mem_hull_set`, so the file stays at that owner layer instead of hard-coding
  `EuclideanSpace ℝ (Fin n)`.

Layer target: `bridge/view`.
-/

namespace PointedCone

/-- Primitive bridge form: membership in a generated cone, stated on ambient finitely supported
coefficients with support constrained to the generator set. -/
theorem mem_cone_set_iff_exists_nonneg_finsupp
    (s : Set E) (x : E) :
    (x ∈ cone[R] s) ↔
      ∃ weights : E →₀ R,
        ↑weights.support ⊆ s ∧
        (∀ a, 0 ≤ weights a) ∧
        weights.sum (fun a r ↦ r • a) = x := by
  simpa using (PointedCone.mem_hull_set (R := R) (s := s) (x := x))

/-- Primitive set-owner form: a generated cone is exactly the set of all nonnegative finitely
supported linear combinations whose support is contained in the generator set. -/
theorem cone_set_eq_setOf_exists_nonneg_finsupp
    (s : Set E) :
    (cone[R] s : Set E) =
      {x : E | ∃ weights : E →₀ R,
          ↑weights.support ⊆ s ∧
          (∀ a, 0 ≤ weights a) ∧
          weights.sum (fun a r ↦ r • a) = x} := by
  ext x
  simpa [Set.mem_setOf_eq] using
    (mem_cone_set_iff_exists_nonneg_finsupp (R := R) (s := s) (x := x))

/-- Intrinsic generator-subtype bridge, derived from
`mem_cone_set_iff_exists_nonneg_finsupp`. -/
theorem mem_cone_set_iff_exists_nonneg_finsupp_subtype
    (s : Set E) (x : E) :
    (x ∈ cone[R] s) ↔
      ∃ weights : s →₀ R,
        (∀ a, 0 ≤ weights a) ∧
        weights.sum (fun a r ↦ r • (a : E)) = x := by
  classical
  constructor
  · intro hx
    rcases (mem_cone_set_iff_exists_nonneg_finsupp (R := R) (s := s) (x := x)).1 hx with
      ⟨weights, hsupport, hnonneg, hsum⟩
    refine ⟨weights.subtypeDomain (· ∈ s), ?_, ?_⟩
    · intro a
      exact hnonneg a
    · exact
        (Finsupp.sum_subtypeDomain_index
          (p := (· ∈ s))
          (v := weights)
          (h := fun a r ↦ r • a)
          hsupport).trans hsum
  · rintro ⟨weights, hnonneg, hsum⟩
    refine (mem_cone_set_iff_exists_nonneg_finsupp (R := R) (s := s) (x := x)).2 ?_
    refine ⟨weights.extendDomain, ?_, ?_, ?_⟩
    · exact Finsupp.support_extendDomain_subset (f := weights)
    · intro a
      by_cases ha : a ∈ s
      · simpa [Finsupp.extendDomain, ha] using hnonneg ⟨a, ha⟩
      · simp [Finsupp.extendDomain, ha]
    · calc
        weights.extendDomain.sum (fun a r ↦ r • a) =
            weights.sum (fun a r ↦ r • (a : E)) := by
          simpa [Finsupp.extendDomain_eq_embDomain_subtype] using
            (Finsupp.sum_embDomain
              (f := Function.Embedding.subtype (· ∈ s))
              (v := weights)
              (g := fun a r ↦ r • a))
        _ = x := hsum

/-- Primitive set-owner form using intrinsic generator subtypes. -/
theorem cone_set_eq_setOf_exists_nonneg_finsupp_subtype
    (s : Set E) :
    (cone[R] s : Set E) =
      {x : E | ∃ weights : s →₀ R,
          (∀ a, 0 ≤ weights a) ∧
          weights.sum (fun a r ↦ r • (a : E)) = x} := by
  ext x
  simpa [Set.mem_setOf_eq] using
    (mem_cone_set_iff_exists_nonneg_finsupp_subtype (R := R) (s := s) (x := x))

/-- Finset specialization of `mem_cone_set_iff_exists_nonneg_finsupp`. -/
theorem mem_cone_finset_iff_exists_nonneg_finsupp
    (generators : Finset E) (x : E) :
    (x ∈ cone[R] (generators : Set E)) ↔
      ∃ weights : generators →₀ R,
        (∀ a, 0 ≤ weights a) ∧
        weights.sum (fun a r ↦ r • (a : E)) = x := by
  simpa using
    (mem_cone_set_iff_exists_nonneg_finsupp_subtype
      (R := R)
      (s := (generators : Set E))
      (x := x))

/-- Intrinsic finite-index bridge: membership in a generated cone is equivalent to an ordinary
finite nonnegative sum over the generator subtype. -/
theorem mem_cone_set_iff_exists_nonneg_sum
    (s : Set E) [Fintype s] (x : E) :
    (x ∈ cone[R] s) ↔
      ∃ weights : s → R,
        (∀ a, 0 ≤ weights a) ∧
        (∑ a, weights a • (a : E)) = x := by
  classical
  constructor
  · intro hx
    rcases (mem_cone_set_iff_exists_nonneg_finsupp_subtype (R := R) (s := s) (x := x)).1 hx with
      ⟨weights, hnonneg, hsum⟩
    refine ⟨Finsupp.equivFunOnFinite weights, ?_, ?_⟩
    · intro a
      simpa [Finsupp.equivFunOnFinite_apply] using hnonneg a
    · calc
        (∑ a, (Finsupp.equivFunOnFinite weights) a • (a : E)) =
            weights.sum (fun a r ↦ r • (a : E)) := by
          symm
          simpa [Finsupp.equivFunOnFinite_apply] using
            (Finsupp.sum_fintype
              weights
              (fun a r ↦ r • (a : E))
              (fun a ↦ zero_smul R (a : E)))
        _ = x := hsum
  · rintro ⟨weights, hnonneg, hsum⟩
    let coeffs : s →₀ R := Finsupp.equivFunOnFinite.symm weights
    refine (mem_cone_set_iff_exists_nonneg_finsupp_subtype (R := R) (s := s) (x := x)).2 ?_
    refine ⟨coeffs, ?_, ?_⟩
    · intro a
      simpa [coeffs] using hnonneg a
    · calc
        coeffs.sum (fun a r ↦ r • (a : E)) =
            (∑ a, (Finsupp.equivFunOnFinite coeffs) a • (a : E)) := by
          simpa [Finsupp.equivFunOnFinite_apply] using
            (Finsupp.sum_fintype
              coeffs
              (fun a r ↦ r • (a : E))
              (fun a ↦ zero_smul R (a : E)))
        _ = ∑ a, weights a • (a : E) := by
          simp [coeffs]
        _ = x := hsum

/-- A point lies in the cone generated by a finite family exactly when it is a nonnegative finite
linear combination of those generators. -/
theorem mem_cone_finset_iff_exists_nonneg_sum
    (generators : Finset E) (x : E) :
    (x ∈ cone[R] (generators : Set E)) ↔
      ∃ weights : generators → R,
        (∀ a, 0 ≤ weights a) ∧
        (∑ a, weights a • (a : E)) = x := by
  simpa using
    (mem_cone_set_iff_exists_nonneg_sum
      (R := R)
      (s := (generators : Set E))
      x)

/-- Set-owner form of Text 19.0.5: when the generator subtype is finite, the generated cone is
exactly the set of all nonnegative finite linear combinations of those generators. -/
theorem cone_set_eq_setOf_exists_nonneg_sum
    (s : Set E) [Fintype s] :
    (cone[R] s : Set E) =
      {x : E | ∃ weights : s → R,
          (∀ a, 0 ≤ weights a) ∧
          (∑ a, weights a • (a : E)) = x} := by
  ext x
  simpa [Set.mem_setOf_eq] using
    (mem_cone_set_iff_exists_nonneg_sum (R := R) (s := s) x)

/-- Text 19.0.5: the cone generated by a finite family is exactly the set of all nonnegative
finite linear combinations of those generators. -/
theorem cone_finset_eq_setOf_exists_nonneg_sum
    (generators : Finset E) :
    (cone[R] (generators : Set E) : Set E) =
      {x : E | ∃ weights : generators → R,
          (∀ a, 0 ≤ weights a) ∧
          (∑ a, weights a • (a : E)) = x} := by
  simpa using
    (cone_set_eq_setOf_exists_nonneg_sum
      (R := R)
      (s := (generators : Set E)))

end PointedCone

end
