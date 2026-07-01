import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_3_10

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.3.11 names a polytope as a set that is the convex hull of finitely
  many points.
- `core/canonical`: the owner abstractions are `convexHull 𝕜 s` for convex hulls and `Set E`
  together with `Set.Finite` for finite generating sets, matching mathlib's invariant finite
  convex-hull ecosystem.
- `bridge/view`: finite-family presentations are exposed first through honestly finite index types
  (`Finite`) and `Set.range`, then through `Fintype`-indexed ranges, and finally through the
  concrete `Finset` phrasing via `Set.exists_finite_iff_finset`.
- Primitive data vs derived API: the primitive data are a finite generating set `t : Set E` and
  its convex-hull equality; `Fintype`/`Finset` presentations and convexity are derived API.
- Domain-style sampling: the relevant owner-level declarations are `convexHull`,
  `subset_convexHull`, `convex_convexHull`, `Set.range_val`, `Set.finite_range`, and
  `Set.exists_finite_iff_finset`.

Layer target: `source-facing`. The owner is the chapter predicate `IsPolytope`, owned directly by
the invariant finite-set statement `∃ t : Set E, t.Finite ∧ s = convexHull 𝕜 t`.
Finite-family surfaces are derived: first the intrinsic honestly finite (`Finite`) range view,
then the operational `Fintype` range view, and finally `Finset` as a thin concrete bridge.
-/

/- Abstraction checklist for this item:
- scalar/ambient minimization: the reused canonical APIs `convexHull`, `subset_convexHull`, and
  `convex_convexHull` are all stated over exactly
  `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]`; this file therefore keeps that
  same weakest canonical layer and does not specialize to `ℝ`, ordered rings, topological
  structures, normed spaces, or inner-product spaces.
- owner parameter visibility: the scalar `𝕜` is mathematically essential and is not recoverable from
  `s : Set E`, so it is kept as an explicit owner parameter (`s.IsPolytope 𝕜`).
- codomain-generalization axis: not applicable here, since `IsPolytope` is a subset-level geometric
  predicate and does not introduce an ordered extended codomain owner (`EReal`/`WithBotTop` style).
- topology-generalization axis: not applicable here, since the item uses only algebraic/convex-hull
  data and no ambient/intrinsic topological notions
  (`closure`, `interior`, relative topology, etc.).
- finite-family abstraction axis: the canonical owner stays `Set.Finite`; finite indexing is exposed
  intrinsically first with `Finite`/`Set.range`, then operationally with
  `Fintype`/`Set.range`, before the concrete `Finset` bridge.
-/

open scoped Rockafellar

universe u v

section

variable (𝕜 : Type v) {E : Type u} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]

namespace Set

/-- Definition 2.3.11: a polytope is a set that can be written as the convex hull of a finite set
of points. -/
def IsPolytope (s : Set E) : Prop :=
  ∃ t : Set E, t.Finite ∧ s = conv[𝕜] t

namespace IsPolytope

/-- Constructor at the primitive owner layer: the convex hull of a finite set is a polytope. -/
theorem mk {t : Set E} (ht : t.Finite) : (conv[𝕜] t).IsPolytope 𝕜 :=
  ⟨t, ht, rfl⟩

/-- Intrinsic finite-index constructor: the convex hull of the range of an honestly finite indexed
family is a polytope. -/
theorem mk_finite {ι : Type*} [Finite ι] (points : ι → E) :
    (conv[𝕜] (Set.range points)).IsPolytope 𝕜 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact mk (𝕜 := 𝕜) (Set.finite_range points)

set_option linter.unusedFintypeInType false in
/-- Operational finite-index constructor: the convex hull of a `Fintype`-indexed range is a
polytope. -/
theorem mk_fintype {ι : Type*} [Fintype ι] (points : ι → E) :
    (conv[𝕜] (Set.range points)).IsPolytope 𝕜 := by
  exact mk_finite (𝕜 := 𝕜) points

/-- Operational constructor: the convex hull of a finite family of points is a polytope. -/
theorem mk_finset (t : Finset E) : (conv[𝕜] (t : Set E)).IsPolytope 𝕜 :=
  mk (𝕜 := 𝕜) t.finite_toSet

/-- The empty set is a polytope. -/
theorem empty : (∅ : Set E).IsPolytope 𝕜 := by
  simpa [convexHull_empty] using (mk (𝕜 := 𝕜) (t := (∅ : Set E)) Set.finite_empty)

/-- Every singleton set is a polytope. -/
theorem singleton (x : E) : ({x} : Set E).IsPolytope 𝕜 := by
  simpa [convexHull_singleton] using
    (mk (𝕜 := 𝕜) (t := ({x} : Set E)) (Set.finite_singleton x))

/-- A polytope can equivalently be described as the convex hull of the range of a finite indexed
family of points, at the intrinsic honestly finite index layer. -/
theorem iff_exists_finite {s : Set E} :
    s.IsPolytope 𝕜 ↔
      ∃ (ι : Type u) (_ : Finite ι) (points : ι → E), s = conv[𝕜] (Set.range points) := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    classical
    letI : Fintype ↥t := ht.fintype
    refine ⟨↥t, Finite.of_fintype ↥t, Subtype.val, ?_⟩
    simp
  · rintro ⟨ι, hι, points, rfl⟩
    letI : Finite ι := hι
    exact mk_finite (𝕜 := 𝕜) points

/-- Intrinsic finite-index bridge: a polytope admits an honestly finite indexed range
presentation. -/
theorem exists_finite {s : Set E} (hs : s.IsPolytope 𝕜) :
    ∃ (ι : Type u) (_ : Finite ι) (points : ι → E), s = conv[𝕜] (Set.range points) :=
  (iff_exists_finite (𝕜 := 𝕜)).mp hs

/-- Intrinsic finite-index bridge, converse direction. -/
theorem of_exists_finite {s : Set E}
    (hs : ∃ (ι : Type u) (_ : Finite ι) (points : ι → E), s = conv[𝕜] (Set.range points)) :
    s.IsPolytope 𝕜 := by
  rcases hs with ⟨ι, hι, points, rfl⟩
  letI : Finite ι := hι
  exact mk_finite (𝕜 := 𝕜) points

/-- Operational finite-index bridge: a polytope can equivalently be described as the convex hull
of the range of a `Fintype`-indexed family of points. -/
theorem iff_exists_fintype {s : Set E} :
    s.IsPolytope 𝕜 ↔
      ∃ (ι : Type u) (_ : Fintype ι) (points : ι → E), s = conv[𝕜] (Set.range points) := by
  constructor
  · intro hs
    rcases (iff_exists_finite (𝕜 := 𝕜) (s := s)).mp hs with ⟨ι, hι, points, hEq⟩
    classical
    letI : Finite ι := hι
    letI : Fintype ι := Fintype.ofFinite ι
    exact ⟨ι, inferInstance, points, hEq⟩
  · rintro ⟨ι, _, points, hEq⟩
    rcases hEq
    exact mk_fintype (𝕜 := 𝕜) points

/-- Operational finite-index bridge: a polytope admits a `Fintype`-indexed range presentation. -/
theorem exists_fintype {s : Set E} (hs : s.IsPolytope 𝕜) :
    ∃ (ι : Type u) (_ : Fintype ι) (points : ι → E), s = conv[𝕜] (Set.range points) :=
  (iff_exists_fintype (𝕜 := 𝕜)).mp hs

/-- Operational finite-index bridge, converse direction. -/
theorem of_exists_fintype {s : Set E}
    (hs : ∃ (ι : Type u) (_ : Fintype ι) (points : ι → E), s = conv[𝕜] (Set.range points)) :
    s.IsPolytope 𝕜 := by
  rcases hs with ⟨ι, hι, points, rfl⟩
  letI : Fintype ι := hι
  exact mk_fintype (𝕜 := 𝕜) points

/-- Concrete finite-family bridge: a polytope can equivalently be described as the convex hull of
the underlying set of a `Finset` of points. -/
theorem iff_exists_finset {s : Set E} :
    s.IsPolytope 𝕜 ↔ ∃ t : Finset E, s = conv[𝕜] (t : Set E) := by
  simpa [Set.IsPolytope] using
    (show (∃ t : Set E, t.Finite ∧ s = conv[𝕜] t) ↔
        ∃ t : Finset E, s = conv[𝕜] (t : Set E) from
      Set.exists_finite_iff_finset)

/-- A polytope can be generated by finitely many points that already belong to the set. -/
theorem iff_exists_finite_subset {s : Set E} :
    s.IsPolytope 𝕜 ↔ ∃ t : Set E, t.Finite ∧ t ⊆ s ∧ s = conv[𝕜] t := by
  constructor
  · intro hs
    rcases hs with ⟨t, ht, rfl⟩
    exact ⟨t, ht, subset_convexHull 𝕜 t, rfl⟩
  · intro hs
    rcases hs with ⟨t, ht, _, hEq⟩
    exact ⟨t, ht, hEq⟩

/-- Intrinsic finite-generation bridge: a polytope is generated by finitely many of its own
points. -/
theorem exists_finite_subset {s : Set E} (hs : s.IsPolytope 𝕜) :
    ∃ t : Set E, t.Finite ∧ t ⊆ s ∧ s = conv[𝕜] t :=
  (iff_exists_finite_subset (𝕜 := 𝕜)).mp hs

/-- Intrinsic finite-generation bridge, converse direction. -/
theorem of_exists_finite_subset {s : Set E}
    (hs : ∃ t : Set E, t.Finite ∧ t ⊆ s ∧ s = conv[𝕜] t) : s.IsPolytope 𝕜 :=
  (iff_exists_finite_subset (𝕜 := 𝕜)).mpr hs

/-- Operational bridge: a polytope admits a finite-family (`Finset`) presentation. -/
theorem exists_finset {s : Set E} (hs : s.IsPolytope 𝕜) :
    ∃ t : Finset E, s = conv[𝕜] (t : Set E) :=
  (iff_exists_finset (𝕜 := 𝕜)).mp hs

/-- Operational bridge, converse direction: a finite-family presentation defines a polytope. -/
theorem of_exists_finset {s : Set E}
    (hs : ∃ t : Finset E, s = conv[𝕜] (t : Set E)) : s.IsPolytope 𝕜 :=
  (iff_exists_finset (𝕜 := 𝕜)).mpr hs

/-- Every polytope is convex. -/
theorem convex {s : Set E} (hs : s.IsPolytope 𝕜) : Convex 𝕜 s := by
  rcases hs with ⟨t, _, rfl⟩
  exact convex_convexHull 𝕜 t

end IsPolytope

end Set

end
