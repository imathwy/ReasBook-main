import Mathlib.Analysis.Convex.Combination
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- 
Source/core/bridge triage:
- `source-facing`: Definition 2.3.12 names the convex hull of `m + 1` affinely independent points
  as an `m`-dimensional simplex, with those points as its vertices.
- `core/canonical`: mathlib's owner abstraction is `Affine.Simplex`, a bundled family of
  `m + 1` affinely independent points.
- `bridge/view`: the associated set-theoretic simplex is recovered by the canonical set
  `Affine.Simplex.closedInterior`, and mathlib's owner bridge theorem
  `Affine.Simplex.convexHull_eq_closedInterior` identifies it with the convex hull of the vertex
  set.
- Domain-style sampling used here: `Affine.Simplex`, `Affine.Simplex.points`,
  `Affine.Simplex.closedInterior`, and `Affine.Simplex.convexHull_eq_closedInterior`.
- Primitive data vs derived API: the vertices are primitive data of `Affine.Simplex`; the convex
  hull of those vertices is derived set-theoretic API.
- Layer target: `core/canonical`; this item is a direct recall of the simplex owner together with
  the canonical set-level bridge, so no parallel local simplex wrapper should be introduced here.
-/

/- Definition 2.3.12: an `m`-dimensional simplex is the canonical bundled object
`Affine.Simplex`, whose primitive vertex data are the family `s.points i`. -/
recall Affine.Simplex

section

universe u v w

variable {𝕜 : Type u} {V : Type v} {P : Type w}
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

open Affine

namespace Affine.Simplex

/-- Intrinsic finite-index owner bridge: a family indexed by any finite type of cardinality
`m + 1` is affinely independent exactly when it is the vertex family of an `m`-simplex, up to a
reindexing equivalence. -/
theorem exists_points_comp_equiv_iff {ι : Type*} [Fintype ι] {m : ℕ} {p : ι → P}
    (hcard : Fintype.card ι = m + 1) : (∃ (s : Simplex 𝕜 P m) (e : Fin (m + 1) ≃ ι),
      s.points = p ∘ e) ↔
      AffineIndependent 𝕜 p := by
  classical
  constructor
  · rintro ⟨s, e, hs⟩
    have hpe : AffineIndependent 𝕜 (p ∘ e) := by
      simpa [hs] using s.independent
    exact (affineIndependent_equiv e).1 hpe
  · intro hp
    let e : Fin (m + 1) ≃ ι :=
      Fintype.equivOfCardEq (by simpa [Fintype.card_fin] using hcard.symm)
    refine ⟨⟨p ∘ e, (affineIndependent_equiv e).2 hp⟩, e, rfl⟩

/-- Owner-first bridge: a vertex family is affinely independent exactly when it is the point family
of some bundled simplex (ordered-index bridge specialization of
`exists_points_comp_equiv_iff`). -/
theorem exists_points_iff {m : ℕ} {p : Fin (m + 1) → P} :
    (∃ s : Simplex 𝕜 P m, s.points = p) ↔ AffineIndependent 𝕜 p := by
  constructor
  · rintro ⟨s, rfl⟩
    exact s.independent
  · intro hp
    exact ⟨⟨p, hp⟩, rfl⟩

end Affine.Simplex

namespace AffineIndependent

/-- Primitive constructor-facing bridge at the intrinsic finite-index layer: an affinely
independent family indexed by any finite type of cardinality `m + 1` defines an `m`-simplex
after reindexing. -/
theorem exists_simplex_of_card_eq {ι : Type*} [Fintype ι] {m : ℕ} {p : ι → P}
    (hp : AffineIndependent 𝕜 p) (hcard : Fintype.card ι = m + 1) :
    ∃ (s : Simplex 𝕜 P m) (e : Fin (m + 1) ≃ ι), s.points = p ∘ e :=
  (Affine.Simplex.exists_points_comp_equiv_iff hcard).2 hp

/-- Definition 2.3.12 at the intrinsic finite-index layer: an `m`-simplex with vertices `p`
exists (up to reindexing) exactly when `p` is affinely independent. -/
theorem iff_exists_simplex_of_card_eq {ι : Type*} [Fintype ι] {m : ℕ} {p : ι → P}
    (hcard : Fintype.card ι = m + 1) :
    AffineIndependent 𝕜 p ↔
      ∃ (s : Simplex 𝕜 P m) (e : Fin (m + 1) ≃ ι), s.points = p ∘ e := by
  exact (Affine.Simplex.exists_points_comp_equiv_iff hcard).symm

/-- Primitive constructor-facing bridge: an affinely independent vertex family defines a bundled
simplex with exactly those vertices (ordered-index bridge specialization). -/
theorem exists_simplex {m : ℕ} {p : Fin (m + 1) → P} (hp : AffineIndependent 𝕜 p) :
    ∃ s : Simplex 𝕜 P m, s.points = p :=
  (Affine.Simplex.exists_points_iff).2 hp

/-- Definition 2.3.12 represented at the canonical owner layer: an `m`-simplex with vertex family
`p : Fin (m + 1) → P` exists exactly when `p` is affinely independent. -/
theorem iff_exists_simplex {m : ℕ} {p : Fin (m + 1) → P} :
    AffineIndependent 𝕜 p ↔ ∃ s : Simplex 𝕜 P m, s.points = p := by
  exact (Affine.Simplex.exists_points_iff).symm

end AffineIndependent

end

/- The simplex owner exposes its vertex family directly as `s.points`. -/
recall Affine.Simplex.points

/- The defining affine-independence condition of the vertices is the owner field
`Affine.Simplex.independent`. -/
recall Affine.Simplex.independent

/- Abstraction checklist for this item:
- codomain minimization: not applicable (`Definition 2.3.12` is affine-geometric; no ordered
  extended codomain owner appears).
- scalar minimization: the owner and affine-independence predicate already live over general
  `[Ring 𝕜]`; no concrete scalar (such as `ℝ`) is fixed.
- ambient minimization: the source-facing owner theorem is stated on a general affine space
  `[AddTorsor V P]` over `[Module 𝕜 V]`; no inner-product, normed, topological, or
  coordinate-model assumptions are introduced.
- finite-index minimization: the source-facing bridge is exposed at intrinsic finite-index level
  (`Fintype` + `Fintype.card` cardinal constraint), with `Fin (m + 1)` kept as the
  ordered-index bridge surface
  required by `Affine.Simplex.points`.
- owner decision: the canonical owner remains `Affine.Simplex`; no parallel wrapper owner is
  introduced.
-/

/- The textbook set-level simplex is recovered by the owner bridge theorem
`Affine.Simplex.convexHull_eq_closedInterior`, identifying the convex hull of the vertices with
the canonical set `Affine.Simplex.closedInterior`. -/
recall Affine.Simplex.convexHull_eq_closedInterior
