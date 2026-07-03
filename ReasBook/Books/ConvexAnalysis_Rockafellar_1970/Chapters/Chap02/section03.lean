import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_2_3_1 (from Chap01) -/
open scoped Rockafellar

section

variable {ι : Type*} {𝕜 E : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E]

namespace Set

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.3.1 specializes the finite-convex-combination description of a
  convex hull to a finitely indexed family `b : ι → E`.
- `core/canonical`: the owner abstractions are `conv[𝕜] (range b)` for the hull itself and
  the simplex membership theorem `Set.mem_conv_iff_exists_stdSimplex`; the simplex-side point
  map is the owner-level convex-combination map
  `fun w : StdSimplex 𝕜 ι ↦ (w.map b).convexCombination`.
- `bridge/view`: the set-level bridge theorem is the image equality
  `conv[𝕜] (range b) = Set.range (fun w : StdSimplex 𝕜 ι ↦ (w.map b).convexCombination)`.
- Primitive data vs derived API: the indexed family `b` is the primitive data; nonnegativity and
  total mass `1` are fields of `StdSimplex`, and the owner-level API should expose simplex
  witnesses directly; the range equality is a bridge view of that owner statement.
- Domain-style sampling: this item reuses `StdSimplex`, `StdSimplex.map_map`, and
  `Set.mem_conv_iff_exists_stdSimplex`.
- Layer target: `core/canonical` first (membership via simplex owner), then the range-equality
  bridge.
-/

/-- Helper for Corollary 2.3.1: simplex witnesses on `range b` are equivalent to simplex
witnesses on the original index type `ι`. -/
private theorem exists_stdSimplex_range_iff_exists_stdSimplex
    (b : ι → E) {x : E} :
    (∃ w : StdSimplex 𝕜 (range b), (w.map Subtype.val).convexCombination = x) ↔
      ∃ w : StdSimplex 𝕜 ι, (w.map b).convexCombination = x := by
  constructor
  · rintro ⟨w, hx⟩
    -- Choose a preimage in `ι` for each point of `range b`, then reindex the simplex along it.
    choose c hc using (fun y : range b ↦ y.2)
    refine ⟨w.map c, ?_⟩
    simpa [StdSimplex.map_map, hc] using hx
  · rintro ⟨w, hw⟩
    -- Push the simplex forward along the canonical map from `ι` into `range b`.
    refine ⟨w.map (fun i ↦ ⟨b i, Set.mem_range_self i⟩), ?_⟩
    simpa [StdSimplex.map_map] using hw

/-- Helper for Corollary 2.3.1: owner-level membership form on the canonical set surface.
A point belongs to `conv[𝕜] (range b)` exactly when it belongs to the range of the simplex-map
convex-combination operator induced by `b`. -/
theorem mem_conv_range_iff_mem_range_convexCombination (b : ι → E) {x : E} :
    x ∈ (conv[𝕜] (range b)) ↔
      x ∈ Set.range (fun w : StdSimplex 𝕜 ι ↦ (w.map b).convexCombination) := by
  -- Specialize Theorem 2.3 to `range b`, then replace subtype witnesses by indexed witnesses.
  calc
    x ∈ (conv[𝕜] (range b))
        ↔ ∃ w : StdSimplex 𝕜 (range b), (w.map Subtype.val).convexCombination = x := by
          simpa using
            (Set.mem_conv_iff_exists_stdSimplex (𝕜 := 𝕜) (s := range b) (x := x))
    _ ↔ ∃ w : StdSimplex 𝕜 ι, (w.map b).convexCombination = x :=
      exists_stdSimplex_range_iff_exists_stdSimplex (b := b) (x := x)
    _ ↔ x ∈ Set.range (fun w : StdSimplex 𝕜 ι ↦ (w.map b).convexCombination) := by
      simp [Set.mem_range]

/-- Helper for Corollary 2.3.1: existential simplex-witness form of
`Set.mem_conv_range_iff_mem_range_convexCombination`. -/
theorem mem_conv_range_iff_exists_stdSimplex (b : ι → E) {x : E} :
    x ∈ (conv[𝕜] (range b)) ↔
      ∃ w : StdSimplex 𝕜 ι, (w.map b).convexCombination = x := by
  -- This is just the `Set.range` presentation rewritten as an existential witness.
  simpa [Set.mem_range] using
    (mem_conv_range_iff_mem_range_convexCombination (𝕜 := 𝕜) (b := b) (x := x))

/-- Corollary 2.3.1 as the set-image bridge view of
`Set.mem_conv_range_iff_mem_range_convexCombination`. -/
theorem conv_range_eq_range_convexCombination (b : ι → E) :
    (conv[𝕜] (range b)) =
      Set.range
        (fun w : StdSimplex 𝕜 ι ↦ (w.map b).convexCombination) := by
  -- Extensionality reduces the set equality to the membership theorem above.
  ext x
  simpa using
    (mem_conv_range_iff_mem_range_convexCombination (𝕜 := 𝕜) (b := b) (x := x))

end Set

end

/-! ### Theorem_2_3 (from Chap01) -/
open scoped BigOperators
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Theorem 2.3 says that the convex hull of `S` is exactly the set of all
  finite convex combinations of points of `S`.
- `core/canonical`: mathlib's owner theorem is `mem_convexHull_iff_exists_fintype`, which
  characterizes membership in `convexHull R S` by a finitely supported weighted sum with
  nonnegative coefficients summing to `1`. For finite supports, the canonical owner theorem is
  `Finset.mem_convexHull`, using `Finset.centerMass`.
- `core/owner`: simplex coefficients are intrinsically owned by `StdSimplex R ι`, where
  nonnegativity and total-mass constraints are fields instead of separate hypotheses.
- `bridge/view`: `Finset.mem_convexHull'` is the equivalent finite-support weighted-sum view,
  matching the textbook display formula directly.
- Primitive data vs derived API: the canonical object is `convexHull`; the convex-combination
  presentation is its standard membership theorem and should be recalled directly rather than
  restated through a parallel owner. The chapter surface still benefits from a short notation-first
  bridge using `conv[𝕜]`.
- Domain-style sampling: this item grows from the earlier chapter recall `convexHull` from
  `Definition_2_3_10`, together with the owner theorem
  `mem_convexHull_iff_exists_fintype`, its finite-support companion `Finset.mem_convexHull'`, and
  the minimality view `convexHull_eq_iInter`.
- Layer target: `core/canonical`, with source-facing theorem surfaces written in the chapter's
  `conv[𝕜]` notation and short local bridge names while reusing the same canonical owners.

Abstraction checks for this item:
- Codomain/ambient layer: this item is set-valued (`Set E`) and does not involve extended codomain
  owners (`EReal`, `WithBotTop`), so no codomain lift applies here.
- Scalar structure: the canonical owner theorem used here is
  `mem_convexHull_iff_exists_fintype`, whose current upstream layer is
  `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`; this file keeps exactly that layer.
- Owner choice: upgrade the source-facing core membership theorem to `StdSimplex` owner form, then
  keep the explicit weighted-sum theorem as a bridge view.
- Topology language: not applicable for this item.
- Owner naming/notation: keep the short chapter notation `conv[𝕜]` and use short theorem names in
  `Set`/`Finset` namespaces.
-/

/- Theorem 2.3: a point belongs to the convex hull of `S` exactly when it is a finite convex
combination of points of `S`; this is the canonical theorem
`mem_convexHull_iff_exists_fintype`. -/
recall mem_convexHull_iff_exists_fintype

/- Finite-support membership is canonically packaged by `Finset.mem_convexHull`. -/
recall Finset.mem_convexHull

/- The equivalent explicit weighted-sum formulation is `Finset.mem_convexHull'`. -/
recall Finset.mem_convexHull'

section

variable {𝕜 : Type*} {E : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

namespace Set

/- The owner-level simplex form of Theorem 2.3. -/
theorem mem_conv_iff_exists_stdSimplex {s : Set E} {x : E} :
    x ∈ (conv[𝕜] s) ↔
      ∃ w : StdSimplex 𝕜 s,
        (w.map Subtype.val).convexCombination = x := by
  constructor
  · intro hx
    rcases (mem_convexHull_iff_exists_fintype (R := 𝕜) (s := s) (x := x)).1 hx with
      ⟨ι, _, w, z, hw₀, hw₁, hz, hxsum⟩
    let simplex : StdSimplex 𝕜 ι :=
      { weights := Finsupp.equivFunOnFinite.symm w
        nonneg := by
          intro i
          simpa using hw₀ i
        total := by
          simpa [Finsupp.sum_fintype] using hw₁ }
    refine ⟨simplex.map (fun i ↦ ⟨z i, hz i⟩), ?_⟩
    have hxcomb : (simplex.map (fun i ↦ z i)).convexCombination = x := by
      calc
        (simplex.map (fun i ↦ z i)).convexCombination =
            simplex.sum (fun i r ↦ r • z i) := by
          exact StdSimplex.map_convexCombination_eq_sum (w := simplex) (z := z)
        _ = x := by
          simpa [simplex, Finsupp.sum_fintype] using hxsum
    simpa [StdSimplex.map_map] using hxcomb
  · rintro ⟨w, hxcomb⟩
    let κ := { i // i ∈ w.weights.support }
    have hxsum : w.sum (fun i r ↦ r • (i : E)) = x := by
      calc
        w.sum (fun i r ↦ r • (i : E)) = (w.map Subtype.val).convexCombination := by
          exact
            (StdSimplex.map_convexCombination_eq_sum (w := w) (z := Subtype.val)).symm
        _ = x := hxcomb
    have hw₁ : ∑ i : κ, w.weights i.1 = 1 := by
      have hsub :
          (∑ i : κ, w.weights i.1) = ∑ i ∈ w.weights.support, w.weights i := by
        symm
        refine Finset.sum_subtype (s := w.weights.support) (f := fun i : s ↦ w.weights i) ?_
        intro i
        simp
      calc
        (∑ i : κ, w.weights i.1) = ∑ i ∈ w.weights.support, w.weights i := hsub
        _ = 1 := by
          simpa [Finsupp.sum] using w.total
    have hxκ : ∑ i : κ, w.weights i.1 • ((i.1 : s) : E) = x := by
      have hsub :
          (∑ i : κ, w.weights i.1 • ((i.1 : s) : E)) =
            ∑ i ∈ w.weights.support, w.weights i • (i : E) := by
        symm
        refine Finset.sum_subtype (s := w.weights.support)
          (f := fun i : s ↦ w.weights i • (i : E)) ?_
        intro i
        simp
      calc
        (∑ i : κ, w.weights i.1 • ((i.1 : s) : E)) =
            ∑ i ∈ w.weights.support, w.weights i • (i : E) := hsub
        _ = x := by
          simpa [Finsupp.sum] using hxsum
    exact mem_convexHull_of_exists_fintype
      (s := s)
      (w := fun i : κ ↦ w.weights i.1)
      (z := fun i : κ ↦ (i.1 : E))
      (fun i ↦ w.nonneg i.1) hw₁ (fun i ↦ i.1.2) hxκ

/-- Theorem 2.3 on the chapter surface: membership in `conv[𝕜] s` is equivalent to the existence
of a finite convex-combination representation. This is the weighted-sum bridge view of
`Set.mem_conv_iff_exists_stdSimplex`. -/
theorem mem_conv_iff_exists_fintype {s : Set E} {x : E} :
    x ∈ (conv[𝕜] s) ↔
      ∃ (ι : Type) (_ : Fintype ι) (w : ι → 𝕜) (z : ι → E),
        (∀ i, 0 ≤ w i) ∧
        ∑ i, w i = 1 ∧
        (∀ i, z i ∈ s) ∧
        ∑ i, w i • z i = x := by
  simpa using (mem_convexHull_iff_exists_fintype (R := 𝕜) (s := s) (x := x))

end Set

namespace Finset

/-- Finite-support owner-level simplex form of Theorem 2.3 on the chapter surface. -/
theorem mem_conv_iff_exists_stdSimplex {s : Finset E} {x : E} :
    x ∈ (conv[𝕜] (s : Set E)) ↔
      ∃ w : StdSimplex 𝕜 (s : Set E),
        (w.map Subtype.val).convexCombination = x := by
  simpa using (Set.mem_conv_iff_exists_stdSimplex (𝕜 := 𝕜) (s := (s : Set E)) (x := x))

/-- Finite-support center-mass form of Theorem 2.3 on the chapter surface. -/
theorem mem_conv_iff_exists_centerMass {s : Finset E} {x : E} :
    x ∈ (conv[𝕜] (s : Set E)) ↔
      ∃ w : E → 𝕜,
        (∀ y ∈ s, 0 ≤ w y) ∧
        ∑ y ∈ s, w y = 1 ∧
        s.centerMass w id = x := by
  simpa using
    (Finset.mem_convexHull (R := 𝕜) (s := s) (x := x))

/-- Finite-support weighted-sum form of Theorem 2.3 on the chapter surface. -/
theorem mem_conv_iff_exists_weightedSum {s : Finset E} {x : E} :
    x ∈ (conv[𝕜] (s : Set E)) ↔
      ∃ w : E → 𝕜,
        (∀ y ∈ s, 0 ≤ w y) ∧
        ∑ y ∈ s, w y = 1 ∧
        ∑ y ∈ s, w y • y = x := by
  simpa using
    (Finset.mem_convexHull' (R := 𝕜) (s := s) (x := x))

end Finset

end

/-! ### Definition_2_3_10 (from Chap01) -/
/- 
Source/core/bridge triage:
- `source-facing`: Definition 2.3.10 introduces the convex hull of a subset `S` as the
  intersection of all convex sets containing `S`.
- `core/canonical`: mathlib's owner abstraction is `convexHull 𝕜 s`, the convex-hull closure
  operator on sets.
- `bridge/view`: the textbook's intersection wording is the theorem `convexHull_eq_iInter`.
- Domain-style sampling used here: `convexHull`, `subset_convexHull`, `convex_convexHull`,
  `Convex.convexHull_subset_iff`, and `convexHull_eq_iInter` from
  `Mathlib.Analysis.Convex.Hull`.
- Primitive data vs derived API: the primitive owner interface is the closure-style package
  (`subset_convexHull`, `convex_convexHull`, `Convex.convexHull_subset_iff`) around `convexHull`;
  the explicit intersection formula is derived API and is exposed as a notation-first bridge
  theorem.
- Layer target: `core/canonical`; this item keeps `convexHull` as raw owner, while exposing short
  chapter-surface bridge theorems stated directly in `conv[𝕜]` notation.
-/

/- Abstraction checks for this item:
- Codomain/ambient layer: this item is set-valued (`Set E`), so no ordered extended-codomain
  generalization axis (`EReal`/`WithTopBot`) is involved.
- Scalar/ambient structure: reused upstream owners (`convexHull`, `subset_convexHull`,
  `convex_convexHull`, `convexHull_eq_iInter`) already live at the weakest layer
  `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]`; this file stays on that layer.
- Owner choice: keep `convexHull`/`Convex` as primitive owners; the textbook intersection
  formulations are bridge theorems.
- Topology language: not applicable for this item.
- Notation/API surface: keep the chapter notation `conv[𝕜]`, and expose a binder-light
  subtype-intersection surface to avoid proof-binder noise on theorem statements.
-/

/-- Textbook notation for the convex hull of a set. The raw owner remains `convexHull`. -/
scoped[Rockafellar] notation:max "conv[" 𝕜 "] " s => convexHull 𝕜 s

open scoped Rockafellar

section

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]

namespace Set

/-- Definition 2.3.10 on the chapter surface: every set is contained in its convex hull. -/
theorem subset_conv {s : Set E} : s ⊆ conv[𝕜] s :=
  subset_convexHull 𝕜 s

/-- The convex hull is convex. -/
theorem convex_conv {s : Set E} : Convex 𝕜 (conv[𝕜] s) :=
  convex_convexHull 𝕜 s

/-- Minimality principle in canonical iff form: for convex `t`, containment of `conv[𝕜] s` in `t`
is equivalent to containment of `s` in `t`. -/
theorem conv_subset_iff {s t : Set E} (ht : Convex 𝕜 t) :
    (conv[𝕜] s) ⊆ t ↔ s ⊆ t := by
  simpa using (ht.convexHull_subset_iff (s := s))

/-- Minimality principle in direct implication form: any convex superset of `s` contains
`conv[𝕜] s`. -/
theorem conv_subset {s t : Set E} (hst : s ⊆ t) (ht : Convex 𝕜 t) :
    (conv[𝕜] s) ⊆ t :=
  convexHull_min hst ht

/-- The convex hull as an intersection over the subtype of convex supersets. This keeps the
statement surface free of iterated proof binders. -/
theorem conv_eq_iInter_subtype {s : Set E} :
    (conv[𝕜] s) = ⋂ u : {t : Set E // s ⊆ t ∧ Convex 𝕜 t}, (u : Set E) := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.2 ?_
    intro u
    exact (conv_subset (s := s) (t := (u : Set E)) u.2.1 u.2.2) hx
  · intro hx
    have hx' := Set.mem_iInter.1 hx ⟨conv[𝕜] s, subset_conv, convex_conv⟩
    simpa using hx'

/-- The textbook intersection description of the convex hull. -/
theorem conv_eq_sInter {s : Set E} :
    (conv[𝕜] s) = ⋂₀ {t : Set E | s ⊆ t ∧ Convex 𝕜 t} := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ⋂ u : {t : Set E // s ⊆ t ∧ Convex 𝕜 t}, (u : Set E) := by
      simpa [conv_eq_iInter_subtype] using hx
    refine Set.mem_sInter.2 ?_
    intro t ht
    exact Set.mem_iInter.1 hx' ⟨t, ht⟩
  · intro hx
    have hx' : x ∈ ⋂ u : {t : Set E // s ⊆ t ∧ Convex 𝕜 t}, (u : Set E) := by
      refine Set.mem_iInter.2 ?_
      intro u
      exact Set.mem_sInter.1 hx u u.2
    simpa [conv_eq_iInter_subtype] using hx'

/-- The textbook intersection description of the convex hull, in iterated-`iInter` form. -/
theorem conv_eq_iInter {s : Set E} :
    (conv[𝕜] s) = ⋂ (t : Set E) (_ : s ⊆ t) (_ : Convex 𝕜 t), t := by
  simpa [Set.iInter_subtype, Set.iInter_and] using
    (conv_eq_iInter_subtype (𝕜 := 𝕜) (s := s))

end Set

end

/-! ### Definition_2_3_11 (from Chap01) -/
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

/-! ### Definition_2_3_12 (from Chap01) -/
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

/-! ### Definition_2_3_13 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Definition 2.3.13 names the equal-weight point of an `m`-simplex as its
  midpoint or barycenter.
- `core/canonical`: for a simplex, the owner abstraction is the simplex-specific point
  `Affine.Simplex.centroid`.
- `bridge/view`: the generic finset-level presentation is recovered by
  `Affine.Simplex.univ_centroid_eq`, while the textbook equal-coefficient affine-combination
  formula is recovered from `Affine.Simplex.centroid_eq_affineCombination` together with the
  canonical finset owner lemma `Finset.centroidWeights_eq_const`.
- Domain-style sampling used here: `Affine.Simplex.centroid`,
  `Affine.Simplex.univ_centroid_eq`, `Affine.Simplex.centroid_eq_affineCombination`, and
  `Finset.centroidWeights_eq_const`.
- Primitive data vs derived API: the barycenter itself is the canonical simplex point
  `s.centroid`; the explicit equal-coefficient affine-combination formula and its finset-level
  presentation are derived API and should stay direct recalls rather than parallel local
  definitions.
- Layer target: `core/canonical`; this item is a direct recall of the simplex centroid owner and
  its canonical bridge lemmas, so no local barycenter wrapper or duplicate affine-combination
  owner belongs here.
-/

/- Definition 2.3.13: the midpoint or barycenter of a simplex is its canonical simplex centroid
`Affine.Simplex.centroid`. -/
recall Affine.Simplex.centroid

/- The simplex-specific centroid is exactly the centroid of the full finite vertex family. -/
recall Affine.Simplex.univ_centroid_eq

/- The barycenter is the affine combination of the simplex vertices with the standard centroid
weights. -/
recall Affine.Simplex.centroid_eq_affineCombination

section

universe u v w

open Finset

namespace Affine.Simplex

variable {𝕜 : Type u} {V : Type v} {P : Type w}
variable [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

/-- Simplex-owner bridge to the textbook equal-coefficient surface: the barycenter of an
`n`-simplex is the affine combination of its vertices with uniform coefficient
`(n + 1 : 𝕜)⁻¹`. -/
theorem centroid_eq_affineCombination_uniform {n : ℕ} (s : Simplex 𝕜 P n) :
    s.centroid = affineCombination 𝕜 univ s.points
      (fun _ : Fin (n + 1) => ((n + 1 : 𝕜)⁻¹)) := by
  simpa [Finset.centroidWeights_eq_const, Finset.card_univ, Fintype.card_fin] using
    s.centroid_eq_affineCombination

/-- Finite-index bridge: after reindexing vertices by an arbitrary finite type equivalent to
`Fin (n + 1)`, the simplex barycenter is still the equal-coefficient affine combination. -/
theorem centroid_eq_affineCombination_uniform_comp_equiv {n : ℕ} (s : Simplex 𝕜 P n)
    {ι : Type*} [Fintype ι] (e : ι ≃ Fin (n + 1)) :
    s.centroid = affineCombination 𝕜 univ (s.points ∘ e)
      (fun _ : ι => ((n + 1 : 𝕜)⁻¹)) := by
  calc
    s.centroid = affineCombination 𝕜 (univ : Finset (Fin (n + 1))) s.points
        (fun _ : Fin (n + 1) => ((n + 1 : 𝕜)⁻¹)) := by
      simpa using s.centroid_eq_affineCombination_uniform
    _ = affineCombination 𝕜 (Finset.map e.toEmbedding (univ : Finset ι)) s.points
        (fun _ : Fin (n + 1) => ((n + 1 : 𝕜)⁻¹)) := by
      simp
    _ = affineCombination 𝕜 (univ : Finset ι) (s.points ∘ e)
        ((fun _ : Fin (n + 1) => ((n + 1 : 𝕜)⁻¹)) ∘ e) := by
      simpa using
        (Finset.affineCombination_map (k := 𝕜) (s₂ := (univ : Finset ι))
          (e := e.toEmbedding) (w := fun _ : Fin (n + 1) => ((n + 1 : 𝕜)⁻¹)) (p := s.points))
    _ = affineCombination 𝕜 (univ : Finset ι) (s.points ∘ e)
        (fun _ : ι => ((n + 1 : 𝕜)⁻¹)) := by
      rfl

end Affine.Simplex

end

/-
Abstraction checklist for this item:
- codomain/ambient layer: no ordered-extended codomain owner appears; this item is affine-geometric
  and remains at the simplex owner layer.
- scalar minimization: the reused centroid APIs (`Affine.Simplex.centroid`,
  `Affine.Simplex.centroid_eq_affineCombination`, and `Finset.centroidWeights_eq_const`) are
  already at the canonical `[DivisionRing 𝕜]` layer and do not require specialization to `ℝ`.
- owner correctness: the barycenter owner is the intrinsic simplex owner
  `Affine.Simplex.centroid`; finite-weight formulas are derived bridge theorems.
- topology axis: not applicable; no ambient/intrinsic topology owner is present here.
- notation axis: no new notation is introduced, since the canonical owner names already match the
  source-facing barycenter content without adding parser or wrapper noise.
- finite-index minimization: besides the native `Fin (n + 1)` owner bridge
  `Affine.Simplex.centroid_eq_affineCombination_uniform`, the theorem
  `Affine.Simplex.centroid_eq_affineCombination_uniform_comp_equiv` exposes the same barycenter
  formula after reindexing along an intrinsic finite index type equivalence.
-/

/- For a finite family of vertices, each centroid weight is the reciprocal of the cardinality; in
the simplex case this gives the textbook uniform coefficient `1 / (m + 1)` directly from
`Affine.Simplex.centroid_eq_affineCombination` and `Finset.centroidWeights_eq_const`, without a
parallel local owner declaration. -/
recall Finset.centroidWeights_eq_const
