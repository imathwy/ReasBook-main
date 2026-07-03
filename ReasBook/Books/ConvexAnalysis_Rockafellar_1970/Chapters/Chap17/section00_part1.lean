import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_0_1 (from Chap04) -/
/-
Source/core/bridge triage:
- `source-facing`: Definition 17.0.1 recalls the finite convex-combination notion used in Chapter
  4.
- `core/canonical`: the coefficient owner is `StdSimplex`; the represented point owner is the
  canonical object-prefix declaration `StdSimplex.convexCombination`, and its finite-support
  weighted-sum owner view is the dot-notation surface `w.sum`.
- `bridge/view`: for finite families `w : StdSimplex R ι` and `x : ι → E`, the represented point is
  `(w.map x).convexCombination`. The textbook weighted-sum display is the upstream
  owner-level bridge `StdSimplex.map_convexCombination_eq_sum`, stated on `w.sum` instead of the
  concrete coefficient field `w.weights`.
- Primitive data vs derived API: this file introduces no new primitive data. Nonnegativity and the
  total-mass condition belong to `StdSimplex`; the point and its weighted-sum display are derived
  API.
- Domain-style sampling: the relevant declarations are the earlier project recall
  `Items/Chap01/Definition_2_2_10.lean` together with mathlib's `StdSimplex`,
  `StdSimplex.convexCombination`, and the owner-side weighted-sum bridges
  `StdSimplex.convexCombination_eq_sum` and `StdSimplex.map_convexCombination_eq_sum`.
- Layer target: `core/canonical` recall, with no parallel Chapter 4 wrapper.

Abstraction checks for this item:
- Codomain/ambient concreteness: not applicable. This item is point-valued and introduces no
  ordered-extended codomain owner.
- Scalar/ambient structure: no concrete scalar model is fixed here; all recalled owners remain
  parametric in `R`, index type, and ambient point type.
- Owner choice: keep `StdSimplex` as the primitive coefficient owner; treat weighted-sum formulas
  as bridge views via owner-side theorems.
- Topology language: not applicable; no ambient/intrinsic closure or interior owner appears.
- Owner naming/notation: keep short canonical owners and object-prefix surface
  (`w.sum`, `(w.map x).convexCombination`) rather than concrete coordinate wrappers.
-/

/- Definition 17.0.1 reuses the earlier project recall of the canonical coefficient owner
`StdSimplex`. -/
recall StdSimplex

/- Finite families enter the owner layer via `StdSimplex.map`. -/
recall StdSimplex.map

/- Primitive canonical point owner for simplex coefficients. -/
recall ConvexSpace.convexCombination

/- The represented point owner is the canonical object-prefix declaration
`StdSimplex.convexCombination`. -/
recall StdSimplex.convexCombination

/- Primitive weighted-sum bridge for simplex convex combinations. -/
recall convexCombination_eq_sum

/- The canonical weighted-sum view of simplex convex combinations is the owner-side bridge theorem
`StdSimplex.convexCombination_eq_sum`. -/
recall StdSimplex.convexCombination_eq_sum

/- The textbook weighted-sum presentation is the canonical owner-side bridge theorem, with no
Chapter-4-specific wrapper. -/
recall StdSimplex.map_convexCombination_eq_sum

/-! ### Definition_17_0_2 (from Chap04) -/
open scoped Rockafellar

/- 
Source/core/bridge triage:
- `source-facing`: Definition 17.0.2 recalls the chapter surface `conv[𝕜] s` together with the two
  immediate textbook views used downstream: finite convex-combination membership and minimality
  among convex supersets.
- `core/canonical`: the owner abstraction is `convexHull 𝕜 s`.
- `bridge/view`: the primitive closure-operator package on the chapter surface is recalled through
  `Set.subset_conv`, `Set.convex_conv`, `Set.conv_subset`, and `Set.conv_subset_iff`; the
  definition-level
  intersection characterization is then recalled in primitive binder form `Set.conv_eq_iInter`
  with the textbook set-of-sets surface `Set.conv_eq_sInter` as a display bridge; chapter-surface
  finite-combination membership is recalled first in intrinsic simplex-owner form
  (`Set.mem_conv_iff_exists_stdSimplex`), with direct finite weighted-sum form
  (`Set.mem_conv_iff_exists_fintype`) retained as a source-facing bridge view.
- Domain-style sampling used here: `convexHull`, `Set.mem_conv_iff_exists_stdSimplex`,
  `Set.mem_conv_iff_exists_fintype`, `Set.subset_conv`, `Set.convex_conv`, `Set.conv_subset`,
  `Set.conv_subset_iff`, `Set.conv_eq_iInter`, and `Set.conv_eq_sInter`.
- Primitive data vs derived API: no new primitive data belongs here. The convex hull itself is the
  canonical object `convexHull`; at the chapter level, `Set.subset_conv`, `Set.convex_conv`,
  `Set.conv_subset`, and `Set.conv_subset_iff` are the primitive closure-package bridges, while
  `Set.conv_eq_iInter`, `Set.conv_eq_sInter`, and finite weighted-sum membership are derived
  views reused directly.
- Layer target: source-facing `conv[𝕜]` notation and canonical owner lemmas over the same
  `convexHull` layer, with no parallel Chapter 4 wrapper.

Abstraction checks for this item:
- Codomain concreteness: not applicable. This item is set-valued (`Set E`) and introduces no
  ordered-extended codomain such as `EReal`.
- Scalar/ambient structure: no concrete scalar or model is fixed here; the recalled owner/bridges
  stay parametric in `𝕜` and the ambient space under their canonical mathlib assumptions.
- Owner choice: intrinsic owner is `convexHull`; chapter notation `conv[𝕜] s` is retained only as
  the canonical bridge surface.
- Ambient vs intrinsic topology: not applicable. This item has no `closure`/`interior` or relative
  topology claim.
- Owner naming and notation: keep the short owner `convexHull` and the mathematically primary
  notation `conv[𝕜] s`; use short chapter bridge names (`Set.subset_conv`, `Set.convex_conv`,
  `Set.conv_subset`, `Set.conv_subset_iff`) on the public surface rather than raw owner names.
-/

/- Definition 17.0.2 reuses the canonical convex-hull owner `convexHull`; chapter notation
`conv[𝕜] s` is a definitional bridge to this owner. -/
recall convexHull

/- Primitive closure-package bridge: every set is contained in its chapter-surface convex hull. -/
recall Set.subset_conv

/- Primitive closure-package bridge: the chapter-surface convex hull is convex. -/
recall Set.convex_conv

/- Primitive closure-package bridge: any convex superset of `S` contains `conv[𝕜] S`. -/
recall Set.conv_subset

/- Primitive closure-package bridge in iff form. -/
recall Set.conv_subset_iff

/- Primitive definition-level bridge in binder form: `conv[𝕜] s` is the intersection of all convex
supersets of `s`. -/
recall Set.conv_eq_iInter

/- Textbook set-of-sets display of the same intersection definition. -/
recall Set.conv_eq_sInter

/- Finite convex-combination membership on the chapter surface in intrinsic simplex-owner form. -/
recall Set.mem_conv_iff_exists_stdSimplex

/- Finite convex-combination membership on the chapter surface in direct `Fintype` weighted-sum
bridge form. -/
recall Set.mem_conv_iff_exists_fintype

/-! ### Theorem_17_0_3 (from Chap04) -/
section

open scoped BigOperators
open scoped Rockafellar

universe u v

variable {R : Type u} {E : Type v}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 17.0.3 says that every point of `conv[R] S` can be written as a
  convex combination of points of `S`, with support size at most
  `finrank R (vectorSpan R S) + 1` when `vectorSpan R S` is finite-dimensional.
- `core/canonical`: mathlib's owner theorem
  `eq_pos_convex_span_of_mem_convexHull` already gives a finite affinely independent family in `S`
  with strictly positive convex weights summing to `1`.
- `bridge/view`: the coefficient owner is `StdSimplex R ι`; source-membership is tracked on the
  direct set/function surface by `z : ι → E` together with `Set.range z ⊆ S`.
  `AffineIndependent.card_le_finrank_succ` then bounds the witness cardinality by
  `finrank R (vectorSpan R (Set.range z)) + 1`, and `Submodule.finrank_mono` pushes this bound to
  `finrank R (vectorSpan R S) + 1`.
- Domain-style sampling used here: `StdSimplex`,
  `eq_pos_convex_span_of_mem_convexHull`, and `AffineIndependent.card_le_finrank_succ`.
- Primitive data vs derived API: the primitive coefficient datum is `w : StdSimplex R ι` together
  with point data `z : ι → E` and the source-membership certificate `Set.range z ⊆ S`;
  coefficient nonnegativity and total mass `1` are owner fields of
  `w`, while the weighted-sum display is derived from
  `StdSimplex.map_convexCombination_eq_sum`.
- Layer target: `source-facing`, using chapter notation `conv[R]` and the direct set/function
  surface (`z : ι → E`, `Set.range z ⊆ S`) rather than subtype coercion-heavy output.
- Canonicalization checks (explicit closure):
  1. Codomain concreteness: not applicable; this item is point-valued (`x : E`) and does not use
     an extended scalar codomain owner.
  2. Scalar/ambient minimality: in this Lean/mathlib snapshot, the canonical primitive owner
     layer for ordered-field convexity is the split trio
     `[Field R] [LinearOrder R] [IsStrictOrderedRing R]`. The source-facing theorem matches this
     owner-level minimal interface (no extra ambient hypotheses).
  3. Intrinsic-owner choice: statement uses intrinsic `conv[R] S` and `vectorSpan R S`, not a
     concrete coordinate model.
  4. Topology-language applicability: not applicable; no ambient/interior/closure owner appears.
-/

/-- Theorem 17.0.3: over an ordered field `R`, every point of the convex hull of `S` can be
written as a convex combination of points of `S`, with at most
`Module.finrank R (vectorSpan R S) + 1` points when `vectorSpan R S` is finite-dimensional. -/
theorem exists_convex_combination_card_le_of_mem_conv {S : Set E}
    [FiniteDimensional R (vectorSpan R S)] {x : E}
    (hx : x ∈ conv[R] S) :
    ∃ ι : Type v, ∃ _ : Fintype ι, ∃ w : StdSimplex R ι, ∃ z : ι → E,
      Set.range z ⊆ S ∧
      (w.map z).convexCombination = x ∧
      Fintype.card ι ≤ Module.finrank R (vectorSpan R S) + 1 := by
  classical
  have hx' : x ∈ convexHull R S := by
    simpa using hx
  obtain ⟨ι, _, z, w, hzS, hAff, hwpos, hsum, hcomb⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx'
  let simplex : StdSimplex R ι :=
    { weights := Finsupp.equivFunOnFinite.symm w
      nonneg := fun i ↦ (hwpos i).le
      total := by
        rw [Finsupp.equivFunOnFinite_symm_sum]
        exact hsum }
  have hzSpan : vectorSpan R (Set.range z) ≤ vectorSpan R S :=
    vectorSpan_mono (k := R) hzS
  have hcard_ι : Fintype.card ι ≤ Module.finrank R (vectorSpan R S) + 1 := by
    calc
      Fintype.card ι ≤ Module.finrank R (vectorSpan R (Set.range z)) + 1 :=
        hAff.card_le_finrank_succ
      _ ≤ Module.finrank R (vectorSpan R S) + 1 :=
        Nat.add_le_add_right (Submodule.finrank_mono hzSpan) 1
  refine ⟨ι, inferInstance, simplex, z, hzS, ?_, hcard_ι⟩
  have hsimp (i : ι) : simplex.weights i = w i := by
    simp [simplex]
  have hx_sum : x = ∑ i, simplex.weights i • z i := by
    calc
      x = ∑ i, w i • z i := hcomb.symm
      _ = ∑ i, simplex.weights i • z i := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hsimp]
  have hx_simplex : (simplex.map z).convexCombination = x := by
    calc
      (simplex.map z).convexCombination = simplex.sum (fun i r ↦ r • z i) := by
        exact StdSimplex.map_convexCombination_eq_sum (w := simplex) (z := z)
      _ = ∑ i, simplex.weights i • z i := by
        simpa using
          (Finsupp.sum_fintype (f := simplex.weights) (g := fun i r ↦ r • z i)
            (h := fun _ ↦ by simp))
      _ = x := hx_sum.symm
  exact hx_simplex

end

/-! ### Definition_17_0_4 (from Chap04) -/
universe u v

section

variable {E : Type u}

open Set
open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.0.4 introduces the mixed convex hull generated by a set of points
  `S_0` and a set of directions `S_1`.
- `core/canonical`: the primitive owner abstraction is the smallest set satisfying the three
  source conditions simultaneously: it contains `points`, is convex, and recedes in all vectors
  of `directions`.
- `source-facing owner`: this owner is the direct set-level declaration
  `mixedConvexHull R points directions`, rendered on theorem surfaces by
  `mconv[R](points | directions)`.
- `bridge/view`: the textbook clause "C recedes in all directions in `S_1`" is represented
  canonically as `S_1 ⊆ 0⁺[R] C`.

Domain-style sampling used here:
- mathlib's closure-operator owner `convexHull` (as owner-shape precedent for minimality);
- mathlib's arbitrary-intersection lemma `convex_sInter`;
- the chapter convex-hull bridge notation `conv[R]` and its short owner lemmas
  `Set.subset_conv`, `Set.convex_conv`, and `Set.conv_subset_iff`;
- the project owner `0⁺[R] C` and its bridge `Set.mem_recessionCone_iff`.

Primitive data vs derived API:
- primitive canonical data: the intersection owner over all `C` such that
  `points ⊆ C ∧ Convex R C ∧ directions ⊆ 0⁺[R] C`;
- source-facing owner: `mixedConvexHull`;
- derived API: convexity, point containment, direction containment, minimality, and the
  empty-point-set consequence.
- ambient minimization: the owner only uses the generic convexity and recession APIs already
  available over `R`, so the public surface stays scalar-generic instead of freezing `ℝ` into
  the definition.
-/

section

variable (R : Type v) [Semiring R] [PartialOrder R] [AddCommMonoid E] [SMul R E]

/-- Definition 17.0.4: the mixed convex hull generated by a set of points `points` and a set of
directions `directions` is the smallest convex subset of the ambient space that contains `points`
and recedes in every direction from `directions`. -/
def mixedConvexHull (points directions : Set E) : Set E :=
  sInter {C : Set E | points ⊆ C ∧ Convex R C ∧ directions ⊆ 0⁺[R] C}

/-- Textbook notation for the mixed convex hull generated by points and directions. -/
scoped[Rockafellar] notation3:max "mconv[" R "](" points " | " directions ")" =>
  mixedConvexHull R points directions

/-- The mixed convex hull is convex. -/
-- Proof sketch: each set in the defining intersection is convex, so the intersection is convex.
theorem convex_mixedConvexHull (points directions : Set E) :
    Convex R (mconv[R](points | directions)) := by
  refine convex_sInter ?_
  intro C hC
  exact hC.2.1

/-- The point set lies in its mixed convex hull. -/
-- Proof sketch: every defining set in the intersection contains `points`.
theorem subset_mixedConvexHull (points directions : Set E) :
    points ⊆ mconv[R](points | directions) := by
  intro x hx
  exact Set.mem_sInter.mpr fun C hC ↦ hC.1 hx

/-- Every prescribed direction is a recession direction of the mixed convex hull. -/
-- Proof sketch: every set in the defining intersection contains all directions from `directions`
-- in its recession cone; unpack that condition with `Set.mem_recessionCone_iff`.
theorem directions_subset_recessionCone_mixedConvexHull (points directions : Set E) :
    directions ⊆ 0⁺[R] (mconv[R](points | directions)) := by
  intro y hy
  rw [Set.mem_recessionCone_iff]
  intro x hx a ha
  exact Set.mem_sInter.mpr fun C hC ↦
    (Set.mem_recessionCone_iff.mp (hC.2.2 hy)) x (Set.mem_sInter.mp hx C hC) a ha

/-- The mixed convex hull is the smallest convex set containing the given points and directions. -/
-- Proof sketch: `C` itself is one admissible set in the defining intersection.
theorem mixedConvexHull_min {points directions C : Set E}
    (hC_convex : Convex R C) (hpoints : points ⊆ C)
    (hdirections : directions ⊆ 0⁺[R]C) :
    mconv[R](points | directions) ⊆ C := by
  intro x hx
  exact Set.mem_sInter.mp hx C ⟨hpoints, hC_convex, hdirections⟩

/-- If there are no point generators, the mixed convex hull is empty. -/
-- Proof sketch: the empty set is convex and vacuously has every vector in its recession cone, so
-- `mixedConvexHull_min` gives `mconv[R](∅ | directions) ⊆ ∅`; the reverse inclusion is
-- trivial.
@[simp] theorem mixedConvexHull_empty_points (directions : Set E) :
    mconv[R]((∅ : Set E) | directions) = ∅ := by
  refine subset_antisymm ?_ (Set.empty_subset _)
  exact mixedConvexHull_min R convex_empty (by simp)
    (by simp)

/-- If there are no points, then the mixed convex hull is empty. -/
theorem mixedConvexHull_eq_empty_of_points_eq_empty {points directions : Set E}
    (h_points : points = ∅) :
    mconv[R](points | directions) = ∅ := by
  subst h_points
  exact mixedConvexHull_empty_points (R := R) directions

end

section

variable (R : Type v) [Semiring R] [PartialOrder R] [AddCommMonoid E] [Module R E]

/-- If every direction generator already lies in the recession cone of the point convex hull, then
the mixed convex hull is exactly that convex hull. -/
theorem mixedConvexHull_eq_convexHull_of_directions_subset_recessionCone_convexHull
    {points directions : Set E}
    (hdirections : directions ⊆ 0⁺[R] (conv[R] points)) :
    mconv[R](points | directions) = conv[R] points := by
  refine subset_antisymm ?_ ?_
  · exact mixedConvexHull_min R Set.convex_conv Set.subset_conv hdirections
  · exact Set.conv_subset
      (subset_mixedConvexHull R points directions)
      (convex_mixedConvexHull R points directions)

/-- If all direction generators are zero, then the mixed convex hull reduces to the ordinary
convex hull of the point generators. -/
theorem mixedConvexHull_eq_convexHull_of_directions_subset_zero
    {points directions : Set E} (hdirections : directions ⊆ ({0} : Set E)) :
    mconv[R](points | directions) = conv[R] points := by
  refine mixedConvexHull_eq_convexHull_of_directions_subset_recessionCone_convexHull
      (R := R) ?_
  intro y hy
  have hy0 : y = 0 := by simpa using hdirections hy
  rw [hy0, Set.mem_recessionCone_iff]
  intro x hx a ha
  simpa using hx

/-- With no direction generators, the mixed convex hull is the ordinary convex hull. -/
@[simp] theorem mixedConvexHull_empty_directions (points : Set E) :
    mconv[R](points | (∅ : Set E)) = conv[R] points := by
  exact mixedConvexHull_eq_convexHull_of_directions_subset_recessionCone_convexHull
    (R := R) (by simp)

end

end

/-! ### Definition_17_0_5 (from Chap04) -/
open scoped Pointwise Rockafellar

universe u v

/- 
Source/core/bridge triage:
- `source-facing`: the item introduces the set `ray S_1` determined by a set of directions.
- `core/canonical`: mathlib's owner abstractions here are `Module.Ray R E` for directions,
  `convexHull R` for convex hulls, and `PointedCone.hull R` for convex cones generated by a set.
- `bridge/view`: the source cone over directions is expressed directly on the existing chapter
  generated-cone owner surface `cone[R] (ray S1)`.

Domain-style sampling used here:
- `rayOfNeZero R`;
- `SameRay.sameRay_nonneg_smul_left`;
- `PointedCone.hull`;
- `PointedCone.hull_eq_convexHull_nonnegativeRay`;
- `PointedCone.subset_hull`.

Primitive data vs derived API:
- primitive source-facing data: the ray set `ray S1`;
- derived API: the nonnegative-ray stability of `ray S1`, which is the exact input needed
  to reuse the upstream owner theorem `PointedCone.hull_eq_convexHull_nonnegativeRay`, together
  with the canonical bridge theorem `cone_ray_eq_convexHull` below;
- assumptions policy: this file keeps the canonical assumptions required by the two primitive
  upstream owners used here: `Module.Ray` needs `IsStrictOrderedRing`, and
  `PointedCone.hull_eq_convexHull_nonnegativeRay` contributes `Semifield` and `PosMulReflectLT` in
  the final bridge theorem.
-/

section

variable {R : Type v} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- The set `ray S_1`: the origin together with all nonzero vectors whose direction lies in
`S1`. -/
def rayOfDirections (S1 : Set (Module.Ray R E)) : Set E :=
  {x | x = 0 ∨ ∃ hx : x ≠ 0, rayOfNeZero R x hx ∈ S1}

/-- Textbook notation for the set generated by the directions in `S1`. -/
scoped[Rockafellar] prefix:max "ray " => rayOfDirections

-- Proof sketch: unfold `rayOfDirections`; membership is exactly the defining disjunction saying
-- that the vector is either `0` or has ray class in `S1`.
/-- Membership in `ray S_1` is equivalent to being zero or having direction in `S1`. -/
@[simp] theorem mem_ray_iff (S1 : Set (Module.Ray R E)) (x : E) :
    x ∈ ray S1 ↔ x = 0 ∨ ∃ hx : x ≠ 0, rayOfNeZero R x hx ∈ S1 := Iff.rfl

/-- The origin always belongs to `ray S_1`. -/
@[simp] theorem zero_mem_ray (S1 : Set (Module.Ray R E)) : (0 : E) ∈ ray S1 :=
  (mem_ray_iff (S1 := S1) (x := 0)).2 (Or.inl rfl)

/-- The source-facing ray set is never empty. -/
theorem ray_nonempty (S1 : Set (Module.Ray R E)) : (ray S1).Nonempty :=
  ⟨0, zero_mem_ray (S1 := S1)⟩

/-- The origin half-line determined by a single direction ray. -/
def originRay (r : Module.Ray R E) : Set E :=
  ray ({r} : Set (Module.Ray R E))

/-- Membership in `originRay r` means either being `0` or being a nonzero vector whose direction is
`r`. -/
@[simp] theorem mem_originRay_iff {r : Module.Ray R E} {x : E} :
    x ∈ originRay r ↔ x = 0 ∨ ∃ hx : x ≠ 0, rayOfNeZero R x hx = r := by
  simp [originRay, mem_ray_iff]

/-- The direction set generated by no rays is exactly `{0}`. -/
@[simp] theorem ray_empty : ray (∅ : Set (Module.Ray R E)) = ({0} : Set E) := by
  ext x
  constructor
  · intro hx
    rcases (mem_ray_iff (S1 := (∅ : Set (Module.Ray R E))) x).1 hx with
      rfl | ⟨_, hx⟩
    · simp
    · exact (hx.elim)
  · rintro rfl
    exact zero_mem_ray (S1 := (∅ : Set (Module.Ray R E)))

end

section

variable {R : Type v} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

local notation "R≥0" => Set.Ici (0 : R)

/-- The source-facing set `ray S_1` is already closed under nonnegative scalar multiplication. -/
private theorem nonnegativeRay_ray (S1 : Set (Module.Ray R E)) :
    R≥0 • ray S1 = ray S1 := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rcases Set.mem_smul.mp hx with ⟨a, ha, y, hy, rfl⟩
    rcases hy with rfl | ⟨hy0, hyS1⟩
    · left
      simp
    · by_cases hxy : a • y = (0 : E)
      · left
        exact hxy
      · right
        refine ⟨hxy, ?_⟩
        rw [(ray_eq_iff hxy hy0).2 (SameRay.sameRay_nonneg_smul_left y ha)]
        exact hyS1
  · intro x hx
    exact Set.mem_smul.mpr ⟨1, le_of_lt (zero_lt_one : (0 : R) < 1), x, hx, by simp⟩
end

section

variable {R : Type v} [Semifield R] [PartialOrder R] [IsStrictOrderedRing R] [PosMulReflectLT R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- The cone generated by the ray set `ray S₁` is exactly its convex hull. This is the canonical
owner bridge specialized from Corollary 2.6.11 using `nonnegativeRay_ray`. -/
theorem cone_ray_eq_convexHull (S1 : Set (Module.Ray R E)) :
    (cone[R] (ray S1) : Set E) = convexHull R (ray S1) := by
  rw [PointedCone.hull_eq_convexHull_nonnegativeRay (ray S1) (ray_nonempty S1), nonnegativeRay_ray]

end

/-! ### Proposition_17_0_6 (from Chap04) -/
universe u v

open scoped Pointwise
open scoped Rockafellar

section

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 17.0.6 represents the mixed convex hull generated by a set of
  points `S₀` and a set of directions `S₁` as the convex hull of `S₀ + ray S₁`, and then as
  `conv S₀ + cone[R] (ray S₁)`.
- `core/canonical`: the owner abstractions already present in the project are `mixedConvexHull`,
  `convexHull R`, and the pointwise Minkowski sum of sets.
- `bridge/view`: the directions `S₁` live in `Module.Ray R E`, so the source-facing set of
  admissible recession vectors is rendered by `ray S₁`, while the generated cone is the
  canonical chapter owner `cone[R] (ray S₁)`.

Domain-style sampling used here:
- the project declarations `mixedConvexHull` and `rayOfDirections`;
- the owner bridge theorem `cone_ray_eq_convexHull`;
- mathlib's set-level Minkowski sum under `open scoped Pointwise`;
- mathlib's convex-hull compatibility theorem `convexHull_add`.

Primitive data vs derived API:
- primitive data: the point set and the set of directions;
- derived API: the two representation equalities for the mixed convex hull, stated with the
  canonical generated-cone owner `cone[R] (ray S₁)`.

Layer target: `bridge/view`.
-/

variable {R : Type v} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- Intrinsic owner form of Proposition 17.0.6 (2): for any direction set `directions : Set E`,
the mixed convex hull generated by `points` and `directions` is the Minkowski sum of the ordinary
convex hull of `points` with the cone generated by `directions`. -/
-- Proof sketch: the right-hand side is convex, contains `points`, and every vector in
-- `directions` is a recession direction because the second summand is the generated cone
-- `cone[R] directions`. Minimality of `mixedConvexHull` gives one inclusion. For the
-- reverse inclusion, `convexHull R points` lies in the mixed hull by convexity, while
-- `cone[R] directions`
-- lies in its recession cone because the recession cone is
-- convex and already contains `directions`; translating points of the mixed hull by such
-- recession vectors stays inside the mixed hull.
theorem mixedConvexHull_eq_convexHull_add_cone
    (points directions : Set E) :
    mconv[R](points | directions) =
      (conv[R] points) + cone[R] directions := by
  refine subset_antisymm ?_ ?_
  · refine mixedConvexHull_min R ?_ ?_ ?_
    · simpa using
        (convex_convexHull R points).add (cone[R] directions).convex
    · intro x hx
      exact Set.mem_add.mpr ⟨x, subset_convexHull R points hx, 0,
        (cone[R] directions).zero_mem, by simp⟩
    · intro y hy
      rw [Set.mem_recessionCone_iff]
      intro x hx a ha
      rcases Set.mem_add.mp hx with ⟨u, hu, v, hv, rfl⟩
      exact Set.mem_add.mpr
        ⟨u, hu, v + a • y,
          (cone[R] directions).add_mem hv <|
            (cone[R] directions).smul_mem ha <|
              PointedCone.subset_hull hy,
          by simp [add_assoc]⟩
  · have hpoints :
        (conv[R] points) ⊆ mconv[R](points | directions) :=
      convexHull_min (subset_mixedConvexHull R points directions)
        (convex_mixedConvexHull R points directions)
    have hdirections :
        (cone[R] directions : Set E) ⊆
          0⁺[R] (mconv[R](points | directions)) := by
      let C : Set E := mconv[R](points | directions)
      let Krec : PointedCone R E :=
        PointedCone.ofConeComb (C := 0⁺[R] C)
          ⟨0, zero_mem_recessionCone C⟩ (by
            intro y hy z hz a ha b hb
            rw [Set.mem_recessionCone_iff] at hy hz ⊢
            intro x hx t ht
            have hxy : x + (t * a) • y ∈ C := hy x hx (t * a) (mul_nonneg ht ha)
            have hxyz : x + (t * a) • y + (t * b) • z ∈ C :=
              hz (x + (t * a) • y) hxy (t * b) (mul_nonneg ht hb)
            simpa [smul_add, smul_smul, mul_assoc, add_assoc, add_left_comm, add_comm] using hxyz)
      have hcone_le : (cone[R] directions : PointedCone R E) ≤ Krec := by
        exact Submodule.span_le.mpr <| fun z hz =>
          directions_subset_recessionCone_mixedConvexHull R points directions hz
      intro y hy
      exact hcone_le hy
    intro x hx
    rcases Set.mem_add.mp hx with ⟨u, hu, v, hv, rfl⟩
    simpa using (Set.mem_recessionCone_iff.mp (hdirections hv)) u (hpoints hu) 1 zero_le_one

end

section

variable {R : Type v} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {E : Type u} [AddCommGroup E] [Module R E]

/-- Intrinsic bridge for Proposition 17.0.6 (1): if the generated cone of `directions` coincides
with their convex hull, then the mixed convex hull generated by `points` and `directions` is the
convex hull of `points + directions`. -/
-- Proof sketch: rewrite the mixed convex hull by Proposition 17.0.6 (2), then use the supplied
-- bridge `hcone` and `convexHull_add`.
theorem mixedConvexHull_eq_convexHull_add_of_cone_eq_convexHull
    (points directions : Set E)
    (hcone : (cone[R] directions : Set E) = conv[R] directions) :
    mconv[R](points | directions) =
      conv[R] (points + directions) := by
  calc
    mconv[R](points | directions) =
        (conv[R] points) + cone[R] directions := by
      simpa using mixedConvexHull_eq_convexHull_add_cone
        (R := R) (points := points) (directions := directions)
    _ = (conv[R] points) + conv[R] directions := by rw [hcone]
    _ = conv[R] (points + directions) := by
      simpa using (convexHull_add (R := R) points directions).symm

/-- Proposition 17.0.6 (1), source-facing ray specialization: if directions are provided as rays,
the mixed convex hull is the convex hull of `points + ray directions`. -/
theorem mixedConvexHull_eq_convexHull_add_ray
    (points : Set E) (directions : Set (Module.Ray R E)) :
    mconv[R](points | ray directions) =
      conv[R] (points + ray directions) := by
  refine mixedConvexHull_eq_convexHull_add_of_cone_eq_convexHull
      (R := R) points (ray directions) ?_
  simpa using (cone_ray_eq_convexHull directions)

end

/-! ### Definition_17_0_7 (from Chap04) -/
universe u v

open scoped BigOperators Rockafellar

section

variable {R : Type v} [AddCommMonoid R] [One R] [Preorder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

namespace Set

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.0.7 introduces the predicate that a vector is a mixed convex
  combination drawn from a mixed set with a point part `S₀` and a direction part `S₁`.
- `core/canonical`: the owner abstraction for directions in this chapter is `Module.Ray R E`.
- `bridge/view`: this file keeps both:
  (i) the primitive finite certificate with explicit finite index types over an arbitrary
      direction-carrier set of vectors, and
  (ii) the source-facing ray-indexed owner obtained by specializing that carrier to
      `ray directions`.
- Primitive data vs derived API:
  - primitive data: finite point/direction index types, corresponding point/direction families,
    the point simplex coefficients, and nonnegative direction coefficients;
- derived owner surfaces:
  - `Set.IsMixedConvexCombinationIn` on an arbitrary direction carrier `directionCarrier : Set E`;
  - specialization to direction vectors in `ray directions`, yielding
    `Set.IsMixedConvexCombination`.

Domain-style sampling used here:
- `Module.Ray R E` as the canonical owner for directions;
- `ray`;
- finite sums over arbitrary finite index types in mathlib's `BigOperators` API.

The primitive certificate itself does not use any ray-specific construction; it only needs
`[AddCommMonoid R] [One R] [Preorder R]` and `[SMul R E]`.
-/

/-- Primitive finite mixed-combination certificate on an arbitrary direction-carrier set of
vectors. This is the algebraic core used by Definition 17.0.7 before specializing directions to
`ray directions`. -/
private def IsMixedConvexCombinationCertificate (points directionCarrier : Set E)
    (x : E) (ι κ : Type*) [Fintype ι] [Fintype κ] : Prop :=
  ∃ pointVec : ι → points, ∃ dirVec : κ → directionCarrier,
    ∃ pointCoeff : StdSimplex R ι, ∃ dirCoeff : κ → R,
      x = (∑ i, pointCoeff.weights i • (pointVec i : E)) +
            (∑ j, dirCoeff j • (dirVec j : E)) ∧
      (∀ j, 0 ≤ dirCoeff j)

/-- Definition 17.0.7 core form: a mixed convex combination with fixed finite point/direction
indices over an arbitrary direction-carrier set of vectors. This primitive owner does not depend
on the ray specialization. -/
def IsMixedConvexCombinationWith
    (R : Type v) [AddCommMonoid R] [One R] [Preorder R]
    {E : Type u} [AddCommMonoid E] [SMul R E]
    (points directionCarrier : Set E)
    (x : E) (ι κ : Type*) [Fintype ι] [Fintype κ] : Prop :=
  IsMixedConvexCombinationCertificate (R := R) (E := E) points directionCarrier x ι κ

/-- Owner-level existential mixed-combination predicate on an arbitrary direction-carrier set of
vectors. -/
def IsMixedConvexCombinationIn
    (R : Type v) [AddCommMonoid R] [One R] [Preorder R]
    {E : Type u} [AddCommMonoid E] [SMul R E]
    (points directionCarrier : Set E)
    (x : E) : Prop :=
  ∃ (ι κ : Type (max u v)) (_ : Fintype ι) (_ : Fintype κ),
    IsMixedConvexCombinationWith R points directionCarrier x ι κ

end Set

end

section

variable {R : Type v} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

namespace Set

/-- Definition 17.0.7 on the source-facing ray-owner surface: `x` is a mixed convex combination
of `points` and `directions` iff it is a mixed convex combination on the induced vector-carrier
set `ray directions`. -/
def IsMixedConvexCombination (points : Set E) (directions : Set (Module.Ray R E))
    (x : E) : Prop :=
  IsMixedConvexCombinationIn R points (ray directions) x

end Set

end

/-! ### Proposition_17_0_8 (from Chap04) -/
universe u v

open Set
open scoped Rockafellar

section

-- Intrinsic owner layer: this does not depend on rays, only on the mixed-hull owner and the
-- carrier-level mixed-combination owner.
variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

/-!
Source/core/bridge triage:

- `source-facing`: the mixed-combination witness predicate is
  `points.IsMixedConvexCombination directions x`.
- `core/canonical`: the owner abstraction is the mixed hull
  `mixedConvexHull R points directionCarrier` together with the owner-level mixed-combination
  predicate `Set.IsMixedConvexCombinationIn R points directionCarrier x`.
- `bridge/view`: the source-facing ray statement is recovered by specializing
  `directionCarrier := ray directions`.

Domain-style sampling used here:
- the project owners `mixedConvexHull`, `rayOfDirections`, and
  `IsMixedConvexCombinationIn`;
- the source-facing bridge owner `IsMixedConvexCombination`;
- the direction owner `Module.Ray`, rendered on theorem surfaces via `ray`.

Primitive data vs derived API:
- primitive data: the point set, an arbitrary direction-carrier set of vectors, and `x`;
- derived API: the source-facing ray-indexed existential owner predicate from Definition 17.0.7
  (with finite witness data internally packaged by that owner), recovered as a bridge.
-/

/-- Proposition 17.0.8, owner-level core form: membership in a mixed convex hull over an arbitrary
direction-carrier set of vectors is equivalent to admitting a finite mixed-combination
certificate over that same carrier. -/
theorem mem_mixedConvexHull_iff_isMixedConvexCombinationIn
    (points directionCarrier : Set E) (x : E) :
    x ∈ mconv[R](points | directionCarrier) ↔
      Set.IsMixedConvexCombinationIn R points directionCarrier x := sorry

/-- Owner-level set form of Proposition 17.0.8 on an arbitrary vector direction carrier. -/
theorem mixedConvexHull_eq_setOf_isMixedConvexCombinationIn
    (points directionCarrier : Set E) :
    mconv[R](points | directionCarrier) =
      {x : E | Set.IsMixedConvexCombinationIn R points directionCarrier x} := by
  ext x
  simpa using
    (mem_mixedConvexHull_iff_isMixedConvexCombinationIn points directionCarrier x)

end

section

-- Source-facing ray bridge layer.
variable {R : Type v} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- Proposition 17.0.8, source-facing ray form: membership in the mixed convex hull generated by
`points` and ray directions `directions` is equivalent to the chapter mixed-combination predicate
of Definition 17.0.7. -/
theorem mem_mixedConvexHull_iff_isMixedConvexCombination
    (points : Set E) (directions : Set (Module.Ray R E)) (x : E) :
    x ∈ mconv[R](points | ray directions) ↔
      points.IsMixedConvexCombination directions x := by
  simpa [Set.IsMixedConvexCombination] using
    (mem_mixedConvexHull_iff_isMixedConvexCombinationIn
      (points := points) (directionCarrier := ray directions) x)

/-- Source-facing ray set form of Proposition 17.0.8. -/
theorem mixedConvexHull_eq_setOf_isMixedConvexCombination
    (points : Set E) (directions : Set (Module.Ray R E)) :
    mconv[R](points | ray directions) =
      {x : E | points.IsMixedConvexCombination directions x} := by
  ext x
  simpa using
    (mem_mixedConvexHull_iff_isMixedConvexCombination points directions x)

end

/-! ### Definition_17_0_9 (from Chap04) -/
noncomputable section

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.0.9 introduces the affine hyperplane `H`, the lifted generating
  set `S'`, while the cone `K` generated by `S'` is used through the canonical pointed-cone owner
  `cone[R] (liftingSet R S₀ S₁')`.
  `unitHeightSet := {p : R × E | p.1 = 1}`, which only depends on first-coordinate data; the
  chapter homogenization owner remains `homogenizationSet`; the affine-bridge owner is the short
  `unitHeightHyperplane`.
- `bridge/view`: `unitLift_eq_unitHeightSet_inter_homogenizationSet` is the primitive bridge at
  weak scalar/action assumptions, while
  `unitHeightSet_eq_unitHeightHyperplane` and
  `unitLift_eq_hyperplane_inter_homogenizationSet` provide the affine-hyperplane view through
  `unitHeightHyperplane`.

Domain-style sampling used here:
- `homogenizationSet` and `mem_unitSection_homogenizationSet_iff`;
- `homogenizationSet_eq_pointedConeHull`;
- `PointedCone.hull`;
- `linearHyperplane`, `mem_linearHyperplane_iff`, and the short bridge owner
  `unitHeightHyperplane`.

Primitive data vs derived API:
- primitive source-facing data: `liftingSet`, `zeroLift`, and `unitHeightSet`;
- derived API: `mem_liftingSet_iff`, `unitLift_eq_unitHeightSet_inter_homogenizationSet`,
  and `liftingSet_eq_unitHeightSet_inter_homogenizationSet_union_zeroLift`;
  affine-hyperplane theorems are explicit bridge-view corollaries.

Layer target: `source-facing`.
-/

section

universe u

variable (R : Type*) {E : Type u} [Zero R]

/-- The canonical height-`0` lift `{(0, x) | x ∈ S}` of a set `S`. -/
def zeroLift (S : Set E) : Set (R × E) :=
  Prod.mk (0 : R) '' S

scoped[Rockafellar] notation "L₀[" R " | " C "]" => zeroLift R C

@[simp] theorem mem_zeroLift_iff (S : Set E) (x : E) :
    ((0 : R), x) ∈ L₀[R | S] ↔ x ∈ S := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    cases hxy
    simpa using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable [One R]

/-- The lifted generating set `S'` obtained from `S₀` and the auxiliary set `S₁'`. -/
def liftingSet (S₀ S₁' : Set E) : Set (R × E) :=
  L[R | S₀] ∪ L₀[R | S₁']

/-- Membership in `liftingSet S₀ S₁'` means being either a height-`1` lift of a point of `S₀`
or a height-`0` lift of a point of `S₁'`. -/
@[simp] theorem mem_liftingSet_iff {S₀ S₁' : Set E} {p : R × E} :
    p ∈ liftingSet R S₀ S₁' ↔ (p.1 = 1 ∧ p.2 ∈ S₀) ∨ (p.1 = 0 ∧ p.2 ∈ S₁') := by
  rcases p with ⟨a, x⟩
  constructor
  · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩)
    · cases hxy
      exact Or.inl ⟨rfl, hy⟩
    · cases hxy
      exact Or.inr ⟨rfl, hy⟩
  · rintro (⟨ha, hx⟩ | ⟨ha, hx⟩)
    · left
      change a = 1 at ha
      exact ⟨x, hx, by ext <;> simp [ha]⟩
    · right
      change a = 0 at ha
      exact ⟨x, hx, by ext <;> simp [ha]⟩

end

section

universe u

variable (R : Type*) {E : Type u} [One R]

/-- The intrinsic height-`1` slice in the product space `R × E`. -/
def unitHeightSet : Set (R × E) := {p | p.1 = (1 : R)}

@[simp] theorem mem_unitHeightSet_iff {p : R × E} :
    p ∈ unitHeightSet (R := R) ↔ p.1 = (1 : R) :=
  Iff.rfl

end

section

universe u

variable (R : Type*) {E : Type u}
variable [Monoid R] [Zero R] [LE R] [ZeroLEOneClass R] [MulAction R E]

/-- The height-`1` lift of `S₀` is exactly the intersection of the chapter homogenization owner
`homogenizationSet R S₀` with the intrinsic first-coordinate slice `p.1 = 1`. -/
theorem unitLift_eq_unitHeightSet_inter_homogenizationSet (S₀ : Set E) :
    L[R | S₀] =
      unitHeightSet (R := R) ∩ K[R | S₀] := by
  ext p
  rcases p with ⟨a, x⟩
  constructor
  · rintro ⟨y, hy, hxy⟩
    cases hxy
    constructor
    · simp
    · simpa using (mem_homogenizationSet_one_iff (R := R) (C := S₀) (x := x)).2 hy
  · rintro ⟨ha, hpK⟩
    have ha : a = 1 := by
      simpa [unitHeightSet] using ha
    have hx : x ∈ S₀ := (mem_homogenizationSet_one_iff (R := R) (C := S₀) (x := x)).mp <| by
      simpa [ha] using hpK
    exact ⟨x, hx, by ext <;> simp [ha]⟩

/-- The source-facing lifted set `S'` reuses the chapter homogenization owner on its height-`1`
part; the only extra primitive data are the height-`0` directions from `S₁'`. -/
theorem liftingSet_eq_unitHeightSet_inter_homogenizationSet_union_zeroLift
    (S₀ S₁' : Set E) :
    liftingSet R S₀ S₁' =
      ((unitHeightSet (R := R) ∩ K[R | S₀]) ∪
        L₀[R | S₁']) := by
  rw [liftingSet, unitLift_eq_unitHeightSet_inter_homogenizationSet]

end

section

universe u

variable (R : Type*) (E : Type u)
variable [Ring R] [AddCommGroup E] [Module R E]

/-- The affine hyperplane in `R × E` cut out by the first-coordinate equation `a = 1`. -/
abbrev unitHeightHyperplane : AffineSubspace R (R × E) :=
  linearHyperplane (LinearMap.fst R R E) (1 : R)

/-- Membership in `unitHeightHyperplane` is the first-coordinate equation `a = 1`. -/
@[simp] theorem mem_unitHeightHyperplane_iff {p : R × E} :
    p ∈ unitHeightHyperplane R E ↔ p.1 = (1 : R) := by
  simp [unitHeightHyperplane, mem_linearHyperplane_iff]

/-- Bridge theorem: the intrinsic height-`1` slice is the affine hyperplane cut out by the first
coordinate equation. -/
theorem unitHeightSet_eq_unitHeightHyperplane :
    unitHeightSet (R := R) = (unitHeightHyperplane R E : Set (R × E)) := by
  ext p
  simp [unitHeightSet]

section

variable [LE R] [ZeroLEOneClass R]

/-- Affine-hyperplane bridge view of `unitLift_eq_unitHeightSet_inter_homogenizationSet`. -/
theorem unitLift_eq_hyperplane_inter_homogenizationSet (S₀ : Set E) :
    L[R | S₀] =
      ((unitHeightHyperplane R E : Set (R × E)) ∩ K[R | S₀]) := by
  rw [unitLift_eq_unitHeightSet_inter_homogenizationSet (R := R) S₀,
    unitHeightSet_eq_unitHeightHyperplane (R := R) (E := E)]

/-- Affine-hyperplane bridge view of
`liftingSet_eq_unitHeightSet_inter_homogenizationSet_union_zeroLift`. -/
theorem liftingSet_eq_hyperplane_inter_homogenizationSet_union_zeroLift
    (S₀ S₁' : Set E) :
    liftingSet R S₀ S₁' =
      (((unitHeightHyperplane R E : Set (R × E)) ∩ K[R | S₀]) ∪
        L₀[R | S₁']) := by
  rw [liftingSet_eq_unitHeightSet_inter_homogenizationSet_union_zeroLift (R := R) S₀ S₁',
    unitHeightSet_eq_unitHeightHyperplane (R := R) (E := E)]

end

end

/-! ### Proposition_17_0_10 (from Chap04) -/
open Set
open scoped Pointwise Rockafellar

section

universe u v

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 17.0.10 identifies the mixed convex hull generated by `points` and
  directions with the height-`1` section of the cone generated by the lifted set.
- `core/canonical`: the owner abstractions are `mconv[R](points | directions)`, the Chapter 1
  height-one owners `U[R | S]` and `unitLift R`, the lifted generating set
  `liftingSet R points directions`, and its generated cone owner
  `cone[R] (liftingSet R points directions)`.
- `bridge/view`: the intrinsic owner-level equality is the unit-section identity in `E`; the
  product-space slice equality with `unitHeightSet` is a derived bridge.

Domain-style sampling used here:
- `mixedConvexHull`;
- `mixedConvexHull_min`;
- `mem_unitSection_pointedConeHull_lift_iff`;
- `Set.mem_recessionCone_iff`;
- `PointedCone.ofConeComb`, `PointedCone.hull`, and `cone[R]`.

Primitive data vs derived API:
- primitive source data: the point set `points`, a direction-carrier set `directions`, and the
  lifted generating set `liftingSet R points directions`;
- derived bridge API: the unit-section membership equivalence, the resulting owner equality
  `mconv = U[R | cone[R] (liftingSet R ...)]`, and the product-space slice equality for
  `unitLift`.

Layer target: `bridge/view`.
-/

variable {R : Type v} [Semifield R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

omit [PosMulReflectLT R] in
private theorem convex_unitSection_liftingSetCone
    (points directions : Set E) :
    Convex R (U[R | cone[R] (liftingSet R points directions)] : Set E) := by
  intro x hx y hy a b ha hb hab
  rw [mem_unitSection_iff] at hx hy ⊢
  have hxy :
      a • ((1 : R), x) + b • ((1 : R), y) ∈
        cone[R] (liftingSet R points directions) :=
    (cone[R] (liftingSet R points directions)).convex hx hy ha hb hab
  simpa [Prod.smul_mk, hab, add_assoc, add_left_comm, add_comm] using hxy

omit [PosMulReflectLT R] in
private theorem directions_subset_recession_unitSection_liftingSetCone
    (points directions : Set E) :
    directions ⊆ 0⁺[R] (U[R | cone[R] (liftingSet R points directions)] : Set E) := by
  intro y hy
  rw [Set.mem_recessionCone_iff]
  intro x hx a ha
  rw [mem_unitSection_iff] at hx ⊢
  have hyLift :
      ((0 : R), y) ∈
        cone[R] (liftingSet R points directions) :=
    PointedCone.subset_hull <| by
      rw [mem_liftingSet_iff]
      exact Or.inr ⟨rfl, hy⟩
  have hsum :
      ((1 : R), x) + a • ((0 : R), y) ∈
        cone[R] (liftingSet R points directions) :=
    (cone[R] (liftingSet R points directions)).add_mem hx <|
      (cone[R] (liftingSet R points directions)).smul_mem ha hyLift
  simpa [Prod.smul_mk, add_assoc, add_left_comm, add_comm] using hsum

omit [PosMulReflectLT R] in
private theorem mixedConvexHull_subset_unitSection_liftingSetCone
    (points directions : Set E) :
    mconv[R](points | directions) ⊆
      (U[R | cone[R] (liftingSet R points directions)] : Set E) := by
  refine mixedConvexHull_min R
    (convex_unitSection_liftingSetCone points directions) ?_
    (directions_subset_recession_unitSection_liftingSetCone points directions)
  intro x hx
  rw [mem_unitSection_iff]
  exact PointedCone.subset_hull <| by
    rw [mem_liftingSet_iff]
    exact Or.inl ⟨rfl, hx⟩

private theorem mem_liftingSetCone_one_mem_of_subset_recession
    (points directions : Set E) {C : Set E} (hC_convex : Convex R C)
    (hpoints : points ⊆ C) (hdirections : directions ⊆ 0⁺[R]C) {x : E}
    (hx : ((1 : R), x) ∈ cone[R] (liftingSet R points directions)) :
    x ∈ C := by
  let liftedPointCone : PointedCone R (R × E) := cone[R] (unitLift R C)
  let zeroLiftRecessionCone : PointedCone R (R × E) :=
    PointedCone.ofConeComb (L₀[R | 0⁺[R] C])
      ⟨(0, 0), ⟨0, zero_mem_recessionCone C, rfl⟩⟩
      fun p hp q hq a ha b hb ↦ by
        rcases hp with ⟨y, hy, rfl⟩
        rcases hq with ⟨z, hz, rfl⟩
        have hsum :
            a • y + b • z ∈ 0⁺[R] C := by
          rw [Set.mem_recessionCone_iff]
          intro x hx c hc
          have hxy : x + (c * a) • y ∈ C :=
            (Set.mem_recessionCone_iff.mp hy) x hx (c * a) (mul_nonneg hc ha)
          have hxyz : x + (c * a) • y + (c * b) • z ∈ C :=
            (Set.mem_recessionCone_iff.mp hz) (x + (c * a) • y) hxy (c * b) (mul_nonneg hc hb)
          simpa [smul_add, smul_smul, mul_assoc, add_assoc] using hxyz
        refine ⟨a • y + b • z, hsum, ?_⟩
        simp [Prod.smul_mk]
  have hlift :
      liftingSet R points directions ⊆
        ((liftedPointCone ⊔ zeroLiftRecessionCone : PointedCone R (R × E)) : Set (R × E)) := by
    intro p hp
    rcases p with ⟨a, x⟩
    rw [mem_liftingSet_iff] at hp
    rcases hp with ⟨ha, hx⟩ | ⟨ha, hx⟩
    · have hxC : x ∈ C := hpoints hx
      change a = (1 : R) at ha
      have hmem : ((1 : R), x) ∈ (liftedPointCone : Set (R × E)) :=
        PointedCone.subset_hull ⟨x, hxC, rfl⟩
      simpa [ha] using
        (show ((1 : R), x) ∈
            ((liftedPointCone ⊔ zeroLiftRecessionCone : PointedCone R (R × E)) : Set (R × E))
          from
            (show liftedPointCone ≤ liftedPointCone ⊔ zeroLiftRecessionCone from le_sup_left) hmem)
    · have hmem : ((0 : R), x) ∈ (zeroLiftRecessionCone : Set (R × E)) :=
        ⟨x, hdirections hx, rfl⟩
      change a = (0 : R) at ha
      simpa [ha] using
        (show ((0 : R), x) ∈
            ((liftedPointCone ⊔ zeroLiftRecessionCone : PointedCone R (R × E)) : Set (R × E))
          from
            (show zeroLiftRecessionCone ≤ liftedPointCone ⊔ zeroLiftRecessionCone from
              le_sup_right) hmem)
  have hHull_le :
      (cone[R] (liftingSet R points directions) : PointedCone R (R × E)) ≤
        liftedPointCone ⊔ zeroLiftRecessionCone :=
    Submodule.span_le.mpr hlift
  have hpair :
      ((1 : R), x) ∈
        ((liftedPointCone ⊔ zeroLiftRecessionCone : PointedCone R (R × E)) : Set (R × E)) := by
    exact hHull_le hx
  change ((1 : R), x) ∈ (liftedPointCone ⊔ zeroLiftRecessionCone : PointedCone R (R × E)) at hpair
  rw [Submodule.mem_sup] at hpair
  rcases hpair with ⟨p, hp, q, hq, hpq⟩
  rcases hq with ⟨y, hy, rfl⟩
  rcases p with ⟨a, z⟩
  have hp_fst : a = (1 : R) := by
    simpa using congrArg Prod.fst hpq
  have hpLift : ((1 : R), z) ∈ (liftedPointCone : Set (R × E)) := by
    simpa [hp_fst] using hp
  have hp_section : z ∈ U[R | liftedPointCone] := by
    simpa [mem_unitSection_iff] using hpLift
  have hpC : z ∈ C :=
    (mem_unitSection_pointedConeHull_lift_iff C hC_convex z).1 hp_section
  have hsum : z + y ∈ C := by
    simpa using (Set.mem_recessionCone_iff.mp hy) z hpC 1 zero_le_one
  have hsnd : z + y = x := by
    simpa using congrArg Prod.snd hpq
  simpa [hsnd] using hsum

/-- Membership in the height-`1` section of the cone generated by the lifted set is equivalent to
membership in the mixed convex hull over the same direction carrier. -/
theorem mem_unitSection_liftingSetCone_iff_mem_mixedConvexHull
    (points directions : Set E) (x : E) :
    x ∈ U[R | cone[R] (liftingSet R points directions)] ↔
      x ∈ mconv[R](points | directions) := by
  constructor
  · exact fun hx ↦
      mem_liftingSetCone_one_mem_of_subset_recession points directions
        (convex_mixedConvexHull R points directions)
        (subset_mixedConvexHull R points directions)
        (directions_subset_recessionCone_mixedConvexHull R points directions)
        (by simpa [mem_unitSection_iff] using hx)
  · exact fun hx ↦ mixedConvexHull_subset_unitSection_liftingSetCone points directions hx

/-- Proposition 17.0.10, owner-level form: the mixed convex hull generated by `points` and
`directions` is exactly the height-`1` section of the cone generated by `liftingSet`. -/
theorem mixedConvexHull_eq_unitSection_liftingSetCone
    (points directions : Set E) :
    mconv[R](points | directions) =
      U[R | cone[R] (liftingSet R points directions)] := by
  ext x
  exact (mem_unitSection_liftingSetCone_iff_mem_mixedConvexHull points directions x).symm

/-- Product-space bridge form of Proposition 17.0.10: under the canonical owner `unitLift R`,
the mixed convex hull identifies with the intersection of the lifted cone and the intrinsic
height-`1` slice `unitHeightSet`. -/
theorem unitLift_mixedConvexHull_eq_unitHeightSet_inter_liftingSetCone
    (points directions : Set E) :
    L[R | mconv[R](points | directions)] =
      unitHeightSet (R := R) ∩ cone[R] (liftingSet R points directions) := by
  ext p
  rcases p with ⟨a, x⟩
  constructor
  · rintro ⟨y, hy, hxy⟩
    cases hxy
    constructor
    · simp [unitHeightSet]
    · simpa using
        (mem_unitSection_liftingSetCone_iff_mem_mixedConvexHull points directions x).2 hy
  · rintro ⟨ha, hp⟩
    have ha : a = (1 : R) := by
      simpa [unitHeightSet] using ha
    have hx_section :
        x ∈ U[R | cone[R] (liftingSet R points directions)] := by
      simpa [mem_unitSection_iff, ha] using hp
    have hx : x ∈ mconv[R](points | directions) :=
      (mem_unitSection_liftingSetCone_iff_mem_mixedConvexHull points directions x).1 hx_section
    exact ⟨x, hx, by ext <;> simp [ha]⟩

section

variable [IsStrictOrderedRing R]

/-- Source-facing ray bridge form of Proposition 17.0.10:
membership in the height-`1` section of the lifted cone over `ray directions` is equivalent to
membership in the mixed convex hull generated by `points` and `ray directions`. -/
theorem mem_unitSection_liftingSetCone_iff_mem_mixedConvexHull_ray
    (points : Set E) (directions : Set (Module.Ray R E)) (x : E) :
    x ∈ U[R | cone[R] (liftingSet R points (ray directions))] ↔
      x ∈ mconv[R](points | ray directions) := by
  simpa using
    (mem_unitSection_liftingSetCone_iff_mem_mixedConvexHull
      (R := R) (points := points) (directions := ray directions) x)

/-- Source-facing ray bridge equality form of Proposition 17.0.10. -/
theorem mixedConvexHull_eq_unitSection_liftingSetCone_ray
    (points : Set E) (directions : Set (Module.Ray R E)) :
    mconv[R](points | ray directions) =
      U[R | cone[R] (liftingSet R points (ray directions))] := by
  simpa using
    (mixedConvexHull_eq_unitSection_liftingSetCone
      (R := R) (points := points) (directions := ray directions))

/-- Source-facing ray bridge product-space form of Proposition 17.0.10. -/
theorem unitLift_mixedConvexHull_eq_unitHeightSet_inter_liftingSetCone_ray
    (points : Set E) (directions : Set (Module.Ray R E)) :
    L[R | mconv[R](points | ray directions)] =
      unitHeightSet (R := R) ∩ cone[R] (liftingSet R points (ray directions)) := by
  simpa using
    (unitLift_mixedConvexHull_eq_unitHeightSet_inter_liftingSetCone
      (R := R) (points := points) (directions := ray directions))

end

end

/-! ### Proposition_17_0_11 (from Chap04) -/
universe u v

open scoped Rockafellar

section


/-!
Source/core/bridge triage:

- `source-facing`: Proposition 17.0.11 identifies the convex cone generated by `T` with the mixed
  convex hull obtained from the single point `0` and the directions generated by `T`.
- `core/canonical`: the owner abstractions are `cone[R] T`,
  `mixedConvexHull R ({0} : Set E) T`, and the canonical hull-membership owner
  `PointedCone.mem_hull_set`.
- `bridge/view`: the Chapter 1 positive-linear-combination surface for `cone[R] T` is a derived
  bridge view layered above the canonical hull-membership owner.

Domain-style sampling used here:
- `cone[R] T` from `PointedCone.hull`;
- `mixedConvexHull`;
- `PointedCone.mem_hull_set`;
- `Set.positiveLinearCombination`.

Primitive data vs derived API:
- primitive data: the generating set `T`;
- derived API: the cone/mixed-hull identification, the canonical nonnegative finite-support
  membership characterization from `PointedCone.mem_hull_set`, and the stricter Chapter 1
  positive-linear-combination bridge theorem.

Layer target: `bridge/view`.
-/

variable {R : Type v} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- Proposition 17.0.11: the convex cone generated by `T` is the mixed convex hull generated by
the single point `0` and the direction set `T` itself. This is the canonical owner-level form of
the source statement, because `mixedConvexHull` already records directions as vectors rather than
as an auxiliary set of rays. -/
-- Proof sketch: `cone[R] T` is convex, contains `0`, and recedes in every direction from `T`,
-- so minimality of `mixedConvexHull` gives `mixedConvexHull R ({0} : Set E) T ⊆ cone[R] T`.
-- Conversely, if a convex set contains `0` and recedes in every vector of `T`, then it contains
-- every nonnegative multiple of every generator of `T`, hence it contains the generated cone.
theorem cone_eq_mixedConvexHull_zero (T : Set E) :
    (cone[R] T : Set E) = mconv[R](({0} : Set E) | T) := sorry

/-- Canonical membership form of Proposition 17.0.11: membership in
`mconv[R](({0} : Set E) | T)` is exactly the canonical pointed-cone hull witness form with
nonnegative finitely supported coefficients on `T`. -/
theorem mem_mixedConvexHull_zero_iff_exists_nonneg_finsupp
    (T : Set E) {x : E} :
    x ∈ mconv[R](({0} : Set E) | T) ↔
      ∃ c : E →₀ R,
        (↑c.support : Set E) ⊆ T ∧
        (∀ y, 0 ≤ c y) ∧
        c.sum (fun y a ↦ a • y) = x := by
  constructor
  · intro hx
    have hxCone : x ∈ (cone[R] T : Set E) := by
      simpa [cone_eq_mixedConvexHull_zero (R := R) (T := T)] using hx
    exact (PointedCone.mem_hull_set (R := R) (s := T) (x := x)).1 hxCone
  · rintro ⟨c, hcT, hc0, hsum⟩
    have hxCone : x ∈ (cone[R] T : Set E) :=
      (PointedCone.mem_hull_set (R := R) (s := T) (x := x)).2
        ⟨c, hcT, hc0, hsum⟩
    simpa [cone_eq_mixedConvexHull_zero (R := R) (T := T)] using hxCone

end

section

variable {R : Type v} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-!
Assumption profile for the bridge theorem below:
the extra scalar-order assumptions
`[AddLeftMono R] [AddLeftStrictMono R] [ZeroLEOneClass R] [Nontrivial R]
[PosMulStrictMono R]`
are exactly the assumptions of the upstream Chapter 1 owner bridge
`ConvexCone.mem_hull_iff_exists_positiveLinearCombination`.
This file introduces no additional ambient strengthening beyond that bridge surface.
-/

/-- Proposition 17.0.11, membership form: a vector belongs to the mixed convex hull generated by
the point `0` and the direction set `T` if and only if it is either `0` or a positive linear
combination of vectors of `T`. This is a Chapter 1 bridge/view theorem layered above the
canonical nonnegative-coefficient hull-membership owner. -/
-- Proof sketch: combine `cone_eq_mixedConvexHull_zero` with the canonical owner-level
-- membership bridge from Corollary 2.6.2.
theorem mem_mixedConvexHull_zero_iff_eq_zero_or_mem_positiveLinearCombination
    [AddLeftMono R] [AddLeftStrictMono R]
    [ZeroLEOneClass R] [Nontrivial R] [PosMulStrictMono R]
    (T : Set E) {x : E} :
    x ∈ mconv[R](({0} : Set E) | T) ↔
      x = 0 ∨ x ∈ Set.positiveLinearCombination R T := sorry

end
