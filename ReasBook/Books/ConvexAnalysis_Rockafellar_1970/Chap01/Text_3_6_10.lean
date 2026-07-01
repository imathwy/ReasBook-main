import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_3_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_6_12

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

open Set
open scoped Pointwise
open scoped Rockafellar

variable {R : Type*}
variable [Semiring R] [PartialOrder R]
variable {E : Type u}
variable [AddCommMonoid E] [Module R E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.10 fixes convex sets `C₁` and `C₂`, forms their homogenization sets
  `K₁` and `K₂`, then defines `K` as the set of sums of one point from each and identifies the
  slice of `K` at height `1` with `conv[R] (C₁ ∪ C₂)`.
- `core/canonical`: the owner abstraction for this unit slice is mathlib's `convexJoin R C₁ C₂`,
  whose elements are the convex combinations of one point of `C₁` and one point of `C₂`.
- `bridge/view`: the unit slice of `homogenizationSet C₁ + homogenizationSet C₂` is exactly
  `convexJoin R C₁ C₂`, and for convex nonempty sets `C₁`, `C₂` the owner theorem
  `Convex.convexHull_union` identifies this join with the chapter convex-hull surface
  `conv[R] (C₁ ∪ C₂)`.
- Primitive data vs derived API: `homogenizationSet` remains the primitive source-facing data for
  `K₁` and `K₂`; `convexJoin` and `Convex.convexHull_union` are the derived canonical bridge API.
- Domain-style sampling: this item is guided by `homogenizationSet`, `mem_homogenizationSet_iff`,
  `Set.mem_smul_set`, `mem_convexJoin`, and `Convex.convexHull_union`.
- Layer target: `bridge/view`.
-/

/-- Helper for Text 3.6.10: a point lies in the unit slice of the pointwise sum of the
homogenization sets of `C₁` and `C₂` exactly when it lies in the canonical convex join
`convexJoin R C₁ C₂`. -/
theorem mem_unitSection_homogenizationSet_add_iff_mem_convexJoin
    (C₁ C₂ : Set E) (x : E) :
    x ∈ U[R | (K[R | C₁]) + (K[R | C₂])] ↔
      x ∈ convexJoin R C₁ C₂ := by
  rw [mem_convexJoin]
  constructor
  · intro hx
    -- Unpack the source-facing sum witness into two homogenized summands.
    rcases mem_add.mp hx with ⟨⟨a, x₁⟩, hx₁, ⟨b, x₂⟩, hx₂, hsum⟩
    rw [mem_homogenizationSet_iff R C₁] at hx₁
    rw [mem_homogenizationSet_iff R C₂] at hx₂
    rcases mem_smul_set.mp (by simpa using hx₁.2) with ⟨c₁, hc₁, hc₁eq⟩
    rcases mem_smul_set.mp (by simpa using hx₂.2) with ⟨c₂, hc₂, hc₂eq⟩
    -- Repackage the same witnesses in the canonical `convexJoin` normal form.
    refine ⟨c₁, hc₁, c₂, hc₂, a, b, hx₁.1, hx₂.1, ?_, ?_⟩
    · simpa using congrArg (fun p ↦ p.1) hsum
    · simpa [hc₁eq, hc₂eq] using congrArg (fun p ↦ p.2) hsum
  · rintro ⟨c₁, hc₁, c₂, hc₂, a, b, ha, hb, hab, rfl⟩
    -- Build the two homogenized points and then combine them in the pointwise sum.
    refine mem_add.mpr ⟨(a, a • c₁), ?_, (b, b • c₂), ?_, ?_⟩
    · exact (mem_homogenizationSet_iff R C₁ _).2 ⟨ha, mem_smul_set.mpr ⟨c₁, hc₁, rfl⟩⟩
    · exact (mem_homogenizationSet_iff R C₂ _).2 ⟨hb, mem_smul_set.mpr ⟨c₂, hc₂, rfl⟩⟩
    · ext <;> simp [hab]

/-- Helper for Text 3.6.10: the unit slice of the pointwise sum of the homogenization sets of
`C₁` and `C₂` is exactly the canonical convex join `convexJoin R C₁ C₂`. -/
theorem unitSection_homogenizationSet_add_eq_convexJoin
    (C₁ C₂ : Set E) :
    U[R | (K[R | C₁]) + (K[R | C₂])] =
      convexJoin R C₁ C₂ := by
  -- Extensionality reduces the set equality to the pointwise bridge above.
  ext x
  exact mem_unitSection_homogenizationSet_add_iff_mem_convexJoin C₁ C₂ x

/-- Helper for Text 3.6.10: the unit slice of the pointwise sum of homogenization sets is always
contained in the convex hull of the union. This is the primitive owner-level containment before
imposing convex/nonempty hypotheses that upgrade containment to equality. -/
theorem unitSection_homogenizationSet_add_subset_convexHull_union
    (C₁ C₂ : Set E) :
    U[R | (K[R | C₁]) + (K[R | C₂])] ⊆
      conv[R] (C₁ ∪ C₂) := by
  intro x hx
  -- First move from the homogenization slice to the canonical convex join.
  have hx_join : x ∈ convexJoin R C₁ C₂ :=
    (mem_unitSection_homogenizationSet_add_iff_mem_convexJoin C₁ C₂ x).1 hx
  exact convexJoin_subset_convexHull C₁ C₂ hx_join

end

section

universe u

open Set
open scoped Pointwise
open scoped Rockafellar

variable {R : Type*}
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {E : Type u}
variable [AddCommMonoid E] [Module R E]

/-- Helper for Text 3.6.10: at the closure layer, nonemptiness already identifies the convex hull
of the unit slice of `K[C₁] + K[C₂]` with the convex hull of `C₁ ∪ C₂`. This keeps `convexJoin`
as the primitive owner and treats `conv[R] (C₁ ∪ C₂)` as the derived hull-level bridge. -/
theorem convexHull_unitSection_homogenizationSet_add_eq_convexHull_union
    (C₁ C₂ : Set E) (hC₁_nonempty : C₁.Nonempty) (hC₂_nonempty : C₂.Nonempty) :
    (conv[R] (U[R | (K[R | C₁]) + (K[R | C₂])])) =
      conv[R] (C₁ ∪ C₂) := by
  -- Nonempty sets embed into their convex join, so the union already sits in the owner object.
  have h_union_subset_join : C₁ ∪ C₂ ⊆ convexJoin R C₁ C₂ := by
    exact union_subset
      (subset_convexJoin_left (s := C₁) (t := C₂) hC₂_nonempty)
      (subset_convexJoin_right (s := C₁) (t := C₂) hC₁_nonempty)
  calc
    (conv[R] (U[R | (K[R | C₁]) + (K[R | C₂])])) = conv[R] (convexJoin R C₁ C₂) := by
      simp [unitSection_homogenizationSet_add_eq_convexJoin C₁ C₂]
    _ = conv[R] (C₁ ∪ C₂) := by
      -- The join is contained in the hull of the union, and conversely the union sits in the join.
      apply le_antisymm
      · exact convexHull_min (convexJoin_subset_convexHull C₁ C₂) (convex_convexHull R (C₁ ∪ C₂))
      · exact convexHull_mono h_union_subset_join

end

section

universe u

open Set
open scoped Pointwise
open scoped Rockafellar

variable {R : Type*}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {E : Type u}
variable [AddCommGroup E] [Module R E]

/-- Text 3.6.10: for nonempty convex sets `C₁` and `C₂`, the unit slice of the pointwise sum of
their homogenization sets is exactly `conv[R] (C₁ ∪ C₂)`. -/
-- Proof sketch: first derive the closure-level bridge
-- `conv[R] (U[R | K[C₁] + K[C₂]]) = conv[R] (C₁ ∪ C₂)` from the canonical owner
-- `unitSection_homogenizationSet_add_eq_convexJoin`; then upgrade to equality without hull on the
-- left using convexity of the unit slice (`Convex.convexJoin`) under the convexity assumptions.
theorem unitSection_homogenizationSet_add_eq_convexHull_union
    (C₁ C₂ : Set E) (hC₁ : Convex R C₁) (hC₂ : Convex R C₂)
    (hC₁_nonempty : C₁.Nonempty) (hC₂_nonempty : C₂.Nonempty) :
    U[R | (K[R | C₁]) + (K[R | C₂])] =
      conv[R] (C₁ ∪ C₂) := by
  have hconv_unit :
      Convex R (U[R | (K[R | C₁]) + (K[R | C₂])]) := by
    simpa [unitSection_homogenizationSet_add_eq_convexJoin C₁ C₂] using hC₁.convexJoin hC₂
  have hconv_unit_hull :
      (conv[R] (U[R | (K[R | C₁]) + (K[R | C₂])])) =
        U[R | (K[R | C₁]) + (K[R | C₂])] :=
    hconv_unit.convexHull_eq
  calc
    U[R | (K[R | C₁]) + (K[R | C₂])] =
        conv[R] (U[R | (K[R | C₁]) + (K[R | C₂])]) := by
      simpa [eq_comm] using hconv_unit_hull
    _ = conv[R] (C₁ ∪ C₂) :=
      convexHull_unitSection_homogenizationSet_add_eq_convexHull_union
        (R := R) C₁ C₂ hC₁_nonempty hC₂_nonempty

/-- A point `x` lies in the unit slice of the pointwise sum of the homogenization sets of `C₁` and
`C₂` exactly when it lies in `conv[R] (C₁ ∪ C₂)`. -/
theorem mem_unitSection_homogenizationSet_add_iff_mem_convexHull_union
    (C₁ C₂ : Set E) (hC₁ : Convex R C₁) (hC₂ : Convex R C₂)
    (hC₁_nonempty : C₁.Nonempty) (hC₂_nonempty : C₂.Nonempty) (x : E) :
    x ∈ U[R | (K[R | C₁]) + (K[R | C₂])] ↔
      x ∈ conv[R] (C₁ ∪ C₂) := by
  -- Evaluate the established set equality at the point `x`.
  simpa using congrArg (fun s : Set E ↦ x ∈ s)
    (unitSection_homogenizationSet_add_eq_convexHull_union
      C₁ C₂ hC₁ hC₂ hC₁_nonempty hC₂_nonempty)

end
