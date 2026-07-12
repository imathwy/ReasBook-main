import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_6_12

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

open scoped Rockafellar

variable {R : Type*}
variable [Monoid R]
variable {E : Type u}

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.12 forms the sets `K₁`, `K₂` attached to `C₁`, `C₂` by the rule
  `Kᵢ = {(λ, x) | 0 ≤ λ, x ∈ λ • Cᵢ}`, then defines `K = K₁ ∩ K₂` and identifies the height-`1`
  section of `K`. The source uses `R^n`, but the statement itself only depends on the scalar-action
  structure carried by the chapter owner `homogenizationSet`.
- `core/canonical`: the owner object is the chapter-level source-facing set
  `homogenizationSet C : Set (R × E)` from Text 3.5.5 together with the chapter-level section
  owner `unitSection` (notation `U[R | S]`).
- `bridge/view`: the displayed `K` is exactly `homogenizationSet C₁ ∩ homogenizationSet C₂`, and
  the conclusion is the equality between the height-`1` section of that intersection and
  `C₁ ∩ C₂`, with pointwise membership as the thin companion view. The key owner lemma is the
  upstream unit-section theorem `mem_unitSection_homogenizationSet_iff`.
- Primitive data vs derived API: the homogenization sets are already the primitive source-facing
  data from Text 3.5.5; this item contributes only the section-at-height-`1` characterization.
- Domain-style sampling: this reuses `homogenizationSet`,
  `mem_unitSection_homogenizationSet_iff`, `unitSection`, ordinary set intersection, and
  `Set.mem_inter_iff`.
- Layer target: `bridge/view`.
- Abstraction checks:
  1. Codomain/ambient over-concrete? `No` (`Set (R × E)` and `Set E` are already canonical).
  2. Scalar/ambient structure too strong? `No` for this bridge (it reuses
     `mem_unitSection_homogenizationSet_iff` at its native scalar-action layer).
  3. Owner tied to concrete model? `No`; owners are `K`/`U` only.
  4. Better intrinsic/relative topology surface? `N/A` (non-topological statement).
  5. Owner names too concrete/heavy? `No`; owner names are short and canonical.
  6. Notation needed and used? `Yes`; theorem surfaces use `K[R | _]` / `U[R | _]`,
     including the set-family image form `((fun C => K[R | C]) '' 𝒞)`.
  7. Concrete arity over-specialization? `Yes` before normalization: this bridge naturally
     extends from binary intersections to indexed intersections.
-/

variable [Zero R] [LE R] [ZeroLEOneClass R]
variable [MulAction R E]

/-- The height-`1` section of an indexed intersection of homogenization sets is the indexed
intersection of the underlying sets. -/
@[simp] theorem unitSection_iInter_homogenizationSet_eq {ι : Sort*} (C : ι → Set E) :
    U[R | ⋂ i, K[R | C i]] = ⋂ i, C i := by
  ext x
  simp

/-- Membership in the height-`1` section of an indexed intersection of homogenization sets is
equivalent to membership in the indexed intersection of the underlying sets. -/
@[simp] theorem mem_unitSection_iInter_homogenizationSet_iff {ι : Sort*}
    (C : ι → Set E) (x : E) :
    x ∈ U[R | ⋂ i, K[R | C i]] ↔ x ∈ ⋂ i, C i := by
  simp

/-- The height-`1` section of an intrinsic family intersection of homogenization sets, indexed by
elements of a set of sets, is the corresponding intrinsic family intersection. -/
@[simp] theorem unitSection_iInter_subtype_homogenizationSet_eq (𝒞 : Set (Set E)) :
    U[R | ⋂ C ∈ 𝒞, K[R | C]] = ⋂ C ∈ 𝒞, C := by
  ext x
  simp

/-- Membership in the height-`1` section of an intrinsic family intersection of homogenization
sets, indexed by elements of a set of sets, is equivalent to membership in the corresponding
intrinsic family intersection. -/
@[simp] theorem mem_unitSection_iInter_subtype_homogenizationSet_iff (𝒞 : Set (Set E)) (x : E) :
    x ∈ U[R | ⋂ C ∈ 𝒞, K[R | C]] ↔ x ∈ ⋂ C ∈ 𝒞, C := by
  simp

/-- The height-`1` section of the intersection of a family of homogenization sets indexed by a set
of sets is the intersection of that family. -/
@[simp] theorem unitSection_sInter_homogenizationSet_eq (𝒞 : Set (Set E)) :
    U[R | ⋂₀ ((fun C : Set E => K[R | C]) '' 𝒞)] = ⋂₀ 𝒞 := by
  ext x
  simp [Set.mem_sInter]

/-- Membership in the height-`1` section of the intersection of a family of homogenization sets
indexed by a set of sets is equivalent to membership in that family intersection. -/
@[simp] theorem mem_unitSection_sInter_homogenizationSet_iff (𝒞 : Set (Set E)) (x : E) :
    x ∈ U[R | ⋂₀ ((fun C : Set E => K[R | C]) '' 𝒞)] ↔ x ∈ ⋂₀ 𝒞 := by
  simp [Set.mem_sInter]

/-- Helper for Text 3.6.12: a point belongs to the height-`1` section of the intersection of two
homogenization sets exactly when it belongs to both underlying sets. -/
theorem mem_unitSection_inter_homogenizationSet_and_iff (C₁ C₂ : Set E) (x : E) :
    x ∈ U[R | K[R | C₁] ∩ K[R | C₂]] ↔ x ∈ C₁ ∧ x ∈ C₂ := by
  -- Rewrite the section of the ambient intersection into the two height-`1` membership tests.
  -- Each factor then collapses by the single-set homogenization bridge.
  simp [Set.mem_inter_iff]

/-- Helper for Text 3.6.12: the height-`1` section of the intersection of the homogenization sets
of `C₁` and `C₂` is exactly `C₁ ∩ C₂`. -/
@[simp] theorem unitSection_inter_homogenizationSet_eq (C₁ C₂ : Set E) :
    U[R | K[R | C₁] ∩ K[R | C₂]] = C₁ ∩ C₂ := by
  -- First evaluate the source-facing intersection at a point, then use the helper that turns
  -- the height-`1` condition into the two underlying membership conditions.
  -- Reduce the set equality to the pointwise membership statement provided by the helper.
  ext x
  rw [Set.mem_inter_iff]
  exact mem_unitSection_inter_homogenizationSet_and_iff C₁ C₂ x

/-- Membership in the height-`1` section of the intersection of the homogenization sets of
`C₁` and `C₂` is equivalent to membership in `C₁ ∩ C₂`. -/
@[simp] theorem mem_unitSection_inter_homogenizationSet_iff (C₁ C₂ : Set E) (x : E) :
    x ∈ U[R | K[R | C₁] ∩ K[R | C₂]] ↔ x ∈ C₁ ∩ C₂ := by
  -- Repackage the conjunction description of the helper as ordinary set-intersection membership.
  rw [Set.mem_inter_iff]
  exact mem_unitSection_inter_homogenizationSet_and_iff C₁ C₂ x

/-- Text 3.6.12: ambient membership at height `1` in the intersection of the homogenization sets
of `C₁` and `C₂` is equivalent to membership in `C₁ ∩ C₂`. -/
theorem mem_inter_homogenizationSet_mk_one_iff (C₁ C₂ : Set E) (x : E) :
    ((1 : R), x) ∈ K[R | C₁] ∩ K[R | C₂] ↔ x ∈ C₁ ∩ C₂ := by
  -- Rewrite the ambient pair-membership statement as membership in the height-`1` section.
  -- The unit-section bridge for the intersection then closes the source-facing statement.
  calc
    ((1 : R), x) ∈ K[R | C₁] ∩ K[R | C₂]
        ↔ x ∈ U[R | K[R | C₁] ∩ K[R | C₂]] :=
          (mem_unitSection_iff (S := K[R | C₁] ∩ K[R | C₂]) (x := x)).symm
    _ ↔ x ∈ C₁ ∩ C₂ :=
      mem_unitSection_inter_homogenizationSet_iff C₁ C₂ x

end
