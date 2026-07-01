import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-!
Source/core/bridge triage:

- `source-facing`: Text 21.3.5 gives a family of closed convex sets showing that Helly's
  conclusion can fail without a no-common-recession-direction hypothesis.
- `core/canonical`: the owner abstraction is the upstream set-family owner
  `recessionExamplePositiveWeakSublevelFamily : Set (Set (ℝ × ℝ))`, built from positive-level weak
  sublevel sets.
- `bridge/view`: the textbook member notation `C[k, ε]` is kept as a thin surface for concrete
  branch/level sets, while theorem surfaces are stated on owner membership
  `S ∈ recessionExamplePositiveWeakSublevelFamily`.

Domain-style sampling used here:
- `positiveWeakSublevelFamily` from `Text_21_3_4`;
- `recessionExamplePositiveWeakSublevelFamily` from `Text_21_3_4`;
- `recessionExample_joint_strict_feasibility`;
- `sInter` for the total and finite intersections of the owner set-family.

Primitive data vs derived API:
- primitive data: the upstream owner `recessionExamplePositiveWeakSublevelFamily`;
- derived API: member-wise nonemptiness/closedness/convexity, finite-subfamily
  intersection-nonemptiness, and emptiness of the total intersection.

Layer target: `source-facing`, since the mathematics is the explicit counterexample family itself.

Scalar/ambient note:
- this item is the explicit two-branch counterexample on `R²` from Text 21.3.4, so `ℝ` and
  `ℝ × ℝ`
  are mathematically essential in this file rather than proof-accidental defaults;
- codomain thresholds and owner surfaces are normalized to `WithTopBot ℝ` (not
  `EReal`-named APIs) to match the Chapter 21 canonical layer.
-/

namespace HellyCounterexample

local notation "R2" => ℝ × ℝ

/-- The source-facing textbook member `C_{k,ε}` of Text 21.3.5. -/
scoped notation "C[" k "," ε "]" =>
  recessionExamplePositiveWeakSublevelSet k ε

/-- Short owner notation for the canonical set-family `{C_{k, ε} | k : Branch, ε > 0}`. -/
scoped notation "𝓒" => recessionExamplePositiveWeakSublevelFamily

/-- Owner bridge: membership in `𝓒` is exactly membership in one positive-level textbook member
`C[k, ε]`. -/
theorem mem_family_iff (S : Set R2) :
    S ∈ 𝓒 ↔ ∃ k : Branch, ∃ ε : PositiveLevel, S = C[k, ε] := by
  simpa using mem_recessionExamplePositiveWeakSublevelFamily_iff S

/-- Each textbook member belongs to the canonical owner family. -/
theorem C_mem_family (k : Branch) (ε : PositiveLevel) :
    C[k, ε] ∈ 𝓒 := by
  exact (mem_family_iff _).2 ⟨k, ε, rfl⟩

/-- Every owner member of the canonical counterexample family is nonempty. -/
-- Proof sketch: `recessionExample_joint_strict_feasibility hε` gives a point where both branch
-- functions are `< ε`, hence in particular a point of
-- `recessionExamplePositiveWeakSublevelSet k ε`.
theorem family_nonempty {S : Set R2}
    (hS : S ∈ 𝓒) :
    S.Nonempty := sorry

/-- Textbook member view: each `C[k, ε]` at positive level `ε` is nonempty. -/
theorem C_nonempty (k : Branch) (ε : PositiveLevel) :
    (C[k, ε]).Nonempty := by
  exact family_nonempty (C_mem_family k ε)

/-- Every owner member of the canonical counterexample family is closed. -/
-- Proof sketch: `recessionExampleFamily k` is the `WithTopBot ℝ` lift of one of the two continuous
-- branch functions from `Text 21.3.4`, so the owner solution set
-- `recessionExamplePositiveWeakSublevelSet k ε` is the corresponding
-- closed sublevel set. Since these are subsets of the full ambient space `R²` (not of a proper
-- ambient subset), ambient `IsClosed` is already the intrinsic topology statement here.
theorem family_isClosed {S : Set R2}
    (hS : S ∈ 𝓒) :
    IsClosed S := sorry

/-- Textbook member view: each `C[k, ε]` at positive level `ε` is closed. -/
theorem C_isClosed (k : Branch) (ε : PositiveLevel) :
    IsClosed (C[k, ε]) := by
  exact family_isClosed (C_mem_family k ε)

/-- Every owner member of the canonical counterexample family is convex. -/
-- Proof sketch: apply the canonical single-constraint owner theorem
-- `ConvexInequalityRelation.convex_solutionSet` to the branch owner
-- `recessionExampleFamily k`, using the primitive owner
-- `recessionExampleFamily_convexOn k` and its global bridge
-- `recessionExampleFamily_isConvex k`.
theorem family_convex {S : Set R2}
    (hS : S ∈ 𝓒) :
    Convex ℝ S := sorry

/-- Textbook member view: each `C[k, ε]` at positive level `ε` is convex. -/
theorem C_convex (k : Branch) (ε : PositiveLevel) :
    Convex ℝ (C[k, ε]) := by
  exact family_convex (C_mem_family k ε)

/-- Every finite subfamily of the canonical counterexample family has nonempty intersection. In
particular, this implies the three-member intersection clause in Text 21.3.5 (1). -/
-- Canonical finite-family owner surface: use `Set.Finite` and subset inclusion instead of a
-- `Finset` encoding.
-- Proof sketch: for a finite parameter set `S`, choose `λ` at least as large as the maximum of
-- the thresholds `(1 - ε^2) / (2 ε)` over the positive levels appearing in `S`. Then the diagonal
-- point `λ • recessionExampleDirection` lies in every corresponding member `C[k, ε]`.
theorem finite_subfamily_nonempty {F : Set (Set R2)}
    (hF_finite : F.Finite) (hF_subset : F ⊆ 𝓒) :
    (⋂₀ F).Nonempty :=
  sorry

/-- Text 21.3.5 (2): the total intersection of all sets `C_{k, ε}` with `k ∈ {1, 2}` and
`ε > 0` is empty. -/
-- Proof sketch: a point in the total intersection would satisfy both branch inequalities
-- `recessionExampleF1 x ≤ ε` and `recessionExampleF2 x ≤ ε` for every positive `ε`, hence both
-- branch values are `≤ 0`. The disjointness result from `Text 21.3.4` rules this out.
theorem total_intersection_eq_empty :
    ⋂₀ 𝓒 = (∅ : Set R2) := sorry

end HellyCounterexample
