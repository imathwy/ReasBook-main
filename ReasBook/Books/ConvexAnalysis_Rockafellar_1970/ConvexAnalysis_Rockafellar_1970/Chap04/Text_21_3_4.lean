import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_5_0

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Rockafellar

noncomputable section

section

local notation "R2" => ℝ × ℝ
local notation "e₁" => ((1 : ℝ), (0 : ℝ))
local notation "e₂" => ((0 : ℝ), (1 : ℝ))

/-- The intrinsic two-branch index for Text 21.3.4. -/
inductive Branch where
  | first
  | second
deriving DecidableEq

/-- Canonical owner of the positive-level weak-sublevel family attached to `f`. -/
def positiveWeakSublevelFamily {E : Type*} {ι : Type*} {α : Type*} [Preorder α] [Zero α]
    (f : ι → E → WithTopBot α) : Set (Set E) :=
  {S | ∃ i : ι, ∃ ε : α, 0 < ε ∧
      S = (f i) ⁻¹' Set.Iic (ε : WithTopBot α)}

/-- Membership in a positive-level weak-sublevel family is exactly membership in one branch weak
sublevel set at a positive threshold, encoded intrinsically by a subtype. -/
theorem mem_positiveWeakSublevelFamily_iff {E : Type*} {ι : Type*} {α : Type*}
    [Preorder α] [Zero α] (f : ι → E → WithTopBot α) (S : Set E) :
    S ∈ positiveWeakSublevelFamily f ↔
      ∃ i : ι, ∃ ε : {ε : α // 0 < ε},
        S = (f i) ⁻¹' Set.Iic ((ε : α) : WithTopBot α) := by
  constructor
  · rintro ⟨i, ε, hε, rfl⟩
    exact ⟨i, ⟨ε, hε⟩, rfl⟩
  · rintro ⟨i, ε, rfl⟩
    exact ⟨i, ε, ε.2, rfl⟩

/-!
Source/core/bridge triage:

- `source-facing`: this example fixes two explicit real-valued functions on `R²`, their `0`
  sublevel sets, the failure of a common nonpositive point, strict feasibility at every positive
  level, and a common recession direction.
- `core/canonical`: the owner abstractions are the two functions themselves on the canonical
  ambient space `R2 = ℝ × ℝ`, the canonical codomain lift
  `Function.toWithTopBot`, the derived owner family `recessionExampleFamily` valued in
  `WithTopBot ℝ`, its convex-on-universe owner
  `ConvexOn ℝ Set.univ (recessionExampleFamily k)` and global bridge
  `(recessionExampleFamily k).IsConvex ℝ`, the source-facing branch owners
  `recessionExampleZeroSublevelSet` and `recessionExampleStrictSublevelSet`, the Chapter 8 owner
  recession cones `recessionCone` and `recessionExampleBranchRecessionCone`, together with the
  source-facing recession-direction owner `C.RecedesInDirection ℝ y`.
- `bridge/view`: the special `0`-sublevel sets are the owner sets
  `recessionExampleZeroSublevelSet k`, and the textbook phrase "common direction of recession" is
  recorded concretely by membership of the direction in the corresponding function-recession cones
  and by the explicit witness
  `∃ y, (univ : Set R2).RecedesInDirection ℝ y ∧
    ∀ k : Branch, y ∈ recessionExampleBranchRecessionCone k`.

Domain-style sampling used here:
- `ConvexOn`;
- `Function.IsConvex`;
- `Function.isConvex_coe_of_convexOn_univ`;
- `Function.IsConvex.convex_le`;
- sublevel owners `f ⁻¹' Set.Iic μ` and `f ⁻¹' Set.Iio μ`;
- `recessionCone`;
- `Function.recessionCone` and `Function.mem_recessionCone_iff`;
- `C.RecedesInDirection ℝ y`.

Primitive data vs derived API:
- primitive data: the explicit formulas for the two functions and the direction `e₁ + e₂`;
- derived API: the canonical `WithTopBot ℝ` lift of the two branch functions into the owner family
  `recessionExampleFamily`, global convexity of each family branch, disjointness of the `0`-
  sublevel sets, the absence of a common nonpositive point,
  strict feasibility at every positive level, and the explicit common
  function-recession-direction witness.

Layer target: `source-facing`, with the owner level chosen to match the surrounding chapter API for
convex functions and recession directions.

Scalar/ambient note:
- this source item is intrinsically real and two-dimensional (`Real.sqrt`, coordinate formulas,
  explicit `e₁ + e₂` geometry), so `ℝ` and `R2` are kept on purpose;
- the codomain owner layer is normalized away from `EReal` to the weaker canonical
  `WithTopBot ℝ` layer used by Chapter 21 owners.
-/

/-- The first function in the counterexample from Text 21.3.4. -/
def recessionExampleF1 (x : R2) : ℝ :=
  Real.sqrt (x.1 ^ 2 + 1) - x.2

/-- The second function in the counterexample from Text 21.3.4. -/
def recessionExampleF2 (x : R2) : ℝ :=
  Real.sqrt (x.2 ^ 2 + 1) - x.1

/-- The common direction `e₁ + e₂` used in Text 21.3.4. -/
def recessionExampleDirection : R2 :=
  e₁ + e₂

/-- The canonical two-branch extended-codomain family attached to the counterexample in Text
21.3.4, exposed at the `WithTopBot ℝ` layer. -/
def recessionExampleFamily : Branch → R2 → WithTopBot ℝ
  | .first => recessionExampleF1.toWithTopBot
  | .second => recessionExampleF2.toWithTopBot

/-- The weak `μ`-sublevel set of branch `k` in the counterexample family. -/
abbrev recessionExampleWeakSublevelSet (k : Branch) (μ : WithTopBot ℝ) : Set R2 :=
  (recessionExampleFamily k) ⁻¹' Set.Iic μ

/-- The weak `0`-sublevel set of branch `k` in the counterexample family. -/
abbrev recessionExampleZeroSublevelSet (k : Branch) : Set R2 :=
  recessionExampleWeakSublevelSet k 0

/-- Positive threshold layer used to index weak positive-level sublevel sets. -/
abbrev PositiveLevel : Type := {ε : ℝ // 0 < ε}

/-- The weak positive-level sublevel set of branch `k` in the counterexample family. -/
abbrev recessionExamplePositiveWeakSublevelSet (k : Branch) (ε : PositiveLevel) : Set R2 :=
  recessionExampleWeakSublevelSet k (ε : ℝ)

/-- The function recession cone of branch `k` in the counterexample family. -/
abbrev recessionExampleBranchRecessionCone (k : Branch) : Set R2 :=
  Function.recessionCone ((recessionExampleFamily k)₀⁺)

/-- The strict `ε`-sublevel set of branch `k` in the counterexample family. -/
abbrev recessionExampleStrictSublevelSet (k : Branch) (ε : ℝ) : Set R2 :=
  (recessionExampleFamily k) ⁻¹' Set.Iio (ε : WithTopBot ℝ)

/-- The source family `{C_{k, ε} | k : Branch, ε > 0}` as a set-family owner. -/
abbrev recessionExamplePositiveWeakSublevelFamily : Set (Set R2) :=
  positiveWeakSublevelFamily recessionExampleFamily

/-- Membership in the source set-family is exactly membership in one branch weak sublevel set at
some positive level. -/
theorem mem_recessionExamplePositiveWeakSublevelFamily_iff (S : Set R2) :
    S ∈ recessionExamplePositiveWeakSublevelFamily ↔
      ∃ k : Branch, ∃ ε : PositiveLevel,
        S = recessionExamplePositiveWeakSublevelSet k ε := by
  simpa [recessionExamplePositiveWeakSublevelFamily, recessionExamplePositiveWeakSublevelSet] using
    (mem_positiveWeakSublevelFamily_iff (f := recessionExampleFamily) (S := S))

/-- Each branch of the canonical `WithTopBot ℝ`-valued counterexample family is convex on `univ`
in the primitive set-owner sense. -/
-- Proof sketch: for `k = Branch.first` and `k = Branch.second`, first prove convexity of the
-- corresponding real-valued branch on all of `R²`; then pass to the `WithTopBot` codomain via
-- the canonical lift theorem `Function.isConvex_coe_of_convexOn_univ`.
theorem recessionExampleFamily_convexOn (k : Branch) :
    ConvexOn ℝ Set.univ (recessionExampleFamily k) := sorry

/-- Global-owner bridge form of `recessionExampleFamily_convexOn`. -/
theorem recessionExampleFamily_isConvex (k : Branch) :
    (recessionExampleFamily k).IsConvex ℝ := by
  simpa [Function.IsConvex] using recessionExampleFamily_convexOn (k := k)

/-- The two displayed `0`-sublevel sets in Text 21.3.4 are disjoint. -/
-- Proof sketch: if a point lay in both sublevel sets, then
-- `x.2 ≥ Real.sqrt (x.1 ^ 2 + 1)` and `x.1 ≥ Real.sqrt (x.2 ^ 2 + 1)`. Squaring both
-- inequalities gives `x.2 ^ 2 ≥ x.1 ^ 2 + 1` and `x.1 ^ 2 ≥ x.2 ^ 2 + 1`, whose sum is
-- impossible.
theorem recessionExample_zeroSublevelSets_disjoint :
    Disjoint
      (recessionExampleZeroSublevelSet Branch.first)
      (recessionExampleZeroSublevelSet Branch.second) :=
  sorry

/-- The canonical two-branch family never takes simultaneously nonpositive values. -/
-- Proof sketch: a common nonpositive point would belong to both `0`-sublevel sets, contradicting
-- `recessionExample_zeroSublevelSets_disjoint`.
theorem recessionExample_no_joint_nonpositive_point :
    ¬ ∃ x : R2, ∀ k : Branch, x ∈ recessionExampleZeroSublevelSet k := sorry

/-- At every positive level `ε`, the two-branch family is jointly strictly feasible. -/
-- Proof sketch: along the diagonal ray `t ↦ t • recessionExampleDirection` both branch values are
-- `Real.sqrt (t ^ 2 + 1) - t`, which decreases to `0` through positive values, so for any
-- `ε > 0` some diagonal point satisfies both inequalities strictly.
theorem recessionExample_joint_strict_feasibility {ε : ℝ} (hε : 0 < ε) :
    ∃ x : R2, ∀ k : Branch, x ∈ recessionExampleStrictSublevelSet k ε := sorry

/-- The direction `e₁ + e₂` is a recession direction of the ambient set `R² = univ`. -/
theorem recessionExampleDirection_recedesIn_univ :
    (univ : Set R2).RecedesInDirection ℝ recessionExampleDirection := sorry

/-- The direction `e₁ + e₂` lies in the function recession cone of each branch, recorded in the
canonical Chapter 8 owner language. -/
-- Proof sketch: write `φ(s) = Real.sqrt (s ^ 2 + 1) - s`. The translate profiles of both branch
-- functions along `recessionExampleDirection` are obtained from the decreasing function `φ`, so
-- the corresponding recession-function values are nonpositive.
theorem recessionExampleDirection_mem_functionRecessionCone (k : Branch) :
    recessionExampleDirection ∈ recessionExampleBranchRecessionCone k :=
  sorry

/-- Text 21.3.4 supplies an explicit common nonpositive recession direction for the two-branch
family, thereby witnessing failure of the no-common-recession hypothesis in Theorem 21.3. -/
theorem recessionExample_exists_common_nonpositive_recession_direction :
    ∃ y : R2,
      (univ : Set R2).RecedesInDirection ℝ y ∧
        ∀ k : Branch,
          y ∈ recessionExampleBranchRecessionCone k :=
  sorry

end
