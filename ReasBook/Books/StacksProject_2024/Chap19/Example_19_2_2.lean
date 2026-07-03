import Mathlib
import StacksProject_2024.Chap19.«19_2_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open scoped CategoryTheory

/- Domain-style sampling for Example 19.2.2:
- primary domain: quotient sets in `Type`, sequential colimits, and the represented-Hom
  comparison `colimit.post B (coyoneda.obj (op A))`;
- sampled owner declarations:
  `Quotient.map`,
  `Functor.ofSequence`,
  `colimit.post`,
  `colimit_post_coyoneda_ι_app`;
- best owner abstractions:
  the source-facing quotient stage `collapsedInitialSegment n` and the canonical comparison map
  `colimit.post collapsedInitialSegmentDiagram (coyoneda.obj (op ℕ))`;
- primitive data: the quotient relation collapsing the initial segment `{0, …, n}`;
- derived API: the quotient projection, the collapsed class, the transition maps induced by
  monotonicity of the collapsed segment, and the comparison map from `19.2.0.1`.

Source/core/bridge triage:
- `source-facing`: the sequential quotient system `B_{n + 1}` and the noninjectivity example;
- `core/canonical`: `colimit.post`;
- `bridge/view`: the quotient projection `ℕ → B_{n + 1}` and the constant map at the collapsed
  class.

The raw owner name `collapsedInitialSegment` is already short and stable on this small local API
surface, so no extra `B_n` notation is introduced here.
-/

/-- The equivalence relation on `ℕ` that identifies all elements of the initial segment
`{0, …, n}` and leaves larger elements distinct. -/
def collapsedInitialSegmentSetoid (n : ℕ) : Setoid ℕ where
  r a b := a = b ∨ a ≤ n ∧ b ≤ n
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact Or.inl rfl
    · intro a b h
      rcases h with rfl | ⟨ha, hb⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hb, ha⟩
    · intro a b c hab hbc
      rcases hab with rfl | ⟨ha, hb⟩
      · exact hbc
      · rcases hbc with rfl | ⟨_, hc⟩
        · exact Or.inr ⟨ha, hb⟩
        · exact Or.inr ⟨ha, hc⟩

/-- The quotient set obtained by collapsing the first `n + 1` natural numbers to a single point.
This is the Lean stage indexed by `n`, corresponding to the textbook family `B_{n + 1}`. -/
abbrev collapsedInitialSegment (n : ℕ) : Type :=
  Quotient (collapsedInitialSegmentSetoid n)

/-- The natural quotient projection `ℕ → B_{n + 1}`. -/
def collapsedInitialSegmentProjection (n : ℕ) : ℕ → collapsedInitialSegment n :=
  Quotient.mk _

/-- The collapsed class of the initial segment `{0, …, n}` in `B_{n + 1}`. -/
def collapsedInitialSegmentCollapsedPoint (n : ℕ) : collapsedInitialSegment n :=
  collapsedInitialSegmentProjection n 0

/-- The constant map to the collapsed class in `B_{n + 1}`. -/
def collapsedInitialSegmentCollapsedMap (n : ℕ) : ℕ → collapsedInitialSegment n :=
  fun _ ↦ collapsedInitialSegmentCollapsedPoint n

/-- For `n ≤ m`, the quotient map `B_{n + 1} → B_{m + 1}` induced by collapsing a larger initial
segment. -/
def collapsedInitialSegmentMap {n m : ℕ} (h : n ≤ m) :
    collapsedInitialSegment n → collapsedInitialSegment m :=
  Quotient.map id <| by
    intro a b hab
    rcases hab with rfl | ⟨ha, hb⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨Nat.le_trans ha h, Nat.le_trans hb h⟩

/-- The successor transition `B_{n + 1} → B_{n + 2}` in the collapsed-initial-segment system. -/
def collapsedInitialSegmentStep (n : ℕ) :
    collapsedInitialSegment n → collapsedInitialSegment (n + 1) :=
  collapsedInitialSegmentMap (Nat.le_succ n)

/-- The sequential system `B_{n + 1}` of collapsed initial segments of the natural numbers. -/
def collapsedInitialSegmentDiagram : ℕ ⥤ Type :=
  Functor.ofSequence collapsedInitialSegmentStep

-- Proof sketch: every class in some stage eventually maps to the collapsed point, so in the
-- filtered colimit all representatives become equal to that distinguished class.
/-- Any two points in the colimit of the collapsed-initial-segment system are equal. -/
theorem collapsedInitialSegmentDiagram_colimit_subsingleton :
    Subsingleton (colimit collapsedInitialSegmentDiagram) := sorry

-- Proof sketch: compare the classes in `colim_n Mor(ℕ, B_{n + 1})` represented by the quotient
-- projections `ℕ → B_{n + 1}` and by the constant maps to the collapsed class. They remain
-- distinct in the Hom-colimit, but after composing with the colimit cocone they both become the
-- unique map from `ℕ` to the one-point colimit of the `B_{n + 1}`.
/-- Example 19.2.2: for the sequential system `B_{n + 1}` obtained by collapsing the first
`n + 1` natural numbers, the canonical comparison map
`colim_n Mor(ℕ, B_{n + 1}) → Mor(ℕ, colim_n B_{n + 1})` is not injective. -/
theorem collapsedInitialSegment_hom_colimit_comparison_not_injective :
    ¬ Function.Injective
      (colimit.post collapsedInitialSegmentDiagram (coyoneda.obj (op ℕ))) := sorry
