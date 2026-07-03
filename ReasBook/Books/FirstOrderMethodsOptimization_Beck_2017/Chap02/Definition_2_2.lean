import FirstOrderMethodsinOptimization.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {α : Type u}

section

variable [TopologicalSpace α]

/- Definition 2.2: the textbook notion of a closed extended-real-valued function is the
canonical predicate `LowerSemicontinuous`; for `EReal`-valued functions, mathlib identifies this
with closedness of the epigraph. -/
#check (LowerSemicontinuous : (α → EReal) → Prop)

/- Closed epigraphs are the canonical source-facing characterization of lower semicontinuity for
`EReal`-valued functions. -/
recall lowerSemicontinuous_iff_isClosed_epigraph

end

/-- The extended-real-valued indicator function of a set, equal to `0` on the set and `⊤`
outside it. -/
noncomputable def extendedIndicator (C : Set α) : α → EReal :=
  open scoped Classical in
  C.piecewise (fun _ ↦ (0 : EReal)) fun _ ↦ (⊤ : EReal)

-- Proof sketch: unfold both owners; on `C` the indicator value is `0 < ⊤`, while outside `C` the
-- value is `⊤`, so the effective-domain inequality fails.
/-- The effective domain of the indicator function `δ_C` is exactly the set `C`. -/
@[simp] theorem effective_domain_extendedIndicator (C : Set α) :
    effective_domain (extendedIndicator C) = C := by
  ext x
  by_cases hx : x ∈ C <;> simp [effective_domain, extendedIndicator, hx]

section

variable [TopologicalSpace α]

-- Proof sketch: analyze the sublevel sets of `extendedIndicator C`: they are `∅` below `0`,
-- equal to `C` on every interval `[0, y]` with `y < ⊤`, and equal to `Set.univ` at `⊤`; then use
-- the closed-sublevel-set characterization of `LowerSemicontinuous`.
/-- The indicator function `δ_C` is closed, equivalently lower
semicontinuous, if and only if the underlying set `C` is closed. -/
theorem extendedIndicator_lowerSemicontinuous_iff_isClosed (C : Set α) :
    LowerSemicontinuous (extendedIndicator C) ↔ IsClosed C := sorry

end
