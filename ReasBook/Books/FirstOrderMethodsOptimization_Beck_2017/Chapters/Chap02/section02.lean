import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_2 (from Chap02) -/
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

/-! ### Lemma_2_2 (from Chap02) -/
open scoped Pointwise

/- Lemma 2.2: the Minkowski sum is the canonical pointwise addition of sets in scope
`Pointwise`; the owner declaration `Set.image2_add` identifies it with the binary image
`Set.image2 (· + ·)`. -/
recall Set.image2_add

/- Membership in the Minkowski sum is the canonical owner theorem `Set.mem_add`. -/
recall Set.mem_add

/-! ### Proposition_2_2 (from Chap02) -/
open scoped BigOperators

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E] {f : E → EReal}

-- Proof sketch: use the convexity of the real epigraph from `hf` and show that the convex
-- combination of the points `(x i, f (x i))` with weights `λ` again belongs to the epigraph. The
-- first coordinate is `∑ i, λ i • x i`, while the second coordinate is
-- `∑ i, ((λ i : EReal) * f (x i))`, giving the desired inequality.
/-- Proposition 2.2: Jensen's inequality for a convex extended-real-valued function. If
`λ : stdSimplex ℝ (Fin k)` is the textbook simplex vector `Δ_k`, then
`f (∑ i, λ i • x i) ≤ ∑ i, (λ i : EReal) * f (x i)`. -/
theorem convex_function_jensen_inequality {k : ℕ} (hf : is_convex_function f)
    (x : Fin k → E) (w : stdSimplex ℝ (Fin k)) :
    f (∑ i, w i • x i) ≤ ∑ i, ((w i : EReal) * f (x i)) := sorry

end

/-! ### Theorem_2_2 (from Chap02) -/
open Set

universe u

section

variable {X : Type u}

/-- The source-facing real epigraph of an extended-real-valued function. -/
def realEpigraph (f : X → EReal) : Set (X × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

end

section

variable {X : Type u} [TopologicalSpace X]

-- Proof sketch: compare the real epigraph with the canonical `EReal`-valued epigraph via the
-- continuous embedding `ℝ → EReal`, then invoke
-- `lowerSemicontinuous_iff_isClosed_epigraph`.
/-- A function `f : X → EReal` is lower semicontinuous exactly when its real epigraph is closed. -/
theorem lowerSemicontinuous_iff_isClosed_real_epigraph (f : X → EReal) :
    LowerSemicontinuous f ↔ IsClosed (realEpigraph f) := sorry

-- Proof sketch: use `lowerSemicontinuous_iff_isClosed_preimage` for the easy direction, and for
-- the converse recover the `EReal`-sublevel sets from the real ones, treating `⊤` trivially and
-- `⊥` as an intersection of real sublevel sets.
/-- A function `f : X → EReal` is lower semicontinuous exactly when all of its real sublevel sets
are closed. -/
theorem lowerSemicontinuous_iff_isClosed_real_sublevelSets (f : X → EReal) :
    LowerSemicontinuous f ↔ ∀ a : ℝ, IsClosed (f ⁻¹' Iic (a : EReal)) := sorry

-- Proof sketch: combine `lowerSemicontinuous_iff_isClosed_real_epigraph` with
-- `lowerSemicontinuous_iff_isClosed_real_sublevelSets` and apply `List.TFAE`.
/-- Theorem 2.2: for an extended real-valued function, lower semicontinuity, closedness of the
real epigraph, and closedness of all real sublevel sets are equivalent. -/
theorem ereal_lowerSemicontinuous_tfae (f : X → EReal) :
    List.TFAE
      [LowerSemicontinuous f,
        IsClosed (realEpigraph f),
        ∀ a : ℝ, IsClosed (f ⁻¹' Iic (a : EReal))] := sorry

end
