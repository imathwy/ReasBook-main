import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
