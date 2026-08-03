import Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_definition_3_15_extra_1
import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped MixedIntegerNotation

-- This file reuses the chapter's canonical `MixedRealPoint` / `mixed_integer_lattice` owners,
-- the generic projection API `mem_image_fst_iff`, and the `is_free_of` /
-- `is_maximal_free_of` owners from Theorem 6.18. Full-dimensionality is kept explicit via
-- `affineSpan ℝ C = ⊤`, matching the chapter's lattice-free API.

section Lemma617

variable {n p : ℕ}
variable {C : Set (MixedRealPoint p (n - p))}

/-- A set in `MixedRealPoint p (n - p)` is mixed-integer-free when its interior contains no point
of `ℤ^p × ℝ^(n - p)`. -/
def is_mixed_integer_free
    (C : Set (MixedRealPoint p (n - p))) : Prop :=
  is_free_of (ℤ^p×ℝ^(n - p)) C

/-- `is_mixed_integer_free C` unfolds to the assertion that no mixed-integer point lies in the
interior of `C`. -/
theorem is_mixed_integer_free_iff
    {C : Set (MixedRealPoint p (n - p))} :
    is_mixed_integer_free C ↔
      Disjoint (interior C) (ℤ^p×ℝ^(n - p)) :=
  Iff.rfl

/-- If `C` is mixed-integer-free, then no mixed-integer point lies in its interior. -/
theorem is_mixed_integer_free.not_mem_interior
    {C : Set (MixedRealPoint p (n - p))}
    (hC : is_mixed_integer_free C)
    {xy : MixedRealPoint p (n - p)}
    (hxy : xy ∈ ℤ^p×ℝ^(n - p)) :
    xy ∉ interior C :=
  is_free_of.not_mem_interior hC hxy

/-- A maximal mixed-integer-free convex set in `MixedRealPoint p (n - p)` is a convex
mixed-integer-free set that admits no larger convex mixed-integer-free superset. -/
def is_maximal_mixed_integer_free
    (C : Set (MixedRealPoint p (n - p))) : Prop :=
  is_maximal_free_of (ℤ^p×ℝ^(n - p)) C

/-- `is_maximal_mixed_integer_free C` unfolds to convexity, mixed-integer-freeness, and
maximality among convex mixed-integer-free supersets. -/
theorem is_maximal_mixed_integer_free_iff
    {C : Set (MixedRealPoint p (n - p))} :
    is_maximal_mixed_integer_free C ↔
      Convex ℝ C ∧
        is_mixed_integer_free C ∧
          ∀ C' : Set (MixedRealPoint p (n - p)),
            C ⊆ C' → Convex ℝ C' → is_mixed_integer_free C' → C' = C :=
  Iff.rfl

/-- A maximal mixed-integer-free set is convex. -/
theorem is_maximal_mixed_integer_free.convex
    {C : Set (MixedRealPoint p (n - p))}
    (hC : is_maximal_mixed_integer_free C) :
    Convex ℝ C :=
  is_maximal_free_of.convex hC

/-- A maximal mixed-integer-free set is mixed-integer-free. -/
theorem is_maximal_mixed_integer_free.mixed_integer_free
    {C : Set (MixedRealPoint p (n - p))}
    (hC : is_maximal_mixed_integer_free C) :
    is_mixed_integer_free C :=
  is_maximal_free_of.free hC

/-- Maximality among convex mixed-integer-free supersets gives equality with any larger convex
mixed-integer-free superset. -/
theorem is_maximal_mixed_integer_free.eq_of_subset
    {C C' : Set (MixedRealPoint p (n - p))}
    (hC : is_maximal_mixed_integer_free C)
    (hCC' : C ⊆ C')
    (hC'_convex : Convex ℝ C')
    (hC'_mixed_integer_free : is_mixed_integer_free C') :
    C' = C :=
  is_maximal_free_of.eq_of_subset hC hCC' hC'_convex hC'_mixed_integer_free

/-- Lemma 6.17 (1). Let `C` be a full-dimensional maximal `ℤ^p × ℝ^(n - p)`-free convex set and
let `Prod.fst '' C` be its orthogonal projection onto `ℝ^p`. Then this projection is a maximal
`ℤ^p`-free convex set. -/
theorem mixed_integer_projection_is_maximal_lattice_free
    (hfull : affineSpan ℝ C = ⊤)
    (hC : is_maximal_mixed_integer_free C) :
    is_maximal_lattice_free (Prod.fst '' C) := sorry

/-- Lemma 6.17 (2). Let `C` be a full-dimensional maximal `ℤ^p × ℝ^(n - p)`-free convex set and
let `Prod.fst '' C` be its orthogonal projection onto `ℝ^p`. Then
`C = (Prod.fst '' C) × ℝ^(n - p)`, represented here as the mixed-integer cylinder over the
projection. -/
theorem eq_mixed_integer_cylinder_of_full_dimensional_maximal_mixed_integer_free
    (hfull : affineSpan ℝ C = ⊤)
    (hC : is_maximal_mixed_integer_free C) :
    C = (Prod.fst '' C) ×ˢ (Set.univ : Set (Fin (n - p) → ℝ)) := sorry

end Lemma617
